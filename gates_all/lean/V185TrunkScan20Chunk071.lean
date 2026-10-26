import V185TrunkScan20Chunk070

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_431283 : List Nat := [1, 1, 1, 2, 3, 2, 4, 3, 3]
def baseStart_431283 : Nat := 118140960795 + 431283 * 2 ^ 59
def prefixEnd_431283 : Nat := 4983230072969 + 3 ^ 40 * 431283 * 2
def baseEnd_431283 : Nat := 196849312989458966203619

theorem tailTrace_431283 : CollatzResearch.WordTrace tailWord_431283 prefixEnd_431283 196849312989458966203619 := by
  unfold tailWord_431283
  simp only [CollatzResearch.WordTrace]
  refine ⟨15730183296542823117354503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10486788864361882078236335 15730183296542823117354503)
  ·
    refine ⟨23595274944814234676031755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15730183296542823117354503 23595274944814234676031755)
    ·
      refine ⟨35392912417221352014047633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23595274944814234676031755 35392912417221352014047633)
      ·
        refine ⟨26544684312916014010535725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35392912417221352014047633 26544684312916014010535725)
        ·
          refine ⟨9954256617343505253950897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26544684312916014010535725 9954256617343505253950897)
          ·
            refine ⟨7465692463007628940463173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9954256617343505253950897 7465692463007628940463173)
            ·
              refine ⟨1399817336813930426336845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7465692463007628940463173 1399817336813930426336845)
              ·
                refine ⟨524931501305223909876317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1399817336813930426336845 524931501305223909876317)
                ·
                  refine ⟨196849312989458966203619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 524931501305223909876317 196849312989458966203619)
                  ·
                    rfl

theorem cell20_431283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 3].length) (baseStart_431283 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431283 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431283 prefixEnd_431283 := by exact prefixLift 431283
  have htrace : WordTrace (prefixWord ++ tailWord_431283) baseStart_431283 baseEnd_431283 := by
    simpa [prefixWord, tailWord_431283, baseEnd_431283] using wordTrace_append hprefix tailTrace_431283
  have hstable : (prefixWord ++ tailWord_431283).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431283).length < 2 ^ (prefixWord ++ tailWord_431283).sum := by decide
  have hdescent : baseEnd_431283 < baseStart_431283 := by decide
  rcases family_descends (prefixWord ++ tailWord_431283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431317 : List Nat := [1, 3, 2, 4, 1, 3, 1, 2, 3]
def baseStart_431317 : Nat := 118140960795 + 431317 * 2 ^ 59
def prefixEnd_431317 : Nat := 4983230072969 + 3 ^ 40 * 431317 * 2
def baseEnd_431317 : Nat := 196864831515905959070147

theorem tailTrace_431317 : CollatzResearch.WordTrace tailWord_431317 prefixEnd_431317 196864831515905959070147 := by
  unfold tailWord_431317
  simp only [CollatzResearch.WordTrace]
  refine ⟨15731423378419646924092205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10487615585613097949394803 15731423378419646924092205)
  ·
    refine ⟨5899283766907367596534577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15731423378419646924092205 5899283766907367596534577)
    ·
      refine ⟨4424462825180525697400933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5899283766907367596534577 4424462825180525697400933)
      ·
        refine ⟨829586779721348568262675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4424462825180525697400933 829586779721348568262675)
        ·
          refine ⟨1244380169582022852394013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 829586779721348568262675 1244380169582022852394013)
          ·
            refine ⟨466642563593258569647755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1244380169582022852394013 466642563593258569647755)
            ·
              refine ⟨699963845389887854471633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466642563593258569647755 699963845389887854471633)
              ·
                refine ⟨524972884042415890853725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 699963845389887854471633 524972884042415890853725)
                ·
                  refine ⟨196864831515905959070147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 524972884042415890853725 196864831515905959070147)
                  ·
                    rfl

theorem cell20_431317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_431317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431317 prefixEnd_431317 := by exact prefixLift 431317
  have htrace : WordTrace (prefixWord ++ tailWord_431317) baseStart_431317 baseEnd_431317 := by
    simpa [prefixWord, tailWord_431317, baseEnd_431317] using wordTrace_append hprefix tailTrace_431317
  have hstable : (prefixWord ++ tailWord_431317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431317).length < 2 ^ (prefixWord ++ tailWord_431317).sum := by decide
  have hdescent : baseEnd_431317 < baseStart_431317 := by decide
  rcases family_descends (prefixWord ++ tailWord_431317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431328 : List Nat := [2, 1, 1, 3, 1, 4, 1, 3, 4]
def baseStart_431328 : Nat := 118140960795 + 431328 * 2 ^ 59
def prefixEnd_431328 : Nat := 4983230072969 + 3 ^ 40 * 431328 * 2
def baseEnd_431328 : Nat := 196869852215638809703435

theorem tailTrace_431328 : CollatzResearch.WordTrace tailWord_431328 prefixEnd_431328 196869852215638809703435 := by
  unfold tailWord_431328
  simp only [CollatzResearch.WordTrace]
  refine ⟨7865912290689897901371319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10487883054253197201828425 7865912290689897901371319)
  ·
    refine ⟨11798868436034846852056979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7865912290689897901371319 11798868436034846852056979)
    ·
      refine ⟨17698302654052270278085469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11798868436034846852056979 17698302654052270278085469)
      ·
        refine ⟨6636863495269601354282051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17698302654052270278085469 6636863495269601354282051)
        ·
          refine ⟨9955295242904402031423077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6636863495269601354282051 9955295242904402031423077)
          ·
            refine ⟨1866617858044575380891827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9955295242904402031423077 1866617858044575380891827)
            ·
              refine ⟨2799926787066863071337741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1866617858044575380891827 2799926787066863071337741)
              ·
                refine ⟨1049972545150073651751653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2799926787066863071337741 1049972545150073651751653)
                ·
                  refine ⟨196869852215638809703435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1049972545150073651751653 196869852215638809703435)
                  ·
                    rfl

theorem cell20_431328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_431328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431328 prefixEnd_431328 := by exact prefixLift 431328
  have htrace : WordTrace (prefixWord ++ tailWord_431328) baseStart_431328 baseEnd_431328 := by
    simpa [prefixWord, tailWord_431328, baseEnd_431328] using wordTrace_append hprefix tailTrace_431328
  have hstable : (prefixWord ++ tailWord_431328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431328).length < 2 ^ (prefixWord ++ tailWord_431328).sum := by decide
  have hdescent : baseEnd_431328 < baseStart_431328 := by decide
  rcases family_descends (prefixWord ++ tailWord_431328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431411 : List Nat := [1, 1, 1, 2, 5, 2, 2, 6]
def baseStart_431411 : Nat := 118140960795 + 431411 * 2 ^ 59
def prefixEnd_431411 : Nat := 4983230072969 + 3 ^ 40 * 431411 * 2
def baseEnd_431411 : Nat := 65635911892419803312143

theorem tailTrace_431411 : CollatzResearch.WordTrace tailWord_431411 prefixEnd_431411 65635911892419803312143 := by
  unfold tailWord_431411
  simp only [CollatzResearch.WordTrace]
  refine ⟨15734851840079100978014087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10489901226719400652009391 15734851840079100978014087)
  ·
    refine ⟨23602277760118651467021131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15734851840079100978014087 23602277760118651467021131)
    ·
      refine ⟨35403416640177977200531697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23602277760118651467021131 35403416640177977200531697)
      ·
        refine ⟨26552562480133482900398773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35403416640177977200531697 26552562480133482900398773)
        ·
          refine ⟨2489302732512514021912385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26552562480133482900398773 2489302732512514021912385)
          ·
            refine ⟨1866977049384385516434289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2489302732512514021912385 1866977049384385516434289)
            ·
              refine ⟨1400232787038289137325717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1866977049384385516434289 1400232787038289137325717)
              ·
                refine ⟨65635911892419803312143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1400232787038289137325717 65635911892419803312143)
                ·
                  rfl

theorem cell20_431411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 6].length) (baseStart_431411 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431411 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431411 prefixEnd_431411 := by exact prefixLift 431411
  have htrace : WordTrace (prefixWord ++ tailWord_431411) baseStart_431411 baseEnd_431411 := by
    simpa [prefixWord, tailWord_431411, baseEnd_431411] using wordTrace_append hprefix tailTrace_431411
  have hstable : (prefixWord ++ tailWord_431411).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431411).length < 2 ^ (prefixWord ++ tailWord_431411).sum := by decide
  have hdescent : baseEnd_431411 < baseStart_431411 := by decide
  rcases family_descends (prefixWord ++ tailWord_431411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431428 : List Nat := [2, 3, 4, 1, 1, 9]
def baseStart_431428 : Nat := 118140960795 + 431428 * 2 ^ 59
def prefixEnd_431428 : Nat := 4983230072969 + 3 ^ 40 * 431428 * 2
def baseEnd_431428 : Nat := 7293166479277144680359

theorem tailTrace_431428 : CollatzResearch.WordTrace tailWord_431428 prefixEnd_431428 7293166479277144680359 := by
  unfold tailWord_431428
  simp only [CollatzResearch.WordTrace]
  refine ⟨7867735940508756440691469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10490314587345008587588625 7867735940508756440691469)
  ·
    refine ⟨2950400977690783665259301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7867735940508756440691469 2950400977690783665259301)
    ·
      refine ⟨553200183317021937236119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2950400977690783665259301 553200183317021937236119)
      ·
        refine ⟨829800274975532905854179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553200183317021937236119 829800274975532905854179)
        ·
          refine ⟨1244700412463299358781269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 829800274975532905854179 1244700412463299358781269)
          ·
            refine ⟨7293166479277144680359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1244700412463299358781269 7293166479277144680359)
            ·
              rfl

theorem cell20_431428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 9].length) (baseStart_431428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431428 prefixEnd_431428 := by exact prefixLift 431428
  have htrace : WordTrace (prefixWord ++ tailWord_431428) baseStart_431428 baseEnd_431428 := by
    simpa [prefixWord, tailWord_431428, baseEnd_431428] using wordTrace_append hprefix tailTrace_431428
  have hstable : (prefixWord ++ tailWord_431428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431428).length < 2 ^ (prefixWord ++ tailWord_431428).sum := by decide
  have hdescent : baseEnd_431428 < baseStart_431428 := by decide
  rcases family_descends (prefixWord ++ tailWord_431428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431430 : List Nat := [6, 1, 1, 3, 1, 2, 2, 2, 2]
def baseStart_431430 : Nat := 118140960795 + 431430 * 2 ^ 59
def prefixEnd_431430 : Nat := 4983230072969 + 3 ^ 40 * 431430 * 2
def baseEnd_431430 : Nat := 196916407794979788303019

theorem tailTrace_431430 : CollatzResearch.WordTrace tailWord_431430 prefixEnd_431430 196916407794979788303019 := by
  unfold tailWord_431430
  simp only [CollatzResearch.WordTrace]
  refine ⟨491735775844070850717367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10490363218006844815303829 491735775844070850717367)
  ·
    refine ⟨737603663766106276076051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 491735775844070850717367 737603663766106276076051)
    ·
      refine ⟨1106405495649159414114077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 737603663766106276076051 1106405495649159414114077)
      ·
        refine ⟨414902060868434780292779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1106405495649159414114077 414902060868434780292779)
        ·
          refine ⟨622353091302652170439169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414902060868434780292779 622353091302652170439169)
          ·
            refine ⟨466764818476989127829377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 622353091302652170439169 466764818476989127829377)
            ·
              refine ⟨350073613857741845872033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466764818476989127829377 350073613857741845872033)
              ·
                refine ⟨262555210393306384404025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350073613857741845872033 262555210393306384404025)
                ·
                  refine ⟨196916407794979788303019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 262555210393306384404025 196916407794979788303019)
                  ·
                    rfl

theorem cell20_431430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_431430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431430 prefixEnd_431430 := by exact prefixLift 431430
  have htrace : WordTrace (prefixWord ++ tailWord_431430) baseStart_431430 baseEnd_431430 := by
    simpa [prefixWord, tailWord_431430, baseEnd_431430] using wordTrace_append hprefix tailTrace_431430
  have hstable : (prefixWord ++ tailWord_431430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431430).length < 2 ^ (prefixWord ++ tailWord_431430).sum := by decide
  have hdescent : baseEnd_431430 < baseStart_431430 := by decide
  rcases family_descends (prefixWord ++ tailWord_431430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431442 : List Nat := [3, 2, 2, 1, 1, 1, 1, 5, 4]
def baseStart_431442 : Nat := 118140960795 + 431442 * 2 ^ 59
def prefixEnd_431442 : Nat := 4983230072969 + 3 ^ 40 * 431442 * 2
def baseEnd_431442 : Nat := 196921884921961079902969

theorem tailTrace_431442 : CollatzResearch.WordTrace tailWord_431442 prefixEnd_431442 196921884921961079902969 := by
  unfold tailWord_431442
  simp only [CollatzResearch.WordTrace]
  refine ⟨3933995625741698318098145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10490655001977862181595053 3933995625741698318098145)
  ·
    refine ⟨2950496719306273738573609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3933995625741698318098145 2950496719306273738573609)
    ·
      refine ⟨2212872539479705303930207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2950496719306273738573609 2212872539479705303930207)
      ·
        refine ⟨3319308809219557955895311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2212872539479705303930207 3319308809219557955895311)
        ·
          refine ⟨4978963213829336933842967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3319308809219557955895311 4978963213829336933842967)
          ·
            refine ⟨7468444820744005400764451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4978963213829336933842967 7468444820744005400764451)
            ·
              refine ⟨11202667231116008101146677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7468444820744005400764451 11202667231116008101146677)
              ·
                refine ⟨1050250052917125759482501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11202667231116008101146677 1050250052917125759482501)
                ·
                  refine ⟨196921884921961079902969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1050250052917125759482501 196921884921961079902969)
                  ·
                    rfl

theorem cell20_431442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_431442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431442 prefixEnd_431442 := by exact prefixLift 431442
  have htrace : WordTrace (prefixWord ++ tailWord_431442) baseStart_431442 baseEnd_431442 := by
    simpa [prefixWord, tailWord_431442, baseEnd_431442] using wordTrace_append hprefix tailTrace_431442
  have hstable : (prefixWord ++ tailWord_431442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431442).length < 2 ^ (prefixWord ++ tailWord_431442).sum := by decide
  have hdescent : baseEnd_431442 < baseStart_431442 := by decide
  rcases family_descends (prefixWord ++ tailWord_431442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431449 : List Nat := [1, 2, 1, 2, 2, 2, 5, 5]
def baseStart_431449 : Nat := 118140960795 + 431449 * 2 ^ 59
def prefixEnd_431449 : Nat := 4983230072969 + 3 ^ 40 * 431449 * 2
def baseEnd_431449 : Nat := 65641693304233388889869

theorem tailTrace_431449 : CollatzResearch.WordTrace tailWord_431449 prefixEnd_431449 65641693304233388889869 := by
  unfold tailWord_431449
  simp only [CollatzResearch.WordTrace]
  refine ⟨15736237813941433467897401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10490825209294288978598267 15736237813941433467897401)
  ·
    refine ⟨11802178360456075100923051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15736237813941433467897401 11802178360456075100923051)
    ·
      refine ⟨17703267540684112651384577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11802178360456075100923051 17703267540684112651384577)
      ·
        refine ⟨13277450655513084488538433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17703267540684112651384577 13277450655513084488538433)
        ·
          refine ⟨9958087991634813366403825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13277450655513084488538433 9958087991634813366403825)
          ·
            refine ⟨7468565993726110024802869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9958087991634813366403825 7468565993726110024802869)
            ·
              refine ⟨700178061911822814825269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7468565993726110024802869 700178061911822814825269)
              ·
                refine ⟨65641693304233388889869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 700178061911822814825269 65641693304233388889869)
                ·
                  rfl

theorem cell20_431449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 5].length) (baseStart_431449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431449 prefixEnd_431449 := by exact prefixLift 431449
  have htrace : WordTrace (prefixWord ++ tailWord_431449) baseStart_431449 baseEnd_431449 := by
    simpa [prefixWord, tailWord_431449, baseEnd_431449] using wordTrace_append hprefix tailTrace_431449
  have hstable : (prefixWord ++ tailWord_431449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431449).length < 2 ^ (prefixWord ++ tailWord_431449).sum := by decide
  have hdescent : baseEnd_431449 < baseStart_431449 := by decide
  rcases family_descends (prefixWord ++ tailWord_431449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431497 : List Nat := [1, 2, 1, 1, 7, 1, 2, 1, 4]
def baseStart_431497 : Nat := 118140960795 + 431497 * 2 ^ 59
def prefixEnd_431497 : Nat := 4983230072969 + 3 ^ 40 * 431497 * 2
def baseEnd_431497 : Nat := 196946988420625333069411

theorem tailTrace_431497 : CollatzResearch.WordTrace tailWord_431497 prefixEnd_431497 196946988420625333069411 := by
  unfold tailWord_431497
  simp only [CollatzResearch.WordTrace]
  refine ⟨15737988517767537665644745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10491992345178358443763163 15737988517767537665644745)
  ·
    refine ⟨11803491388325653249233559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15737988517767537665644745 11803491388325653249233559)
    ·
      refine ⟨17705237082488479873850339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11803491388325653249233559 17705237082488479873850339)
      ·
        refine ⟨26557855623732719810775509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17705237082488479873850339 26557855623732719810775509)
        ·
          refine ⟨622449741181235620565051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 26557855623732719810775509 622449741181235620565051)
          ·
            refine ⟨933674611771853430847577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622449741181235620565051 933674611771853430847577)
            ·
              refine ⟨700255958828890073135683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 933674611771853430847577 700255958828890073135683)
              ·
                refine ⟨1050383938243335109703525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 700255958828890073135683 1050383938243335109703525)
                ·
                  refine ⟨196946988420625333069411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1050383938243335109703525 196946988420625333069411)
                  ·
                    rfl

theorem cell20_431497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 4].length) (baseStart_431497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431497 prefixEnd_431497 := by exact prefixLift 431497
  have htrace : WordTrace (prefixWord ++ tailWord_431497) baseStart_431497 baseEnd_431497 := by
    simpa [prefixWord, tailWord_431497, baseEnd_431497] using wordTrace_append hprefix tailTrace_431497
  have hstable : (prefixWord ++ tailWord_431497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431497).length < 2 ^ (prefixWord ++ tailWord_431497).sum := by decide
  have hdescent : baseEnd_431497 < baseStart_431497 := by decide
  rcases family_descends (prefixWord ++ tailWord_431497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431532 : List Nat := [2, 2, 1, 1, 1, 1, 5, 2, 5]
def baseStart_431532 : Nat := 118140960795 + 431532 * 2 ^ 59
def prefixEnd_431532 : Nat := 4983230072969 + 3 ^ 40 * 431532 * 2
def baseEnd_431532 : Nat := 196962963374320766902601

theorem tailTrace_431532 : CollatzResearch.WordTrace tailWord_431532 prefixEnd_431532 196962963374320766902601 := by
  unfold tailWord_431532
  simp only [CollatzResearch.WordTrace]
  refine ⟨7869632536320369321584425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10492843381760492428779233 7869632536320369321584425)
  ·
    refine ⟨5902224402240276991188319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7869632536320369321584425 5902224402240276991188319)
    ·
      refine ⟨8853336603360415486782479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5902224402240276991188319 8853336603360415486782479)
      ·
        refine ⟨13280004905040623230173719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8853336603360415486782479 13280004905040623230173719)
        ·
          refine ⟨19920007357560934845260579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13280004905040623230173719 19920007357560934845260579)
          ·
            refine ⟨29880011036341402267890869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19920007357560934845260579 29880011036341402267890869)
            ·
              refine ⟨2801251034657006462614769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29880011036341402267890869 2801251034657006462614769)
              ·
                refine ⟨2100938275992754846961077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2801251034657006462614769 2100938275992754846961077)
                ·
                  refine ⟨196962963374320766902601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2100938275992754846961077 196962963374320766902601)
                  ·
                    rfl

theorem cell20_431532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_431532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431532 prefixEnd_431532 := by exact prefixLift 431532
  have htrace : WordTrace (prefixWord ++ tailWord_431532) baseStart_431532 baseEnd_431532 := by
    simpa [prefixWord, tailWord_431532, baseEnd_431532] using wordTrace_append hprefix tailTrace_431532
  have hstable : (prefixWord ++ tailWord_431532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431532).length < 2 ^ (prefixWord ++ tailWord_431532).sum := by decide
  have hdescent : baseEnd_431532 < baseStart_431532 := by decide
  rcases family_descends (prefixWord ++ tailWord_431532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431539 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 6]
def baseStart_431539 : Nat := 118140960795 + 431539 * 2 ^ 59
def prefixEnd_431539 : Nat := 4983230072969 + 3 ^ 40 * 431539 * 2
def baseEnd_431539 : Nat := 196966158365059853669239

theorem tailTrace_431539 : CollatzResearch.WordTrace tailWord_431539 prefixEnd_431539 196966158365059853669239 := by
  unfold tailWord_431539
  simp only [CollatzResearch.WordTrace]
  refine ⟨15739520383615378838673671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10493013589076919225782447 15739520383615378838673671)
  ·
    refine ⟨23609280575423068258010507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15739520383615378838673671 23609280575423068258010507)
    ·
      refine ⟨35413920863134602387015761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23609280575423068258010507 35413920863134602387015761)
      ·
        refine ⟨26560440647350951790261821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35413920863134602387015761 26560440647350951790261821)
        ·
          refine ⟨9960165242756606921348183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26560440647350951790261821 9960165242756606921348183)
          ·
            refine ⟨14940247864134910382022275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9960165242756606921348183 14940247864134910382022275)
            ·
              refine ⟨22410371796202365573033413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14940247864134910382022275 22410371796202365573033413)
              ·
                refine ⟨4201944711787943544943765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22410371796202365573033413 4201944711787943544943765)
                ·
                  refine ⟨196966158365059853669239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4201944711787943544943765 196966158365059853669239)
                  ·
                    rfl

theorem cell20_431539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 6].length) (baseStart_431539 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431539 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431539 prefixEnd_431539 := by exact prefixLift 431539
  have htrace : WordTrace (prefixWord ++ tailWord_431539) baseStart_431539 baseEnd_431539 := by
    simpa [prefixWord, tailWord_431539, baseEnd_431539] using wordTrace_append hprefix tailTrace_431539
  have hstable : (prefixWord ++ tailWord_431539).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431539).length < 2 ^ (prefixWord ++ tailWord_431539).sum := by decide
  have hdescent : baseEnd_431539 < baseStart_431539 := by decide
  rcases family_descends (prefixWord ++ tailWord_431539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431549 : List Nat := [1, 4, 1, 2, 2, 1, 2, 4, 3]
def baseStart_431549 : Nat := 118140960795 + 431549 * 2 ^ 59
def prefixEnd_431549 : Nat := 4983230072969 + 3 ^ 40 * 431549 * 2
def baseEnd_431549 : Nat := 196970722637544263335865

theorem tailTrace_431549 : CollatzResearch.WordTrace tailWord_431549 prefixEnd_431549 196970722637544263335865 := by
  unfold tailWord_431549
  simp only [CollatzResearch.WordTrace]
  refine ⟨15739885113579150546537701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10493256742386100364358467 15739885113579150546537701)
  ·
    refine ⟨2951228458796090727475819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15739885113579150546537701 2951228458796090727475819)
    ·
      refine ⟨4426842688194136091213729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2951228458796090727475819 4426842688194136091213729)
      ·
        refine ⟨3320132016145602068410297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4426842688194136091213729 3320132016145602068410297)
        ·
          refine ⟨2490099012109201551307723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3320132016145602068410297 2490099012109201551307723)
          ·
            refine ⟨3735148518163802326961585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2490099012109201551307723 3735148518163802326961585)
            ·
              refine ⟨2801361388622851745221189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3735148518163802326961585 2801361388622851745221189)
              ·
                refine ⟨525255260366784702228973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2801361388622851745221189 525255260366784702228973)
                ·
                  refine ⟨196970722637544263335865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 525255260366784702228973 196970722637544263335865)
                  ·
                    rfl

theorem cell20_431549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_431549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431549 prefixEnd_431549 := by exact prefixLift 431549
  have htrace : WordTrace (prefixWord ++ tailWord_431549) baseStart_431549 baseEnd_431549 := by
    simpa [prefixWord, tailWord_431549, baseEnd_431549] using wordTrace_append hprefix tailTrace_431549
  have hstable : (prefixWord ++ tailWord_431549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431549).length < 2 ^ (prefixWord ++ tailWord_431549).sum := by decide
  have hdescent : baseEnd_431549 < baseStart_431549 := by decide
  rcases family_descends (prefixWord ++ tailWord_431549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431566 : List Nat := [4, 1, 1, 1, 2, 1, 6, 1, 3]
def baseStart_431566 : Nat := 118140960795 + 431566 * 2 ^ 59
def prefixEnd_431566 : Nat := 4983230072969 + 3 ^ 40 * 431566 * 2
def baseEnd_431566 : Nat := 196978481900767759769129

theorem tailTrace_431566 : CollatzResearch.WordTrace tailWord_431566 prefixEnd_431566 196978481900767759769129 := by
  unfold tailWord_431566
  simp only [CollatzResearch.WordTrace]
  refine ⟨1967563144314695306238319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10493670103011708299937701 1967563144314695306238319)
  ·
    refine ⟨2951344716472042959357479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1967563144314695306238319 2951344716472042959357479)
    ·
      refine ⟨4427017074708064439036219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2951344716472042959357479 4427017074708064439036219)
      ·
        refine ⟨6640525612062096658554329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4427017074708064439036219 6640525612062096658554329)
        ·
          refine ⟨4980394209046572493915747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6640525612062096658554329 4980394209046572493915747)
          ·
            refine ⟨7470591313569858740873621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4980394209046572493915747 7470591313569858740873621)
            ·
              refine ⟨350183967823587128478451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7470591313569858740873621 350183967823587128478451)
              ·
                refine ⟨525275951735380692717677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350183967823587128478451 525275951735380692717677)
                ·
                  refine ⟨196978481900767759769129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 525275951735380692717677 196978481900767759769129)
                  ·
                    rfl

theorem cell20_431566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_431566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431566 prefixEnd_431566 := by exact prefixLift 431566
  have htrace : WordTrace (prefixWord ++ tailWord_431566) baseStart_431566 baseEnd_431566 := by
    simpa [prefixWord, tailWord_431566, baseEnd_431566] using wordTrace_append hprefix tailTrace_431566
  have hstable : (prefixWord ++ tailWord_431566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431566).length < 2 ^ (prefixWord ++ tailWord_431566).sum := by decide
  have hdescent : baseEnd_431566 < baseStart_431566 := by decide
  rcases family_descends (prefixWord ++ tailWord_431566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431614 : List Nat := [4, 2, 2, 3, 1, 2, 1, 5]
def baseStart_431614 : Nat := 118140960795 + 431614 * 2 ^ 59
def prefixEnd_431614 : Nat := 4983230072969 + 3 ^ 40 * 431614 * 2
def baseEnd_431614 : Nat := 65666796802897642056311

theorem tailTrace_431614 : CollatzResearch.WordTrace tailWord_431614 prefixEnd_431614 65666796802897642056311 := by
  unfold tailWord_431614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1967781982292958330956737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10494837238895777765102597 1967781982292958330956737)
  ·
    refine ⟨1475836486719718748217553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1967781982292958330956737 1475836486719718748217553)
    ·
      refine ⟨1106877365039789061163165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1475836486719718748217553 1106877365039789061163165)
      ·
        refine ⟨415079011889920897936187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1106877365039789061163165 415079011889920897936187)
        ·
          refine ⟨622618517834881346904281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415079011889920897936187 622618517834881346904281)
          ·
            refine ⟨466963888376161010178211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 622618517834881346904281 466963888376161010178211)
            ·
              refine ⟨700445832564241515267317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466963888376161010178211 700445832564241515267317)
              ·
                refine ⟨65666796802897642056311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 700445832564241515267317 65666796802897642056311)
                ·
                  rfl

theorem cell20_431614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_431614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431614 prefixEnd_431614 := by exact prefixLift 431614
  have htrace : WordTrace (prefixWord ++ tailWord_431614) baseStart_431614 baseEnd_431614 := by
    simpa [prefixWord, tailWord_431614, baseEnd_431614] using wordTrace_append hprefix tailTrace_431614
  have hstable : (prefixWord ++ tailWord_431614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431614).length < 2 ^ (prefixWord ++ tailWord_431614).sum := by decide
  have hdescent : baseEnd_431614 < baseStart_431614 := by decide
  rcases family_descends (prefixWord ++ tailWord_431614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431649 : List Nat := [1, 2, 3, 2, 2, 2, 1, 5, 2]
def baseStart_431649 : Nat := 118140960795 + 431649 * 2 ^ 59
def prefixEnd_431649 : Nat := 4983230072969 + 3 ^ 40 * 431649 * 2
def baseEnd_431649 : Nat := 197016365362388360002123

theorem tailTrace_431649 : CollatzResearch.WordTrace tailWord_431649 prefixEnd_431649 197016365362388360002123 := by
  unfold tailWord_431649
  simp only [CollatzResearch.WordTrace]
  refine ⟨15743532413216867625178001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10495688275477911750118667 15743532413216867625178001)
  ·
    refine ⟨11807649309912650718883501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15743532413216867625178001 11807649309912650718883501)
    ·
      refine ⟨4427868491217244019581313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11807649309912650718883501 4427868491217244019581313)
      ·
        refine ⟨3320901368412933014685985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4427868491217244019581313 3320901368412933014685985)
        ·
          refine ⟨2490676026309699761014489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3320901368412933014685985 2490676026309699761014489)
          ·
            refine ⟨1868007019732274820760867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2490676026309699761014489 1868007019732274820760867)
            ·
              refine ⟨2802010529598412231141301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1868007019732274820760867 2802010529598412231141301)
              ·
                refine ⟨262688487149851146669497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2802010529598412231141301 262688487149851146669497)
                ·
                  refine ⟨197016365362388360002123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 262688487149851146669497 197016365362388360002123)
                  ·
                    rfl

theorem cell20_431649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 5, 2].length) (baseStart_431649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431649 prefixEnd_431649 := by exact prefixLift 431649
  have htrace : WordTrace (prefixWord ++ tailWord_431649) baseStart_431649 baseEnd_431649 := by
    simpa [prefixWord, tailWord_431649, baseEnd_431649] using wordTrace_append hprefix tailTrace_431649
  have hstable : (prefixWord ++ tailWord_431649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431649).length < 2 ^ (prefixWord ++ tailWord_431649).sum := by decide
  have hdescent : baseEnd_431649 < baseStart_431649 := by decide
  rcases family_descends (prefixWord ++ tailWord_431649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431653 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 8]
def baseStart_431653 : Nat := 118140960795 + 431653 * 2 ^ 59
def prefixEnd_431653 : Nat := 4983230072969 + 3 ^ 40 * 431653 * 2
def baseEnd_431653 : Nat := 197018191071382123868773

theorem tailTrace_431653 : CollatzResearch.WordTrace tailWord_431653 prefixEnd_431653 197018191071382123868773 := by
  unfold tailWord_431653
  simp only [CollatzResearch.WordTrace]
  refine ⟨15743678305202376308323613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10495785536801584205549075 15743678305202376308323613)
  ·
    refine ⟨5903879364450891115621355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15743678305202376308323613 5903879364450891115621355)
    ·
      refine ⟨8855819046676336673432033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5903879364450891115621355 8855819046676336673432033)
      ·
        refine ⟨6641864285007252505074025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8855819046676336673432033 6641864285007252505074025)
        ·
          refine ⟨4981398213755439378805519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6641864285007252505074025 4981398213755439378805519)
          ·
            refine ⟨7472097320633159068208279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4981398213755439378805519 7472097320633159068208279)
            ·
              refine ⟨11208145980949738602312419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7472097320633159068208279 11208145980949738602312419)
              ·
                refine ⟨16812218971424607903468629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11208145980949738602312419 16812218971424607903468629)
                ·
                  refine ⟨197018191071382123868773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16812218971424607903468629 197018191071382123868773)
                  ·
                    rfl

theorem cell20_431653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_431653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431653 prefixEnd_431653 := by exact prefixLift 431653
  have htrace : WordTrace (prefixWord ++ tailWord_431653) baseStart_431653 baseEnd_431653 := by
    simpa [prefixWord, tailWord_431653, baseEnd_431653] using wordTrace_append hprefix tailTrace_431653
  have hstable : (prefixWord ++ tailWord_431653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431653).length < 2 ^ (prefixWord ++ tailWord_431653).sum := by decide
  have hdescent : baseEnd_431653 < baseStart_431653 := by decide
  rcases family_descends (prefixWord ++ tailWord_431653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431656 : List Nat := [2, 1, 5, 2, 2, 1, 7]
def baseStart_431656 : Nat := 118140960795 + 431656 * 2 ^ 59
def prefixEnd_431656 : Nat := 4983230072969 + 3 ^ 40 * 431656 * 2
def baseEnd_431656 : Nat := 21891062261458605196529

theorem tailTrace_431656 : CollatzResearch.WordTrace tailWord_431656 prefixEnd_431656 21891062261458605196529 := by
  unfold tailWord_431656
  simp only [CollatzResearch.WordTrace]
  refine ⟨7871893862095753910341411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10495858482794338547121881 7871893862095753910341411)
  ·
    refine ⟨11807840793143630865512117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7871893862095753910341411 11807840793143630865512117)
    ·
      refine ⟨1106985074357215393641761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11807840793143630865512117 1106985074357215393641761)
      ·
        refine ⟨830238805767911545231321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1106985074357215393641761 830238805767911545231321)
        ·
          refine ⟨622679104325933658923491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 830238805767911545231321 622679104325933658923491)
          ·
            refine ⟨934018656488900488385237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622679104325933658923491 934018656488900488385237)
            ·
              refine ⟨21891062261458605196529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 934018656488900488385237 21891062261458605196529)
              ·
                rfl

theorem cell20_431656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 7].length) (baseStart_431656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431656 prefixEnd_431656 := by exact prefixLift 431656
  have htrace : WordTrace (prefixWord ++ tailWord_431656) baseStart_431656 baseEnd_431656 := by
    simpa [prefixWord, tailWord_431656, baseEnd_431656] using wordTrace_append hprefix tailTrace_431656
  have hstable : (prefixWord ++ tailWord_431656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431656).length < 2 ^ (prefixWord ++ tailWord_431656).sum := by decide
  have hdescent : baseEnd_431656 < baseStart_431656 := by decide
  rcases family_descends (prefixWord ++ tailWord_431656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431715 : List Nat := [1, 1, 1, 5, 1, 5, 6]
def baseStart_431715 : Nat := 118140960795 + 431715 * 2 ^ 59
def prefixEnd_431715 : Nat := 4983230072969 + 3 ^ 40 * 431715 * 2
def baseEnd_431715 : Nat := 21894054395642829311317

theorem tailTrace_431715 : CollatzResearch.WordTrace tailWord_431715 prefixEnd_431715 21894054395642829311317 := by
  unfold tailWord_431715
  simp only [CollatzResearch.WordTrace]
  refine ⟨15745939630977760897080599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10497293087318507264720399 15745939630977760897080599)
  ·
    refine ⟨23618909446466641345620899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15745939630977760897080599 23618909446466641345620899)
    ·
      refine ⟨35428364169699962018431349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23618909446466641345620899 35428364169699962018431349)
      ·
        refine ⟨3321409140909371439227939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35428364169699962018431349 3321409140909371439227939)
        ·
          refine ⟨4982113711364057158841909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3321409140909371439227939 4982113711364057158841909)
          ·
            refine ⟨467073160440380358641429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4982113711364057158841909 467073160440380358641429)
            ·
              refine ⟨21894054395642829311317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 467073160440380358641429 21894054395642829311317)
              ·
                rfl

theorem cell20_431715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 6].length) (baseStart_431715 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431715 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431715 prefixEnd_431715 := by exact prefixLift 431715
  have htrace : WordTrace (prefixWord ++ tailWord_431715) baseStart_431715 baseEnd_431715 := by
    simpa [prefixWord, tailWord_431715, baseEnd_431715] using wordTrace_append hprefix tailTrace_431715
  have hstable : (prefixWord ++ tailWord_431715).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431715).length < 2 ^ (prefixWord ++ tailWord_431715).sum := by decide
  have hdescent : baseEnd_431715 < baseStart_431715 := by decide
  rcases family_descends (prefixWord ++ tailWord_431715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431777 : List Nat := [1, 2, 3, 3, 2, 1, 1, 4, 3]
def baseStart_431777 : Nat := 118140960795 + 431777 * 2 ^ 59
def prefixEnd_431777 : Nat := 4983230072969 + 3 ^ 40 * 431777 * 2
def baseEnd_431777 : Nat := 197074788050188803734933

theorem tailTrace_431777 : CollatzResearch.WordTrace tailWord_431777 prefixEnd_431777 197074788050188803734933 := by
  unfold tailWord_431777
  simp only [CollatzResearch.WordTrace]
  refine ⟨15748200956753145485837585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10498800637835430323891723 15748200956753145485837585)
  ·
    refine ⟨11811150717564859114378189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15748200956753145485837585 11811150717564859114378189)
    ·
      refine ⟨4429181519086822167891821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11811150717564859114378189 4429181519086822167891821)
      ·
        refine ⟨1660943069657558312959433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4429181519086822167891821 1660943069657558312959433)
        ·
          refine ⟨1245707302243168734719575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1660943069657558312959433 1245707302243168734719575)
          ·
            refine ⟨1868560953364753102079363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1245707302243168734719575 1868560953364753102079363)
            ·
              refine ⟨2802841430047129653119045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1868560953364753102079363 2802841430047129653119045)
              ·
                refine ⟨525532768133836809959821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2802841430047129653119045 525532768133836809959821)
                ·
                  refine ⟨197074788050188803734933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 525532768133836809959821 197074788050188803734933)
                  ·
                    rfl

theorem cell20_431777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 3].length) (baseStart_431777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431777 prefixEnd_431777 := by exact prefixLift 431777
  have htrace : WordTrace (prefixWord ++ tailWord_431777) baseStart_431777 baseEnd_431777 := by
    simpa [prefixWord, tailWord_431777, baseEnd_431777] using wordTrace_append hprefix tailTrace_431777
  have hstable : (prefixWord ++ tailWord_431777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431777).length < 2 ^ (prefixWord ++ tailWord_431777).sum := by decide
  have hdescent : baseEnd_431777 < baseStart_431777 := by decide
  rcases family_descends (prefixWord ++ tailWord_431777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431780 : List Nat := [2, 3, 1, 2, 2, 2, 4, 2, 2]
def baseStart_431780 : Nat := 118140960795 + 431780 * 2 ^ 59
def prefixEnd_431780 : Nat := 4983230072969 + 3 ^ 40 * 431780 * 2
def baseEnd_431780 : Nat := 197076157331934126634921

theorem tailTrace_431780 : CollatzResearch.WordTrace tailWord_431780 prefixEnd_431780 197076157331934126634921 := by
  unfold tailWord_431780
  simp only [CollatzResearch.WordTrace]
  refine ⟨7874155187871138499098397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10498873583828184665464529 7874155187871138499098397)
  ·
    refine ⟨2952808195451676937161899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7874155187871138499098397 2952808195451676937161899)
    ·
      refine ⟨4429212293177515405742849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2952808195451676937161899 4429212293177515405742849)
      ·
        refine ⟨3321909219883136554307137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4429212293177515405742849 3321909219883136554307137)
        ·
          refine ⟨2491431914912352415730353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3321909219883136554307137 2491431914912352415730353)
          ·
            refine ⟨1868573936184264311797765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2491431914912352415730353 1868573936184264311797765)
            ·
              refine ⟨350357613034549558462081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1868573936184264311797765 350357613034549558462081)
              ·
                refine ⟨262768209775912168846561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350357613034549558462081 262768209775912168846561)
                ·
                  refine ⟨197076157331934126634921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 262768209775912168846561 197076157331934126634921)
                  ·
                    rfl

theorem cell20_431780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_431780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431780 prefixEnd_431780 := by exact prefixLift 431780
  have htrace : WordTrace (prefixWord ++ tailWord_431780) baseStart_431780 baseEnd_431780 := by
    simpa [prefixWord, tailWord_431780, baseEnd_431780] using wordTrace_append hprefix tailTrace_431780
  have hstable : (prefixWord ++ tailWord_431780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431780).length < 2 ^ (prefixWord ++ tailWord_431780).sum := by decide
  have hdescent : baseEnd_431780 < baseStart_431780 := by decide
  rcases family_descends (prefixWord ++ tailWord_431780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431814 : List Nat := [6, 1, 2, 1, 1, 2, 2, 3, 2]
def baseStart_431814 : Nat := 118140960795 + 431814 * 2 ^ 59
def prefixEnd_431814 : Nat := 4983230072969 + 3 ^ 40 * 431814 * 2
def baseEnd_431814 : Nat := 197091675858381119501449

theorem tailTrace_431814 : CollatzResearch.WordTrace tailWord_431814 prefixEnd_431814 197091675858381119501449 := by
  unfold tailWord_431814
  simp only [CollatzResearch.WordTrace]
  refine ⟨492173451800596900154203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10499700305079400536622997 492173451800596900154203)
  ·
    refine ⟨738260177700895350231305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 492173451800596900154203 738260177700895350231305)
    ·
      refine ⟨553695133275671512673479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 738260177700895350231305 553695133275671512673479)
      ·
        refine ⟨830542699913507269010219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553695133275671512673479 830542699913507269010219)
        ·
          refine ⟨1245814049870260903515329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 830542699913507269010219 1245814049870260903515329)
          ·
            refine ⟨934360537402695677636497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1245814049870260903515329 934360537402695677636497)
            ·
              refine ⟨700770403052021758227373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 934360537402695677636497 700770403052021758227373)
              ·
                refine ⟨262788901144508159335265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 700770403052021758227373 262788901144508159335265)
                ·
                  refine ⟨197091675858381119501449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 262788901144508159335265 197091675858381119501449)
                  ·
                    rfl

theorem cell20_431814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_431814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431814 prefixEnd_431814 := by exact prefixLift 431814
  have htrace : WordTrace (prefixWord ++ tailWord_431814) baseStart_431814 baseEnd_431814 := by
    simpa [prefixWord, tailWord_431814, baseEnd_431814] using wordTrace_append hprefix tailTrace_431814
  have hstable : (prefixWord ++ tailWord_431814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431814).length < 2 ^ (prefixWord ++ tailWord_431814).sum := by decide
  have hdescent : baseEnd_431814 < baseStart_431814 := by decide
  rcases family_descends (prefixWord ++ tailWord_431814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431818 : List Nat := [3, 1, 2, 1, 5, 1, 2, 3, 2]
def baseStart_431818 : Nat := 118140960795 + 431818 * 2 ^ 59
def prefixEnd_431818 : Nat := 4983230072969 + 3 ^ 40 * 431818 * 2
def baseEnd_431818 : Nat := 197093501567374883368099

theorem tailTrace_431818 : CollatzResearch.WordTrace tailWord_431818 prefixEnd_431818 197093501567374883368099 := by
  unfold tailWord_431818
  simp only [CollatzResearch.WordTrace]
  refine ⟨3937424087401152372020027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10499797566403072992053405 3937424087401152372020027)
  ·
    refine ⟨5906136131101728558030041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3937424087401152372020027 5906136131101728558030041)
    ·
      refine ⟨4429602098326296418522531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5906136131101728558030041 4429602098326296418522531)
      ·
        refine ⟨6644403147489444627783797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4429602098326296418522531 6644403147489444627783797)
        ·
          refine ⟨622912795077135433854731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6644403147489444627783797 622912795077135433854731)
          ·
            refine ⟨934369192615703150782097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622912795077135433854731 934369192615703150782097)
            ·
              refine ⟨700776894461777363086573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 934369192615703150782097 700776894461777363086573)
              ·
                refine ⟨262791335423166511157465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 700776894461777363086573 262791335423166511157465)
                ·
                  refine ⟨197093501567374883368099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 262791335423166511157465 197093501567374883368099)
                  ·
                    rfl

theorem cell20_431818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 3, 2].length) (baseStart_431818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431818 prefixEnd_431818 := by exact prefixLift 431818
  have htrace : WordTrace (prefixWord ++ tailWord_431818) baseStart_431818 baseEnd_431818 := by
    simpa [prefixWord, tailWord_431818, baseEnd_431818] using wordTrace_append hprefix tailTrace_431818
  have hstable : (prefixWord ++ tailWord_431818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431818).length < 2 ^ (prefixWord ++ tailWord_431818).sum := by decide
  have hdescent : baseEnd_431818 < baseStart_431818 := by decide
  rcases family_descends (prefixWord ++ tailWord_431818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431898 : List Nat := [3, 1, 1, 3, 2, 2, 3, 1, 4]
def baseStart_431898 : Nat := 118140960795 + 431898 * 2 ^ 59
def prefixEnd_431898 : Nat := 4983230072969 + 3 ^ 40 * 431898 * 2
def baseEnd_431898 : Nat := 197130015747250160701105

theorem tailTrace_431898 : CollatzResearch.WordTrace tailWord_431898 prefixEnd_431898 197130015747250160701105 := by
  unfold tailWord_431898
  simp only [CollatzResearch.WordTrace]
  refine ⟨3938153547328695787748087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10501742792876522100661565 3938153547328695787748087)
  ·
    refine ⟨5907230320993043681622131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3938153547328695787748087 5907230320993043681622131)
    ·
      refine ⟨8860845481489565522433197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5907230320993043681622131 8860845481489565522433197)
      ·
        refine ⟨3322817055558587070912449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8860845481489565522433197 3322817055558587070912449)
        ·
          refine ⟨2492112791668940303184337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3322817055558587070912449 2492112791668940303184337)
          ·
            refine ⟨1869084593751705227388253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2492112791668940303184337 1869084593751705227388253)
            ·
              refine ⟨700906722656889460270595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1869084593751705227388253 700906722656889460270595)
              ·
                refine ⟨1051360083985334190405893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 700906722656889460270595 1051360083985334190405893)
                ·
                  refine ⟨197130015747250160701105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1051360083985334190405893 197130015747250160701105)
                  ·
                    rfl

theorem cell20_431898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_431898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431898 prefixEnd_431898 := by exact prefixLift 431898
  have htrace : WordTrace (prefixWord ++ tailWord_431898) baseStart_431898 baseEnd_431898 := by
    simpa [prefixWord, tailWord_431898, baseEnd_431898] using wordTrace_append hprefix tailTrace_431898
  have hstable : (prefixWord ++ tailWord_431898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431898).length < 2 ^ (prefixWord ++ tailWord_431898).sum := by decide
  have hdescent : baseEnd_431898 < baseStart_431898 := by decide
  rcases family_descends (prefixWord ++ tailWord_431898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431905 : List Nat := [1, 2, 3, 2, 1, 4, 2, 5]
def baseStart_431905 : Nat := 118140960795 + 431905 * 2 ^ 59
def prefixEnd_431905 : Nat := 4983230072969 + 3 ^ 40 * 431905 * 2
def baseEnd_431905 : Nat := 65711070245996415822581

theorem tailTrace_431905 : CollatzResearch.WordTrace tailWord_431905 prefixEnd_431905 65711070245996415822581 := by
  unfold tailWord_431905
  simp only [CollatzResearch.WordTrace]
  refine ⟨15752869500289423346497169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10501913000192948897664779 15752869500289423346497169)
  ·
    refine ⟨11814652125217067509872877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15752869500289423346497169 11814652125217067509872877)
    ·
      refine ⟨4430494546956400316202329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11814652125217067509872877 4430494546956400316202329)
      ·
        refine ⟨3322870910217300237151747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4430494546956400316202329 3322870910217300237151747)
        ·
          refine ⟨4984306365325950355727621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3322870910217300237151747 4984306365325950355727621)
          ·
            refine ⟨934557443498615691698929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4984306365325950355727621 934557443498615691698929)
            ·
              refine ⟨700918082623961768774197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 934557443498615691698929 700918082623961768774197)
              ·
                refine ⟨65711070245996415822581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 700918082623961768774197 65711070245996415822581)
                ·
                  rfl

theorem cell20_431905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 5].length) (baseStart_431905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431905 prefixEnd_431905 := by exact prefixLift 431905
  have htrace : WordTrace (prefixWord ++ tailWord_431905) baseStart_431905 baseEnd_431905 := by
    simpa [prefixWord, tailWord_431905, baseEnd_431905] using wordTrace_append hprefix tailTrace_431905
  have hstable : (prefixWord ++ tailWord_431905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431905).length < 2 ^ (prefixWord ++ tailWord_431905).sum := by decide
  have hdescent : baseEnd_431905 < baseStart_431905 := by decide
  rcases family_descends (prefixWord ++ tailWord_431905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431908 : List Nat := [2, 3, 1, 3, 2, 1, 4, 1, 3]
def baseStart_431908 : Nat := 118140960795 + 431908 * 2 ^ 59
def prefixEnd_431908 : Nat := 4983230072969 + 3 ^ 40 * 431908 * 2
def baseEnd_431908 : Nat := 197134580019734570367731

theorem tailTrace_431908 : CollatzResearch.WordTrace tailWord_431908 prefixEnd_431908 197134580019734570367731 := by
  unfold tailWord_431908
  simp only [CollatzResearch.WordTrace]
  refine ⟨7876489459639277429428189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10501985946185703239237585 7876489459639277429428189)
  ·
    refine ⟨2953683547364729036035571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7876489459639277429428189 2953683547364729036035571)
    ·
      refine ⟨4430525321047093554053357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2953683547364729036035571 4430525321047093554053357)
      ·
        refine ⟨1661446995392660082770009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4430525321047093554053357 1661446995392660082770009)
        ·
          refine ⟨1246085246544495062077507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1661446995392660082770009 1246085246544495062077507)
          ·
            refine ⟨1869127869816742593116261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1246085246544495062077507 1869127869816742593116261)
            ·
              refine ⟨350461475590639236209299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1869127869816742593116261 350461475590639236209299)
              ·
                refine ⟨525692213385958854313949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350461475590639236209299 525692213385958854313949)
                ·
                  refine ⟨197134580019734570367731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 525692213385958854313949 197134580019734570367731)
                  ·
                    rfl

theorem cell20_431908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_431908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431908 prefixEnd_431908 := by exact prefixLift 431908
  have htrace : WordTrace (prefixWord ++ tailWord_431908) baseStart_431908 baseEnd_431908 := by
    simpa [prefixWord, tailWord_431908, baseEnd_431908] using wordTrace_append hprefix tailTrace_431908
  have hstable : (prefixWord ++ tailWord_431908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431908).length < 2 ^ (prefixWord ++ tailWord_431908).sum := by decide
  have hdescent : baseEnd_431908 < baseStart_431908 := by decide
  rcases family_descends (prefixWord ++ tailWord_431908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431949 : List Nat := [1, 6, 1, 2, 1, 1, 4, 2, 2]
def baseStart_431949 : Nat := 118140960795 + 431949 * 2 ^ 59
def prefixEnd_431949 : Nat := 4983230072969 + 3 ^ 40 * 431949 * 2
def baseEnd_431949 : Nat := 197153293536920650000897

theorem tailTrace_431949 : CollatzResearch.WordTrace tailWord_431949 prefixEnd_431949 197153293536920650000897 := by
  unfold tailWord_431949
  simp only [CollatzResearch.WordTrace]
  refine ⟨15754474312130018861098901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10502982874753345907399267 15754474312130018861098901)
  ·
    refine ⟨738490983381094634114011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15754474312130018861098901 738490983381094634114011)
    ·
      refine ⟨1107736475071641951171017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 738490983381094634114011 1107736475071641951171017)
      ·
        refine ⟨830802356303731463378263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1107736475071641951171017 830802356303731463378263)
        ·
          refine ⟨1246203534455597195067395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 830802356303731463378263 1246203534455597195067395)
          ·
            refine ⟨1869305301683395792601093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1246203534455597195067395 1869305301683395792601093)
            ·
              refine ⟨350494744065636711112705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1869305301683395792601093 350494744065636711112705)
              ·
                refine ⟨262871058049227533334529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350494744065636711112705 262871058049227533334529)
                ·
                  refine ⟨197153293536920650000897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 262871058049227533334529 197153293536920650000897)
                  ·
                    rfl

theorem cell20_431949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_431949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431949 prefixEnd_431949 := by exact prefixLift 431949
  have htrace : WordTrace (prefixWord ++ tailWord_431949) baseStart_431949 baseEnd_431949 := by
    simpa [prefixWord, tailWord_431949, baseEnd_431949] using wordTrace_append hprefix tailTrace_431949
  have hstable : (prefixWord ++ tailWord_431949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431949).length < 2 ^ (prefixWord ++ tailWord_431949).sum := by decide
  have hdescent : baseEnd_431949 < baseStart_431949 := by decide
  rcases family_descends (prefixWord ++ tailWord_431949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431953 : List Nat := [1, 2, 2, 1, 5, 2, 1, 4, 2]
def baseStart_431953 : Nat := 118140960795 + 431953 * 2 ^ 59
def prefixEnd_431953 : Nat := 4983230072969 + 3 ^ 40 * 431953 * 2
def baseEnd_431953 : Nat := 197155119245914413867547

theorem tailTrace_431953 : CollatzResearch.WordTrace tailWord_431953 prefixEnd_431953 197155119245914413867547 := by
  unfold tailWord_431953
  simp only [CollatzResearch.WordTrace]
  refine ⟨15754620204115527544244513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10503080136077018362829675 15754620204115527544244513)
  ·
    refine ⟨11815965153086645658183385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15754620204115527544244513 11815965153086645658183385)
    ·
      refine ⟨8861973864814984243637539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11815965153086645658183385 8861973864814984243637539)
      ·
        refine ⟨13292960797222476365456309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8861973864814984243637539 13292960797222476365456309)
        ·
          refine ⟨1246215074739607159261529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13292960797222476365456309 1246215074739607159261529)
          ·
            refine ⟨934661306054705369446147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1246215074739607159261529 934661306054705369446147)
            ·
              refine ⟨1401991959082058054169221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 934661306054705369446147 1401991959082058054169221)
              ·
                refine ⟨262873492327885885156729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1401991959082058054169221 262873492327885885156729)
                ·
                  refine ⟨197155119245914413867547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 262873492327885885156729 197155119245914413867547)
                  ·
                    rfl

theorem cell20_431953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 4, 2].length) (baseStart_431953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431953 prefixEnd_431953 := by exact prefixLift 431953
  have htrace : WordTrace (prefixWord ++ tailWord_431953) baseStart_431953 baseEnd_431953 := by
    simpa [prefixWord, tailWord_431953, baseEnd_431953] using wordTrace_append hprefix tailTrace_431953
  have hstable : (prefixWord ++ tailWord_431953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431953).length < 2 ^ (prefixWord ++ tailWord_431953).sum := by decide
  have hdescent : baseEnd_431953 < baseStart_431953 := by decide
  rcases family_descends (prefixWord ++ tailWord_431953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431998 : List Nat := [4, 2, 3, 1, 1, 2, 7]
def baseStart_431998 : Nat := 118140960795 + 431998 * 2 ^ 59
def prefixEnd_431998 : Nat := 4983230072969 + 3 ^ 40 * 431998 * 2
def baseEnd_431998 : Nat := 21908406496899361929707

theorem tailTrace_431998 : CollatzResearch.WordTrace tailWord_431998 prefixEnd_431998 21908406496899361929707 := by
  unfold tailWord_431998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1969532686119062528704081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10504174325968333486421765 1969532686119062528704081)
  ·
    refine ⟨1477149514589296896528061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1969532686119062528704081 1477149514589296896528061)
    ·
      refine ⟨553931067970986336198023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1477149514589296896528061 553931067970986336198023)
      ·
        refine ⟨830896601956479504297035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553931067970986336198023 830896601956479504297035)
        ·
          refine ⟨1246344902934719256445553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 830896601956479504297035 1246344902934719256445553)
          ·
            refine ⟨934758677201039442334165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1246344902934719256445553 934758677201039442334165)
            ·
              refine ⟨21908406496899361929707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 934758677201039442334165 21908406496899361929707)
              ·
                rfl

theorem cell20_431998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 7].length) (baseStart_431998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_431998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_431998 prefixEnd_431998 := by exact prefixLift 431998
  have htrace : WordTrace (prefixWord ++ tailWord_431998) baseStart_431998 baseEnd_431998 := by
    simpa [prefixWord, tailWord_431998, baseEnd_431998] using wordTrace_append hprefix tailTrace_431998
  have hstable : (prefixWord ++ tailWord_431998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431998).length < 2 ^ (prefixWord ++ tailWord_431998).sum := by decide
  have hdescent : baseEnd_431998 < baseStart_431998 := by decide
  rcases family_descends (prefixWord ++ tailWord_431998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432001 : List Nat := [1, 2, 4, 4, 1, 2, 1, 2, 3]
def baseStart_432001 : Nat := 118140960795 + 432001 * 2 ^ 59
def prefixEnd_432001 : Nat := 4983230072969 + 3 ^ 40 * 432001 * 2
def baseEnd_432001 : Nat := 197177027753839580267351

theorem tailTrace_432001 : CollatzResearch.WordTrace tailWord_432001 prefixEnd_432001 197177027753839580267351 := by
  unfold tailWord_432001
  simp only [CollatzResearch.WordTrace]
  refine ⟨15756370907941631741991857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10504247271961087827994571 15756370907941631741991857)
  ·
    refine ⟨11817278180956223806493893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15756370907941631741991857 11817278180956223806493893)
    ·
      refine ⟨2215739658929291963717605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11817278180956223806493893 2215739658929291963717605)
      ·
        refine ⟨415451186049242243197051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2215739658929291963717605 415451186049242243197051)
        ·
          refine ⟨623176779073863364795577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415451186049242243197051 623176779073863364795577)
          ·
            refine ⟨467382584305397523596683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 623176779073863364795577 467382584305397523596683)
            ·
              refine ⟨701073876458096285395025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467382584305397523596683 701073876458096285395025)
              ·
                refine ⟨525805407343572214046269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 701073876458096285395025 525805407343572214046269)
                ·
                  refine ⟨197177027753839580267351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 525805407343572214046269 197177027753839580267351)
                  ·
                    rfl

theorem cell20_432001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 3].length) (baseStart_432001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_432001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_432001 prefixEnd_432001 := by exact prefixLift 432001
  have htrace : WordTrace (prefixWord ++ tailWord_432001) baseStart_432001 baseEnd_432001 := by
    simpa [prefixWord, tailWord_432001, baseEnd_432001] using wordTrace_append hprefix tailTrace_432001
  have hstable : (prefixWord ++ tailWord_432001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432001).length < 2 ^ (prefixWord ++ tailWord_432001).sum := by decide
  have hdescent : baseEnd_432001 < baseStart_432001 := by decide
  rcases family_descends (prefixWord ++ tailWord_432001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432036 : List Nat := [2, 3, 1, 2, 1, 5, 2, 4]
def baseStart_432036 : Nat := 118140960795 + 432036 * 2 ^ 59
def prefixEnd_432036 : Nat := 4983230072969 + 3 ^ 40 * 432036 * 2
def baseEnd_432036 : Nat := 65731000902511671366847

theorem tailTrace_432036 : CollatzResearch.WordTrace tailWord_432036 prefixEnd_432036 65731000902511671366847 := by
  unfold tailWord_432036
  simp only [CollatzResearch.WordTrace]
  refine ⟨7878823731407416359757981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10505098308543221813010641 7878823731407416359757981)
  ·
    refine ⟨2954558899277781134909243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7878823731407416359757981 2954558899277781134909243)
    ·
      refine ⟨4431838348916671702363865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2954558899277781134909243 4431838348916671702363865)
      ·
        refine ⟨3323878761687503776772899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4431838348916671702363865 3323878761687503776772899)
        ·
          refine ⟨4985818142531255665159349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3323878761687503776772899 4985818142531255665159349)
          ·
            refine ⟨467420450862305218608689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4985818142531255665159349 467420450862305218608689)
            ·
              refine ⟨350565338146728913956517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 467420450862305218608689 350565338146728913956517)
              ·
                refine ⟨65731000902511671366847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 350565338146728913956517 65731000902511671366847)
                ·
                  rfl

theorem cell20_432036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 4].length) (baseStart_432036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_432036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_432036 prefixEnd_432036 := by exact prefixLift 432036
  have htrace : WordTrace (prefixWord ++ tailWord_432036) baseStart_432036 baseEnd_432036 := by
    simpa [prefixWord, tailWord_432036, baseEnd_432036] using wordTrace_append hprefix tailTrace_432036
  have hstable : (prefixWord ++ tailWord_432036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432036).length < 2 ^ (prefixWord ++ tailWord_432036).sum := by decide
  have hdescent : baseEnd_432036 < baseStart_432036 := by decide
  rcases family_descends (prefixWord ++ tailWord_432036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432047 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 7]
def baseStart_432047 : Nat := 118140960795 + 432047 * 2 ^ 59
def prefixEnd_432047 : Nat := 4983230072969 + 3 ^ 40 * 432047 * 2
def baseEnd_432047 : Nat := 197198023407267864733829

theorem tailTrace_432047 : CollatzResearch.WordTrace tailWord_432047 prefixEnd_432047 197198023407267864733829 := by
  unfold tailWord_432047
  simp only [CollatzResearch.WordTrace]
  refine ⟨15758048665774981598166395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10505365777183321065444263 15758048665774981598166395)
  ·
    refine ⟨23637072998662472397249593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15758048665774981598166395 23637072998662472397249593)
    ·
      refine ⟨17727804748996854297937195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23637072998662472397249593 17727804748996854297937195)
      ·
        refine ⟨26591707123495281446905793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17727804748996854297937195 26591707123495281446905793)
        ·
          refine ⟨19943780342621461085179345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26591707123495281446905793 19943780342621461085179345)
          ·
            refine ⟨14957835256966095813884509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19943780342621461085179345 14957835256966095813884509)
            ·
              refine ⟨5609188221362285930206691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14957835256966095813884509 5609188221362285930206691)
              ·
                refine ⟨8413782332043428895310037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5609188221362285930206691 8413782332043428895310037)
                ·
                  refine ⟨197198023407267864733829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8413782332043428895310037 197198023407267864733829)
                  ·
                    rfl

theorem cell20_432047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 7].length) (baseStart_432047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_432047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_432047 prefixEnd_432047 := by exact prefixLift 432047
  have htrace : WordTrace (prefixWord ++ tailWord_432047) baseStart_432047 baseEnd_432047 := by
    simpa [prefixWord, tailWord_432047, baseEnd_432047] using wordTrace_append hprefix tailTrace_432047
  have hstable : (prefixWord ++ tailWord_432047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432047).length < 2 ^ (prefixWord ++ tailWord_432047).sum := by decide
  have hdescent : baseEnd_432047 < baseStart_432047 := by decide
  rcases family_descends (prefixWord ++ tailWord_432047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432064 : List Nat := [2, 1, 1, 2, 3, 2, 2, 4, 3]
def baseStart_432064 : Nat := 118140960795 + 432064 * 2 ^ 59
def prefixEnd_432064 : Nat := 4983230072969 + 3 ^ 40 * 432064 * 2
def baseEnd_432064 : Nat := 197205782670491361167093

theorem tailTrace_432064 : CollatzResearch.WordTrace tailWord_432064 prefixEnd_432064 197205782670491361167093 := by
  unfold tailWord_432064
  simp only [CollatzResearch.WordTrace]
  refine ⟨7879334353356696750767623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10505779137808929001023497 7879334353356696750767623)
  ·
    refine ⟨11819001530035045126151435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7879334353356696750767623 11819001530035045126151435)
    ·
      refine ⟨17728502295052567689227153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11819001530035045126151435 17728502295052567689227153)
      ·
        refine ⟨13296376721289425766920365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17728502295052567689227153 13296376721289425766920365)
        ·
          refine ⟨4986141270483534662595137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13296376721289425766920365 4986141270483534662595137)
          ·
            refine ⟨3739605952862650996946353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4986141270483534662595137 3739605952862650996946353)
            ·
              refine ⟨2804704464646988247709765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3739605952862650996946353 2804704464646988247709765)
              ·
                refine ⟨525882087121310296445581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2804704464646988247709765 525882087121310296445581)
                ·
                  refine ⟨197205782670491361167093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 525882087121310296445581 197205782670491361167093)
                  ·
                    rfl

theorem cell20_432064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 3].length) (baseStart_432064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_432064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_432064 prefixEnd_432064 := by exact prefixLift 432064
  have htrace : WordTrace (prefixWord ++ tailWord_432064) baseStart_432064 baseEnd_432064 := by
    simpa [prefixWord, tailWord_432064, baseEnd_432064] using wordTrace_append hprefix tailTrace_432064
  have hstable : (prefixWord ++ tailWord_432064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432064).length < 2 ^ (prefixWord ++ tailWord_432064).sum := by decide
  have hdescent : baseEnd_432064 < baseStart_432064 := by decide
  rcases family_descends (prefixWord ++ tailWord_432064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432118 : List Nat := [5, 1, 1, 1, 5, 1, 2, 2, 2]
def baseStart_432118 : Nat := 118140960795 + 432118 * 2 ^ 59
def prefixEnd_432118 : Nat := 4983230072969 + 3 ^ 40 * 432118 * 2
def baseEnd_432118 : Nat := 197230429741907173366873

theorem tailTrace_432118 : CollatzResearch.WordTrace tailWord_432118 prefixEnd_432118 197230429741907173366873 := by
  unfold tailWord_432118
  simp only [CollatzResearch.WordTrace]
  refine ⟨985039890532360045250063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10507092165678507149334005 985039890532360045250063)
  ·
    refine ⟨1477559835798540067875095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 985039890532360045250063 1477559835798540067875095)
    ·
      refine ⟨2216339753697810101812643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1477559835798540067875095 2216339753697810101812643)
      ·
        refine ⟨3324509630546715152718965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2216339753697810101812643 3324509630546715152718965)
        ·
          refine ⟨311672777863754545567403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3324509630546715152718965 311672777863754545567403)
          ·
            refine ⟨467509166795631818351105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311672777863754545567403 467509166795631818351105)
            ·
              refine ⟨350631875096723863763329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 467509166795631818351105 350631875096723863763329)
              ·
                refine ⟨262973906322542897822497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350631875096723863763329 262973906322542897822497)
                ·
                  refine ⟨197230429741907173366873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 262973906322542897822497 197230429741907173366873)
                  ·
                    rfl

theorem cell20_432118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_432118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_432118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_432118 prefixEnd_432118 := by exact prefixLift 432118
  have htrace : WordTrace (prefixWord ++ tailWord_432118) baseStart_432118 baseEnd_432118 := by
    simpa [prefixWord, tailWord_432118, baseEnd_432118] using wordTrace_append hprefix tailTrace_432118
  have hstable : (prefixWord ++ tailWord_432118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432118).length < 2 ^ (prefixWord ++ tailWord_432118).sum := by decide
  have hdescent : baseEnd_432118 < baseStart_432118 := by decide
  rcases family_descends (prefixWord ++ tailWord_432118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432123 : List Nat := [1, 1, 1, 1, 1, 3, 4, 3, 5]
def baseStart_432123 : Nat := 118140960795 + 432123 * 2 ^ 59
def prefixEnd_432123 : Nat := 4983230072969 + 3 ^ 40 * 432123 * 2
def baseEnd_432123 : Nat := 197232711878149378200185

theorem tailTrace_432123 : CollatzResearch.WordTrace tailWord_432123 prefixEnd_432123 197232711878149378200185 := by
  unfold tailWord_432123
  simp only [CollatzResearch.WordTrace]
  refine ⟨15760820613499646577933023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10507213742333097718622015 15760820613499646577933023)
  ·
    refine ⟨23641230920249469866899535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15760820613499646577933023 23641230920249469866899535)
    ·
      refine ⟨35461846380374204800349303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23641230920249469866899535 35461846380374204800349303)
      ·
        refine ⟨53192769570561307200523955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35461846380374204800349303 53192769570561307200523955)
        ·
          refine ⟨79789154355841960800785933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53192769570561307200523955 79789154355841960800785933)
          ·
            refine ⟨29920932883440735300294725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79789154355841960800785933 29920932883440735300294725)
            ·
              refine ⟨5610174915645137868805261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29920932883440735300294725 5610174915645137868805261)
              ·
                refine ⟨2103815593366926700801973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5610174915645137868805261 2103815593366926700801973)
                ·
                  refine ⟨197232711878149378200185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2103815593366926700801973 197232711878149378200185)
                  ·
                    rfl

theorem cell20_432123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 5].length) (baseStart_432123 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_432123 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_432123 prefixEnd_432123 := by exact prefixLift 432123
  have htrace : WordTrace (prefixWord ++ tailWord_432123) baseStart_432123 baseEnd_432123 := by
    simpa [prefixWord, tailWord_432123, baseEnd_432123] using wordTrace_append hprefix tailTrace_432123
  have hstable : (prefixWord ++ tailWord_432123).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432123).length < 2 ^ (prefixWord ++ tailWord_432123).sum := by decide
  have hdescent : baseEnd_432123 < baseStart_432123 := by decide
  rcases family_descends (prefixWord ++ tailWord_432123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432133 : List Nat := [1, 3, 1, 1, 2, 6, 1, 5]
def baseStart_432133 : Nat := 118140960795 + 432133 * 2 ^ 59
def prefixEnd_432133 : Nat := 4983230072969 + 3 ^ 40 * 432133 * 2
def baseEnd_432133 : Nat := 65745758716877929288937

theorem tailTrace_432133 : CollatzResearch.WordTrace tailWord_432133 prefixEnd_432133 65745758716877929288937 := by
  unfold tailWord_432133
  simp only [CollatzResearch.WordTrace]
  refine ⟨15761185343463418285797053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10507456895642278857198035 15761185343463418285797053)
  ·
    refine ⟨5910444503798781857173895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15761185343463418285797053 5910444503798781857173895)
    ·
      refine ⟨8865666755698172785760843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5910444503798781857173895 8865666755698172785760843)
      ·
        refine ⟨13298500133547259178641265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8865666755698172785760843 13298500133547259178641265)
        ·
          refine ⟨9973875100160444383980949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13298500133547259178641265 9973875100160444383980949)
          ·
            refine ⟨467525395320020830499107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9973875100160444383980949 467525395320020830499107)
            ·
              refine ⟨701288092980031245748661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467525395320020830499107 701288092980031245748661)
              ·
                refine ⟨65745758716877929288937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 701288092980031245748661 65745758716877929288937)
                ·
                  rfl

theorem cell20_432133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 5].length) (baseStart_432133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_432133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_432133 prefixEnd_432133 := by exact prefixLift 432133
  have htrace : WordTrace (prefixWord ++ tailWord_432133) baseStart_432133 baseEnd_432133 := by
    simpa [prefixWord, tailWord_432133, baseEnd_432133] using wordTrace_append hprefix tailTrace_432133
  have hstable : (prefixWord ++ tailWord_432133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432133).length < 2 ^ (prefixWord ++ tailWord_432133).sum := by decide
  have hdescent : baseEnd_432133 < baseStart_432133 := by decide
  rcases family_descends (prefixWord ++ tailWord_432133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432140 : List Nat := [2, 2, 1, 2, 3, 1, 1, 5, 3]
def baseStart_432140 : Nat := 118140960795 + 432140 * 2 ^ 59
def prefixEnd_432140 : Nat := 4983230072969 + 3 ^ 40 * 432140 * 2
def baseEnd_432140 : Nat := 197240471141372874633449

theorem tailTrace_432140 : CollatzResearch.WordTrace tailWord_432140 prefixEnd_432140 197240471141372874633449 := by
  unfold tailWord_432140
  simp only [CollatzResearch.WordTrace]
  refine ⟨7880720327219029240650937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10507627102958705654201249 7880720327219029240650937)
  ·
    refine ⟨5910540245414271930488203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7880720327219029240650937 5910540245414271930488203)
    ·
      refine ⟨8865810368121407895732305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5910540245414271930488203 8865810368121407895732305)
      ·
        refine ⟨6649357776091055921799229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8865810368121407895732305 6649357776091055921799229)
        ·
          refine ⟨2493509166034145970674711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6649357776091055921799229 2493509166034145970674711)
          ·
            refine ⟨3740263749051218956012067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2493509166034145970674711 3740263749051218956012067)
            ·
              refine ⟨5610395623576828434018101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3740263749051218956012067 5610395623576828434018101)
              ·
                refine ⟨525974589710327665689197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5610395623576828434018101 525974589710327665689197)
                ·
                  refine ⟨197240471141372874633449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 525974589710327665689197 197240471141372874633449)
                  ·
                    rfl

theorem cell20_432140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_432140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_432140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_432140 prefixEnd_432140 := by exact prefixLift 432140
  have htrace : WordTrace (prefixWord ++ tailWord_432140) baseStart_432140 baseEnd_432140 := by
    simpa [prefixWord, tailWord_432140, baseEnd_432140] using wordTrace_append hprefix tailTrace_432140
  have hstable : (prefixWord ++ tailWord_432140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432140).length < 2 ^ (prefixWord ++ tailWord_432140).sum := by decide
  have hdescent : baseEnd_432140 < baseStart_432140 := by decide
  rcases family_descends (prefixWord ++ tailWord_432140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432174 : List Nat := [4, 1, 3, 1, 1, 4, 1, 2, 3]
def baseStart_432174 : Nat := 118140960795 + 432174 * 2 ^ 59
def prefixEnd_432174 : Nat := 4983230072969 + 3 ^ 40 * 432174 * 2
def baseEnd_432174 : Nat := 197255989667819867499977

theorem tailTrace_432174 : CollatzResearch.WordTrace tailWord_432174 prefixEnd_432174 197255989667819867499977 := by
  unfold tailWord_432174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1970335092039360286004947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10508453824209921525359717 1970335092039360286004947)
  ·
    refine ⟨2955502638059040429007421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1970335092039360286004947 2955502638059040429007421)
    ·
      refine ⟨1108313489272140160877783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2955502638059040429007421 1108313489272140160877783)
      ·
        refine ⟨1662470233908210241316675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1108313489272140160877783 1662470233908210241316675)
        ·
          refine ⟨2493705350862315361975013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1662470233908210241316675 2493705350862315361975013)
          ·
            refine ⟨467569753286684130370315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2493705350862315361975013 467569753286684130370315)
            ·
              refine ⟨701354629930026195555473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467569753286684130370315 701354629930026195555473)
              ·
                refine ⟨526015972447519646666605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 701354629930026195555473 526015972447519646666605)
                ·
                  refine ⟨197255989667819867499977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 526015972447519646666605 197255989667819867499977)
                  ·
                    rfl

theorem cell20_432174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_432174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_432174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_432174 prefixEnd_432174 := by exact prefixLift 432174
  have htrace : WordTrace (prefixWord ++ tailWord_432174) baseStart_432174 baseEnd_432174 := by
    simpa [prefixWord, tailWord_432174, baseEnd_432174] using wordTrace_append hprefix tailTrace_432174
  have hstable : (prefixWord ++ tailWord_432174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432174).length < 2 ^ (prefixWord ++ tailWord_432174).sum := by decide
  have hdescent : baseEnd_432174 < baseStart_432174 := by decide
  rcases family_descends (prefixWord ++ tailWord_432174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432178 : List Nat := [3, 2, 1, 1, 2, 4, 1, 1, 5]
def baseStart_432178 : Nat := 118140960795 + 432178 * 2 ^ 59
def prefixEnd_432178 : Nat := 4983230072969 + 3 ^ 40 * 432178 * 2
def baseEnd_432178 : Nat := 197257815376813631366627

theorem tailTrace_432178 : CollatzResearch.WordTrace tailWord_432178 prefixEnd_432178 197257815376813631366627 := by
  unfold tailWord_432178
  simp only [CollatzResearch.WordTrace]
  refine ⟨3940706657075097742796297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10508551085533593980790125 3940706657075097742796297)
  ·
    refine ⟨2955529992806323307097223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3940706657075097742796297 2955529992806323307097223)
    ·
      refine ⟨4433294989209484960645835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2955529992806323307097223 4433294989209484960645835)
      ·
        refine ⟨6649942483814227440968753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4433294989209484960645835 6649942483814227440968753)
        ·
          refine ⟨4987456862860670580726565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6649942483814227440968753 4987456862860670580726565)
          ·
            refine ⟨935148161786375733886231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4987456862860670580726565 935148161786375733886231)
            ·
              refine ⟨1402722242679563600829347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 935148161786375733886231 1402722242679563600829347)
              ·
                refine ⟨2104083364019345401244021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1402722242679563600829347 2104083364019345401244021)
                ·
                  refine ⟨197257815376813631366627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2104083364019345401244021 197257815376813631366627)
                  ·
                    rfl

theorem cell20_432178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_432178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_432178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_432178 prefixEnd_432178 := by exact prefixLift 432178
  have htrace : WordTrace (prefixWord ++ tailWord_432178) baseStart_432178 baseEnd_432178 := by
    simpa [prefixWord, tailWord_432178, baseEnd_432178] using wordTrace_append hprefix tailTrace_432178
  have hstable : (prefixWord ++ tailWord_432178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432178).length < 2 ^ (prefixWord ++ tailWord_432178).sum := by decide
  have hdescent : baseEnd_432178 < baseStart_432178 := by decide
  rcases family_descends (prefixWord ++ tailWord_432178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432222 : List Nat := [4, 4, 1, 1, 3, 1, 6]
def baseStart_432222 : Nat := 118140960795 + 432222 * 2 ^ 59
def prefixEnd_432222 : Nat := 4983230072969 + 3 ^ 40 * 432222 * 2
def baseEnd_432222 : Nat := 21919766463971670433309

theorem tailTrace_432222 : CollatzResearch.WordTrace tailWord_432222 prefixEnd_432222 21919766463971670433309 := by
  unfold tailWord_432222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1970553930017623310723365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10509620960093990990524613 1970553930017623310723365)
  ·
    refine ⟨369478861878304370760631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1970553930017623310723365 369478861878304370760631)
    ·
      refine ⟨554218292817456556140947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369478861878304370760631 554218292817456556140947)
      ·
        refine ⟨831327439226184834211421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554218292817456556140947 831327439226184834211421)
        ·
          refine ⟨311747789709819312829283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 831327439226184834211421 311747789709819312829283)
          ·
            refine ⟨467621684564728969243925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311747789709819312829283 467621684564728969243925)
            ·
              refine ⟨21919766463971670433309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 467621684564728969243925 21919766463971670433309)
              ·
                rfl

theorem cell20_432222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 6].length) (baseStart_432222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_432222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_432222 prefixEnd_432222 := by exact prefixLift 432222
  have htrace : WordTrace (prefixWord ++ tailWord_432222) baseStart_432222 baseEnd_432222 := by
    simpa [prefixWord, tailWord_432222, baseEnd_432222] using wordTrace_append hprefix tailTrace_432222
  have hstable : (prefixWord ++ tailWord_432222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432222).length < 2 ^ (prefixWord ++ tailWord_432222).sum := by decide
  have hdescent : baseEnd_432222 < baseStart_432222 := by decide
  rcases family_descends (prefixWord ++ tailWord_432222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432226 : List Nat := [3, 3, 2, 2, 2, 2, 6]
def baseStart_432226 : Nat := 118140960795 + 432226 * 2 ^ 59
def prefixEnd_432226 : Nat := 4983230072969 + 3 ^ 40 * 432226 * 2
def baseEnd_432226 : Nat := 21919969320526533085159

theorem tailTrace_432226 : CollatzResearch.WordTrace tailWord_432226 prefixEnd_432226 21919969320526533085159 := by
  unfold tailWord_432226
  simp only [CollatzResearch.WordTrace]
  refine ⟨3941144333031623792233133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10509718221417663445955021 3941144333031623792233133)
  ·
    refine ⟨1477929124886858922087425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3941144333031623792233133 1477929124886858922087425)
    ·
      refine ⟨1108446843665144191565569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1477929124886858922087425 1108446843665144191565569)
      ·
        refine ⟨831335132748858143674177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1108446843665144191565569 831335132748858143674177)
        ·
          refine ⟨623501349561643607755633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 831335132748858143674177 623501349561643607755633)
          ·
            refine ⟨467626012171232705816725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 623501349561643607755633 467626012171232705816725)
            ·
              refine ⟨21919969320526533085159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 467626012171232705816725 21919969320526533085159)
              ·
                rfl

theorem cell20_432226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 6].length) (baseStart_432226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_432226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_432226 prefixEnd_432226 := by exact prefixLift 432226
  have htrace : WordTrace (prefixWord ++ tailWord_432226) baseStart_432226 baseEnd_432226 := by
    simpa [prefixWord, tailWord_432226, baseEnd_432226] using wordTrace_append hprefix tailTrace_432226
  have hstable : (prefixWord ++ tailWord_432226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432226).length < 2 ^ (prefixWord ++ tailWord_432226).sum := by decide
  have hdescent : baseEnd_432226 < baseStart_432226 := by decide
  rcases family_descends (prefixWord ++ tailWord_432226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432240 : List Nat := [2, 1, 1, 1, 5, 4, 1, 1, 4]
def baseStart_432240 : Nat := 118140960795 + 432240 * 2 ^ 59
def prefixEnd_432240 : Nat := 4983230072969 + 3 ^ 40 * 432240 * 2
def baseEnd_432240 : Nat := 197286113866216971299707

theorem tailTrace_432240 : CollatzResearch.WordTrace tailWord_432240 prefixEnd_432240 197286113866216971299707 := by
  unfold tailWord_432240
  simp only [CollatzResearch.WordTrace]
  refine ⟨7882543977037887779971087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10510058636050517039961449 7882543977037887779971087)
  ·
    refine ⟨11823815965556831669956631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7882543977037887779971087 11823815965556831669956631)
    ·
      refine ⟨17735723948335247504934947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11823815965556831669956631 17735723948335247504934947)
      ·
        refine ⟨26603585922502871257402421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17735723948335247504934947 26603585922502871257402421)
        ·
          refine ⟨2494086180234644180381477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26603585922502871257402421 2494086180234644180381477)
          ·
            refine ⟨467641158793995783821527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2494086180234644180381477 467641158793995783821527)
            ·
              refine ⟨701461738190993675732291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467641158793995783821527 701461738190993675732291)
              ·
                refine ⟨1052192607286490513598437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 701461738190993675732291 1052192607286490513598437)
                ·
                  refine ⟨197286113866216971299707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1052192607286490513598437 197286113866216971299707)
                  ·
                    rfl

theorem cell20_432240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 4].length) (baseStart_432240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_432240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_432240 prefixEnd_432240 := by exact prefixLift 432240
  have htrace : WordTrace (prefixWord ++ tailWord_432240) baseStart_432240 baseEnd_432240 := by
    simpa [prefixWord, tailWord_432240, baseEnd_432240] using wordTrace_append hprefix tailTrace_432240
  have hstable : (prefixWord ++ tailWord_432240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432240).length < 2 ^ (prefixWord ++ tailWord_432240).sum := by decide
  have hdescent : baseEnd_432240 < baseStart_432240 := by decide
  rcases family_descends (prefixWord ++ tailWord_432240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432316 : List Nat := [2, 2, 2, 3, 3, 1, 1, 2, 4]
def baseStart_432316 : Nat := 118140960795 + 432316 * 2 ^ 59
def prefixEnd_432316 : Nat := 4983230072969 + 3 ^ 40 * 432316 * 2
def baseEnd_432316 : Nat := 197320802337098484766063

theorem tailTrace_432316 : CollatzResearch.WordTrace tailWord_432316 prefixEnd_432316 197320802337098484766063 := by
  unfold tailWord_432316
  simp only [CollatzResearch.WordTrace]
  refine ⟨7883929950900220269854401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10511906601200293693139201 7883929950900220269854401)
  ·
    refine ⟨5912947463175165202390801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7883929950900220269854401 5912947463175165202390801)
    ·
      refine ⟨4434710597381373901793101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5912947463175165202390801 4434710597381373901793101)
      ·
        refine ⟨1663016474018015213172413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4434710597381373901793101 1663016474018015213172413)
        ·
          refine ⟨623631177756755704939655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1663016474018015213172413 623631177756755704939655)
          ·
            refine ⟨935446766635133557409483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623631177756755704939655 935446766635133557409483)
            ·
              refine ⟨1403170149952700336114225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 935446766635133557409483 1403170149952700336114225)
              ·
                refine ⟨1052377612464525252085669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1403170149952700336114225 1052377612464525252085669)
                ·
                  refine ⟨197320802337098484766063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1052377612464525252085669 197320802337098484766063)
                  ·
                    rfl

theorem cell20_432316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_432316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_432316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_432316 prefixEnd_432316 := by exact prefixLift 432316
  have htrace : WordTrace (prefixWord ++ tailWord_432316) baseStart_432316 baseEnd_432316 := by
    simpa [prefixWord, tailWord_432316, baseEnd_432316] using wordTrace_append hprefix tailTrace_432316
  have hstable : (prefixWord ++ tailWord_432316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432316).length < 2 ^ (prefixWord ++ tailWord_432316).sum := by decide
  have hdescent : baseEnd_432316 < baseStart_432316 := by decide
  rcases family_descends (prefixWord ++ tailWord_432316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432344 : List Nat := [2, 1, 2, 2, 4, 2, 7]
def baseStart_432344 : Nat := 118140960795 + 432344 * 2 ^ 59
def prefixEnd_432344 : Nat := 4983230072969 + 3 ^ 40 * 432344 * 2
def baseEnd_432344 : Nat := 21925953588894981314735

theorem tailTrace_432344 : CollatzResearch.WordTrace tailWord_432344 prefixEnd_432344 21925953588894981314735 := by
  unfold tailWord_432344
  simp only [CollatzResearch.WordTrace]
  refine ⟨7884440572849500660864043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10512587430466000881152057 7884440572849500660864043)
  ·
    refine ⟨11826660859274250991296065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7884440572849500660864043 11826660859274250991296065)
    ·
      refine ⟨8869995644455688243472049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11826660859274250991296065 8869995644455688243472049)
      ·
        refine ⟨6652496733341766182604037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8869995644455688243472049 6652496733341766182604037)
        ·
          refine ⟨1247343137501581159238257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6652496733341766182604037 1247343137501581159238257)
          ·
            refine ⟨935507353126185869428693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1247343137501581159238257 935507353126185869428693)
            ·
              refine ⟨21925953588894981314735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 935507353126185869428693 21925953588894981314735)
              ·
                rfl

theorem cell20_432344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 7].length) (baseStart_432344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_432344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_432344 prefixEnd_432344 := by exact prefixLift 432344
  have htrace : WordTrace (prefixWord ++ tailWord_432344) baseStart_432344 baseEnd_432344 := by
    simpa [prefixWord, tailWord_432344, baseEnd_432344] using wordTrace_append hprefix tailTrace_432344
  have hstable : (prefixWord ++ tailWord_432344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432344).length < 2 ^ (prefixWord ++ tailWord_432344).sum := by decide
  have hdescent : baseEnd_432344 < baseStart_432344 := by decide
  rcases family_descends (prefixWord ++ tailWord_432344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432388 : List Nat := [2, 3, 2, 2, 3, 2, 1, 3, 2]
def baseStart_432388 : Nat := 118140960795 + 432388 * 2 ^ 59
def prefixEnd_432388 : Nat := 4983230072969 + 3 ^ 40 * 432388 * 2
def baseEnd_432388 : Nat := 197353665098986234365769

theorem tailTrace_432388 : CollatzResearch.WordTrace tailWord_432388 prefixEnd_432388 197353665098986234365769 := by
  unfold tailWord_432388
  simp only [CollatzResearch.WordTrace]
  refine ⟨7885242978769798418164909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10513657305026397890886545 7885242978769798418164909)
  ·
    refine ⟨2956966117038674406811841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7885242978769798418164909 2956966117038674406811841)
    ·
      refine ⟨2217724587779005805108881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2956966117038674406811841 2217724587779005805108881)
      ·
        refine ⟨1663293440834254353831661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2217724587779005805108881 1663293440834254353831661)
        ·
          refine ⟨623735040312845382686873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1663293440834254353831661 623735040312845382686873)
          ·
            refine ⟨467801280234634037015155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 623735040312845382686873 467801280234634037015155)
            ·
              refine ⟨701701920351951055522733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467801280234634037015155 701701920351951055522733)
              ·
                refine ⟨263138220131981645821025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 701701920351951055522733 263138220131981645821025)
                ·
                  refine ⟨197353665098986234365769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 263138220131981645821025 197353665098986234365769)
                  ·
                    rfl

theorem cell20_432388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_432388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_432388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_432388 prefixEnd_432388 := by exact prefixLift 432388
  have htrace : WordTrace (prefixWord ++ tailWord_432388) baseStart_432388 baseEnd_432388 := by
    simpa [prefixWord, tailWord_432388, baseEnd_432388] using wordTrace_append hprefix tailTrace_432388
  have hstable : (prefixWord ++ tailWord_432388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432388).length < 2 ^ (prefixWord ++ tailWord_432388).sum := by decide
  have hdescent : baseEnd_432388 < baseStart_432388 := by decide
  rcases family_descends (prefixWord ++ tailWord_432388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432420 : List Nat := [2, 3, 1, 3, 1, 2, 1, 7]
def baseStart_432420 : Nat := 118140960795 + 432420 * 2 ^ 59
def prefixEnd_432420 : Nat := 4983230072969 + 3 ^ 40 * 432420 * 2
def baseEnd_432420 : Nat := 65789423590312115099657

theorem tailTrace_432420 : CollatzResearch.WordTrace tailWord_432420 prefixEnd_432420 65789423590312115099657 := by
  unfold tailWord_432420
  simp only [CollatzResearch.WordTrace]
  refine ⟨7885826546711833150747357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10514435395615777534329809 7885826546711833150747357)
  ·
    refine ⟨2957184955016937431530259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7885826546711833150747357 2957184955016937431530259)
    ·
      refine ⟨4435777432525406147295389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2957184955016937431530259 4435777432525406147295389)
      ·
        refine ⟨1663416537197027305235771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4435777432525406147295389 1663416537197027305235771)
        ·
          refine ⟨2495124805795540957853657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1663416537197027305235771 2495124805795540957853657)
          ·
            refine ⟨1871343604346655718390243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2495124805795540957853657 1871343604346655718390243)
            ·
              refine ⟨2807015406519983577585365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1871343604346655718390243 2807015406519983577585365)
              ·
                refine ⟨65789423590312115099657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2807015406519983577585365 65789423590312115099657)
                ·
                  rfl

theorem cell20_432420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 7].length) (baseStart_432420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_432420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_432420 prefixEnd_432420 := by exact prefixLift 432420
  have htrace : WordTrace (prefixWord ++ tailWord_432420) baseStart_432420 baseEnd_432420 := by
    simpa [prefixWord, tailWord_432420, baseEnd_432420] using wordTrace_append hprefix tailTrace_432420
  have hstable : (prefixWord ++ tailWord_432420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432420).length < 2 ^ (prefixWord ++ tailWord_432420).sum := by decide
  have hdescent : baseEnd_432420 < baseStart_432420 := by decide
  rcases family_descends (prefixWord ++ tailWord_432420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432551 : List Nat := [1, 1, 6, 1, 1, 2, 4, 4]
def baseStart_432551 : Nat := 118140960795 + 432551 * 2 ^ 59
def prefixEnd_432551 : Nat := 4983230072969 + 3 ^ 40 * 432551 * 2
def baseEnd_432551 : Nat := 65809354246827370643923

theorem tailTrace_432551 : CollatzResearch.WordTrace tailWord_432551 prefixEnd_432551 65809354246827370643923 := by
  unfold tailWord_432551
  simp only [CollatzResearch.WordTrace]
  refine ⟨15776431055949075674513507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10517620703966050449675671 15776431055949075674513507)
  ·
    refine ⟨23664646583923613511770261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15776431055949075674513507 23664646583923613511770261)
    ·
      refine ⟨1109280308621419383364231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23664646583923613511770261 1109280308621419383364231)
      ·
        refine ⟨1663920462932129075046347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1109280308621419383364231 1663920462932129075046347)
        ·
          refine ⟨2495880694398193612569521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1663920462932129075046347 2495880694398193612569521)
          ·
            refine ⟨1871910520798645209427141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2495880694398193612569521 1871910520798645209427141)
            ·
              refine ⟨350983222649745976767589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1871910520798645209427141 350983222649745976767589)
              ·
                refine ⟨65809354246827370643923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 350983222649745976767589 65809354246827370643923)
                ·
                  rfl

theorem cell20_432551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 4].length) (baseStart_432551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_432551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_432551 prefixEnd_432551 := by exact prefixLift 432551
  have htrace : WordTrace (prefixWord ++ tailWord_432551) baseStart_432551 baseEnd_432551 := by
    simpa [prefixWord, tailWord_432551, baseEnd_432551] using wordTrace_append hprefix tailTrace_432551
  have hstable : (prefixWord ++ tailWord_432551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432551).length < 2 ^ (prefixWord ++ tailWord_432551).sum := by decide
  have hdescent : baseEnd_432551 < baseStart_432551 := by decide
  rcases family_descends (prefixWord ++ tailWord_432551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432557 : List Nat := [1, 5, 2, 2, 3, 1, 1, 3, 2]
def baseStart_432557 : Nat := 118140960795 + 432557 * 2 ^ 59
def prefixEnd_432557 : Nat := 4983230072969 + 3 ^ 40 * 432557 * 2
def baseEnd_432557 : Nat := 197430801303972757731745

theorem tailTrace_432557 : CollatzResearch.WordTrace tailWord_432557 prefixEnd_432557 197430801303972757731745 := by
  unfold tailWord_432557
  simp only [CollatzResearch.WordTrace]
  refine ⟨15776649893927338699231925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10517766595951559132821283 15776649893927338699231925)
  ·
    refine ⟨1479060927555688003052993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15776649893927338699231925 1479060927555688003052993)
    ·
      refine ⟨1109295695666766002289745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1479060927555688003052993 1109295695666766002289745)
      ·
        refine ⟨831971771750074501717309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1109295695666766002289745 831971771750074501717309)
        ·
          refine ⟨311989414406277938143991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 831971771750074501717309 311989414406277938143991)
          ·
            refine ⟨467984121609416907215987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311989414406277938143991 467984121609416907215987)
            ·
              refine ⟨701976182414125360823981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467984121609416907215987 701976182414125360823981)
              ·
                refine ⟨263241068405297010308993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 701976182414125360823981 263241068405297010308993)
                ·
                  refine ⟨197430801303972757731745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 263241068405297010308993 197430801303972757731745)
                  ·
                    rfl

theorem cell20_432557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_432557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_432557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_432557 prefixEnd_432557 := by exact prefixLift 432557
  have htrace : WordTrace (prefixWord ++ tailWord_432557) baseStart_432557 baseEnd_432557 := by
    simpa [prefixWord, tailWord_432557, baseEnd_432557] using wordTrace_append hprefix tailTrace_432557
  have hstable : (prefixWord ++ tailWord_432557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432557).length < 2 ^ (prefixWord ++ tailWord_432557).sum := by decide
  have hdescent : baseEnd_432557 < baseStart_432557 := by decide
  rcases family_descends (prefixWord ++ tailWord_432557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432561 : List Nat := [1, 2, 2, 4, 1, 4, 1, 3, 2]
def baseStart_432561 : Nat := 118140960795 + 432561 * 2 ^ 59
def prefixEnd_432561 : Nat := 4983230072969 + 3 ^ 40 * 432561 * 2
def baseEnd_432561 : Nat := 197432627012966521598395

theorem tailTrace_432561 : CollatzResearch.WordTrace tailWord_432561 prefixEnd_432561 197432627012966521598395 := by
  unfold tailWord_432561
  simp only [CollatzResearch.WordTrace]
  refine ⟨15776795785912847382377537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10517863857275231588251691 15776795785912847382377537)
  ·
    refine ⟨11832596839434635536783153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15776795785912847382377537 11832596839434635536783153)
    ·
      refine ⟨8874447629575976652587365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11832596839434635536783153 8874447629575976652587365)
      ·
        refine ⟨1663958930545495622360131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8874447629575976652587365 1663958930545495622360131)
        ·
          refine ⟨2495938395818243433540197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1663958930545495622360131 2495938395818243433540197)
          ·
            refine ⟨467988449215920643788787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2495938395818243433540197 467988449215920643788787)
            ·
              refine ⟨701982673823880965683181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467988449215920643788787 701982673823880965683181)
              ·
                refine ⟨263243502683955362131193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 701982673823880965683181 263243502683955362131193)
                ·
                  refine ⟨197432627012966521598395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 263243502683955362131193 197432627012966521598395)
                  ·
                    rfl

theorem cell20_432561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 3, 2].length) (baseStart_432561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_432561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_432561 prefixEnd_432561 := by exact prefixLift 432561
  have htrace : WordTrace (prefixWord ++ tailWord_432561) baseStart_432561 baseEnd_432561 := by
    simpa [prefixWord, tailWord_432561, baseEnd_432561] using wordTrace_append hprefix tailTrace_432561
  have hstable : (prefixWord ++ tailWord_432561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432561).length < 2 ^ (prefixWord ++ tailWord_432561).sum := by decide
  have hdescent : baseEnd_432561 < baseStart_432561 := by decide
  rcases family_descends (prefixWord ++ tailWord_432561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432572 : List Nat := [2, 2, 2, 4, 1, 1, 8]
def baseStart_432572 : Nat := 118140960795 + 432572 * 2 ^ 59
def prefixEnd_432572 : Nat := 4983230072969 + 3 ^ 40 * 432572 * 2
def baseEnd_432572 : Nat := 21937516412522152470187

theorem tailTrace_432572 : CollatzResearch.WordTrace tailWord_432572 prefixEnd_432572 21937516412522152470187 := by
  unfold tailWord_432572
  simp only [CollatzResearch.WordTrace]
  refine ⟨7888598494436498130513985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10518131325915330840685313 7888598494436498130513985)
  ·
    refine ⟨5916448870827373597885489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7888598494436498130513985 5916448870827373597885489)
    ·
      refine ⟨4437336653120530198414117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5916448870827373597885489 4437336653120530198414117)
      ·
        refine ⟨832000622460099412202647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4437336653120530198414117 832000622460099412202647)
        ·
          refine ⟨1248000933690149118303971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 832000622460099412202647 1248000933690149118303971)
          ·
            refine ⟨1872001400535223677455957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1248000933690149118303971 1872001400535223677455957)
            ·
              refine ⟨21937516412522152470187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1872001400535223677455957 21937516412522152470187)
              ·
                rfl

theorem cell20_432572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 8].length) (baseStart_432572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_432572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_432572 prefixEnd_432572 := by exact prefixLift 432572
  have htrace : WordTrace (prefixWord ++ tailWord_432572) baseStart_432572 baseEnd_432572 := by
    simpa [prefixWord, tailWord_432572, baseEnd_432572] using wordTrace_append hprefix tailTrace_432572
  have hstable : (prefixWord ++ tailWord_432572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432572).length < 2 ^ (prefixWord ++ tailWord_432572).sum := by decide
  have hdescent : baseEnd_432572 < baseStart_432572 := by decide
  rcases family_descends (prefixWord ++ tailWord_432572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432579 : List Nat := [1, 1, 1, 3, 1, 1, 3, 6, 3]
def baseStart_432579 : Nat := 118140960795 + 432579 * 2 ^ 59
def prefixEnd_432579 : Nat := 4983230072969 + 3 ^ 40 * 432579 * 2
def baseEnd_432579 : Nat := 197440842703438458998321

theorem tailTrace_432579 : CollatzResearch.WordTrace tailWord_432579 prefixEnd_432579 197440842703438458998321 := by
  unfold tailWord_432579
  simp only [CollatzResearch.WordTrace]
  refine ⟨15777452299847636456532791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10518301533231757637688527 15777452299847636456532791)
  ·
    refine ⟨23666178449771454684799187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15777452299847636456532791 23666178449771454684799187)
    ·
      refine ⟨35499267674657182027198781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23666178449771454684799187 35499267674657182027198781)
      ·
        refine ⟨13312225377996443260199543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35499267674657182027198781 13312225377996443260199543)
        ·
          refine ⟨19968338066994664890299315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13312225377996443260199543 19968338066994664890299315)
          ·
            refine ⟨29952507100491997335448973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19968338066994664890299315 29952507100491997335448973)
            ·
              refine ⟨11232190162684499000793365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29952507100491997335448973 11232190162684499000793365)
              ·
                refine ⟨526508913875835890662189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11232190162684499000793365 526508913875835890662189)
                ·
                  refine ⟨197440842703438458998321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 526508913875835890662189 197440842703438458998321)
                  ·
                    rfl

theorem cell20_432579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 3].length) (baseStart_432579 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_432579 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_432579 prefixEnd_432579 := by exact prefixLift 432579
  have htrace : WordTrace (prefixWord ++ tailWord_432579) baseStart_432579 baseEnd_432579 := by
    simpa [prefixWord, tailWord_432579, baseEnd_432579] using wordTrace_append hprefix tailTrace_432579
  have hstable : (prefixWord ++ tailWord_432579).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432579).length < 2 ^ (prefixWord ++ tailWord_432579).sum := by decide
  have hdescent : baseEnd_432579 < baseStart_432579 := by decide
  rcases family_descends (prefixWord ++ tailWord_432579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432693 : List Nat := [1, 3, 3, 1, 1, 2, 3, 1, 5]
def baseStart_432693 : Nat := 118140960795 + 432693 * 2 ^ 59
def prefixEnd_432693 : Nat := 4983230072969 + 3 ^ 40 * 432693 * 2
def baseEnd_432693 : Nat := 197492875409760729197855

theorem tailTrace_432693 : CollatzResearch.WordTrace tailWord_432693 prefixEnd_432693 197492875409760729197855 := by
  unfold tailWord_432693
  simp only [CollatzResearch.WordTrace]
  refine ⟨15781610221434633926182733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10521073480956422617455155 15781610221434633926182733)
  ·
    refine ⟨5918103833037987722318525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15781610221434633926182733 5918103833037987722318525)
    ·
      refine ⟨2219288937389245395869447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5918103833037987722318525 2219288937389245395869447)
      ·
        refine ⟨3328933406083868093804171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2219288937389245395869447 3328933406083868093804171)
        ·
          refine ⟨4993400109125802140706257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3328933406083868093804171 4993400109125802140706257)
          ·
            refine ⟨3745050081844351605529693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4993400109125802140706257 3745050081844351605529693)
            ·
              refine ⟨1404393780691631852073635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3745050081844351605529693 1404393780691631852073635)
              ·
                refine ⟨2106590671037447778110453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1404393780691631852073635 2106590671037447778110453)
                ·
                  refine ⟨197492875409760729197855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2106590671037447778110453 197492875409760729197855)
                  ·
                    rfl

theorem cell20_432693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_432693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_432693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_432693 prefixEnd_432693 := by exact prefixLift 432693
  have htrace : WordTrace (prefixWord ++ tailWord_432693) baseStart_432693 baseEnd_432693 := by
    simpa [prefixWord, tailWord_432693, baseEnd_432693] using wordTrace_append hprefix tailTrace_432693
  have hstable : (prefixWord ++ tailWord_432693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432693).length < 2 ^ (prefixWord ++ tailWord_432693).sum := by decide
  have hdescent : baseEnd_432693 < baseStart_432693 := by decide
  rcases family_descends (prefixWord ++ tailWord_432693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432724 : List Nat := [2, 4, 1, 1, 1, 4, 1, 6]
def baseStart_432724 : Nat := 118140960795 + 432724 * 2 ^ 59
def prefixEnd_432724 : Nat := 4983230072969 + 3 ^ 40 * 432724 * 2
def baseEnd_432724 : Nat := 65835674884820799721465

theorem tailTrace_432724 : CollatzResearch.WordTrace tailWord_432724 prefixEnd_432724 65835674884820799721465 := by
  unfold tailWord_432724
  simp only [CollatzResearch.WordTrace]
  refine ⟨7891370442161163110280613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10521827256214884147040817 7891370442161163110280613)
  ·
    refine ⟨1479631957905218083177615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7891370442161163110280613 1479631957905218083177615)
    ·
      refine ⟨2219447936857827124766423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1479631957905218083177615 2219447936857827124766423)
      ·
        refine ⟨3329171905286740687149635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2219447936857827124766423 3329171905286740687149635)
        ·
          refine ⟨4993757857930111030724453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3329171905286740687149635 4993757857930111030724453)
          ·
            refine ⟨936329598361895818260835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4993757857930111030724453 936329598361895818260835)
            ·
              refine ⟨1404494397542843727391253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 936329598361895818260835 1404494397542843727391253)
              ·
                refine ⟨65835674884820799721465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1404494397542843727391253 65835674884820799721465)
                ·
                  rfl

theorem cell20_432724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 6].length) (baseStart_432724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_432724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_432724 prefixEnd_432724 := by exact prefixLift 432724
  have htrace : WordTrace (prefixWord ++ tailWord_432724) baseStart_432724 baseEnd_432724 := by
    simpa [prefixWord, tailWord_432724, baseEnd_432724] using wordTrace_append hprefix tailTrace_432724
  have hstable : (prefixWord ++ tailWord_432724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432724).length < 2 ^ (prefixWord ++ tailWord_432724).sum := by decide
  have hdescent : baseEnd_432724 < baseStart_432724 := by decide
  rcases family_descends (prefixWord ++ tailWord_432724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432741 : List Nat := [1, 3, 1, 3, 5, 1, 6]
def baseStart_432741 : Nat := 118140960795 + 432741 * 2 ^ 59
def prefixEnd_432741 : Nat := 4983230072969 + 3 ^ 40 * 432741 * 2
def baseEnd_432741 : Nat := 21946087101965099510851

theorem tailTrace_432741 : CollatzResearch.WordTrace tailWord_432741 prefixEnd_432741 21946087101965099510851 := by
  unfold tailWord_432741
  simp only [CollatzResearch.WordTrace]
  refine ⟨15783360925260738123930077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10522240616840492082620051 15783360925260738123930077)
  ·
    refine ⟨5918760346972776796473779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15783360925260738123930077 5918760346972776796473779)
    ·
      refine ⟨8878140520459165194710669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5918760346972776796473779 8878140520459165194710669)
      ·
        refine ⟨3329302695172186948016501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8878140520459165194710669 3329302695172186948016501)
        ·
          refine ⟨312122127672392526376547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3329302695172186948016501 312122127672392526376547)
          ·
            refine ⟨468183191508588789564821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312122127672392526376547 468183191508588789564821)
            ·
              refine ⟨21946087101965099510851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 468183191508588789564821 21946087101965099510851)
              ·
                rfl

theorem cell20_432741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 6].length) (baseStart_432741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_432741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_432741 prefixEnd_432741 := by exact prefixLift 432741
  have htrace : WordTrace (prefixWord ++ tailWord_432741) baseStart_432741 baseEnd_432741 := by
    simpa [prefixWord, tailWord_432741, baseEnd_432741] using wordTrace_append hprefix tailTrace_432741
  have hstable : (prefixWord ++ tailWord_432741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432741).length < 2 ^ (prefixWord ++ tailWord_432741).sum := by decide
  have hdescent : baseEnd_432741 < baseStart_432741 := by decide
  rcases family_descends (prefixWord ++ tailWord_432741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432793 : List Nat := [1, 2, 1, 2, 1, 2, 4, 5, 2]
def baseStart_432793 : Nat := 118140960795 + 432793 * 2 ^ 59
def prefixEnd_432793 : Nat := 4983230072969 + 3 ^ 40 * 432793 * 2
def baseEnd_432793 : Nat := 197538518134604825864113

theorem tailTrace_432793 : CollatzResearch.WordTrace tailWord_432793 prefixEnd_432793 197538518134604825864113 := by
  unfold tailWord_432793
  simp only [CollatzResearch.WordTrace]
  refine ⟨15785257521072351004823033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10523505014048234003215355 15785257521072351004823033)
  ·
    refine ⟨11838943140804263253617275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15785257521072351004823033 11838943140804263253617275)
    ·
      refine ⟨17758414711206394880425913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11838943140804263253617275 17758414711206394880425913)
      ·
        refine ⟨13318811033404796160319435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17758414711206394880425913 13318811033404796160319435)
        ·
          refine ⟨19978216550107194240479153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13318811033404796160319435 19978216550107194240479153)
          ·
            refine ⟨14983662412580395680359365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19978216550107194240479153 14983662412580395680359365)
            ·
              refine ⟨2809436702358824190067381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14983662412580395680359365 2809436702358824190067381)
              ·
                refine ⟨263384690846139767818817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2809436702358824190067381 263384690846139767818817)
                ·
                  refine ⟨197538518134604825864113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 263384690846139767818817 197538518134604825864113)
                  ·
                    rfl

theorem cell20_432793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 5, 2].length) (baseStart_432793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_432793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_432793 prefixEnd_432793 := by exact prefixLift 432793
  have htrace : WordTrace (prefixWord ++ tailWord_432793) baseStart_432793 baseEnd_432793 := by
    simpa [prefixWord, tailWord_432793, baseEnd_432793] using wordTrace_append hprefix tailTrace_432793
  have hstable : (prefixWord ++ tailWord_432793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432793).length < 2 ^ (prefixWord ++ tailWord_432793).sum := by decide
  have hdescent : baseEnd_432793 < baseStart_432793 := by decide
  rcases family_descends (prefixWord ++ tailWord_432793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432800 : List Nat := [2, 1, 1, 4, 5, 7]
def baseStart_432800 : Nat := 118140960795 + 432800 * 2 ^ 59
def prefixEnd_432800 : Nat := 4983230072969 + 3 ^ 40 * 432800 * 2
def baseEnd_432800 : Nat := 7316359745383107875213

theorem tailTrace_432800 : CollatzResearch.WordTrace tailWord_432800 prefixEnd_432800 7316359745383107875213 := by
  unfold tailWord_432800
  simp only [CollatzResearch.WordTrace]
  refine ⟨7892756416023495600163927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10523675221364660800218569 7892756416023495600163927)
  ·
    refine ⟨11839134624035243400245891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7892756416023495600163927 11839134624035243400245891)
    ·
      refine ⟨17758701936052865100368837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11839134624035243400245891 17758701936052865100368837)
      ·
        refine ⟨3329756613009912206319157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17758701936052865100368837 3329756613009912206319157)
        ·
          refine ⟨312164682469679269342421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3329756613009912206319157 312164682469679269342421)
          ·
            refine ⟨7316359745383107875213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 312164682469679269342421 7316359745383107875213)
            ·
              rfl

theorem cell20_432800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 7].length) (baseStart_432800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_432800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_432800 prefixEnd_432800 := by exact prefixLift 432800
  have htrace : WordTrace (prefixWord ++ tailWord_432800) baseStart_432800 baseEnd_432800 := by
    simpa [prefixWord, tailWord_432800, baseEnd_432800] using wordTrace_append hprefix tailTrace_432800
  have hstable : (prefixWord ++ tailWord_432800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432800).length < 2 ^ (prefixWord ++ tailWord_432800).sum := by decide
  have hdescent : baseEnd_432800 < baseStart_432800 := by decide
  rcases family_descends (prefixWord ++ tailWord_432800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432869 : List Nat := [1, 3, 1, 4, 1, 3, 2, 1, 4]
def baseStart_432869 : Nat := 118140960795 + 432869 * 2 ^ 59
def prefixEnd_432869 : Nat := 4983230072969 + 3 ^ 40 * 432869 * 2
def baseEnd_432869 : Nat := 197573206605486339330469

theorem tailTrace_432869 : CollatzResearch.WordTrace tailWord_432869 prefixEnd_432869 197573206605486339330469 := by
  unfold tailWord_432869
  simp only [CollatzResearch.WordTrace]
  refine ⟨15788029468797015984589661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10525352979198010656393107 15788029468797015984589661)
  ·
    refine ⟨5920511050798880994221123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15788029468797015984589661 5920511050798880994221123)
    ·
      refine ⟨8880766576198321491331685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5920511050798880994221123 8880766576198321491331685)
      ·
        refine ⟨1665143733037185279624691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8880766576198321491331685 1665143733037185279624691)
        ·
          refine ⟨2497715599555777919437037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1665143733037185279624691 2497715599555777919437037)
          ·
            refine ⟨936643349833416719788889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2497715599555777919437037 936643349833416719788889)
            ·
              refine ⟨702482512375062539841667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 936643349833416719788889 702482512375062539841667)
              ·
                refine ⟨1053723768562593809762501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 702482512375062539841667 1053723768562593809762501)
                ·
                  refine ⟨197573206605486339330469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1053723768562593809762501 197573206605486339330469)
                  ·
                    rfl

theorem cell20_432869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_432869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_432869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_432869 prefixEnd_432869 := by exact prefixLift 432869
  have htrace : WordTrace (prefixWord ++ tailWord_432869) baseStart_432869 baseEnd_432869 := by
    simpa [prefixWord, tailWord_432869, baseEnd_432869] using wordTrace_append hprefix tailTrace_432869
  have hstable : (prefixWord ++ tailWord_432869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432869).length < 2 ^ (prefixWord ++ tailWord_432869).sum := by decide
  have hdescent : baseEnd_432869 < baseStart_432869 := by decide
  rcases family_descends (prefixWord ++ tailWord_432869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432890 : List Nat := [3, 1, 1, 1, 1, 3, 4, 2, 4]
def baseStart_432890 : Nat := 118140960795 + 432890 * 2 ^ 59
def prefixEnd_432890 : Nat := 4983230072969 + 3 ^ 40 * 432890 * 2
def baseEnd_432890 : Nat := 197582791577703599630383

theorem tailTrace_432890 : CollatzResearch.WordTrace tailWord_432890 prefixEnd_432890 197582791577703599630383 := by
  unfold tailWord_432890
  simp only [CollatzResearch.WordTrace]
  refine ⟨3947198850430234142776031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10525863601147291047402749 3947198850430234142776031)
  ·
    refine ⟨5920798275645351214164047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3947198850430234142776031 5920798275645351214164047)
    ·
      refine ⟨8881197413468026821246071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5920798275645351214164047 8881197413468026821246071)
      ·
        refine ⟨13321796120202040231869107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8881197413468026821246071 13321796120202040231869107)
        ·
          refine ⟨19982694180303060347803661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13321796120202040231869107 19982694180303060347803661)
          ·
            refine ⟨7493510317613647630426373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19982694180303060347803661 7493510317613647630426373)
            ·
              refine ⟨1405033184552558930704945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7493510317613647630426373 1405033184552558930704945)
              ·
                refine ⟨1053774888414419198028709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1405033184552558930704945 1053774888414419198028709)
                ·
                  refine ⟨197582791577703599630383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1053774888414419198028709 197582791577703599630383)
                  ·
                    rfl

theorem cell20_432890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_432890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_432890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_432890 prefixEnd_432890 := by exact prefixLift 432890
  have htrace : WordTrace (prefixWord ++ tailWord_432890) baseStart_432890 baseEnd_432890 := by
    simpa [prefixWord, tailWord_432890, baseEnd_432890] using wordTrace_append hprefix tailTrace_432890
  have hstable : (prefixWord ++ tailWord_432890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432890).length < 2 ^ (prefixWord ++ tailWord_432890).sum := by decide
  have hdescent : baseEnd_432890 < baseStart_432890 := by decide
  rcases family_descends (prefixWord ++ tailWord_432890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432903 : List Nat := [1, 1, 4, 4, 1, 3, 1, 3, 2]
def baseStart_432903 : Nat := 118140960795 + 432903 * 2 ^ 59
def prefixEnd_432903 : Nat := 4983230072969 + 3 ^ 40 * 432903 * 2
def baseEnd_432903 : Nat := 197588725131933332196997

theorem tailTrace_432903 : CollatzResearch.WordTrace tailWord_432903 prefixEnd_432903 197588725131933332196997 := by
  unfold tailWord_432903
  simp only [CollatzResearch.WordTrace]
  refine ⟨15789269550673839791327363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10526179700449226527551575 15789269550673839791327363)
  ·
    refine ⟨23683904326010759686991045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15789269550673839791327363 23683904326010759686991045)
    ·
      refine ⟨4440732061127017441310821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23683904326010759686991045 4440732061127017441310821)
      ·
        refine ⟨832637261461315770245779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4440732061127017441310821 832637261461315770245779)
        ·
          refine ⟨1248955892191973655368669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 832637261461315770245779 1248955892191973655368669)
          ·
            refine ⟨468358459571990120763251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1248955892191973655368669 468358459571990120763251)
            ·
              refine ⟨702537689357985181144877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468358459571990120763251 702537689357985181144877)
              ·
                refine ⟨263451633509244442929329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 702537689357985181144877 263451633509244442929329)
                ·
                  refine ⟨197588725131933332196997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 263451633509244442929329 197588725131933332196997)
                  ·
                    rfl

theorem cell20_432903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 3, 2].length) (baseStart_432903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_432903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_432903 prefixEnd_432903 := by exact prefixLift 432903
  have htrace : WordTrace (prefixWord ++ tailWord_432903) baseStart_432903 baseEnd_432903 := by
    simpa [prefixWord, tailWord_432903, baseEnd_432903] using wordTrace_append hprefix tailTrace_432903
  have hstable : (prefixWord ++ tailWord_432903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432903).length < 2 ^ (prefixWord ++ tailWord_432903).sum := by decide
  have hdescent : baseEnd_432903 < baseStart_432903 := by decide
  rcases family_descends (prefixWord ++ tailWord_432903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432997 : List Nat := [1, 3, 1, 3, 1, 1, 4, 3, 3]
def baseStart_432997 : Nat := 118140960795 + 432997 * 2 ^ 59
def prefixEnd_432997 : Nat := 4983230072969 + 3 ^ 40 * 432997 * 2
def baseEnd_432997 : Nat := 197631629293286783063279

theorem tailTrace_432997 : CollatzResearch.WordTrace tailWord_432997 prefixEnd_432997 197631629293286783063279 := by
  unfold tailWord_432997
  simp only [CollatzResearch.WordTrace]
  refine ⟨15792698012333293845249245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10528465341555529230166163 15792698012333293845249245)
  ·
    refine ⟨5922261754624985191968467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15792698012333293845249245 5922261754624985191968467)
    ·
      refine ⟨8883392631937477787952701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5922261754624985191968467 8883392631937477787952701)
      ·
        refine ⟨3331272236976554170482263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8883392631937477787952701 3331272236976554170482263)
        ·
          refine ⟨4996908355464831255723395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3331272236976554170482263 4996908355464831255723395)
          ·
            refine ⟨7495362533197246883585093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4996908355464831255723395 7495362533197246883585093)
            ·
              refine ⟨1405380474974483790672205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7495362533197246883585093 1405380474974483790672205)
              ·
                refine ⟨527017678115431421502077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1405380474974483790672205 527017678115431421502077)
                ·
                  refine ⟨197631629293286783063279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 527017678115431421502077 197631629293286783063279)
                  ·
                    rfl

theorem cell20_432997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_432997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_432997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_432997 prefixEnd_432997 := by exact prefixLift 432997
  have htrace : WordTrace (prefixWord ++ tailWord_432997) baseStart_432997 baseEnd_432997 := by
    simpa [prefixWord, tailWord_432997, baseEnd_432997] using wordTrace_append hprefix tailTrace_432997
  have hstable : (prefixWord ++ tailWord_432997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432997).length < 2 ^ (prefixWord ++ tailWord_432997).sum := by decide
  have hdescent : baseEnd_432997 < baseStart_432997 := by decide
  rcases family_descends (prefixWord ++ tailWord_432997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433004 : List Nat := [2, 2, 1, 1, 4, 1, 3, 2, 4]
def baseStart_433004 : Nat := 118140960795 + 433004 * 2 ^ 59
def prefixEnd_433004 : Nat := 4983230072969 + 3 ^ 40 * 433004 * 2
def baseEnd_433004 : Nat := 197634824284025869829917

theorem tailTrace_433004 : CollatzResearch.WordTrace tailWord_433004 prefixEnd_433004 197634824284025869829917 := by
  unfold tailWord_433004
  simp only [CollatzResearch.WordTrace]
  refine ⟨7896476661653967020377033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10528635548871956027169377 7896476661653967020377033)
  ·
    refine ⟨5922357496240475265282775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7896476661653967020377033 5922357496240475265282775)
    ·
      refine ⟨8883536244360712897924163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5922357496240475265282775 8883536244360712897924163)
      ·
        refine ⟨13325304366541069346886245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8883536244360712897924163 13325304366541069346886245)
        ·
          refine ⟨2498494568726450502541171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13325304366541069346886245 2498494568726450502541171)
          ·
            refine ⟨3747741853089675753811757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2498494568726450502541171 3747741853089675753811757)
            ·
              refine ⟨1405403194908628407679409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3747741853089675753811757 1405403194908628407679409)
              ·
                refine ⟨1054052396181471305759557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1405403194908628407679409 1054052396181471305759557)
                ·
                  refine ⟨197634824284025869829917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1054052396181471305759557 197634824284025869829917)
                  ·
                    rfl

theorem cell20_433004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_433004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433004 prefixEnd_433004 := by exact prefixLift 433004
  have htrace : WordTrace (prefixWord ++ tailWord_433004) baseStart_433004 baseEnd_433004 := by
    simpa [prefixWord, tailWord_433004, baseEnd_433004] using wordTrace_append hprefix tailTrace_433004
  have hstable : (prefixWord ++ tailWord_433004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433004).length < 2 ^ (prefixWord ++ tailWord_433004).sum := by decide
  have hdescent : baseEnd_433004 < baseStart_433004 := by decide
  rcases family_descends (prefixWord ++ tailWord_433004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433018 : List Nat := [3, 1, 1, 1, 1, 1, 3, 4, 5]
def baseStart_433018 : Nat := 118140960795 + 433018 * 2 ^ 59
def prefixEnd_433018 : Nat := 4983230072969 + 3 ^ 40 * 433018 * 2
def baseEnd_433018 : Nat := 197641214265504043363193

theorem tailTrace_433018 : CollatzResearch.WordTrace tailWord_433018 prefixEnd_433018 197641214265504043363193 := by
  unfold tailWord_433018
  simp only [CollatzResearch.WordTrace]
  refine ⟨3948365986314303607940927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10528975963504809621175805 3948365986314303607940927)
  ·
    refine ⟨5922548979471455411911391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3948365986314303607940927 5922548979471455411911391)
    ·
      refine ⟨8883823469207183117867087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5922548979471455411911391 8883823469207183117867087)
      ·
        refine ⟨13325735203810774676800631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8883823469207183117867087 13325735203810774676800631)
        ·
          refine ⟨19988602805716162015200947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13325735203810774676800631 19988602805716162015200947)
          ·
            refine ⟨29982904208574243022801421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19988602805716162015200947 29982904208574243022801421)
            ·
              refine ⟨11243589078215341133550533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29982904208574243022801421 11243589078215341133550533)
              ·
                refine ⟨2108172952165376462540725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11243589078215341133550533 2108172952165376462540725)
                ·
                  refine ⟨197641214265504043363193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2108172952165376462540725 197641214265504043363193)
                  ·
                    rfl

theorem cell20_433018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_433018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433018 prefixEnd_433018 := by exact prefixLift 433018
  have htrace : WordTrace (prefixWord ++ tailWord_433018) baseStart_433018 baseEnd_433018 := by
    simpa [prefixWord, tailWord_433018, baseEnd_433018] using wordTrace_append hprefix tailTrace_433018
  have hstable : (prefixWord ++ tailWord_433018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433018).length < 2 ^ (prefixWord ++ tailWord_433018).sum := by decide
  have hdescent : baseEnd_433018 < baseStart_433018 := by decide
  rcases family_descends (prefixWord ++ tailWord_433018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433021 : List Nat := [1, 4, 1, 1, 2, 1, 3, 5, 2]
def baseStart_433021 : Nat := 118140960795 + 433021 * 2 ^ 59
def prefixEnd_433021 : Nat := 4983230072969 + 3 ^ 40 * 433021 * 2
def baseEnd_433021 : Nat := 197642583547249366263181

theorem tailTrace_433021 : CollatzResearch.WordTrace tailWord_433021 prefixEnd_433021 197642583547249366263181 := by
  unfold tailWord_433021
  simp only [CollatzResearch.WordTrace]
  refine ⟨15793573364246345944122917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10529048909497563962748611 15793573364246345944122917)
  ·
    refine ⟨2961295005796189864523047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15793573364246345944122917 2961295005796189864523047)
    ·
      refine ⟨4441942508694284796784571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2961295005796189864523047 4441942508694284796784571)
      ·
        refine ⟨6662913763041427195176857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4441942508694284796784571 6662913763041427195176857)
        ·
          refine ⟨4997185322281070396382643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6662913763041427195176857 4997185322281070396382643)
          ·
            refine ⟨7495777983421605594573965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4997185322281070396382643 7495777983421605594573965)
            ·
              refine ⟨2810916743783102097965237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7495777983421605594573965 2810916743783102097965237)
              ·
                refine ⟨263523444729665821684241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2810916743783102097965237 263523444729665821684241)
                ·
                  refine ⟨197642583547249366263181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 263523444729665821684241 197642583547249366263181)
                  ·
                    rfl

theorem cell20_433021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_433021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433021 prefixEnd_433021 := by exact prefixLift 433021
  have htrace : WordTrace (prefixWord ++ tailWord_433021) baseStart_433021 baseEnd_433021 := by
    simpa [prefixWord, tailWord_433021, baseEnd_433021] using wordTrace_append hprefix tailTrace_433021
  have hstable : (prefixWord ++ tailWord_433021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433021).length < 2 ^ (prefixWord ++ tailWord_433021).sum := by decide
  have hdescent : baseEnd_433021 < baseStart_433021 := by decide
  rcases family_descends (prefixWord ++ tailWord_433021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433035 : List Nat := [1, 1, 1, 1, 4, 2, 5, 2, 3]
def baseStart_433035 : Nat := 118140960795 + 433035 * 2 ^ 59
def prefixEnd_433035 : Nat := 4983230072969 + 3 ^ 40 * 433035 * 2
def baseEnd_433035 : Nat := 197648973528727539796457

theorem tailTrace_433035 : CollatzResearch.WordTrace tailWord_433035 prefixEnd_433035 197648973528727539796457 := by
  unfold tailWord_433035
  simp only [CollatzResearch.WordTrace]
  refine ⟨15794083986195626335132559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10529389324130417556755039 15794083986195626335132559)
  ·
    refine ⟨23691125979293439502698839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15794083986195626335132559 23691125979293439502698839)
    ·
      refine ⟨35536688968940159254048259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23691125979293439502698839 35536688968940159254048259)
      ·
        refine ⟨53305033453410238881072389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35536688968940159254048259 53305033453410238881072389)
        ·
          refine ⟨9994693772514419790201073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53305033453410238881072389 9994693772514419790201073)
          ·
            refine ⟨7496020329385814842650805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9994693772514419790201073 7496020329385814842650805)
            ·
              refine ⟨702751905879920141498513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7496020329385814842650805 702751905879920141498513)
              ·
                refine ⟨527063929409940106123885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 702751905879920141498513 527063929409940106123885)
                ·
                  refine ⟨197648973528727539796457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 527063929409940106123885 197648973528727539796457)
                  ·
                    rfl

theorem cell20_433035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2, 3].length) (baseStart_433035 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433035 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433035 prefixEnd_433035 := by exact prefixLift 433035
  have htrace : WordTrace (prefixWord ++ tailWord_433035) baseStart_433035 baseEnd_433035 := by
    simpa [prefixWord, tailWord_433035, baseEnd_433035] using wordTrace_append hprefix tailTrace_433035
  have hstable : (prefixWord ++ tailWord_433035).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433035).length < 2 ^ (prefixWord ++ tailWord_433035).sum := by decide
  have hdescent : baseEnd_433035 < baseStart_433035 := by decide
  rcases family_descends (prefixWord ++ tailWord_433035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433163 : List Nat := [1, 1, 1, 1, 6, 2, 3, 5]
def baseStart_433163 : Nat := 118140960795 + 433163 * 2 ^ 59
def prefixEnd_433163 : Nat := 4983230072969 + 3 ^ 40 * 433163 * 2
def baseEnd_433163 : Nat := 65902465405509327843089

theorem tailTrace_433163 : CollatzResearch.WordTrace tailWord_433163 prefixEnd_433163 65902465405509327843089 := by
  unfold tailWord_433163
  simp only [CollatzResearch.WordTrace]
  refine ⟨15798752529731904195792143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10532501686487936130528095 15798752529731904195792143)
  ·
    refine ⟨23698128794597856293688215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15798752529731904195792143 23698128794597856293688215)
    ·
      refine ⟨35547193191896784440532323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23698128794597856293688215 35547193191896784440532323)
      ·
        refine ⟨53320789787845176660798485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35547193191896784440532323 53320789787845176660798485)
        ·
          refine ⟨2499412021305242655974929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53320789787845176660798485 2499412021305242655974929)
          ·
            refine ⟨1874559015978931991981197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2499412021305242655974929 1874559015978931991981197)
            ·
              refine ⟨702959630992099496992949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1874559015978931991981197 702959630992099496992949)
              ·
                refine ⟨65902465405509327843089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 702959630992099496992949 65902465405509327843089)
                ·
                  rfl

theorem cell20_433163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 5].length) (baseStart_433163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433163 prefixEnd_433163 := by exact prefixLift 433163
  have htrace : WordTrace (prefixWord ++ tailWord_433163) baseStart_433163 baseEnd_433163 := by
    simpa [prefixWord, tailWord_433163, baseEnd_433163] using wordTrace_append hprefix tailTrace_433163
  have hstable : (prefixWord ++ tailWord_433163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433163).length < 2 ^ (prefixWord ++ tailWord_433163).sum := by decide
  have hdescent : baseEnd_433163 < baseStart_433163 := by decide
  rcases family_descends (prefixWord ++ tailWord_433163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433177 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 6]
def baseStart_433177 : Nat := 118140960795 + 433177 * 2 ^ 59
def prefixEnd_433177 : Nat := 4983230072969 + 3 ^ 40 * 433177 * 2
def baseEnd_433177 : Nat := 197713786198006157062543

theorem tailTrace_433177 : CollatzResearch.WordTrace tailWord_433177 prefixEnd_433177 197713786198006157062543 := by
  unfold tailWord_433177
  simp only [CollatzResearch.WordTrace]
  refine ⟨15799263151681184586801785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10532842101120789724534523 15799263151681184586801785)
  ·
    refine ⟨11849447363760888440101339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15799263151681184586801785 11849447363760888440101339)
    ·
      refine ⟨17774171045641332660152009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11849447363760888440101339 17774171045641332660152009)
      ·
        refine ⟨13330628284230999495114007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17774171045641332660152009 13330628284230999495114007)
        ·
          refine ⟨19995942426346499242671011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13330628284230999495114007 19995942426346499242671011)
          ·
            refine ⟨29993913639519748864006517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19995942426346499242671011 29993913639519748864006517)
            ·
              refine ⟨2811929403704976456000611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29993913639519748864006517 2811929403704976456000611)
              ·
                refine ⟨4217894105557464684000917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2811929403704976456000611 4217894105557464684000917)
                ·
                  refine ⟨197713786198006157062543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4217894105557464684000917 197713786198006157062543)
                  ·
                    rfl

theorem cell20_433177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_433177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433177 prefixEnd_433177 := by exact prefixLift 433177
  have htrace : WordTrace (prefixWord ++ tailWord_433177) baseStart_433177 baseEnd_433177 := by
    simpa [prefixWord, tailWord_433177, baseEnd_433177] using wordTrace_append hprefix tailTrace_433177
  have hstable : (prefixWord ++ tailWord_433177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433177).length < 2 ^ (prefixWord ++ tailWord_433177).sum := by decide
  have hdescent : baseEnd_433177 < baseStart_433177 := by decide
  rcases family_descends (prefixWord ++ tailWord_433177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433204 : List Nat := [2, 5, 1, 2, 1, 2, 1, 1, 5]
def baseStart_433204 : Nat := 118140960795 + 433204 * 2 ^ 59
def prefixEnd_433204 : Nat := 4983230072969 + 3 ^ 40 * 433204 * 2
def baseEnd_433204 : Nat := 197726109733714063162433

theorem tailTrace_433204 : CollatzResearch.WordTrace tailWord_433204 prefixEnd_433204 197726109733714063162433 := by
  unfold tailWord_433204
  simp only [CollatzResearch.WordTrace]
  refine ⟨7900123961291684099017333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10533498615055578798689777 7900123961291684099017333)
  ·
    refine ⟨740636621371095384282875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7900123961291684099017333 740636621371095384282875)
    ·
      refine ⟨1110954932056643076424313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 740636621371095384282875 1110954932056643076424313)
      ·
        refine ⟨833216199042482307318235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1110954932056643076424313 833216199042482307318235)
        ·
          refine ⟨1249824298563723460977353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 833216199042482307318235 1249824298563723460977353)
          ·
            refine ⟨937368223922792595733015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1249824298563723460977353 937368223922792595733015)
            ·
              refine ⟨1406052335884188893599523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 937368223922792595733015 1406052335884188893599523)
              ·
                refine ⟨2109078503826283340399285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1406052335884188893599523 2109078503826283340399285)
                ·
                  refine ⟨197726109733714063162433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2109078503826283340399285 197726109733714063162433)
                  ·
                    rfl

theorem cell20_433204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_433204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433204 prefixEnd_433204 := by exact prefixLift 433204
  have htrace : WordTrace (prefixWord ++ tailWord_433204) baseStart_433204 baseEnd_433204 := by
    simpa [prefixWord, tailWord_433204, baseEnd_433204] using wordTrace_append hprefix tailTrace_433204
  have hstable : (prefixWord ++ tailWord_433204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433204).length < 2 ^ (prefixWord ++ tailWord_433204).sum := by decide
  have hdescent : baseEnd_433204 < baseStart_433204 := by decide
  rcases family_descends (prefixWord ++ tailWord_433204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433249 : List Nat := [1, 2, 3, 1, 1, 2, 5, 3, 2]
def baseStart_433249 : Nat := 118140960795 + 433249 * 2 ^ 59
def prefixEnd_433249 : Nat := 4983230072969 + 3 ^ 40 * 433249 * 2
def baseEnd_433249 : Nat := 197746648959893906662249

theorem tailTrace_433249 : CollatzResearch.WordTrace tailWord_433249 prefixEnd_433249 197746648959893906662249 := by
  unfold tailWord_433249
  simp only [CollatzResearch.WordTrace]
  refine ⟨15801889207420340883422801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10534592804946893922281867 15801889207420340883422801)
  ·
    refine ⟨11851416905565255662567101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15801889207420340883422801 11851416905565255662567101)
    ·
      refine ⟨4444281339586970873462663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11851416905565255662567101 4444281339586970873462663)
      ·
        refine ⟨6666422009380456310193995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4444281339586970873462663 6666422009380456310193995)
        ·
          refine ⟨9999633014070684465290993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6666422009380456310193995 9999633014070684465290993)
          ·
            refine ⟨7499724760553013348968245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9999633014070684465290993 7499724760553013348968245)
            ·
              refine ⟨703099196301845001465773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7499724760553013348968245 703099196301845001465773)
              ·
                refine ⟨263662198613191875549665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 703099196301845001465773 263662198613191875549665)
                ·
                  refine ⟨197746648959893906662249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 263662198613191875549665 197746648959893906662249)
                  ·
                    rfl

theorem cell20_433249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 3, 2].length) (baseStart_433249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433249 prefixEnd_433249 := by exact prefixLift 433249
  have htrace : WordTrace (prefixWord ++ tailWord_433249) baseStart_433249 baseEnd_433249 := by
    simpa [prefixWord, tailWord_433249, baseEnd_433249] using wordTrace_append hprefix tailTrace_433249
  have hstable : (prefixWord ++ tailWord_433249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433249).length < 2 ^ (prefixWord ++ tailWord_433249).sum := by decide
  have hdescent : baseEnd_433249 < baseStart_433249 := by decide
  rcases family_descends (prefixWord ++ tailWord_433249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433266 : List Nat := [3, 2, 1, 2, 2, 1, 5, 2, 2]
def baseStart_433266 : Nat := 118140960795 + 433266 * 2 ^ 59
def prefixEnd_433266 : Nat := 4983230072969 + 3 ^ 40 * 433266 * 2
def baseEnd_433266 : Nat := 197754408223117403095513

theorem tailTrace_433266 : CollatzResearch.WordTrace tailWord_433266 prefixEnd_433266 197754408223117403095513 := by
  unfold tailWord_433266
  simp only [CollatzResearch.WordTrace]
  refine ⟨3950627312089688196697913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10535006165572501857861101 3950627312089688196697913)
  ·
    refine ⟨2962970484067266147523435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3950627312089688196697913 2962970484067266147523435)
    ·
      refine ⟨4444455726100899221285153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2962970484067266147523435 4444455726100899221285153)
      ·
        refine ⟨3333341794575674415963865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4444455726100899221285153 3333341794575674415963865)
        ·
          refine ⟨2500006345931755811972899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3333341794575674415963865 2500006345931755811972899)
          ·
            refine ⟨3750009518897633717959349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2500006345931755811972899 3750009518897633717959349)
            ·
              refine ⟨351563392396653161058689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3750009518897633717959349 351563392396653161058689)
              ·
                refine ⟨263672544297489870794017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 351563392396653161058689 263672544297489870794017)
                ·
                  refine ⟨197754408223117403095513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 263672544297489870794017 197754408223117403095513)
                  ·
                    rfl

theorem cell20_433266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_433266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433266 prefixEnd_433266 := by exact prefixLift 433266
  have htrace : WordTrace (prefixWord ++ tailWord_433266) baseStart_433266 baseEnd_433266 := by
    simpa [prefixWord, tailWord_433266, baseEnd_433266] using wordTrace_append hprefix tailTrace_433266
  have hstable : (prefixWord ++ tailWord_433266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433266).length < 2 ^ (prefixWord ++ tailWord_433266).sum := by decide
  have hdescent : baseEnd_433266 < baseStart_433266 := by decide
  rcases family_descends (prefixWord ++ tailWord_433266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433277 : List Nat := [1, 4, 1, 1, 3, 1, 4, 5]
def baseStart_433277 : Nat := 118140960795 + 433277 * 2 ^ 59
def prefixEnd_433277 : Nat := 4983230072969 + 3 ^ 40 * 433277 * 2
def baseEnd_433277 : Nat := 65919809640950084576267

theorem tailTrace_433277 : CollatzResearch.WordTrace tailWord_433277 prefixEnd_433277 65919809640950084576267 := by
  unfold tailWord_433277
  simp only [CollatzResearch.WordTrace]
  refine ⟨15802910451318901665442085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10535273634212601110294723 15802910451318901665442085)
  ·
    refine ⟨2963045709622294062270391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15802910451318901665442085 2963045709622294062270391)
    ·
      refine ⟨4444568564433441093405587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2963045709622294062270391 4444568564433441093405587)
      ·
        refine ⟨6666852846650161640108381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4444568564433441093405587 6666852846650161640108381)
        ·
          refine ⟨2500069817493810615040643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6666852846650161640108381 2500069817493810615040643)
          ·
            refine ⟨3750104726240715922560965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2500069817493810615040643 3750104726240715922560965)
            ·
              refine ⟨703144636170134235480181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3750104726240715922560965 703144636170134235480181)
              ·
                refine ⟨65919809640950084576267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 703144636170134235480181 65919809640950084576267)
                ·
                  rfl

theorem cell20_433277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 5].length) (baseStart_433277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433277 prefixEnd_433277 := by exact prefixLift 433277
  have htrace : WordTrace (prefixWord ++ tailWord_433277) baseStart_433277 baseEnd_433277 := by
    simpa [prefixWord, tailWord_433277, baseEnd_433277] using wordTrace_append hprefix tailTrace_433277
  have hstable : (prefixWord ++ tailWord_433277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433277).length < 2 ^ (prefixWord ++ tailWord_433277).sum := by decide
  have hdescent : baseEnd_433277 < baseStart_433277 := by decide
  rcases family_descends (prefixWord ++ tailWord_433277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433291 : List Nat := [1, 1, 1, 1, 4, 1, 1, 6, 4]
def baseStart_433291 : Nat := 118140960795 + 433291 * 2 ^ 59
def prefixEnd_433291 : Nat := 4983230072969 + 3 ^ 40 * 433291 * 2
def baseEnd_433291 : Nat := 197765818904328427262077

theorem tailTrace_433291 : CollatzResearch.WordTrace tailWord_433291 prefixEnd_433291 197765818904328427262077 := by
  unfold tailWord_433291
  simp only [CollatzResearch.WordTrace]
  refine ⟨15803421073268182056451727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10535614048845454704301151 15803421073268182056451727)
  ·
    refine ⟨23705131609902273084677591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15803421073268182056451727 23705131609902273084677591)
    ·
      refine ⟨35557697414853409627016387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23705131609902273084677591 35557697414853409627016387)
      ·
        refine ⟨53336546122280114440524581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35557697414853409627016387 53336546122280114440524581)
        ·
          refine ⟨10000602397927521457598359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53336546122280114440524581 10000602397927521457598359)
          ·
            refine ⟨15000903596891282186397539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10000602397927521457598359 15000903596891282186397539)
            ·
              refine ⟨22501355395336923279596309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15000903596891282186397539 22501355395336923279596309)
              ·
                refine ⟨1054751034156418278731077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22501355395336923279596309 1054751034156418278731077)
                ·
                  refine ⟨197765818904328427262077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1054751034156418278731077 197765818904328427262077)
                  ·
                    rfl

theorem cell20_433291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 4].length) (baseStart_433291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433291 prefixEnd_433291 := by exact prefixLift 433291
  have htrace : WordTrace (prefixWord ++ tailWord_433291) baseStart_433291 baseEnd_433291 := by
    simpa [prefixWord, tailWord_433291, baseEnd_433291] using wordTrace_append hprefix tailTrace_433291
  have hstable : (prefixWord ++ tailWord_433291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433291).length < 2 ^ (prefixWord ++ tailWord_433291).sum := by decide
  have hdescent : baseEnd_433291 < baseStart_433291 := by decide
  rcases family_descends (prefixWord ++ tailWord_433291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433336 : List Nat := [2, 1, 2, 1, 2, 1, 2, 9]
def baseStart_433336 : Nat := 118140960795 + 433336 * 2 ^ 59
def prefixEnd_433336 : Nat := 4983230072969 + 3 ^ 40 * 433336 * 2
def baseEnd_433336 : Nat := 65928786043502756920631

theorem tailTrace_433336 : CollatzResearch.WordTrace tailWord_433336 prefixEnd_433336 65928786043502756920631 := by
  unfold tailWord_433336
  simp only [CollatzResearch.WordTrace]
  refine ⟨7902531179052577370919931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10536708238736769827893241 7902531179052577370919931)
  ·
    refine ⟨11853796768578866056379897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7902531179052577370919931 11853796768578866056379897)
    ·
      refine ⟨8890347576434149542284923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11853796768578866056379897 8890347576434149542284923)
      ·
        refine ⟨13335521364651224313427385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8890347576434149542284923 13335521364651224313427385)
        ·
          refine ⟨10001641023488418235070539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13335521364651224313427385 10001641023488418235070539)
          ·
            refine ⟨15002461535232627352605809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10001641023488418235070539 15002461535232627352605809)
            ·
              refine ⟨11251846151424470514454357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15002461535232627352605809 11251846151424470514454357)
              ·
                refine ⟨65928786043502756920631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11251846151424470514454357 65928786043502756920631)
                ·
                  rfl

theorem cell20_433336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 9].length) (baseStart_433336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433336 prefixEnd_433336 := by exact prefixLift 433336
  have htrace : WordTrace (prefixWord ++ tailWord_433336) baseStart_433336 baseEnd_433336 := by
    simpa [prefixWord, tailWord_433336, baseEnd_433336] using wordTrace_append hprefix tailTrace_433336
  have hstable : (prefixWord ++ tailWord_433336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433336).length < 2 ^ (prefixWord ++ tailWord_433336).sum := by decide
  have hdescent : baseEnd_433336 < baseStart_433336 := by decide
  rcases family_descends (prefixWord ++ tailWord_433336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433373 : List Nat := [1, 4, 3, 2, 2, 2, 1, 2, 3]
def baseStart_433373 : Nat := 118140960795 + 433373 * 2 ^ 59
def prefixEnd_433373 : Nat := 4983230072969 + 3 ^ 40 * 433373 * 2
def baseEnd_433373 : Nat := 197803245938700586528409

theorem tailTrace_433373 : CollatzResearch.WordTrace tailWord_433373 prefixEnd_433373 197803245938700586528409 := by
  unfold tailWord_433373
  simp only [CollatzResearch.WordTrace]
  refine ⟨15806411858971110060936773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10537607905980740040624515 15806411858971110060936773)
  ·
    refine ⟨2963702223557083136425645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15806411858971110060936773 2963702223557083136425645)
    ·
      refine ⟨1111388333833906176159617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2963702223557083136425645 1111388333833906176159617)
      ·
        refine ⟨833541250375429632119713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1111388333833906176159617 833541250375429632119713)
        ·
          refine ⟨625155937781572224089785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 833541250375429632119713 625155937781572224089785)
          ·
            refine ⟨468866953336179168067339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 625155937781572224089785 468866953336179168067339)
            ·
              refine ⟨703300430004268752101009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468866953336179168067339 703300430004268752101009)
              ·
                refine ⟨527475322503201564075757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 703300430004268752101009 527475322503201564075757)
                ·
                  refine ⟨197803245938700586528409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 527475322503201564075757 197803245938700586528409)
                  ·
                    rfl

theorem cell20_433373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_433373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433373 prefixEnd_433373 := by exact prefixLift 433373
  have htrace : WordTrace (prefixWord ++ tailWord_433373) baseStart_433373 baseEnd_433373 := by
    simpa [prefixWord, tailWord_433373, baseEnd_433373] using wordTrace_append hprefix tailTrace_433373
  have hstable : (prefixWord ++ tailWord_433373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433373).length < 2 ^ (prefixWord ++ tailWord_433373).sum := by decide
  have hdescent : baseEnd_433373 < baseStart_433373 := by decide
  rcases family_descends (prefixWord ++ tailWord_433373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433377 : List Nat := [1, 2, 3, 1, 3, 2, 3, 2, 3]
def baseStart_433377 : Nat := 118140960795 + 433377 * 2 ^ 59
def prefixEnd_433377 : Nat := 4983230072969 + 3 ^ 40 * 433377 * 2
def baseEnd_433377 : Nat := 197805071647694350395059

theorem tailTrace_433377 : CollatzResearch.WordTrace tailWord_433377 prefixEnd_433377 197805071647694350395059 := by
  unfold tailWord_433377
  simp only [CollatzResearch.WordTrace]
  refine ⟨15806557750956618744082385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10537705167304412496054923 15806557750956618744082385)
  ·
    refine ⟨11854918313217464058061789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15806557750956618744082385 11854918313217464058061789)
    ·
      refine ⟨4445594367456549021773171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11854918313217464058061789 4445594367456549021773171)
      ·
        refine ⟨6668391551184823532659757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4445594367456549021773171 6668391551184823532659757)
        ·
          refine ⟨2500646831694308824747409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6668391551184823532659757 2500646831694308824747409)
          ·
            refine ⟨1875485123770731618560557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2500646831694308824747409 1875485123770731618560557)
            ·
              refine ⟨703306921414024356960209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1875485123770731618560557 703306921414024356960209)
              ·
                refine ⟨527480191060518267720157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 703306921414024356960209 527480191060518267720157)
                ·
                  refine ⟨197805071647694350395059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 527480191060518267720157 197805071647694350395059)
                  ·
                    rfl

theorem cell20_433377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 3].length) (baseStart_433377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433377 prefixEnd_433377 := by exact prefixLift 433377
  have htrace : WordTrace (prefixWord ++ tailWord_433377) baseStart_433377 baseEnd_433377 := by
    simpa [prefixWord, tailWord_433377, baseEnd_433377] using wordTrace_append hprefix tailTrace_433377
  have hstable : (prefixWord ++ tailWord_433377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433377).length < 2 ^ (prefixWord ++ tailWord_433377).sum := by decide
  have hdescent : baseEnd_433377 < baseStart_433377 := by decide
  rcases family_descends (prefixWord ++ tailWord_433377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433384 : List Nat := [2, 1, 4, 1, 2, 1, 4, 1, 4]
def baseStart_433384 : Nat := 118140960795 + 433384 * 2 ^ 59
def prefixEnd_433384 : Nat := 4983230072969 + 3 ^ 40 * 433384 * 2
def baseEnd_433384 : Nat := 197808266638433437161697

theorem tailTrace_433384 : CollatzResearch.WordTrace tailWord_433384 prefixEnd_433384 197808266638433437161697 := by
  unfold tailWord_433384
  simp only [CollatzResearch.WordTrace]
  refine ⟨7903406530965629469793603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10537875374620839293058137 7903406530965629469793603)
  ·
    refine ⟨11855109796448444204690405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7903406530965629469793603 11855109796448444204690405)
    ·
      refine ⟨2222833086834083288379451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11855109796448444204690405 2222833086834083288379451)
      ·
        refine ⟨3334249630251124932569177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2222833086834083288379451 3334249630251124932569177)
        ·
          refine ⟨2500687222688343699426883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3334249630251124932569177 2500687222688343699426883)
          ·
            refine ⟨3751030834032515549140325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2500687222688343699426883 3751030834032515549140325)
            ·
              refine ⟨703318281381096665463811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3751030834032515549140325 703318281381096665463811)
              ·
                refine ⟨1054977422071644998195717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 703318281381096665463811 1054977422071644998195717)
                ·
                  refine ⟨197808266638433437161697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1054977422071644998195717 197808266638433437161697)
                  ·
                    rfl

theorem cell20_433384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 4].length) (baseStart_433384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433384 prefixEnd_433384 := by exact prefixLift 433384
  have htrace : WordTrace (prefixWord ++ tailWord_433384) baseStart_433384 baseEnd_433384 := by
    simpa [prefixWord, tailWord_433384, baseEnd_433384] using wordTrace_append hprefix tailTrace_433384
  have hstable : (prefixWord ++ tailWord_433384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433384).length < 2 ^ (prefixWord ++ tailWord_433384).sum := by decide
  have hdescent : baseEnd_433384 < baseStart_433384 := by decide
  rcases family_descends (prefixWord ++ tailWord_433384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433436 : List Nat := [2, 2, 3, 1, 1, 1, 4, 1, 5]
def baseStart_433436 : Nat := 118140960795 + 433436 * 2 ^ 59
def prefixEnd_433436 : Nat := 4983230072969 + 3 ^ 40 * 433436 * 2
def baseEnd_433436 : Nat := 197832000855352367428151

theorem tailTrace_433436 : CollatzResearch.WordTrace tailWord_433436 prefixEnd_433436 197832000855352367428151 := by
  unfold tailWord_433436
  simp only [CollatzResearch.WordTrace]
  refine ⟨7904354828871435910240081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10539139771828581213653441 7904354828871435910240081)
  ·
    refine ⟨5928266121653576932680061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7904354828871435910240081 5928266121653576932680061)
    ·
      refine ⟨2223099795620091349755023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5928266121653576932680061 2223099795620091349755023)
      ·
        refine ⟨3334649693430137024632535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2223099795620091349755023 3334649693430137024632535)
        ·
          refine ⟨5001974540145205536948803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3334649693430137024632535 5001974540145205536948803)
          ·
            refine ⟨7502961810217808305423205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5001974540145205536948803 7502961810217808305423205)
            ·
              refine ⟨1406805339415839057266851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7502961810217808305423205 1406805339415839057266851)
              ·
                refine ⟨2110208009123758585900277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1406805339415839057266851 2110208009123758585900277)
                ·
                  refine ⟨197832000855352367428151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2110208009123758585900277 197832000855352367428151)
                  ·
                    rfl

theorem cell20_433436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_433436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433436 prefixEnd_433436 := by exact prefixLift 433436
  have htrace : WordTrace (prefixWord ++ tailWord_433436) baseStart_433436 baseEnd_433436 := by
    simpa [prefixWord, tailWord_433436, baseEnd_433436] using wordTrace_append hprefix tailTrace_433436
  have hstable : (prefixWord ++ tailWord_433436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433436).length < 2 ^ (prefixWord ++ tailWord_433436).sum := by decide
  have hdescent : baseEnd_433436 < baseStart_433436 := by decide
  rcases family_descends (prefixWord ++ tailWord_433436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433439 : List Nat := [1, 1, 2, 4, 4, 2, 1, 1, 4]
def baseStart_433439 : Nat := 118140960795 + 433439 * 2 ^ 59
def prefixEnd_433439 : Nat := 4983230072969 + 3 ^ 40 * 433439 * 2
def baseEnd_433439 : Nat := 197833370137097690328139

theorem tailTrace_433439 : CollatzResearch.WordTrace tailWord_433439 prefixEnd_433439 197833370137097690328139 := by
  unfold tailWord_433439
  simp only [CollatzResearch.WordTrace]
  refine ⟨15808819076732003332839371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10539212717821335555226247 15808819076732003332839371)
  ·
    refine ⟨23713228615098004999259057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15808819076732003332839371 23713228615098004999259057)
    ·
      refine ⟨17784921461323503749444293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23713228615098004999259057 17784921461323503749444293)
      ·
        refine ⟨3334672773998156953020805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17784921461323503749444293 3334672773998156953020805)
        ·
          refine ⟨625251145124654428691401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3334672773998156953020805 625251145124654428691401)
          ·
            refine ⟨468938358843490821518551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 625251145124654428691401 468938358843490821518551)
            ·
              refine ⟨703407538265236232277827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468938358843490821518551 703407538265236232277827)
              ·
                refine ⟨1055111307397854348416741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 703407538265236232277827 1055111307397854348416741)
                ·
                  refine ⟨197833370137097690328139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1055111307397854348416741 197833370137097690328139)
                  ·
                    rfl

theorem cell20_433439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 4].length) (baseStart_433439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433439 prefixEnd_433439 := by exact prefixLift 433439
  have htrace : WordTrace (prefixWord ++ tailWord_433439) baseStart_433439 baseEnd_433439 := by
    simpa [prefixWord, tailWord_433439, baseEnd_433439] using wordTrace_append hprefix tailTrace_433439
  have hstable : (prefixWord ++ tailWord_433439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433439).length < 2 ^ (prefixWord ++ tailWord_433439).sum := by decide
  have hdescent : baseEnd_433439 < baseStart_433439 := by decide
  rcases family_descends (prefixWord ++ tailWord_433439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433460 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 6]
def baseStart_433460 : Nat := 118140960795 + 433460 * 2 ^ 59
def prefixEnd_433460 : Nat := 4983230072969 + 3 ^ 40 * 433460 * 2
def baseEnd_433460 : Nat := 197842955109314950628053

theorem tailTrace_433460 : CollatzResearch.WordTrace tailWord_433460 prefixEnd_433460 197842955109314950628053 := by
  unfold tailWord_433460
  simp only [CollatzResearch.WordTrace]
  refine ⟨7904792504827961959676917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10539723339770615946235889 7904792504827961959676917)
  ·
    refine ⟨741074297327621433719711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7904792504827961959676917 741074297327621433719711)
    ·
      refine ⟨1111611445991432150579567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 741074297327621433719711 1111611445991432150579567)
      ·
        refine ⟨1667417168987148225869351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1111611445991432150579567 1667417168987148225869351)
        ·
          refine ⟨2501125753480722338804027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1667417168987148225869351 2501125753480722338804027)
          ·
            refine ⟨3751688630221083508206041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2501125753480722338804027 3751688630221083508206041)
            ·
              refine ⟨2813766472665812631154531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3751688630221083508206041 2813766472665812631154531)
              ·
                refine ⟨4220649708998718946731797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2813766472665812631154531 4220649708998718946731797)
                ·
                  refine ⟨197842955109314950628053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4220649708998718946731797 197842955109314950628053)
                  ·
                    rfl

theorem cell20_433460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_433460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433460 prefixEnd_433460 := by exact prefixLift 433460
  have htrace : WordTrace (prefixWord ++ tailWord_433460) baseStart_433460 baseEnd_433460 := by
    simpa [prefixWord, tailWord_433460, baseEnd_433460] using wordTrace_append hprefix tailTrace_433460
  have hstable : (prefixWord ++ tailWord_433460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433460).length < 2 ^ (prefixWord ++ tailWord_433460).sum := by decide
  have hdescent : baseEnd_433460 < baseStart_433460 := by decide
  rcases family_descends (prefixWord ++ tailWord_433460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433519 : List Nat := [1, 1, 2, 1, 3, 1, 5, 2, 4]
def baseStart_433519 : Nat := 118140960795 + 433519 * 2 ^ 59
def prefixEnd_433519 : Nat := 4983230072969 + 3 ^ 40 * 433519 * 2
def baseEnd_433519 : Nat := 197869884316972967661145

theorem tailTrace_433519 : CollatzResearch.WordTrace tailWord_433519 prefixEnd_433519 197869884316972967661145 := by
  unfold tailWord_433519
  simp only [CollatzResearch.WordTrace]
  refine ⟨15811736916442176995751611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10541157944294784663834407 15811736916442176995751611)
  ·
    refine ⟨23717605374663265493627417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15811736916442176995751611 23717605374663265493627417)
    ·
      refine ⟨17788204030997449120220563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23717605374663265493627417 17788204030997449120220563)
      ·
        refine ⟨26682306046496173680330845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17788204030997449120220563 26682306046496173680330845)
        ·
          refine ⟨10005864767436065130124067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26682306046496173680330845 10005864767436065130124067)
          ·
            refine ⟨15008797151154097695186101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10005864767436065130124067 15008797151154097695186101)
            ·
              refine ⟨1407074732920696658923697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15008797151154097695186101 1407074732920696658923697)
              ·
                refine ⟨1055306049690522494192773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1407074732920696658923697 1055306049690522494192773)
                ·
                  refine ⟨197869884316972967661145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1055306049690522494192773 197869884316972967661145)
                  ·
                    rfl

theorem cell20_433519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 2, 4].length) (baseStart_433519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433519 prefixEnd_433519 := by exact prefixLift 433519
  have htrace : WordTrace (prefixWord ++ tailWord_433519) baseStart_433519 baseEnd_433519 := by
    simpa [prefixWord, tailWord_433519, baseEnd_433519] using wordTrace_append hprefix tailTrace_433519
  have hstable : (prefixWord ++ tailWord_433519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433519).length < 2 ^ (prefixWord ++ tailWord_433519).sum := by decide
  have hdescent : baseEnd_433519 < baseStart_433519 := by decide
  rcases family_descends (prefixWord ++ tailWord_433519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433557 : List Nat := [1, 3, 2, 1, 1, 2, 3, 3, 4]
def baseStart_433557 : Nat := 118140960795 + 433557 * 2 ^ 59
def prefixEnd_433557 : Nat := 4983230072969 + 3 ^ 40 * 433557 * 2
def baseEnd_433557 : Nat := 197887228552413724394323

theorem tailTrace_433557 : CollatzResearch.WordTrace tailWord_433557 prefixEnd_433557 197887228552413724394323 := by
  unfold tailWord_433557
  simp only [CollatzResearch.WordTrace]
  refine ⟨15813122890304509485634925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10542081926869672990423283 15813122890304509485634925)
  ·
    refine ⟨5929921083864191057113097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15813122890304509485634925 5929921083864191057113097)
    ·
      refine ⟨4447440812898143292834823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5929921083864191057113097 4447440812898143292834823)
      ·
        refine ⟨6671161219347214939252235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4447440812898143292834823 6671161219347214939252235)
        ·
          refine ⟨10006741829020822408878353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6671161219347214939252235 10006741829020822408878353)
          ·
            refine ⟨7505056371765616806658765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10006741829020822408878353 7505056371765616806658765)
            ·
              refine ⟨2814396139412106302497037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7505056371765616806658765 2814396139412106302497037)
              ·
                refine ⟨1055398552279539863436389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2814396139412106302497037 1055398552279539863436389)
                ·
                  refine ⟨197887228552413724394323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1055398552279539863436389 197887228552413724394323)
                  ·
                    rfl

theorem cell20_433557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_433557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433557 prefixEnd_433557 := by exact prefixLift 433557
  have htrace : WordTrace (prefixWord ++ tailWord_433557) baseStart_433557 baseEnd_433557 := by
    simpa [prefixWord, tailWord_433557, baseEnd_433557] using wordTrace_append hprefix tailTrace_433557
  have hstable : (prefixWord ++ tailWord_433557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433557).length < 2 ^ (prefixWord ++ tailWord_433557).sum := by decide
  have hdescent : baseEnd_433557 < baseStart_433557 := by decide
  rcases family_descends (prefixWord ++ tailWord_433557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433612 : List Nat := [2, 2, 1, 4, 2, 1, 3, 1, 4]
def baseStart_433612 : Nat := 118140960795 + 433612 * 2 ^ 59
def prefixEnd_433612 : Nat := 4983230072969 + 3 ^ 40 * 433612 * 2
def baseEnd_433612 : Nat := 197912332051077977560765

theorem tailTrace_433612 : CollatzResearch.WordTrace tailWord_433612 prefixEnd_433612 197912332051077977560765 := by
  unfold tailWord_433612
  simp only [CollatzResearch.WordTrace]
  refine ⟨7907564452552626939443545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10543419270070169252591393 7907564452552626939443545)
  ·
    refine ⟨5930673339414470204582659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7907564452552626939443545 5930673339414470204582659)
    ·
      refine ⟨8896010009121705306873989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5930673339414470204582659 8896010009121705306873989)
      ·
        refine ⟨1668001876710319745038873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8896010009121705306873989 1668001876710319745038873)
        ·
          refine ⟨1251001407532739808779155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1668001876710319745038873 1251001407532739808779155)
          ·
            refine ⟨1876502111299109713168733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1251001407532739808779155 1876502111299109713168733)
            ·
              refine ⟨703688291737166142438275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1876502111299109713168733 703688291737166142438275)
              ·
                refine ⟨1055532437605749213657413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 703688291737166142438275 1055532437605749213657413)
                ·
                  refine ⟨197912332051077977560765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1055532437605749213657413 197912332051077977560765)
                  ·
                    rfl

theorem cell20_433612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_433612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433612 prefixEnd_433612 := by exact prefixLift 433612
  have htrace : WordTrace (prefixWord ++ tailWord_433612) baseStart_433612 baseEnd_433612 := by
    simpa [prefixWord, tailWord_433612, baseEnd_433612] using wordTrace_append hprefix tailTrace_433612
  have hstable : (prefixWord ++ tailWord_433612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433612).length < 2 ^ (prefixWord ++ tailWord_433612).sum := by decide
  have hdescent : baseEnd_433612 < baseStart_433612 := by decide
  rcases family_descends (prefixWord ++ tailWord_433612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433622 : List Nat := [5, 2, 1, 1, 1, 3, 1, 3, 3]
def baseStart_433622 : Nat := 118140960795 + 433622 * 2 ^ 59
def prefixEnd_433622 : Nat := 4983230072969 + 3 ^ 40 * 433622 * 2
def baseEnd_433622 : Nat := 197916896323562387227391

theorem tailTrace_433622 : CollatzResearch.WordTrace tailWord_433622 prefixEnd_433622 197916896323562387227391 := by
  unfold tailWord_433622
  simp only [CollatzResearch.WordTrace]
  refine ⟨988468352191814099171945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10543662423379350391167413 988468352191814099171945)
  ·
    refine ⟨741351264143860574378959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 988468352191814099171945 741351264143860574378959)
    ·
      refine ⟨1112026896215790861568439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 741351264143860574378959 1112026896215790861568439)
      ·
        refine ⟨1668040344323686292352659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1112026896215790861568439 1668040344323686292352659)
        ·
          refine ⟨2502060516485529438528989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1668040344323686292352659 2502060516485529438528989)
          ·
            refine ⟨938272693682073539448371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2502060516485529438528989 938272693682073539448371)
            ·
              refine ⟨1407409040523110309172557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 938272693682073539448371 1407409040523110309172557)
              ·
                refine ⟨527778390196166365939709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1407409040523110309172557 527778390196166365939709)
                ·
                  refine ⟨197916896323562387227391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 527778390196166365939709 197916896323562387227391)
                  ·
                    rfl

theorem cell20_433622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_433622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433622 prefixEnd_433622 := by exact prefixLift 433622
  have htrace : WordTrace (prefixWord ++ tailWord_433622) baseStart_433622 baseEnd_433622 := by
    simpa [prefixWord, tailWord_433622, baseEnd_433622] using wordTrace_append hprefix tailTrace_433622
  have hstable : (prefixWord ++ tailWord_433622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433622).length < 2 ^ (prefixWord ++ tailWord_433622).sum := by decide
  have hdescent : baseEnd_433622 < baseStart_433622 := by decide
  rcases family_descends (prefixWord ++ tailWord_433622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433640 : List Nat := [2, 1, 4, 1, 1, 2, 1, 8]
def baseStart_433640 : Nat := 118140960795 + 433640 * 2 ^ 59
def prefixEnd_433640 : Nat := 4983230072969 + 3 ^ 40 * 433640 * 2
def baseEnd_433640 : Nat := 65975037338011441542439

theorem tailTrace_433640 : CollatzResearch.WordTrace tailWord_433640 prefixEnd_433640 65975037338011441542439 := by
  unfold tailWord_433640
  simp only [CollatzResearch.WordTrace]
  refine ⟨7908075074501907330453187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10544100099335876440604249 7908075074501907330453187)
  ·
    refine ⟨11862112611752860995679781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7908075074501907330453187 11862112611752860995679781)
    ·
      refine ⟨2224146114703661436689959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11862112611752860995679781 2224146114703661436689959)
      ·
        refine ⟨3336219172055492155034939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2224146114703661436689959 3336219172055492155034939)
        ·
          refine ⟨5004328758083238232552409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3336219172055492155034939 5004328758083238232552409)
          ·
            refine ⟨3753246568562428674414307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5004328758083238232552409 3753246568562428674414307)
            ·
              refine ⟨5629869852843643011621461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3753246568562428674414307 5629869852843643011621461)
              ·
                refine ⟨65975037338011441542439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5629869852843643011621461 65975037338011441542439)
                ·
                  rfl

theorem cell20_433640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 8].length) (baseStart_433640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433640 prefixEnd_433640 := by exact prefixLift 433640
  have htrace : WordTrace (prefixWord ++ tailWord_433640) baseStart_433640 baseEnd_433640 := by
    simpa [prefixWord, tailWord_433640, baseEnd_433640] using wordTrace_append hprefix tailTrace_433640
  have hstable : (prefixWord ++ tailWord_433640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433640).length < 2 ^ (prefixWord ++ tailWord_433640).sum := by decide
  have hdescent : baseEnd_433640 < baseStart_433640 := by decide
  rcases family_descends (prefixWord ++ tailWord_433640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433647 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 7]
def baseStart_433647 : Nat := 118140960795 + 433647 * 2 ^ 59
def prefixEnd_433647 : Nat := 4983230072969 + 3 ^ 40 * 433647 * 2
def baseEnd_433647 : Nat := 197928307004773411393955

theorem tailTrace_433647 : CollatzResearch.WordTrace tailWord_433647 prefixEnd_433647 197928307004773411393955 := by
  unfold tailWord_433647
  simp only [CollatzResearch.WordTrace]
  refine ⟨15816405459978454856411195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10544270306652303237607463 15816405459978454856411195)
  ·
    refine ⟨23724608189967682284616793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15816405459978454856411195 23724608189967682284616793)
    ·
      refine ⟨17793456142475761713462595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23724608189967682284616793 17793456142475761713462595)
      ·
        refine ⟨26690184213713642570193893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17793456142475761713462595 26690184213713642570193893)
        ·
          refine ⟨5004409540071307981911355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26690184213713642570193893 5004409540071307981911355)
          ·
            refine ⟨7506614310106961972867033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5004409540071307981911355 7506614310106961972867033)
            ·
              refine ⟨5629960732580221479650275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7506614310106961972867033 5629960732580221479650275)
              ·
                refine ⟨8444941098870332219475413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5629960732580221479650275 8444941098870332219475413)
                ·
                  refine ⟨197928307004773411393955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8444941098870332219475413 197928307004773411393955)
                  ·
                    rfl

theorem cell20_433647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 7].length) (baseStart_433647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433647 prefixEnd_433647 := by exact prefixLift 433647
  have htrace : WordTrace (prefixWord ++ tailWord_433647) baseStart_433647 baseEnd_433647 := by
    simpa [prefixWord, tailWord_433647, baseEnd_433647] using wordTrace_append hprefix tailTrace_433647
  have hstable : (prefixWord ++ tailWord_433647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433647).length < 2 ^ (prefixWord ++ tailWord_433647).sum := by decide
  have hdescent : baseEnd_433647 < baseStart_433647 := by decide
  rcases family_descends (prefixWord ++ tailWord_433647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433688 : List Nat := [2, 1, 2, 3, 4, 1, 1, 2, 4]
def baseStart_433688 : Nat := 118140960795 + 433688 * 2 ^ 59
def prefixEnd_433688 : Nat := 4983230072969 + 3 ^ 40 * 433688 * 2
def baseEnd_433688 : Nat := 197947020521959491027121

theorem tailTrace_433688 : CollatzResearch.WordTrace tailWord_433688 prefixEnd_433688 197947020521959491027121 := by
  unfold tailWord_433688
  simp only [CollatzResearch.WordTrace]
  refine ⟨7908950426414959429326859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10545267235219945905769145 7908950426414959429326859)
  ·
    refine ⟨11863425639622439143990289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7908950426414959429326859 11863425639622439143990289)
    ·
      refine ⟨8897569229716829357992717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11863425639622439143990289 8897569229716829357992717)
      ·
        refine ⟨3336588461143811009247269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8897569229716829357992717 3336588461143811009247269)
        ·
          refine ⟨625610336464464564233863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3336588461143811009247269 625610336464464564233863)
          ·
            refine ⟨938415504696696846350795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625610336464464564233863 938415504696696846350795)
            ·
              refine ⟨1407623257045045269526193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 938415504696696846350795 1407623257045045269526193)
              ·
                refine ⟨1055717442783783952144645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1407623257045045269526193 1055717442783783952144645)
                ·
                  refine ⟨197947020521959491027121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1055717442783783952144645 197947020521959491027121)
                  ·
                    rfl

theorem cell20_433688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 4].length) (baseStart_433688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433688 prefixEnd_433688 := by exact prefixLift 433688
  have htrace : WordTrace (prefixWord ++ tailWord_433688) baseStart_433688 baseEnd_433688 := by
    simpa [prefixWord, tailWord_433688, baseEnd_433688] using wordTrace_append hprefix tailTrace_433688
  have hstable : (prefixWord ++ tailWord_433688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433688).length < 2 ^ (prefixWord ++ tailWord_433688).sum := by decide
  have hdescent : baseEnd_433688 < baseStart_433688 := by decide
  rcases family_descends (prefixWord ++ tailWord_433688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433719 : List Nat := [1, 1, 3, 1, 2, 6, 1, 2, 3]
def baseStart_433719 : Nat := 118140960795 + 433719 * 2 ^ 59
def prefixEnd_433719 : Nat := 4983230072969 + 3 ^ 40 * 433719 * 2
def baseEnd_433719 : Nat := 197961169766661160993661

theorem tailTrace_433719 : CollatzResearch.WordTrace tailWord_433719 prefixEnd_433719 197961169766661160993661 := by
  unfold tailWord_433719
  simp only [CollatzResearch.WordTrace]
  refine ⟨15819031515717611153032211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10546021010478407435354807 15819031515717611153032211)
  ·
    refine ⟨23728547273576416729548317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15819031515717611153032211 23728547273576416729548317)
    ·
      refine ⟨8898205227591156273580619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23728547273576416729548317 8898205227591156273580619)
      ·
        refine ⟨13347307841386734410370929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8898205227591156273580619 13347307841386734410370929)
        ·
          refine ⟨10010480881040050807778197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13347307841386734410370929 10010480881040050807778197)
          ·
            refine ⟨469241291298752381614603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10010480881040050807778197 469241291298752381614603)
            ·
              refine ⟨703861936948128572421905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 469241291298752381614603 703861936948128572421905)
              ·
                refine ⟨527896452711096429316429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 703861936948128572421905 527896452711096429316429)
                ·
                  refine ⟨197961169766661160993661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 527896452711096429316429 197961169766661160993661)
                  ·
                    rfl

theorem cell20_433719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 3].length) (baseStart_433719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433719 prefixEnd_433719 := by exact prefixLift 433719
  have htrace : WordTrace (prefixWord ++ tailWord_433719) baseStart_433719 baseEnd_433719 := by
    simpa [prefixWord, tailWord_433719, baseEnd_433719] using wordTrace_append hprefix tailTrace_433719
  have hstable : (prefixWord ++ tailWord_433719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433719).length < 2 ^ (prefixWord ++ tailWord_433719).sum := by decide
  have hdescent : baseEnd_433719 < baseStart_433719 := by decide
  rcases family_descends (prefixWord ++ tailWord_433719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433761 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 7]
def baseStart_433761 : Nat := 118140960795 + 433761 * 2 ^ 59
def prefixEnd_433761 : Nat := 4983230072969 + 3 ^ 40 * 433761 * 2
def baseEnd_433761 : Nat := 197980339711095681593489

theorem tailTrace_433761 : CollatzResearch.WordTrace tailWord_433761 prefixEnd_433761 197980339711095681593489 := by
  unfold tailWord_433761
  simp only [CollatzResearch.WordTrace]
  refine ⟨15820563381565452326061137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10547042254376968217374091 15820563381565452326061137)
  ·
    refine ⟨11865422536174089244545853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15820563381565452326061137 11865422536174089244545853)
    ·
      refine ⟨4449533451065283466704695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11865422536174089244545853 4449533451065283466704695)
      ·
        refine ⟨6674300176597925200057043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4449533451065283466704695 6674300176597925200057043)
        ·
          refine ⟨10011450264896887800085565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6674300176597925200057043 10011450264896887800085565)
          ·
            refine ⟨3754293849336332925032087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10011450264896887800085565 3754293849336332925032087)
            ·
              refine ⟨5631440774004499387548131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3754293849336332925032087 5631440774004499387548131)
              ·
                refine ⟨8447161161006749081322197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5631440774004499387548131 8447161161006749081322197)
                ·
                  refine ⟨197980339711095681593489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8447161161006749081322197 197980339711095681593489)
                  ·
                    rfl

theorem cell20_433761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_433761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433761 prefixEnd_433761 := by exact prefixLift 433761
  have htrace : WordTrace (prefixWord ++ tailWord_433761) baseStart_433761 baseEnd_433761 := by
    simpa [prefixWord, tailWord_433761, baseEnd_433761] using wordTrace_append hprefix tailTrace_433761
  have hstable : (prefixWord ++ tailWord_433761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433761).length < 2 ^ (prefixWord ++ tailWord_433761).sum := by decide
  have hdescent : baseEnd_433761 < baseStart_433761 := by decide
  rcases family_descends (prefixWord ++ tailWord_433761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433778 : List Nat := [3, 2, 1, 2, 3, 1, 2, 1, 5]
def baseStart_433778 : Nat := 118140960795 + 433778 * 2 ^ 59
def prefixEnd_433778 : Nat := 4983230072969 + 3 ^ 40 * 433778 * 2
def baseEnd_433778 : Nat := 197988098974319178026753

theorem tailTrace_433778 : CollatzResearch.WordTrace tailWord_433778 prefixEnd_433778 197988098974319178026753 := by
  unfold tailWord_433778
  simp only [CollatzResearch.WordTrace]
  refine ⟨3955295855625966057357497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10547455615002576152953325 3955295855625966057357497)
  ·
    refine ⟨2966471891719474543018123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3955295855625966057357497 2966471891719474543018123)
    ·
      refine ⟨4449707837579211814527185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2966471891719474543018123 4449707837579211814527185)
      ·
        refine ⟨3337280878184408860895389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4449707837579211814527185 3337280878184408860895389)
        ·
          refine ⟨1251480329319153322835771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3337280878184408860895389 1251480329319153322835771)
          ·
            refine ⟨1877220493978729984253657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1251480329319153322835771 1877220493978729984253657)
            ·
              refine ⟨1407915370484047488190243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1877220493978729984253657 1407915370484047488190243)
              ·
                refine ⟨2111873055726071232285365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1407915370484047488190243 2111873055726071232285365)
                ·
                  refine ⟨197988098974319178026753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2111873055726071232285365 197988098974319178026753)
                  ·
                    rfl

theorem cell20_433778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_433778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433778 prefixEnd_433778 := by exact prefixLift 433778
  have htrace : WordTrace (prefixWord ++ tailWord_433778) baseStart_433778 baseEnd_433778 := by
    simpa [prefixWord, tailWord_433778, baseEnd_433778] using wordTrace_append hprefix tailTrace_433778
  have hstable : (prefixWord ++ tailWord_433778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433778).length < 2 ^ (prefixWord ++ tailWord_433778).sum := by decide
  have hdescent : baseEnd_433778 < baseStart_433778 := by decide
  rcases family_descends (prefixWord ++ tailWord_433778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433781 : List Nat := [1, 3, 4, 2, 1, 3, 1, 1, 4]
def baseStart_433781 : Nat := 118140960795 + 433781 * 2 ^ 59
def prefixEnd_433781 : Nat := 4983230072969 + 3 ^ 40 * 433781 * 2
def baseEnd_433781 : Nat := 197989468256064500926741

theorem tailTrace_433781 : CollatzResearch.WordTrace tailWord_433781 prefixEnd_433781 197989468256064500926741 := by
  unfold tailWord_433781
  simp only [CollatzResearch.WordTrace]
  refine ⟨15821292841492995741789197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10547528560995330494526131 15821292841492995741789197)
  ·
    refine ⟨5932984815559873403170949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15821292841492995741789197 5932984815559873403170949)
    ·
      refine ⟨1112434652917476263094553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5932984815559873403170949 1112434652917476263094553)
      ·
        refine ⟨834325989688107197320915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1112434652917476263094553 834325989688107197320915)
        ·
          refine ⟨1251488984532160795981373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 834325989688107197320915 1251488984532160795981373)
          ·
            refine ⟨469308369199560298493015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1251488984532160795981373 469308369199560298493015)
            ·
              refine ⟨703962553799340447739523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 469308369199560298493015 703962553799340447739523)
              ·
                refine ⟨1055943830699010671609285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 703962553799340447739523 1055943830699010671609285)
                ·
                  refine ⟨197989468256064500926741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1055943830699010671609285 197989468256064500926741)
                  ·
                    rfl

theorem cell20_433781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_433781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433781 prefixEnd_433781 := by exact prefixLift 433781
  have htrace : WordTrace (prefixWord ++ tailWord_433781) baseStart_433781 baseEnd_433781 := by
    simpa [prefixWord, tailWord_433781, baseEnd_433781] using wordTrace_append hprefix tailTrace_433781
  have hstable : (prefixWord ++ tailWord_433781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433781).length < 2 ^ (prefixWord ++ tailWord_433781).sum := by decide
  have hdescent : baseEnd_433781 < baseStart_433781 := by decide
  rcases family_descends (prefixWord ++ tailWord_433781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433792 : List Nat := [2, 1, 1, 2, 1, 4, 4, 5]
def baseStart_433792 : Nat := 118140960795 + 433792 * 2 ^ 59
def prefixEnd_433792 : Nat := 4983230072969 + 3 ^ 40 * 433792 * 2
def baseEnd_433792 : Nat := 65998162985265783853343

theorem tailTrace_433792 : CollatzResearch.WordTrace tailWord_433792 prefixEnd_433792 65998162985265783853343 := by
  unfold tailWord_433792
  simp only [CollatzResearch.WordTrace]
  refine ⟨7910847022226572310219815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10547796029635429746959753 7910847022226572310219815)
  ·
    refine ⟨11866270533339858465329723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7910847022226572310219815 11866270533339858465329723)
    ·
      refine ⟨17799405800009787697994585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11866270533339858465329723 17799405800009787697994585)
      ·
        refine ⟨13349554350007340773495939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17799405800009787697994585 13349554350007340773495939)
        ·
          refine ⟨20024331525011011160243909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13349554350007340773495939 20024331525011011160243909)
          ·
            refine ⟨3754562160939564592545733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20024331525011011160243909 3754562160939564592545733)
            ·
              refine ⟨703980405176168361102325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3754562160939564592545733 703980405176168361102325)
              ·
                refine ⟨65998162985265783853343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 703980405176168361102325 65998162985265783853343)
                ·
                  rfl

theorem cell20_433792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 5].length) (baseStart_433792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433792 prefixEnd_433792 := by exact prefixLift 433792
  have htrace : WordTrace (prefixWord ++ tailWord_433792) baseStart_433792 baseEnd_433792 := by
    simpa [prefixWord, tailWord_433792, baseEnd_433792] using wordTrace_append hprefix tailTrace_433792
  have hstable : (prefixWord ++ tailWord_433792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433792).length < 2 ^ (prefixWord ++ tailWord_433792).sum := by decide
  have hdescent : baseEnd_433792 < baseStart_433792 := by decide
  rcases family_descends (prefixWord ++ tailWord_433792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433826 : List Nat := [3, 3, 1, 4, 2, 7]
def baseStart_433826 : Nat := 118140960795 + 433826 * 2 ^ 59
def prefixEnd_433826 : Nat := 4983230072969 + 3 ^ 40 * 433826 * 2
def baseEnd_433826 : Nat := 7333703980823864608391

theorem tailTrace_433826 : CollatzResearch.WordTrace tailWord_433826 prefixEnd_433826 7333703980823864608391 := by
  unfold tailWord_433826
  simp only [CollatzResearch.WordTrace]
  refine ⟨3955733531582492106794333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10548622750886645618118221 3955733531582492106794333)
  ·
    refine ⟨1483400074343434540047875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3955733531582492106794333 1483400074343434540047875)
    ·
      refine ⟨2225100111515151810071813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1483400074343434540047875 2225100111515151810071813)
      ·
        refine ⟨417206270909090964388465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2225100111515151810071813 417206270909090964388465)
        ·
          refine ⟨312904703181818223291349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417206270909090964388465 312904703181818223291349)
          ·
            refine ⟨7333703980823864608391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 312904703181818223291349 7333703980823864608391)
            ·
              rfl

theorem cell20_433826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 7].length) (baseStart_433826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433826 prefixEnd_433826 := by exact prefixLift 433826
  have htrace : WordTrace (prefixWord ++ tailWord_433826) baseStart_433826 baseEnd_433826 := by
    simpa [prefixWord, tailWord_433826, baseEnd_433826] using wordTrace_append hprefix tailTrace_433826
  have hstable : (prefixWord ++ tailWord_433826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433826).length < 2 ^ (prefixWord ++ tailWord_433826).sum := by decide
  have hdescent : baseEnd_433826 < baseStart_433826 := by decide
  rcases family_descends (prefixWord ++ tailWord_433826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433847 : List Nat := [1, 1, 3, 1, 5, 3, 1, 5]
def baseStart_433847 : Nat := 118140960795 + 433847 * 2 ^ 59
def prefixEnd_433847 : Nat := 4983230072969 + 3 ^ 40 * 433847 * 2
def baseEnd_433847 : Nat := 66006530818153868242157

theorem tailTrace_433847 : CollatzResearch.WordTrace tailWord_433847 prefixEnd_433847 66006530818153868242157 := by
  unfold tailWord_433847
  simp only [CollatzResearch.WordTrace]
  refine ⟨15823700059253889013691795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10549133372835926009127863 15823700059253889013691795)
  ·
    refine ⟨23735550088880833520537693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15823700059253889013691795 23735550088880833520537693)
    ·
      refine ⟨8900831283330312570201635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23735550088880833520537693 8900831283330312570201635)
      ·
        refine ⟨13351246924995468855302453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8900831283330312570201635 13351246924995468855302453)
        ·
          refine ⟨1251679399218325205184605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13351246924995468855302453 1251679399218325205184605)
          ·
            refine ⟨469379774706871951944227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1251679399218325205184605 469379774706871951944227)
            ·
              refine ⟨704069662060307927916341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 469379774706871951944227 704069662060307927916341)
              ·
                refine ⟨66006530818153868242157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 704069662060307927916341 66006530818153868242157)
                ·
                  rfl

theorem cell20_433847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 5].length) (baseStart_433847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433847 prefixEnd_433847 := by exact prefixLift 433847
  have htrace : WordTrace (prefixWord ++ tailWord_433847) baseStart_433847 baseEnd_433847 := by
    simpa [prefixWord, tailWord_433847, baseEnd_433847] using wordTrace_append hprefix tailTrace_433847
  have hstable : (prefixWord ++ tailWord_433847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433847).length < 2 ^ (prefixWord ++ tailWord_433847).sum := by decide
  have hdescent : baseEnd_433847 < baseStart_433847 := by decide
  rcases family_descends (prefixWord ++ tailWord_433847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433895 : List Nat := [1, 1, 5, 4, 1, 1, 2, 1, 4]
def baseStart_433895 : Nat := 118140960795 + 433895 * 2 ^ 59
def prefixEnd_433895 : Nat := 4983230072969 + 3 ^ 40 * 433895 * 2
def baseEnd_433895 : Nat := 198041500962386771126275

theorem tailTrace_433895 : CollatzResearch.WordTrace tailWord_433895 prefixEnd_433895 198041500962386771126275 := by
  unfold tailWord_433895
  simp only [CollatzResearch.WordTrace]
  refine ⟨15825450763079993211439139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10550300508719995474292759 15825450763079993211439139)
  ·
    refine ⟨23738176144619989817158709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15825450763079993211439139 23738176144619989817158709)
    ·
      refine ⟨2225454013558124045358629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23738176144619989817158709 2225454013558124045358629)
      ·
        refine ⟨417272627542148258504743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2225454013558124045358629 417272627542148258504743)
        ·
          refine ⟨625908941313222387757115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417272627542148258504743 625908941313222387757115)
          ·
            refine ⟨938863411969833581635673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625908941313222387757115 938863411969833581635673)
            ·
              refine ⟨704147558977375186226755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 938863411969833581635673 704147558977375186226755)
              ·
                refine ⟨1056221338466062779340133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 704147558977375186226755 1056221338466062779340133)
                ·
                  refine ⟨198041500962386771126275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1056221338466062779340133 198041500962386771126275)
                  ·
                    rfl

theorem cell20_433895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 4].length) (baseStart_433895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433895 prefixEnd_433895 := by exact prefixLift 433895
  have htrace : WordTrace (prefixWord ++ tailWord_433895) baseStart_433895 baseEnd_433895 := by
    simpa [prefixWord, tailWord_433895, baseEnd_433895] using wordTrace_append hprefix tailTrace_433895
  have hstable : (prefixWord ++ tailWord_433895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433895).length < 2 ^ (prefixWord ++ tailWord_433895).sum := by decide
  have hdescent : baseEnd_433895 < baseStart_433895 := by decide
  rcases family_descends (prefixWord ++ tailWord_433895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433906 : List Nat := [3, 2, 1, 3, 1, 1, 2, 7]
def baseStart_433906 : Nat := 118140960795 + 433906 * 2 ^ 59
def prefixEnd_433906 : Nat := 4983230072969 + 3 ^ 40 * 433906 * 2
def baseEnd_433906 : Nat := 66015507220706540586521

theorem tailTrace_433906 : CollatzResearch.WordTrace tailWord_433906 prefixEnd_433906 66015507220706540586521 := by
  unfold tailWord_433906
  simp only [CollatzResearch.WordTrace]
  refine ⟨3956462991510035522522393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10550567977360094726726381 3956462991510035522522393)
  ·
    refine ⟨2967347243632526641891795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3956462991510035522522393 2967347243632526641891795)
    ·
      refine ⟨4451020865448789962837693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2967347243632526641891795 4451020865448789962837693)
      ·
        refine ⟨1669132824543296236064135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4451020865448789962837693 1669132824543296236064135)
        ·
          refine ⟨2503699236814944354096203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1669132824543296236064135 2503699236814944354096203)
          ·
            refine ⟨3755548855222416531144305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2503699236814944354096203 3755548855222416531144305)
            ·
              refine ⟨2816661641416812398358229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3755548855222416531144305 2816661641416812398358229)
              ·
                refine ⟨66015507220706540586521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2816661641416812398358229 66015507220706540586521)
                ·
                  rfl

theorem cell20_433906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_433906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433906 prefixEnd_433906 := by exact prefixLift 433906
  have htrace : WordTrace (prefixWord ++ tailWord_433906) baseStart_433906 baseEnd_433906 := by
    simpa [prefixWord, tailWord_433906, baseEnd_433906] using wordTrace_append hprefix tailTrace_433906
  have hstable : (prefixWord ++ tailWord_433906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433906).length < 2 ^ (prefixWord ++ tailWord_433906).sum := by decide
  have hdescent : baseEnd_433906 < baseStart_433906 := by decide
  rcases family_descends (prefixWord ++ tailWord_433906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433951 : List Nat := [1, 1, 2, 4, 2, 1, 1, 3, 5]
def baseStart_433951 : Nat := 118140960795 + 433951 * 2 ^ 59
def prefixEnd_433951 : Nat := 4983230072969 + 3 ^ 40 * 433951 * 2
def baseEnd_433951 : Nat := 198067060888299465259379

theorem tailTrace_433951 : CollatzResearch.WordTrace tailWord_433951 prefixEnd_433951 198067060888299465259379 := by
  unfold tailWord_433951
  simp only [CollatzResearch.WordTrace]
  refine ⟨15827493250877114775477707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10551662167251409850318471 15827493250877114775477707)
  ·
    refine ⟨23741239876315672163216561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15827493250877114775477707 23741239876315672163216561)
    ·
      refine ⟨17805929907236754122412421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23741239876315672163216561 17805929907236754122412421)
      ·
        refine ⟨3338611857606891397952329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17805929907236754122412421 3338611857606891397952329)
        ·
          refine ⟨2503958893205168548464247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3338611857606891397952329 2503958893205168548464247)
          ·
            refine ⟨3755938339807752822696371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2503958893205168548464247 3755938339807752822696371)
            ·
              refine ⟨5633907509711629234044557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3755938339807752822696371 5633907509711629234044557)
              ·
                refine ⟨2112715316141860962766709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5633907509711629234044557 2112715316141860962766709)
                ·
                  refine ⟨198067060888299465259379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2112715316141860962766709 198067060888299465259379)
                  ·
                    rfl

theorem cell20_433951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 5].length) (baseStart_433951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_433951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_433951 prefixEnd_433951 := by exact prefixLift 433951
  have htrace : WordTrace (prefixWord ++ tailWord_433951) baseStart_433951 baseEnd_433951 := by
    simpa [prefixWord, tailWord_433951, baseEnd_433951] using wordTrace_append hprefix tailTrace_433951
  have hstable : (prefixWord ++ tailWord_433951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433951).length < 2 ^ (prefixWord ++ tailWord_433951).sum := by decide
  have hdescent : baseEnd_433951 < baseStart_433951 := by decide
  rcases family_descends (prefixWord ++ tailWord_433951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434030 : List Nat := [4, 1, 2, 3, 1, 2, 1, 2, 4]
def baseStart_434030 : Nat := 118140960795 + 434030 * 2 ^ 59
def prefixEnd_434030 : Nat := 4983230072969 + 3 ^ 40 * 434030 * 2
def baseEnd_434030 : Nat := 198103118640926301625723

theorem tailTrace_434030 : CollatzResearch.WordTrace tailWord_434030 prefixEnd_434030 198103118640926301625723 := by
  unfold tailWord_434030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1978796827198863908450443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10553583078393940845069029 1978796827198863908450443)
  ·
    refine ⟨2968195240798295862675665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1978796827198863908450443 2968195240798295862675665)
    ·
      refine ⟨2226146430598721897006749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2968195240798295862675665 2226146430598721897006749)
      ·
        refine ⟨834804911474520711377531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2226146430598721897006749 834804911474520711377531)
        ·
          refine ⟨1252207367211781067066297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 834804911474520711377531 1252207367211781067066297)
          ·
            refine ⟨939155525408835800299723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1252207367211781067066297 939155525408835800299723)
            ·
              refine ⟨1408733288113253700449585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 939155525408835800299723 1408733288113253700449585)
              ·
                refine ⟨1056549966084940275337189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1408733288113253700449585 1056549966084940275337189)
                ·
                  refine ⟨198103118640926301625723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1056549966084940275337189 198103118640926301625723)
                  ·
                    rfl

theorem cell20_434030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_434030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434030 prefixEnd_434030 := by exact prefixLift 434030
  have htrace : WordTrace (prefixWord ++ tailWord_434030) baseStart_434030 baseEnd_434030 := by
    simpa [prefixWord, tailWord_434030, baseEnd_434030] using wordTrace_append hprefix tailTrace_434030
  have hstable : (prefixWord ++ tailWord_434030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434030).length < 2 ^ (prefixWord ++ tailWord_434030).sum := by decide
  have hdescent : baseEnd_434030 < baseStart_434030 := by decide
  rcases family_descends (prefixWord ++ tailWord_434030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434037 : List Nat := [1, 3, 4, 1, 1, 1, 5, 4]
def baseStart_434037 : Nat := 118140960795 + 434037 * 2 ^ 59
def prefixEnd_434037 : Nat := 4983230072969 + 3 ^ 40 * 434037 * 2
def baseEnd_434037 : Nat := 66035437877221796130787

theorem tailTrace_434037 : CollatzResearch.WordTrace tailWord_434037 prefixEnd_434037 66035437877221796130787 := by
  unfold tailWord_434037
  simp only [CollatzResearch.WordTrace]
  refine ⟨15830629928565551463108365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10553753285710367642072243 15830629928565551463108365)
  ·
    refine ⟨5936486223212081798665637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15830629928565551463108365 5936486223212081798665637)
    ·
      refine ⟨1113091166852265337249807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5936486223212081798665637 1113091166852265337249807)
      ·
        refine ⟨1669636750278398005874711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1113091166852265337249807 1669636750278398005874711)
        ·
          refine ⟨2504455125417597008812067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1669636750278398005874711 2504455125417597008812067)
          ·
            refine ⟨3756682688126395513218101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2504455125417597008812067 3756682688126395513218101)
            ·
              refine ⟨352189002011849579364197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3756682688126395513218101 352189002011849579364197)
              ·
                refine ⟨66035437877221796130787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 352189002011849579364197 66035437877221796130787)
                ·
                  rfl

theorem cell20_434037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 4].length) (baseStart_434037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434037 prefixEnd_434037 := by exact prefixLift 434037
  have htrace : WordTrace (prefixWord ++ tailWord_434037) baseStart_434037 baseEnd_434037 := by
    simpa [prefixWord, tailWord_434037, baseEnd_434037] using wordTrace_append hprefix tailTrace_434037
  have hstable : (prefixWord ++ tailWord_434037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434037).length < 2 ^ (prefixWord ++ tailWord_434037).sum := by decide
  have hdescent : baseEnd_434037 < baseStart_434037 := by decide
  rcases family_descends (prefixWord ++ tailWord_434037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434068 : List Nat := [2, 4, 2, 1, 1, 3, 2, 1, 4]
def baseStart_434068 : Nat := 118140960795 + 434068 * 2 ^ 59
def prefixEnd_434068 : Nat := 4983230072969 + 3 ^ 40 * 434068 * 2
def baseEnd_434068 : Nat := 198120462876367058358901

theorem tailTrace_434068 : CollatzResearch.WordTrace tailWord_434068 prefixEnd_434068 198120462876367058358901 := by
  unfold tailWord_434068
  simp only [CollatzResearch.WordTrace]
  refine ⟨7915880295726621878743429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10554507060968829171657905 7915880295726621878743429)
  ·
    refine ⟨1484227555448741602264393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7915880295726621878743429 1484227555448741602264393)
    ·
      refine ⟨1113170666586556201698295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1484227555448741602264393 1113170666586556201698295)
      ·
        refine ⟨1669755999879834302547443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1113170666586556201698295 1669755999879834302547443)
        ·
          refine ⟨2504633999819751453821165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1669755999879834302547443 2504633999819751453821165)
          ·
            refine ⟨939237749932406795182937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2504633999819751453821165 939237749932406795182937)
            ·
              refine ⟨704428312449305096387203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 939237749932406795182937 704428312449305096387203)
              ·
                refine ⟨1056642468673957644580805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 704428312449305096387203 1056642468673957644580805)
                ·
                  refine ⟨198120462876367058358901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1056642468673957644580805 198120462876367058358901)
                  ·
                    rfl

theorem cell20_434068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_434068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434068 prefixEnd_434068 := by exact prefixLift 434068
  have htrace : WordTrace (prefixWord ++ tailWord_434068) baseStart_434068 baseEnd_434068 := by
    simpa [prefixWord, tailWord_434068, baseEnd_434068] using wordTrace_append hprefix tailTrace_434068
  have hstable : (prefixWord ++ tailWord_434068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434068).length < 2 ^ (prefixWord ++ tailWord_434068).sum := by decide
  have hdescent : baseEnd_434068 < baseStart_434068 := by decide
  rcases family_descends (prefixWord ++ tailWord_434068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434088 : List Nat := [2, 1, 6, 2, 2, 1, 2, 4]
def baseStart_434088 : Nat := 118140960795 + 434088 * 2 ^ 59
def prefixEnd_434088 : Nat := 4983230072969 + 3 ^ 40 * 434088 * 2
def baseEnd_434088 : Nat := 66043197140445292564051

theorem tailTrace_434088 : CollatzResearch.WordTrace tailWord_434088 prefixEnd_434088 66043197140445292564051 := by
  unfold tailWord_434088
  simp only [CollatzResearch.WordTrace]
  refine ⟨7916245025690393586607459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10554993367587191448809945 7916245025690393586607459)
  ·
    refine ⟨11874367538535590379911189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7916245025690393586607459 11874367538535590379911189)
    ·
      refine ⟨556610978368855799058337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11874367538535590379911189 556610978368855799058337)
      ·
        refine ⟨417458233776641849293753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 556610978368855799058337 417458233776641849293753)
        ·
          refine ⟨313093675332481386970315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417458233776641849293753 313093675332481386970315)
          ·
            refine ⟨469640512998722080455473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313093675332481386970315 469640512998722080455473)
            ·
              refine ⟨352230384749041560341605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 469640512998722080455473 352230384749041560341605)
              ·
                refine ⟨66043197140445292564051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 352230384749041560341605 66043197140445292564051)
                ·
                  rfl

theorem cell20_434088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 4].length) (baseStart_434088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434088 prefixEnd_434088 := by exact prefixLift 434088
  have htrace : WordTrace (prefixWord ++ tailWord_434088) baseStart_434088 baseEnd_434088 := by
    simpa [prefixWord, tailWord_434088, baseEnd_434088] using wordTrace_append hprefix tailTrace_434088
  have hstable : (prefixWord ++ tailWord_434088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434088).length < 2 ^ (prefixWord ++ tailWord_434088).sum := by decide
  have hdescent : baseEnd_434088 < baseStart_434088 := by decide
  rcases family_descends (prefixWord ++ tailWord_434088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434148 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 6]
def baseStart_434148 : Nat := 118140960795 + 434148 * 2 ^ 59
def prefixEnd_434148 : Nat := 4983230072969 + 3 ^ 40 * 434148 * 2
def baseEnd_434148 : Nat := 198156977056242335691907

theorem tailTrace_434148 : CollatzResearch.WordTrace tailWord_434148 prefixEnd_434148 198156977056242335691907 := by
  unfold tailWord_434148
  simp only [CollatzResearch.WordTrace]
  refine ⟨7917339215581708710199549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10556452287442278280266065 7917339215581708710199549)
  ·
    refine ⟨2969002205843140766324831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7917339215581708710199549 2969002205843140766324831)
    ·
      refine ⟨4453503308764711149487247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2969002205843140766324831 4453503308764711149487247)
      ·
        refine ⟨6680254963147066724230871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4453503308764711149487247 6680254963147066724230871)
        ·
          refine ⟨10020382444720600086346307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6680254963147066724230871 10020382444720600086346307)
          ·
            refine ⟨15030573667080900129519461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10020382444720600086346307 15030573667080900129519461)
            ·
              refine ⟨2818232562577668774284899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15030573667080900129519461 2818232562577668774284899)
              ·
                refine ⟨4227348843866503161427349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2818232562577668774284899 4227348843866503161427349)
                ·
                  refine ⟨198156977056242335691907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4227348843866503161427349 198156977056242335691907)
                  ·
                    rfl

theorem cell20_434148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_434148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434148 prefixEnd_434148 := by exact prefixLift 434148
  have htrace : WordTrace (prefixWord ++ tailWord_434148) baseStart_434148 baseEnd_434148 := by
    simpa [prefixWord, tailWord_434148, baseEnd_434148] using wordTrace_append hprefix tailTrace_434148
  have hstable : (prefixWord ++ tailWord_434148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434148).length < 2 ^ (prefixWord ++ tailWord_434148).sum := by decide
  have hdescent : baseEnd_434148 < baseStart_434148 := by decide
  rcases family_descends (prefixWord ++ tailWord_434148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434216 : List Nat := [2, 1, 5, 3, 1, 1, 2, 3, 2]
def baseStart_434216 : Nat := 118140960795 + 434216 * 2 ^ 59
def prefixEnd_434216 : Nat := 4983230072969 + 3 ^ 40 * 434216 * 2
def baseEnd_434216 : Nat := 198188014109136321424963

theorem tailTrace_434216 : CollatzResearch.WordTrace tailWord_434216 prefixEnd_434216 198188014109136321424963 := by
  unfold tailWord_434216
  simp only [CollatzResearch.WordTrace]
  refine ⟨7918579297458532516937251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10558105729944710022583001 7918579297458532516937251)
  ·
    refine ⟨11877868946187798775405877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7918579297458532516937251 11877868946187798775405877)
    ·
      refine ⟨1113550213705106135194301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11877868946187798775405877 1113550213705106135194301)
      ·
        refine ⟨417581330139414800697863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1113550213705106135194301 417581330139414800697863)
        ·
          refine ⟨626371995209122201046795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417581330139414800697863 626371995209122201046795)
          ·
            refine ⟨939557992813683301570193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626371995209122201046795 939557992813683301570193)
            ·
              refine ⟨704668494610262476177645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 939557992813683301570193 704668494610262476177645)
              ·
                refine ⟨264250685478848428566617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 704668494610262476177645 264250685478848428566617)
                ·
                  refine ⟨198188014109136321424963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264250685478848428566617 198188014109136321424963)
                  ·
                    rfl

theorem cell20_434216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 3, 2].length) (baseStart_434216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434216 prefixEnd_434216 := by exact prefixLift 434216
  have htrace : WordTrace (prefixWord ++ tailWord_434216) baseStart_434216 baseEnd_434216 := by
    simpa [prefixWord, tailWord_434216, baseEnd_434216] using wordTrace_append hprefix tailTrace_434216
  have hstable : (prefixWord ++ tailWord_434216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434216).length < 2 ^ (prefixWord ++ tailWord_434216).sum := by decide
  have hdescent : baseEnd_434216 < baseStart_434216 := by decide
  rcases family_descends (prefixWord ++ tailWord_434216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434241 : List Nat := [1, 2, 5, 1, 2, 1, 1, 3, 4]
def baseStart_434241 : Nat := 118140960795 + 434241 * 2 ^ 59
def prefixEnd_434241 : Nat := 4983230072969 + 3 ^ 40 * 434241 * 2
def baseEnd_434241 : Nat := 198199424790347345591527

theorem tailTrace_434241 : CollatzResearch.WordTrace tailWord_434241 prefixEnd_434241 198199424790347345591527 := by
  unfold tailWord_434241
  simp only [CollatzResearch.WordTrace]
  refine ⟨15838070419826494303534577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10558713613217662869023051 15838070419826494303534577)
  ·
    refine ⟨11878552814869870727650933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15838070419826494303534577 11878552814869870727650933)
    ·
      refine ⟨1113614326394050380717275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11878552814869870727650933 1113614326394050380717275)
      ·
        refine ⟨1670421489591075571075913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1113614326394050380717275 1670421489591075571075913)
        ·
          refine ⟨1252816117193306678306935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1670421489591075571075913 1252816117193306678306935)
          ·
            refine ⟨1879224175789960017460403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1252816117193306678306935 1879224175789960017460403)
            ·
              refine ⟨2818836263684940026190605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1879224175789960017460403 2818836263684940026190605)
              ·
                refine ⟨1057063598881852509821477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2818836263684940026190605 1057063598881852509821477)
                ·
                  refine ⟨198199424790347345591527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1057063598881852509821477 198199424790347345591527)
                  ·
                    rfl

theorem cell20_434241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_434241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434241 prefixEnd_434241 := by exact prefixLift 434241
  have htrace : WordTrace (prefixWord ++ tailWord_434241) baseStart_434241 baseEnd_434241 := by
    simpa [prefixWord, tailWord_434241, baseEnd_434241] using wordTrace_append hprefix tailTrace_434241
  have hstable : (prefixWord ++ tailWord_434241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434241).length < 2 ^ (prefixWord ++ tailWord_434241).sum := by decide
  have hdescent : baseEnd_434241 < baseStart_434241 := by decide
  rcases family_descends (prefixWord ++ tailWord_434241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434307 : List Nat := [1, 1, 1, 3, 3, 3, 1, 7]
def baseStart_434307 : Nat := 118140960795 + 434307 * 2 ^ 59
def prefixEnd_434307 : Nat := 4983230072969 + 3 ^ 40 * 434307 * 2
def baseEnd_434307 : Nat := 66076516329581483130419

theorem tailTrace_434307 : CollatzResearch.WordTrace tailWord_434307 prefixEnd_434307 66076516329581483130419 := by
  unfold tailWord_434307
  simp only [CollatzResearch.WordTrace]
  refine ⟨15840477637587387575437175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10560318425058258383624783 15840477637587387575437175)
  ·
    refine ⟨23760716456381081363155763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15840477637587387575437175 23760716456381081363155763)
    ·
      refine ⟨35641074684571622044733645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23760716456381081363155763 35641074684571622044733645)
      ·
        refine ⟨13365403006714358266775117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35641074684571622044733645 13365403006714358266775117)
        ·
          refine ⟨5012026127517884350040669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13365403006714358266775117 5012026127517884350040669)
          ·
            refine ⟨1879509797819206631265251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5012026127517884350040669 1879509797819206631265251)
            ·
              refine ⟨2819264696728809946897877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1879509797819206631265251 2819264696728809946897877)
              ·
                refine ⟨66076516329581483130419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2819264696728809946897877 66076516329581483130419)
                ·
                  rfl

theorem cell20_434307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 7].length) (baseStart_434307 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434307 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434307 prefixEnd_434307 := by exact prefixLift 434307
  have htrace : WordTrace (prefixWord ++ tailWord_434307) baseStart_434307 baseEnd_434307 := by
    simpa [prefixWord, tailWord_434307, baseEnd_434307] using wordTrace_append hprefix tailTrace_434307
  have hstable : (prefixWord ++ tailWord_434307).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434307).length < 2 ^ (prefixWord ++ tailWord_434307).sum := by decide
  have hdescent : baseEnd_434307 < baseStart_434307 := by decide
  rcases family_descends (prefixWord ++ tailWord_434307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434389 : List Nat := [1, 3, 2, 4, 2, 1, 2, 3, 2]
def baseStart_434389 : Nat := 118140960795 + 434389 * 2 ^ 59
def prefixEnd_434389 : Nat := 4983230072969 + 3 ^ 40 * 434389 * 2
def baseEnd_434389 : Nat := 198266976023116608657589

theorem tailTrace_434389 : CollatzResearch.WordTrace tailWord_434389 prefixEnd_434389 198266976023116608657589 := by
  unfold tailWord_434389
  simp only [CollatzResearch.WordTrace]
  refine ⟨15843468423290315579922221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10562312282193543719948147 15843468423290315579922221)
  ·
    refine ⟨5941300658733868342470833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15843468423290315579922221 5941300658733868342470833)
    ·
      refine ⟨4455975494050401256853125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5941300658733868342470833 4455975494050401256853125)
      ·
        refine ⟨835495405134450235659961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4455975494050401256853125 835495405134450235659961)
        ·
          refine ⟨626621553850837676744971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 835495405134450235659961 626621553850837676744971)
          ·
            refine ⟨939932330776256515117457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626621553850837676744971 939932330776256515117457)
            ·
              refine ⟨704949248082192386338093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 939932330776256515117457 704949248082192386338093)
              ·
                refine ⟨264355968030822144876785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 704949248082192386338093 264355968030822144876785)
                ·
                  refine ⟨198266976023116608657589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264355968030822144876785 198266976023116608657589)
                  ·
                    rfl

theorem cell20_434389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 3, 2].length) (baseStart_434389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434389 prefixEnd_434389 := by exact prefixLift 434389
  have htrace : WordTrace (prefixWord ++ tailWord_434389) baseStart_434389 baseEnd_434389 := by
    simpa [prefixWord, tailWord_434389, baseEnd_434389] using wordTrace_append hprefix tailTrace_434389
  have hstable : (prefixWord ++ tailWord_434389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434389).length < 2 ^ (prefixWord ++ tailWord_434389).sum := by decide
  have hdescent : baseEnd_434389 < baseStart_434389 := by decide
  rcases family_descends (prefixWord ++ tailWord_434389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434393 : List Nat := [1, 2, 1, 2, 3, 1, 3, 5, 2]
def baseStart_434393 : Nat := 118140960795 + 434393 * 2 ^ 59
def prefixEnd_434393 : Nat := 4983230072969 + 3 ^ 40 * 434393 * 2
def baseEnd_434393 : Nat := 198268801732110372524239

theorem tailTrace_434393 : CollatzResearch.WordTrace tailWord_434393 prefixEnd_434393 198268801732110372524239 := by
  unfold tailWord_434393
  simp only [CollatzResearch.WordTrace]
  refine ⟨15843614315275824263067833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10562409543517216175378555 15843614315275824263067833)
  ·
    refine ⟨11882710736456868197300875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15843614315275824263067833 11882710736456868197300875)
    ·
      refine ⟨17824066104685302295951313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11882710736456868197300875 17824066104685302295951313)
      ·
        refine ⟨13368049578513976721963485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17824066104685302295951313 13368049578513976721963485)
        ·
          refine ⟨5013018591942741270736307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13368049578513976721963485 5013018591942741270736307)
          ·
            refine ⟨7519527887914111906104461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5013018591942741270736307 7519527887914111906104461)
            ·
              refine ⟨2819822957967791964789173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7519527887914111906104461 2819822957967791964789173)
              ·
                refine ⟨264358402309480496698985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2819822957967791964789173 264358402309480496698985)
                ·
                  refine ⟨198268801732110372524239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264358402309480496698985 198268801732110372524239)
                  ·
                    rfl

theorem cell20_434393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 5, 2].length) (baseStart_434393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434393 prefixEnd_434393 := by exact prefixLift 434393
  have htrace : WordTrace (prefixWord ++ tailWord_434393) baseStart_434393 baseEnd_434393 := by
    simpa [prefixWord, tailWord_434393, baseEnd_434393] using wordTrace_append hprefix tailTrace_434393
  have hstable : (prefixWord ++ tailWord_434393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434393).length < 2 ^ (prefixWord ++ tailWord_434393).sum := by decide
  have hdescent : baseEnd_434393 < baseStart_434393 := by decide
  rcases family_descends (prefixWord ++ tailWord_434393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434434 : List Nat := [3, 4, 1, 1, 2, 3, 2, 4]
def baseStart_434434 : Nat := 118140960795 + 434434 * 2 ^ 59
def prefixEnd_434434 : Nat := 4983230072969 + 3 ^ 40 * 434434 * 2
def baseEnd_434434 : Nat := 66095838416432150719135

theorem tailTrace_434434 : CollatzResearch.WordTrace tailWord_434434 prefixEnd_434434 66095838416432150719135 := by
  unfold tailWord_434434
  simp only [CollatzResearch.WordTrace]
  refine ⟨3961277427031822066327589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10563406472084858843540237 3961277427031822066327589)
  ·
    refine ⟨742739517568466637436423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3961277427031822066327589 742739517568466637436423)
    ·
      refine ⟨1114109276352699956154635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 742739517568466637436423 1114109276352699956154635)
      ·
        refine ⟨1671163914529049934231953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1114109276352699956154635 1671163914529049934231953)
        ·
          refine ⟨1253372935896787450673965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1671163914529049934231953 1253372935896787450673965)
          ·
            refine ⟨470014850961295294002737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1253372935896787450673965 470014850961295294002737)
            ·
              refine ⟨352511138220971470502053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 470014850961295294002737 352511138220971470502053)
              ·
                refine ⟨66095838416432150719135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 352511138220971470502053 66095838416432150719135)
                ·
                  rfl

theorem cell20_434434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_434434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434434 prefixEnd_434434 := by exact prefixLift 434434
  have htrace : WordTrace (prefixWord ++ tailWord_434434) baseStart_434434 baseEnd_434434 := by
    simpa [prefixWord, tailWord_434434, baseEnd_434434] using wordTrace_append hprefix tailTrace_434434
  have hstable : (prefixWord ++ tailWord_434434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434434).length < 2 ^ (prefixWord ++ tailWord_434434).sum := by decide
  have hdescent : baseEnd_434434 < baseStart_434434 := by decide
  rcases family_descends (prefixWord ++ tailWord_434434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434483 : List Nat := [1, 1, 1, 2, 5, 1, 3, 3, 3]
def baseStart_434483 : Nat := 118140960795 + 434483 * 2 ^ 59
def prefixEnd_434483 : Nat := 4983230072969 + 3 ^ 40 * 434483 * 2
def baseEnd_434483 : Nat := 198309880184470059523871

theorem tailTrace_434483 : CollatzResearch.WordTrace tailWord_434483 prefixEnd_434483 198309880184470059523871 := by
  unfold tailWord_434483
  simp only [CollatzResearch.WordTrace]
  refine ⟨15846896884949769633844103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10564597923299846422562735 15846896884949769633844103)
  ·
    refine ⟨23770345327424654450766155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15846896884949769633844103 23770345327424654450766155)
    ·
      refine ⟨35655517991136981676149233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23770345327424654450766155 35655517991136981676149233)
      ·
        refine ⟨26741638493352736257111925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35655517991136981676149233 26741638493352736257111925)
        ·
          refine ⟨2507028608751819024104243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26741638493352736257111925 2507028608751819024104243)
          ·
            refine ⟨3760542913127728536156365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2507028608751819024104243 3760542913127728536156365)
            ·
              refine ⟨1410203592422898201058637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3760542913127728536156365 1410203592422898201058637)
              ·
                refine ⟨528826347158586825396989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1410203592422898201058637 528826347158586825396989)
                ·
                  refine ⟨198309880184470059523871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 528826347158586825396989 198309880184470059523871)
                  ·
                    rfl

theorem cell20_434483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 3].length) (baseStart_434483 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434483 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434483 prefixEnd_434483 := by exact prefixLift 434483
  have htrace : WordTrace (prefixWord ++ tailWord_434483) baseStart_434483 baseEnd_434483 := by
    simpa [prefixWord, tailWord_434483, baseEnd_434483] using wordTrace_append hprefix tailTrace_434483
  have hstable : (prefixWord ++ tailWord_434483).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434483).length < 2 ^ (prefixWord ++ tailWord_434483).sum := by decide
  have hdescent : baseEnd_434483 < baseStart_434483 := by decide
  rcases family_descends (prefixWord ++ tailWord_434483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434504 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 7]
def baseStart_434504 : Nat := 118140960795 + 434504 * 2 ^ 59
def prefixEnd_434504 : Nat := 4983230072969 + 3 ^ 40 * 434504 * 2
def baseEnd_434504 : Nat := 198319465156687319823785

theorem tailTrace_434504 : CollatzResearch.WordTrace tailWord_434504 prefixEnd_434504 198319465156687319823785 := by
  unfold tailWord_434504
  simp only [CollatzResearch.WordTrace]
  refine ⟨7923831408936845110179283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10565108545249126813572377 7923831408936845110179283)
  ·
    refine ⟨11885747113405267665268925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7923831408936845110179283 11885747113405267665268925)
    ·
      refine ⟨4457155167526975374475847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11885747113405267665268925 4457155167526975374475847)
      ·
        refine ⟨6685732751290463061713771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4457155167526975374475847 6685732751290463061713771)
        ·
          refine ⟨10028599126935694592570657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6685732751290463061713771 10028599126935694592570657)
          ·
            refine ⟨7521449345201770944427993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10028599126935694592570657 7521449345201770944427993)
            ·
              refine ⟨5641087008901328208320995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7521449345201770944427993 5641087008901328208320995)
              ·
                refine ⟨8461630513351992312481493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5641087008901328208320995 8461630513351992312481493)
                ·
                  refine ⟨198319465156687319823785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8461630513351992312481493 198319465156687319823785)
                  ·
                    rfl

theorem cell20_434504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_434504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434504 prefixEnd_434504 := by exact prefixLift 434504
  have htrace : WordTrace (prefixWord ++ tailWord_434504) baseStart_434504 baseEnd_434504 := by
    simpa [prefixWord, tailWord_434504, baseEnd_434504] using wordTrace_append hprefix tailTrace_434504
  have hstable : (prefixWord ++ tailWord_434504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434504).length < 2 ^ (prefixWord ++ tailWord_434504).sum := by decide
  have hdescent : baseEnd_434504 < baseStart_434504 := by decide
  rcases family_descends (prefixWord ++ tailWord_434504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434511 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 8]
def baseStart_434511 : Nat := 118140960795 + 434511 * 2 ^ 59
def prefixEnd_434511 : Nat := 4983230072969 + 3 ^ 40 * 434511 * 2
def baseEnd_434511 : Nat := 198322660147426406590423

theorem tailTrace_434511 : CollatzResearch.WordTrace tailWord_434511 prefixEnd_434511 198322660147426406590423 := by
  unfold tailWord_434511
  simp only [CollatzResearch.WordTrace]
  refine ⟨15847918128848330415863387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10565278752565553610575591 15847918128848330415863387)
  ·
    refine ⟨23771877193272495623795081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15847918128848330415863387 23771877193272495623795081)
    ·
      refine ⟨17828907894954371717846311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23771877193272495623795081 17828907894954371717846311)
      ·
        refine ⟨26743361842431557576769467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17828907894954371717846311 26743361842431557576769467)
        ·
          refine ⟨40115042763647336365154201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26743361842431557576769467 40115042763647336365154201)
          ·
            refine ⟨30086282072735502273865651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40115042763647336365154201 30086282072735502273865651)
            ·
              refine ⟨45129423109103253410798477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30086282072735502273865651 45129423109103253410798477)
              ·
                refine ⟨16923533665913720029049429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45129423109103253410798477 16923533665913720029049429)
                ·
                  refine ⟨198322660147426406590423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16923533665913720029049429 198322660147426406590423)
                  ·
                    rfl

theorem cell20_434511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 8].length) (baseStart_434511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434511 prefixEnd_434511 := by exact prefixLift 434511
  have htrace : WordTrace (prefixWord ++ tailWord_434511) baseStart_434511 baseEnd_434511 := by
    simpa [prefixWord, tailWord_434511, baseEnd_434511] using wordTrace_append hprefix tailTrace_434511
  have hstable : (prefixWord ++ tailWord_434511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434511).length < 2 ^ (prefixWord ++ tailWord_434511).sum := by decide
  have hdescent : baseEnd_434511 < baseStart_434511 := by decide
  rcases family_descends (prefixWord ++ tailWord_434511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434538 : List Nat := [3, 1, 3, 3, 1, 1, 2, 3, 3]
def baseStart_434538 : Nat := 118140960795 + 434538 * 2 ^ 59
def prefixEnd_434538 : Nat := 4983230072969 + 3 ^ 40 * 434538 * 2
def baseEnd_434538 : Nat := 198334983683134312690313

theorem tailTrace_434538 : CollatzResearch.WordTrace tailWord_434538 prefixEnd_434538 198334983683134312690313 := by
  unfold tailWord_434538
  simp only [CollatzResearch.WordTrace]
  refine ⟨3962225724937628506774067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10565935266500342684730845 3962225724937628506774067)
  ·
    refine ⟨5943338587406442760161101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3962225724937628506774067 5943338587406442760161101)
    ·
      refine ⟨2228751970277416035060413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5943338587406442760161101 2228751970277416035060413)
      ·
        refine ⟨835781988854031013147655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2228751970277416035060413 835781988854031013147655)
        ·
          refine ⟨1253672983281046519721483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 835781988854031013147655 1253672983281046519721483)
          ·
            refine ⟨1880509474921569779582225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1253672983281046519721483 1880509474921569779582225)
            ·
              refine ⟨1410382106191177334686669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1880509474921569779582225 1410382106191177334686669)
              ·
                refine ⟨528893289821691500507501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1410382106191177334686669 528893289821691500507501)
                ·
                  refine ⟨198334983683134312690313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 528893289821691500507501 198334983683134312690313)
                  ·
                    rfl

theorem cell20_434538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_434538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434538 prefixEnd_434538 := by exact prefixLift 434538
  have htrace : WordTrace (prefixWord ++ tailWord_434538) baseStart_434538 baseEnd_434538 := by
    simpa [prefixWord, tailWord_434538, baseEnd_434538] using wordTrace_append hprefix tailTrace_434538
  have hstable : (prefixWord ++ tailWord_434538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434538).length < 2 ^ (prefixWord ++ tailWord_434538).sum := by decide
  have hdescent : baseEnd_434538 < baseStart_434538 := by decide
  rcases family_descends (prefixWord ++ tailWord_434538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434583 : List Nat := [1, 1, 3, 3, 1, 1, 4, 4, 2]
def baseStart_434583 : Nat := 118140960795 + 434583 * 2 ^ 59
def prefixEnd_434583 : Nat := 4983230072969 + 3 ^ 40 * 434583 * 2
def baseEnd_434583 : Nat := 198355522909314156190129

theorem tailTrace_434583 : CollatzResearch.WordTrace tailWord_434583 prefixEnd_434583 198355522909314156190129 := by
  unfold tailWord_434583
  simp only [CollatzResearch.WordTrace]
  refine ⟨15850544184587486712484403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10567029456391657808322935 15850544184587486712484403)
  ·
    refine ⟨23775816276881230068726605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15850544184587486712484403 23775816276881230068726605)
    ·
      refine ⟨8915931103830461275772477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23775816276881230068726605 8915931103830461275772477)
      ·
        refine ⟨3343474163936422978414679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8915931103830461275772477 3343474163936422978414679)
        ·
          refine ⟨5015211245904634467622019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3343474163936422978414679 5015211245904634467622019)
          ·
            refine ⟨7522816868856951701433029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5015211245904634467622019 7522816868856951701433029)
            ·
              refine ⟨1410528162910678444018693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7522816868856951701433029 1410528162910678444018693)
              ·
                refine ⟨264474030545752208253505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1410528162910678444018693 264474030545752208253505)
                ·
                  refine ⟨198355522909314156190129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264474030545752208253505 198355522909314156190129)
                  ·
                    rfl

theorem cell20_434583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 4, 2].length) (baseStart_434583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434583 prefixEnd_434583 := by exact prefixLift 434583
  have htrace : WordTrace (prefixWord ++ tailWord_434583) baseStart_434583 baseEnd_434583 := by
    simpa [prefixWord, tailWord_434583, baseEnd_434583] using wordTrace_append hprefix tailTrace_434583
  have hstable : (prefixWord ++ tailWord_434583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434583).length < 2 ^ (prefixWord ++ tailWord_434583).sum := by decide
  have hdescent : baseEnd_434583 < baseStart_434583 := by decide
  rcases family_descends (prefixWord ++ tailWord_434583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434649 : List Nat := [1, 2, 1, 2, 4, 1, 4, 5]
def baseStart_434649 : Nat := 118140960795 + 434649 * 2 ^ 59
def prefixEnd_434649 : Nat := 4983230072969 + 3 ^ 40 * 434649 * 2
def baseEnd_434649 : Nat := 66128549035903753329953

theorem tailTrace_434649 : CollatzResearch.WordTrace tailWord_434649 prefixEnd_434649 66128549035903753329953 := by
  unfold tailWord_434649
  simp only [CollatzResearch.WordTrace]
  refine ⟨15852951402348379984387001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10568634268232253322924667 15852951402348379984387001)
  ·
    refine ⟨11889713551761284988290251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15852951402348379984387001 11889713551761284988290251)
    ·
      refine ⟨17834570327641927482435377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11889713551761284988290251 17834570327641927482435377)
      ·
        refine ⟨13375927745731445611826533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17834570327641927482435377 13375927745731445611826533)
        ·
          refine ⟨2507986452324646052217475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13375927745731445611826533 2507986452324646052217475)
          ·
            refine ⟨3761979678486969078326213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2507986452324646052217475 3761979678486969078326213)
            ·
              refine ⟨705371189716306702186165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3761979678486969078326213 705371189716306702186165)
              ·
                refine ⟨66128549035903753329953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 705371189716306702186165 66128549035903753329953)
                ·
                  rfl

theorem cell20_434649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 5].length) (baseStart_434649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434649 prefixEnd_434649 := by exact prefixLift 434649
  have htrace : WordTrace (prefixWord ++ tailWord_434649) baseStart_434649 baseEnd_434649 := by
    simpa [prefixWord, tailWord_434649, baseEnd_434649] using wordTrace_append hprefix tailTrace_434649
  have hstable : (prefixWord ++ tailWord_434649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434649).length < 2 ^ (prefixWord ++ tailWord_434649).sum := by decide
  have hdescent : baseEnd_434649 < baseStart_434649 := by decide
  rcases family_descends (prefixWord ++ tailWord_434649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434739 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 6]
def baseStart_434739 : Nat := 118140960795 + 434739 * 2 ^ 59
def prefixEnd_434739 : Nat := 4983230072969 + 3 ^ 40 * 434739 * 2
def baseEnd_434739 : Nat := 198426725560070946989491

theorem tailTrace_434739 : CollatzResearch.WordTrace tailWord_434739 prefixEnd_434739 198426725560070946989491 := by
  unfold tailWord_434739
  simp only [CollatzResearch.WordTrace]
  refine ⟨15856233972022325355163271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10570822648014883570108847 15856233972022325355163271)
  ·
    refine ⟨23784350958033488032744907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15856233972022325355163271 23784350958033488032744907)
    ·
      refine ⟨35676526437050232049117361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23784350958033488032744907 35676526437050232049117361)
      ·
        refine ⟨26757394827787674036838021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35676526437050232049117361 26757394827787674036838021)
        ·
          refine ⟨5017011530210188881907129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26757394827787674036838021 5017011530210188881907129)
          ·
            refine ⟨3762758647657641661430347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5017011530210188881907129 3762758647657641661430347)
            ·
              refine ⟨5644137971486462492145521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3762758647657641661430347 5644137971486462492145521)
              ·
                refine ⟨4233103478614846869109141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5644137971486462492145521 4233103478614846869109141)
                ·
                  refine ⟨198426725560070946989491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4233103478614846869109141 198426725560070946989491)
                  ·
                    rfl

theorem cell20_434739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 6].length) (baseStart_434739 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434739 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434739 prefixEnd_434739 := by exact prefixLift 434739
  have htrace : WordTrace (prefixWord ++ tailWord_434739) baseStart_434739 baseEnd_434739 := by
    simpa [prefixWord, tailWord_434739, baseEnd_434739] using wordTrace_append hprefix tailTrace_434739
  have hstable : (prefixWord ++ tailWord_434739).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434739).length < 2 ^ (prefixWord ++ tailWord_434739).sum := by decide
  have hdescent : baseEnd_434739 < baseStart_434739 := by decide
  rcases family_descends (prefixWord ++ tailWord_434739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434742 : List Nat := [5, 1, 2, 1, 2, 2, 7]
def baseStart_434742 : Nat := 118140960795 + 434742 * 2 ^ 59
def prefixEnd_434742 : Nat := 4983230072969 + 3 ^ 40 * 434742 * 2
def baseEnd_434742 : Nat := 22047566093535141098831

theorem tailTrace_434742 : CollatzResearch.WordTrace tailWord_434742 prefixEnd_434742 22047566093535141098831 := by
  unfold tailWord_434742
  simp only [CollatzResearch.WordTrace]
  refine ⟨991021461938216054220155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10570895594007637911681653 991021461938216054220155)
  ·
    refine ⟨1486532192907324081330233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 991021461938216054220155 1486532192907324081330233)
    ·
      refine ⟨1114899144680493060997675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1486532192907324081330233 1114899144680493060997675)
      ·
        refine ⟨1672348717020739591496513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1114899144680493060997675 1672348717020739591496513)
        ·
          refine ⟨1254261537765554693622385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1672348717020739591496513 1254261537765554693622385)
          ·
            refine ⟨940696153324166020216789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1254261537765554693622385 940696153324166020216789)
            ·
              refine ⟨22047566093535141098831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 940696153324166020216789 22047566093535141098831)
              ·
                rfl

theorem cell20_434742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 7].length) (baseStart_434742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434742 prefixEnd_434742 := by exact prefixLift 434742
  have htrace : WordTrace (prefixWord ++ tailWord_434742) baseStart_434742 baseEnd_434742 := by
    simpa [prefixWord, tailWord_434742, baseEnd_434742] using wordTrace_append hprefix tailTrace_434742
  have hstable : (prefixWord ++ tailWord_434742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434742).length < 2 ^ (prefixWord ++ tailWord_434742).sum := by decide
  have hdescent : baseEnd_434742 < baseStart_434742 := by decide
  rcases family_descends (prefixWord ++ tailWord_434742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434749 : List Nat := [1, 4, 1, 3, 2, 2, 1, 1, 5]
def baseStart_434749 : Nat := 118140960795 + 434749 * 2 ^ 59
def prefixEnd_434749 : Nat := 4983230072969 + 3 ^ 40 * 434749 * 2
def baseEnd_434749 : Nat := 198431289832555356656117

theorem tailTrace_434749 : CollatzResearch.WordTrace tailWord_434749 prefixEnd_434749 198431289832555356656117 := by
  unfold tailWord_434749
  simp only [CollatzResearch.WordTrace]
  refine ⟨15856598701986097063027301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10571065801324064708684867 15856598701986097063027301)
  ·
    refine ⟨2973112256622393199317619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15856598701986097063027301 2973112256622393199317619)
    ·
      refine ⟨4459668384933589798976429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2973112256622393199317619 4459668384933589798976429)
      ·
        refine ⟨1672375644350096174616161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4459668384933589798976429 1672375644350096174616161)
        ·
          refine ⟨1254281733262572130962121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1672375644350096174616161 1254281733262572130962121)
          ·
            refine ⟨940711299946929098221591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1254281733262572130962121 940711299946929098221591)
            ·
              refine ⟨1411066949920393647332387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 940711299946929098221591 1411066949920393647332387)
              ·
                refine ⟨2116600424880590470998581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1411066949920393647332387 2116600424880590470998581)
                ·
                  refine ⟨198431289832555356656117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2116600424880590470998581 198431289832555356656117)
                  ·
                    rfl

theorem cell20_434749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_434749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434749 prefixEnd_434749 := by exact prefixLift 434749
  have htrace : WordTrace (prefixWord ++ tailWord_434749) baseStart_434749 baseEnd_434749 := by
    simpa [prefixWord, tailWord_434749, baseEnd_434749] using wordTrace_append hprefix tailTrace_434749
  have hstable : (prefixWord ++ tailWord_434749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434749).length < 2 ^ (prefixWord ++ tailWord_434749).sum := by decide
  have hdescent : baseEnd_434749 < baseStart_434749 := by decide
  rcases family_descends (prefixWord ++ tailWord_434749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434780 : List Nat := [2, 2, 4, 1, 3, 1, 1, 6]
def baseStart_434780 : Nat := 118140960795 + 434780 * 2 ^ 59
def prefixEnd_434780 : Nat := 4983230072969 + 3 ^ 40 * 434780 * 2
def baseEnd_434780 : Nat := 66148479692419008874219

theorem tailTrace_434780 : CollatzResearch.WordTrace tailWord_434780 prefixEnd_434780 66148479692419008874219 := by
  unfold tailWord_434780
  simp only [CollatzResearch.WordTrace]
  refine ⟨7928864682436894678702897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10571819576582526238270529 7928864682436894678702897)
  ·
    refine ⟨5946648511827671009027173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7928864682436894678702897 5946648511827671009027173)
    ·
      refine ⟨1114996595967688314192595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5946648511827671009027173 1114996595967688314192595)
      ·
        refine ⟨1672494893951532471288893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1114996595967688314192595 1672494893951532471288893)
        ·
          refine ⟨627185585231824676733335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1672494893951532471288893 627185585231824676733335)
          ·
            refine ⟨940778377847737015100003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627185585231824676733335 940778377847737015100003)
            ·
              refine ⟨1411167566771605522650005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 940778377847737015100003 1411167566771605522650005)
              ·
                refine ⟨66148479692419008874219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1411167566771605522650005 66148479692419008874219)
                ·
                  rfl

theorem cell20_434780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 6].length) (baseStart_434780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434780 prefixEnd_434780 := by exact prefixLift 434780
  have htrace : WordTrace (prefixWord ++ tailWord_434780) baseStart_434780 baseEnd_434780 := by
    simpa [prefixWord, tailWord_434780, baseEnd_434780] using wordTrace_append hprefix tailTrace_434780
  have hstable : (prefixWord ++ tailWord_434780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434780).length < 2 ^ (prefixWord ++ tailWord_434780).sum := by decide
  have hdescent : baseEnd_434780 < baseStart_434780 := by decide
  rcases family_descends (prefixWord ++ tailWord_434780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434782 : List Nat := [4, 4, 1, 2, 2, 1, 1, 3, 2]
def baseStart_434782 : Nat := 118140960795 + 434782 * 2 ^ 59
def prefixEnd_434782 : Nat := 4983230072969 + 3 ^ 40 * 434782 * 2
def baseEnd_434782 : Nat := 198446351931753908555983

theorem tailTrace_434782 : CollatzResearch.WordTrace tailWord_434782 prefixEnd_434782 198446351931753908555983 := by
  unfold tailWord_434782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1982225288858317962372325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10571868207244362465985733 1982225288858317962372325)
  ·
    refine ⟨371667241660934617944811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1982225288858317962372325 371667241660934617944811)
    ·
      refine ⟨557500862491401926917217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371667241660934617944811 557500862491401926917217)
      ·
        refine ⟨418125646868551445187913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 557500862491401926917217 418125646868551445187913)
        ·
          refine ⟨313594235151413583890935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418125646868551445187913 313594235151413583890935)
          ·
            refine ⟨470391352727120375836403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313594235151413583890935 470391352727120375836403)
            ·
              refine ⟨705587029090680563754605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470391352727120375836403 705587029090680563754605)
              ·
                refine ⟨264595135909005211407977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 705587029090680563754605 264595135909005211407977)
                ·
                  refine ⟨198446351931753908555983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264595135909005211407977 198446351931753908555983)
                  ·
                    rfl

theorem cell20_434782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_434782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434782 prefixEnd_434782 := by exact prefixLift 434782
  have htrace : WordTrace (prefixWord ++ tailWord_434782) baseStart_434782 baseEnd_434782 := by
    simpa [prefixWord, tailWord_434782, baseEnd_434782] using wordTrace_append hprefix tailTrace_434782
  have hstable : (prefixWord ++ tailWord_434782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434782).length < 2 ^ (prefixWord ++ tailWord_434782).sum := by decide
  have hdescent : baseEnd_434782 < baseStart_434782 := by decide
  rcases family_descends (prefixWord ++ tailWord_434782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434786 : List Nat := [3, 3, 2, 3, 1, 2, 1, 3, 2]
def baseStart_434786 : Nat := 118140960795 + 434786 * 2 ^ 59
def prefixEnd_434786 : Nat := 4983230072969 + 3 ^ 40 * 434786 * 2
def baseEnd_434786 : Nat := 198448177640747672422633

theorem tailTrace_434786 : CollatzResearch.WordTrace tailWord_434786 prefixEnd_434786 198448177640747672422633 := by
  unfold tailWord_434786
  simp only [CollatzResearch.WordTrace]
  refine ⟨3964487050713013095531053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10571965468568034921416141 3964487050713013095531053)
  ·
    refine ⟨1486682644017379910824145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3964487050713013095531053 1486682644017379910824145)
    ·
      refine ⟨1115011983013034933118109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1486682644017379910824145 1115011983013034933118109)
      ·
        refine ⟨418129493629888099919291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1115011983013034933118109 418129493629888099919291)
        ·
          refine ⟨627194240444832149878937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418129493629888099919291 627194240444832149878937)
          ·
            refine ⟨470395680333624112409203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 627194240444832149878937 470395680333624112409203)
            ·
              refine ⟨705593520500436168613805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470395680333624112409203 705593520500436168613805)
              ·
                refine ⟨264597570187663563230177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 705593520500436168613805 264597570187663563230177)
                ·
                  refine ⟨198448177640747672422633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264597570187663563230177 198448177640747672422633)
                  ·
                    rfl

theorem cell20_434786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_434786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434786 prefixEnd_434786 := by exact prefixLift 434786
  have htrace : WordTrace (prefixWord ++ tailWord_434786) baseStart_434786 baseEnd_434786 := by
    simpa [prefixWord, tailWord_434786, baseEnd_434786] using wordTrace_append hprefix tailTrace_434786
  have hstable : (prefixWord ++ tailWord_434786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434786).length < 2 ^ (prefixWord ++ tailWord_434786).sum := by decide
  have hdescent : baseEnd_434786 < baseStart_434786 := by decide
  rcases family_descends (prefixWord ++ tailWord_434786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434815 : List Nat := [1, 1, 2, 2, 1, 1, 1, 7, 4]
def baseStart_434815 : Nat := 118140960795 + 434815 * 2 ^ 59
def prefixEnd_434815 : Nat := 4983230072969 + 3 ^ 40 * 434815 * 2
def baseEnd_434815 : Nat := 198461414030952460455847

theorem tailTrace_434815 : CollatzResearch.WordTrace tailWord_434815 prefixEnd_434815 198461414030952460455847 := by
  unfold tailWord_434815
  simp only [CollatzResearch.WordTrace]
  refine ⟨15859005919746990334929899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10572670613164660223286599 15859005919746990334929899)
  ·
    refine ⟨23788508879620485502394849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15859005919746990334929899 23788508879620485502394849)
    ·
      refine ⟨17841381659715364126796137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23788508879620485502394849 17841381659715364126796137)
      ·
        refine ⟨13381036244786523095097103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17841381659715364126796137 13381036244786523095097103)
        ·
          refine ⟨20071554367179784642645655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13381036244786523095097103 20071554367179784642645655)
          ·
            refine ⟨30107331550769676963968483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20071554367179784642645655 30107331550769676963968483)
            ·
              refine ⟨45160997326154515445952725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30107331550769676963968483 45160997326154515445952725)
              ·
                refine ⟨1058460874831746455764517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 45160997326154515445952725 1058460874831746455764517)
                ·
                  refine ⟨198461414030952460455847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1058460874831746455764517 198461414030952460455847)
                  ·
                    rfl

theorem cell20_434815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 4].length) (baseStart_434815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434815 prefixEnd_434815 := by exact prefixLift 434815
  have htrace : WordTrace (prefixWord ++ tailWord_434815) baseStart_434815 baseEnd_434815 := by
    simpa [prefixWord, tailWord_434815, baseEnd_434815] using wordTrace_append hprefix tailTrace_434815
  have hstable : (prefixWord ++ tailWord_434815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434815).length < 2 ^ (prefixWord ++ tailWord_434815).sum := by decide
  have hdescent : baseEnd_434815 < baseStart_434815 := by decide
  rcases family_descends (prefixWord ++ tailWord_434815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434862 : List Nat := [4, 1, 4, 1, 1, 3, 2, 2, 2]
def baseStart_434862 : Nat := 118140960795 + 434862 * 2 ^ 59
def prefixEnd_434862 : Nat := 4983230072969 + 3 ^ 40 * 434862 * 2
def baseEnd_434862 : Nat := 198482866111629185888989

theorem tailTrace_434862 : CollatzResearch.WordTrace tailWord_434862 prefixEnd_434862 198482866111629185888989 := by
  unfold tailWord_434862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1982590018822089670236355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10573813433717811574593893 1982590018822089670236355)
  ·
    refine ⟨2973885028233134505354533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1982590018822089670236355 2973885028233134505354533)
    ·
      refine ⟨557603442793712719753975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2973885028233134505354533 557603442793712719753975)
      ·
        refine ⟨836405164190569079630963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557603442793712719753975 836405164190569079630963)
        ·
          refine ⟨1254607746285853619446445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 836405164190569079630963 1254607746285853619446445)
          ·
            refine ⟨470477904857195107292417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1254607746285853619446445 470477904857195107292417)
            ·
              refine ⟨352858428642896330469313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 470477904857195107292417 352858428642896330469313)
              ·
                refine ⟨264643821482172247851985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 352858428642896330469313 264643821482172247851985)
                ·
                  refine ⟨198482866111629185888989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264643821482172247851985 198482866111629185888989)
                  ·
                    rfl

theorem cell20_434862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_434862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434862 prefixEnd_434862 := by exact prefixLift 434862
  have htrace : WordTrace (prefixWord ++ tailWord_434862) baseStart_434862 baseEnd_434862 := by
    simpa [prefixWord, tailWord_434862, baseEnd_434862] using wordTrace_append hprefix tailTrace_434862
  have hstable : (prefixWord ++ tailWord_434862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434862).length < 2 ^ (prefixWord ++ tailWord_434862).sum := by decide
  have hdescent : baseEnd_434862 < baseStart_434862 := by decide
  rcases family_descends (prefixWord ++ tailWord_434862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434863 : List Nat := [1, 1, 2, 1, 2, 6, 2, 2, 3]
def baseStart_434863 : Nat := 118140960795 + 434863 * 2 ^ 59
def prefixEnd_434863 : Nat := 4983230072969 + 3 ^ 40 * 434863 * 2
def baseEnd_434863 : Nat := 198483322538877626855651

theorem tailTrace_434863 : CollatzResearch.WordTrace tailWord_434863 prefixEnd_434863 198483322538877626855651 := by
  unfold tailWord_434863
  simp only [CollatzResearch.WordTrace]
  refine ⟨15860756623573094532677243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10573837749048729688451495 15860756623573094532677243)
  ·
    refine ⟨23791134935359641799015865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15860756623573094532677243 23791134935359641799015865)
    ·
      refine ⟨17843351201519731349261899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23791134935359641799015865 17843351201519731349261899)
      ·
        refine ⟨26765026802279597023892849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17843351201519731349261899 26765026802279597023892849)
        ·
          refine ⟨20073770101709697767919637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26765026802279597023892849 20073770101709697767919637)
          ·
            refine ⟨940957973517642082871233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20073770101709697767919637 940957973517642082871233)
            ·
              refine ⟨705718480138231562153425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 940957973517642082871233 705718480138231562153425)
              ·
                refine ⟨529288860103673671615069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 705718480138231562153425 529288860103673671615069)
                ·
                  refine ⟨198483322538877626855651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 529288860103673671615069 198483322538877626855651)
                  ·
                    rfl

theorem cell20_434863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 3].length) (baseStart_434863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434863 prefixEnd_434863 := by exact prefixLift 434863
  have htrace : WordTrace (prefixWord ++ tailWord_434863) baseStart_434863 baseEnd_434863 := by
    simpa [prefixWord, tailWord_434863, baseEnd_434863] using wordTrace_append hprefix tailTrace_434863
  have hstable : (prefixWord ++ tailWord_434863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434863).length < 2 ^ (prefixWord ++ tailWord_434863).sum := by decide
  have hdescent : baseEnd_434863 < baseStart_434863 := by decide
  rcases family_descends (prefixWord ++ tailWord_434863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434877 : List Nat := [1, 4, 1, 2, 1, 3, 3, 5]
def baseStart_434877 : Nat := 118140960795 + 434877 * 2 ^ 59
def prefixEnd_434877 : Nat := 4983230072969 + 3 ^ 40 * 434877 * 2
def baseEnd_434877 : Nat := 66163237506785266796309

theorem tailTrace_434877 : CollatzResearch.WordTrace tailWord_434877 prefixEnd_434877 66163237506785266796309 := by
  unfold tailWord_434877
  simp only [CollatzResearch.WordTrace]
  refine ⟨15861267245522374923686885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10574178163681583282457923 15861267245522374923686885)
  ·
    refine ⟨2973987608535445298191291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15861267245522374923686885 2973987608535445298191291)
    ·
      refine ⟨4460981412803167947286937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2973987608535445298191291 4460981412803167947286937)
      ·
        refine ⟨3345736059602375960465203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4460981412803167947286937 3345736059602375960465203)
        ·
          refine ⟨5018604089403563940697805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3345736059602375960465203 5018604089403563940697805)
          ·
            refine ⟨1881976533526336477761677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5018604089403563940697805 1881976533526336477761677)
            ·
              refine ⟨705741200072376179160629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1881976533526336477761677 705741200072376179160629)
              ·
                refine ⟨66163237506785266796309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 705741200072376179160629 66163237506785266796309)
                ·
                  rfl

theorem cell20_434877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 5].length) (baseStart_434877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434877 prefixEnd_434877 := by exact prefixLift 434877
  have htrace : WordTrace (prefixWord ++ tailWord_434877) baseStart_434877 baseEnd_434877 := by
    simpa [prefixWord, tailWord_434877, baseEnd_434877] using wordTrace_append hprefix tailTrace_434877
  have hstable : (prefixWord ++ tailWord_434877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434877).length < 2 ^ (prefixWord ++ tailWord_434877).sum := by decide
  have hdescent : baseEnd_434877 < baseStart_434877 := by decide
  rcases family_descends (prefixWord ++ tailWord_434877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434894 : List Nat := [4, 1, 1, 1, 3, 3, 3, 4]
def baseStart_434894 : Nat := 118140960795 + 434894 * 2 ^ 59
def prefixEnd_434894 : Nat := 4983230072969 + 3 ^ 40 * 434894 * 2
def baseEnd_434894 : Nat := 66165823927859765607397

theorem tailTrace_434894 : CollatzResearch.WordTrace tailWord_434894 prefixEnd_434894 66165823927859765607397 := by
  unfold tailWord_434894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1982735910807598353381967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10574591524307191218037157 1982735910807598353381967)
  ·
    refine ⟨2974103866211397530072951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1982735910807598353381967 2974103866211397530072951)
    ·
      refine ⟨4461155799317096295109427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2974103866211397530072951 4461155799317096295109427)
      ·
        refine ⟨6691733698975644442664141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4461155799317096295109427 6691733698975644442664141)
        ·
          refine ⟨2509400137115866665999053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6691733698975644442664141 2509400137115866665999053)
          ·
            refine ⟨941025051418449999749645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2509400137115866665999053 941025051418449999749645)
            ·
              refine ⟨352884394281918749906117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 941025051418449999749645 352884394281918749906117)
              ·
                refine ⟨66165823927859765607397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 352884394281918749906117 66165823927859765607397)
                ·
                  rfl

theorem cell20_434894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_434894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434894 prefixEnd_434894 := by exact prefixLift 434894
  have htrace : WordTrace (prefixWord ++ tailWord_434894) baseStart_434894 baseEnd_434894 := by
    simpa [prefixWord, tailWord_434894, baseEnd_434894] using wordTrace_append hprefix tailTrace_434894
  have hstable : (prefixWord ++ tailWord_434894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434894).length < 2 ^ (prefixWord ++ tailWord_434894).sum := by decide
  have hdescent : baseEnd_434894 < baseStart_434894 := by decide
  rcases family_descends (prefixWord ++ tailWord_434894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434915 : List Nat := [1, 1, 1, 7, 1, 2, 7]
def baseStart_434915 : Nat := 118140960795 + 434915 * 2 ^ 59
def prefixEnd_434915 : Nat := 4983230072969 + 3 ^ 40 * 434915 * 2
def baseEnd_434915 : Nat := 22056339639532950791345

theorem tailTrace_434915 : CollatzResearch.WordTrace tailWord_434915 prefixEnd_434915 22056339639532950791345 := by
  unfold tailWord_434915
  simp only [CollatzResearch.WordTrace]
  refine ⟨15862653219384707413570199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10575102146256471609046799 15862653219384707413570199)
  ·
    refine ⟨23793979829077061120355299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15862653219384707413570199 23793979829077061120355299)
    ·
      refine ⟨35690969743615591680532949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23793979829077061120355299 35690969743615591680532949)
      ·
        refine ⟨836507103365990430012491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 35690969743615591680532949 836507103365990430012491)
        ·
          refine ⟨1254760655048985645018737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 836507103365990430012491 1254760655048985645018737)
          ·
            refine ⟨941070491286739233764053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1254760655048985645018737 941070491286739233764053)
            ·
              refine ⟨22056339639532950791345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 941070491286739233764053 22056339639532950791345)
              ·
                rfl

theorem cell20_434915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 7].length) (baseStart_434915 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434915 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434915 prefixEnd_434915 := by exact prefixLift 434915
  have htrace : WordTrace (prefixWord ++ tailWord_434915) baseStart_434915 baseEnd_434915 := by
    simpa [prefixWord, tailWord_434915, baseEnd_434915] using wordTrace_append hprefix tailTrace_434915
  have hstable : (prefixWord ++ tailWord_434915).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434915).length < 2 ^ (prefixWord ++ tailWord_434915).sum := by decide
  have hdescent : baseEnd_434915 < baseStart_434915 := by decide
  rcases family_descends (prefixWord ++ tailWord_434915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434925 : List Nat := [1, 5, 1, 2, 1, 1, 1, 6, 2]
def baseStart_434925 : Nat := 118140960795 + 434925 * 2 ^ 59
def prefixEnd_434925 : Nat := 4983230072969 + 3 ^ 40 * 434925 * 2
def baseEnd_434925 : Nat := 198511621028280966788731

theorem tailTrace_434925 : CollatzResearch.WordTrace tailWord_434925 prefixEnd_434925 198511621028280966788731 := by
  unfold tailWord_434925
  simp only [CollatzResearch.WordTrace]
  refine ⟨15863017949348479121434229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10575345299565652747622819 15863017949348479121434229)
  ·
    refine ⟨1487157932751419917634459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15863017949348479121434229 1487157932751419917634459)
    ·
      refine ⟨2230736899127129876451689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1487157932751419917634459 2230736899127129876451689)
      ·
        refine ⟨1673052674345347407338767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2230736899127129876451689 1673052674345347407338767)
        ·
          refine ⟨2509579011518021111008151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1673052674345347407338767 2509579011518021111008151)
          ·
            refine ⟨3764368517277031666512227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2509579011518021111008151 3764368517277031666512227)
            ·
              refine ⟨5646552775915547499768341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3764368517277031666512227 5646552775915547499768341)
              ·
                refine ⟨264682161371041289051641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5646552775915547499768341 264682161371041289051641)
                ·
                  refine ⟨198511621028280966788731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264682161371041289051641 198511621028280966788731)
                  ·
                    rfl

theorem cell20_434925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_434925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434925 prefixEnd_434925 := by exact prefixLift 434925
  have htrace : WordTrace (prefixWord ++ tailWord_434925) baseStart_434925 baseEnd_434925 := by
    simpa [prefixWord, tailWord_434925, baseEnd_434925] using wordTrace_append hprefix tailTrace_434925
  have hstable : (prefixWord ++ tailWord_434925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434925).length < 2 ^ (prefixWord ++ tailWord_434925).sum := by decide
  have hdescent : baseEnd_434925 < baseStart_434925 := by decide
  rcases family_descends (prefixWord ++ tailWord_434925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434936 : List Nat := [2, 1, 2, 1, 1, 2, 4, 7]
def baseStart_434936 : Nat := 118140960795 + 434936 * 2 ^ 59
def prefixEnd_434936 : Nat := 4983230072969 + 3 ^ 40 * 434936 * 2
def baseEnd_434936 : Nat := 66172213909337939140673

theorem tailTrace_434936 : CollatzResearch.WordTrace tailWord_434936 prefixEnd_434936 66172213909337939140673 := by
  unfold tailWord_434936
  simp only [CollatzResearch.WordTrace]
  refine ⟨7931709576154314000042331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10575612768205752000056441 7931709576154314000042331)
  ·
    refine ⟨11897564364231471000063497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7931709576154314000042331 11897564364231471000063497)
    ·
      refine ⟨8923173273173603250047623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11897564364231471000063497 8923173273173603250047623)
      ·
        refine ⟨13384759909760404875071435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8923173273173603250047623 13384759909760404875071435)
        ·
          refine ⟨20077139864640607312607153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13384759909760404875071435 20077139864640607312607153)
          ·
            refine ⟨15057854898480455484455365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20077139864640607312607153 15057854898480455484455365)
            ·
              refine ⟨2823347793465085403335381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15057854898480455484455365 2823347793465085403335381)
              ·
                refine ⟨66172213909337939140673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2823347793465085403335381 66172213909337939140673)
                ·
                  rfl

theorem cell20_434936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 7].length) (baseStart_434936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434936 prefixEnd_434936 := by exact prefixLift 434936
  have htrace : WordTrace (prefixWord ++ tailWord_434936) baseStart_434936 baseEnd_434936 := by
    simpa [prefixWord, tailWord_434936, baseEnd_434936] using wordTrace_append hprefix tailTrace_434936
  have hstable : (prefixWord ++ tailWord_434936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434936).length < 2 ^ (prefixWord ++ tailWord_434936).sum := by decide
  have hdescent : baseEnd_434936 < baseStart_434936 := by decide
  rcases family_descends (prefixWord ++ tailWord_434936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434953 : List Nat := [1, 2, 1, 1, 3, 2, 6, 4]
def baseStart_434953 : Nat := 118140960795 + 434953 * 2 ^ 59
def prefixEnd_434953 : Nat := 4983230072969 + 3 ^ 40 * 434953 * 2
def baseEnd_434953 : Nat := 66174800330412437951761

theorem tailTrace_434953 : CollatzResearch.WordTrace tailWord_434953 prefixEnd_434953 66174800330412437951761 := by
  unfold tailWord_434953
  simp only [CollatzResearch.WordTrace]
  refine ⟨15864039193247039903453513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10576026128831359935635675 15864039193247039903453513)
  ·
    refine ⟨11898029394935279927590135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15864039193247039903453513 11898029394935279927590135)
    ·
      refine ⟨17847044092402919891385203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11898029394935279927590135 17847044092402919891385203)
      ·
        refine ⟨26770566138604379837077805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17847044092402919891385203 26770566138604379837077805)
        ·
          refine ⟨10038962301976642438904177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26770566138604379837077805 10038962301976642438904177)
          ·
            refine ⟨7529221726482481829178133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10038962301976642438904177 7529221726482481829178133)
            ·
              refine ⟨352932268428866335742725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7529221726482481829178133 352932268428866335742725)
              ·
                refine ⟨66174800330412437951761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 352932268428866335742725 66174800330412437951761)
                ·
                  rfl

theorem cell20_434953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 4].length) (baseStart_434953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434953 prefixEnd_434953 := by exact prefixLift 434953
  have htrace : WordTrace (prefixWord ++ tailWord_434953) baseStart_434953 baseEnd_434953 := by
    simpa [prefixWord, tailWord_434953, baseEnd_434953] using wordTrace_append hprefix tailTrace_434953
  have hstable : (prefixWord ++ tailWord_434953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434953).length < 2 ^ (prefixWord ++ tailWord_434953).sum := by decide
  have hdescent : baseEnd_434953 < baseStart_434953 := by decide
  rcases family_descends (prefixWord ++ tailWord_434953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434980 : List Nat := [2, 3, 1, 3, 4, 1, 1, 1, 4]
def baseStart_434980 : Nat := 118140960795 + 434980 * 2 ^ 59
def prefixEnd_434980 : Nat := 4983230072969 + 3 ^ 40 * 434980 * 2
def baseEnd_434980 : Nat := 198536724526945219955173

theorem tailTrace_434980 : CollatzResearch.WordTrace tailWord_434980 prefixEnd_434980 198536724526945219955173 := by
  unfold tailWord_434980
  simp only [CollatzResearch.WordTrace]
  refine ⟨7932511982074611757343197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10576682642766149009790929 7932511982074611757343197)
  ·
    refine ⟨2974691993277979409003699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7932511982074611757343197 2974691993277979409003699)
    ·
      refine ⟨4462037989916969113505549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2974691993277979409003699 4462037989916969113505549)
      ·
        refine ⟨1673264246218863417564581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4462037989916969113505549 1673264246218863417564581)
        ·
          refine ⟨313737046166036890793359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1673264246218863417564581 313737046166036890793359)
          ·
            refine ⟨470605569249055336190039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313737046166036890793359 470605569249055336190039)
            ·
              refine ⟨705908353873583004285059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470605569249055336190039 705908353873583004285059)
              ·
                refine ⟨1058862530810374506427589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 705908353873583004285059 1058862530810374506427589)
                ·
                  refine ⟨198536724526945219955173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1058862530810374506427589 198536724526945219955173)
                  ·
                    rfl

theorem cell20_434980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_434980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_434980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_434980 prefixEnd_434980 := by exact prefixLift 434980
  have htrace : WordTrace (prefixWord ++ tailWord_434980) baseStart_434980 baseEnd_434980 := by
    simpa [prefixWord, tailWord_434980, baseEnd_434980] using wordTrace_append hprefix tailTrace_434980
  have hstable : (prefixWord ++ tailWord_434980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434980).length < 2 ^ (prefixWord ++ tailWord_434980).sum := by decide
  have hdescent : baseEnd_434980 < baseStart_434980 := by decide
  rcases family_descends (prefixWord ++ tailWord_434980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435077 : List Nat := [1, 3, 1, 1, 3, 4, 2, 3, 2]
def baseStart_435077 : Nat := 118140960795 + 435077 * 2 ^ 59
def prefixEnd_435077 : Nat := 4983230072969 + 3 ^ 40 * 435077 * 2
def baseEnd_435077 : Nat := 198580997970043993721443

theorem tailTrace_435077 : CollatzResearch.WordTrace tailWord_435077 prefixEnd_435077 198580997970043993721443 := by
  unfold tailWord_435077
  simp only [CollatzResearch.WordTrace]
  refine ⟨15868561844797809080967485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10579041229865206053978323 15868561844797809080967485)
  ·
    refine ⟨5950710691799178405362807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15868561844797809080967485 5950710691799178405362807)
    ·
      refine ⟨8926066037698767608044211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5950710691799178405362807 8926066037698767608044211)
      ·
        refine ⟨13389099056548151412066317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8926066037698767608044211 13389099056548151412066317)
        ·
          refine ⟨5020912146205556779524869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13389099056548151412066317 5020912146205556779524869)
          ·
            refine ⟨941421027413541896160913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5020912146205556779524869 941421027413541896160913)
            ·
              refine ⟨706065770560156422120685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 941421027413541896160913 706065770560156422120685)
              ·
                refine ⟨264774663960058658295257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 706065770560156422120685 264774663960058658295257)
                ·
                  refine ⟨198580997970043993721443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264774663960058658295257 198580997970043993721443)
                  ·
                    rfl

theorem cell20_435077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 3, 2].length) (baseStart_435077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435077 prefixEnd_435077 := by exact prefixLift 435077
  have htrace : WordTrace (prefixWord ++ tailWord_435077) baseStart_435077 baseEnd_435077 := by
    simpa [prefixWord, tailWord_435077, baseEnd_435077] using wordTrace_append hprefix tailTrace_435077
  have hstable : (prefixWord ++ tailWord_435077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435077).length < 2 ^ (prefixWord ++ tailWord_435077).sum := by decide
  have hdescent : baseEnd_435077 < baseStart_435077 := by decide
  rcases family_descends (prefixWord ++ tailWord_435077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435094 : List Nat := [5, 3, 1, 1, 1, 1, 1, 3, 4]
def baseStart_435094 : Nat := 118140960795 + 435094 * 2 ^ 59
def prefixEnd_435094 : Nat := 4983230072969 + 3 ^ 40 * 435094 * 2
def baseEnd_435094 : Nat := 198588757233267490154707

theorem tailTrace_435094 : CollatzResearch.WordTrace tailWord_435094 prefixEnd_435094 198588757233267490154707 := by
  unfold tailWord_435094
  simp only [CollatzResearch.WordTrace]
  refine ⟨991823867858513811521021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10579454590490813989557557 991823867858513811521021)
  ·
    refine ⟨371933950446942679320383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 991823867858513811521021 371933950446942679320383)
    ·
      refine ⟨557900925670414018980575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371933950446942679320383 557900925670414018980575)
      ·
        refine ⟨836851388505621028470863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557900925670414018980575 836851388505621028470863)
        ·
          refine ⟨1255277082758431542706295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 836851388505621028470863 1255277082758431542706295)
          ·
            refine ⟨1882915624137647314059443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1255277082758431542706295 1882915624137647314059443)
            ·
              refine ⟨2824373436206470971089165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1882915624137647314059443 2824373436206470971089165)
              ·
                refine ⟨1059140038577426614158437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2824373436206470971089165 1059140038577426614158437)
                ·
                  refine ⟨198588757233267490154707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1059140038577426614158437 198588757233267490154707)
                  ·
                    rfl

theorem cell20_435094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_435094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435094 prefixEnd_435094 := by exact prefixLift 435094
  have htrace : WordTrace (prefixWord ++ tailWord_435094) baseStart_435094 baseEnd_435094 := by
    simpa [prefixWord, tailWord_435094, baseEnd_435094] using wordTrace_append hprefix tailTrace_435094
  have hstable : (prefixWord ++ tailWord_435094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435094).length < 2 ^ (prefixWord ++ tailWord_435094).sum := by decide
  have hdescent : baseEnd_435094 < baseStart_435094 := by decide
  rcases family_descends (prefixWord ++ tailWord_435094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435150 : List Nat := [4, 1, 1, 1, 2, 3, 2, 1, 5]
def baseStart_435150 : Nat := 118140960795 + 435150 * 2 ^ 59
def prefixEnd_435150 : Nat := 4983230072969 + 3 ^ 40 * 435150 * 2
def baseEnd_435150 : Nat := 198614317159180184287811

theorem tailTrace_435150 : CollatzResearch.WordTrace tailWord_435150 prefixEnd_435150 198614317159180184287811 := by
  unfold tailWord_435150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1983903046691667818546863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10580816249022228365583269 1983903046691667818546863)
  ·
    refine ⟨2975854570037501727820295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1983903046691667818546863 2975854570037501727820295)
    ·
      refine ⟨4463781855056252591730443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2975854570037501727820295 4463781855056252591730443)
      ·
        refine ⟨6695672782584378887595665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4463781855056252591730443 6695672782584378887595665)
        ·
          refine ⟨5021754586938284165696749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6695672782584378887595665 5021754586938284165696749)
          ·
            refine ⟨1883157970101856562136281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5021754586938284165696749 1883157970101856562136281)
            ·
              refine ⟨1412368477576392421602211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1883157970101856562136281 1412368477576392421602211)
              ·
                refine ⟨2118552716364588632403317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1412368477576392421602211 2118552716364588632403317)
                ·
                  refine ⟨198614317159180184287811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2118552716364588632403317 198614317159180184287811)
                  ·
                    rfl

theorem cell20_435150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_435150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435150 prefixEnd_435150 := by exact prefixLift 435150
  have htrace : WordTrace (prefixWord ++ tailWord_435150) baseStart_435150 baseEnd_435150 := by
    simpa [prefixWord, tailWord_435150, baseEnd_435150] using wordTrace_append hprefix tailTrace_435150
  have hstable : (prefixWord ++ tailWord_435150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435150).length < 2 ^ (prefixWord ++ tailWord_435150).sum := by decide
  have hdescent : baseEnd_435150 < baseStart_435150 := by decide
  rcases family_descends (prefixWord ++ tailWord_435150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435153 : List Nat := [1, 2, 2, 1, 2, 1, 7, 2, 2]
def baseStart_435153 : Nat := 118140960795 + 435153 * 2 ^ 59
def prefixEnd_435153 : Nat := 4983230072969 + 3 ^ 40 * 435153 * 2
def baseEnd_435153 : Nat := 198615686440925507187799

theorem tailTrace_435153 : CollatzResearch.WordTrace tailWord_435153 prefixEnd_435153 198615686440925507187799 := by
  unfold tailWord_435153
  simp only [CollatzResearch.WordTrace]
  refine ⟨15871333792522474060734113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10580889195014982707156075 15871333792522474060734113)
  ·
    refine ⟨11903500344391855545550585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15871333792522474060734113 11903500344391855545550585)
    ·
      refine ⟨8927625258293891659162939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11903500344391855545550585 8927625258293891659162939)
      ·
        refine ⟨13391437887440837488744409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8927625258293891659162939 13391437887440837488744409)
        ·
          refine ⟨10043578415580628116558307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13391437887440837488744409 10043578415580628116558307)
          ·
            refine ⟨15065367623370942174837461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10043578415580628116558307 15065367623370942174837461)
            ·
              refine ⟨353094553672756457222753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 15065367623370942174837461 353094553672756457222753)
              ·
                refine ⟨264820915254567342917065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 353094553672756457222753 264820915254567342917065)
                ·
                  refine ⟨198615686440925507187799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264820915254567342917065 198615686440925507187799)
                  ·
                    rfl

theorem cell20_435153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 2, 2].length) (baseStart_435153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435153 prefixEnd_435153 := by exact prefixLift 435153
  have htrace : WordTrace (prefixWord ++ tailWord_435153) baseStart_435153 baseEnd_435153 := by
    simpa [prefixWord, tailWord_435153, baseEnd_435153] using wordTrace_append hprefix tailTrace_435153
  have hstable : (prefixWord ++ tailWord_435153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435153).length < 2 ^ (prefixWord ++ tailWord_435153).sum := by decide
  have hdescent : baseEnd_435153 < baseStart_435153 := by decide
  rcases family_descends (prefixWord ++ tailWord_435153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435167 : List Nat := [1, 1, 2, 3, 5, 1, 1, 3, 3]
def baseStart_435167 : Nat := 118140960795 + 435167 * 2 ^ 59
def prefixEnd_435167 : Nat := 4983230072969 + 3 ^ 40 * 435167 * 2
def baseEnd_435167 : Nat := 198622076422403680721075

theorem tailTrace_435167 : CollatzResearch.WordTrace tailWord_435167 prefixEnd_435167 198622076422403680721075 := by
  unfold tailWord_435167
  simp only [CollatzResearch.WordTrace]
  refine ⟨15871844414471754451743755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10581229609647836301162503 15871844414471754451743755)
  ·
    refine ⟨23807766621707631677615633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15871844414471754451743755 23807766621707631677615633)
    ·
      refine ⟨17855824966280723758211725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23807766621707631677615633 17855824966280723758211725)
      ·
        refine ⟨6695934362355271409329397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17855824966280723758211725 6695934362355271409329397)
        ·
          refine ⟨627743846470806694624631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6695934362355271409329397 627743846470806694624631)
          ·
            refine ⟨941615769706210041936947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627743846470806694624631 941615769706210041936947)
            ·
              refine ⟨1412423654559315062905421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 941615769706210041936947 1412423654559315062905421)
              ·
                refine ⟨529658870459743148589533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1412423654559315062905421 529658870459743148589533)
                ·
                  refine ⟨198622076422403680721075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 529658870459743148589533 198622076422403680721075)
                  ·
                    rfl

theorem cell20_435167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 3].length) (baseStart_435167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435167 prefixEnd_435167 := by exact prefixLift 435167
  have htrace : WordTrace (prefixWord ++ tailWord_435167) baseStart_435167 baseEnd_435167 := by
    simpa [prefixWord, tailWord_435167, baseEnd_435167] using wordTrace_append hprefix tailTrace_435167
  have hstable : (prefixWord ++ tailWord_435167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435167).length < 2 ^ (prefixWord ++ tailWord_435167).sum := by decide
  have hdescent : baseEnd_435167 < baseStart_435167 := by decide
  rcases family_descends (prefixWord ++ tailWord_435167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435198 : List Nat := [4, 2, 2, 2, 3, 7]
def baseStart_435198 : Nat := 118140960795 + 435198 * 2 ^ 59
def prefixEnd_435198 : Nat := 4983230072969 + 3 ^ 40 * 435198 * 2
def baseEnd_435198 : Nat := 7356897246929827803245

theorem tailTrace_435198 : CollatzResearch.WordTrace tailWord_435198 prefixEnd_435198 7356897246929827803245 := by
  unfold tailWord_435198
  simp only [CollatzResearch.WordTrace]
  refine ⟨1984121884669930843265281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10581983384906297830748165 1984121884669930843265281)
  ·
    refine ⟨1488091413502448132448961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1984121884669930843265281 1488091413502448132448961)
    ·
      refine ⟨1116068560126836099336721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1488091413502448132448961 1116068560126836099336721)
      ·
        refine ⟨837051420095127074502541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1116068560126836099336721 837051420095127074502541)
        ·
          refine ⟨313894282535672652938453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 837051420095127074502541 313894282535672652938453)
          ·
            refine ⟨7356897246929827803245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 313894282535672652938453 7356897246929827803245)
            ·
              rfl

theorem cell20_435198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 7].length) (baseStart_435198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435198 prefixEnd_435198 := by exact prefixLift 435198
  have htrace : WordTrace (prefixWord ++ tailWord_435198) baseStart_435198 baseEnd_435198 := by
    simpa [prefixWord, tailWord_435198, baseEnd_435198] using wordTrace_append hprefix tailTrace_435198
  have hstable : (prefixWord ++ tailWord_435198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435198).length < 2 ^ (prefixWord ++ tailWord_435198).sum := by decide
  have hdescent : baseEnd_435198 < baseStart_435198 := by decide
  rcases family_descends (prefixWord ++ tailWord_435198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435208 : List Nat := [2, 1, 3, 2, 1, 5, 2, 2, 2]
def baseStart_435208 : Nat := 118140960795 + 435208 * 2 ^ 59
def prefixEnd_435208 : Nat := 4983230072969 + 3 ^ 40 * 435208 * 2
def baseEnd_435208 : Nat := 198640789939589760354241

theorem tailTrace_435208 : CollatzResearch.WordTrace tailWord_435208 prefixEnd_435208 198640789939589760354241 := by
  unfold tailWord_435208
  simp only [CollatzResearch.WordTrace]
  refine ⟨7936669903661609226993139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10582226538215478969324185 7936669903661609226993139)
  ·
    refine ⟨11905004855492413840489709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7936669903661609226993139 11905004855492413840489709)
    ·
      refine ⟨4464376820809655190183641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11905004855492413840489709 4464376820809655190183641)
      ·
        refine ⟨3348282615607241392637731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4464376820809655190183641 3348282615607241392637731)
        ·
          refine ⟨5022423923410862088956597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3348282615607241392637731 5022423923410862088956597)
          ·
            refine ⟨470852242819768320839681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5022423923410862088956597 470852242819768320839681)
            ·
              refine ⟨353139182114826240629761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 470852242819768320839681 353139182114826240629761)
              ·
                refine ⟨264854386586119680472321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 353139182114826240629761 264854386586119680472321)
                ·
                  refine ⟨198640789939589760354241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264854386586119680472321 198640789939589760354241)
                  ·
                    rfl

theorem cell20_435208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 2, 2].length) (baseStart_435208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435208 prefixEnd_435208 := by exact prefixLift 435208
  have htrace : WordTrace (prefixWord ++ tailWord_435208) baseStart_435208 baseEnd_435208 := by
    simpa [prefixWord, tailWord_435208, baseEnd_435208] using wordTrace_append hprefix tailTrace_435208
  have hstable : (prefixWord ++ tailWord_435208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435208).length < 2 ^ (prefixWord ++ tailWord_435208).sum := by decide
  have hdescent : baseEnd_435208 < baseStart_435208 := by decide
  rcases family_descends (prefixWord ++ tailWord_435208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435209 : List Nat := [1, 2, 1, 1, 3, 1, 1, 5, 5]
def baseStart_435209 : Nat := 118140960795 + 435209 * 2 ^ 59
def prefixEnd_435209 : Nat := 4983230072969 + 3 ^ 40 * 435209 * 2
def baseEnd_435209 : Nat := 198641246366838201320903

theorem tailTrace_435209 : CollatzResearch.WordTrace tailWord_435209 prefixEnd_435209 198641246366838201320903 := by
  unfold tailWord_435209
  simp only [CollatzResearch.WordTrace]
  refine ⟨15873376280319595624772681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10582250853546397083181787 15873376280319595624772681)
  ·
    refine ⟨11905032210239696718579511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15873376280319595624772681 11905032210239696718579511)
    ·
      refine ⟨17857548315359545077869267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11905032210239696718579511 17857548315359545077869267)
      ·
        refine ⟨26786322473039317616803901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17857548315359545077869267 26786322473039317616803901)
        ·
          refine ⟨10044870927389744106301463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26786322473039317616803901 10044870927389744106301463)
          ·
            refine ⟨15067306391084616159452195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10044870927389744106301463 15067306391084616159452195)
            ·
              refine ⟨22600959586626924239178293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15067306391084616159452195 22600959586626924239178293)
              ·
                refine ⟨2118839961246274147422965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22600959586626924239178293 2118839961246274147422965)
                ·
                  refine ⟨198641246366838201320903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2118839961246274147422965 198641246366838201320903)
                  ·
                    rfl

theorem cell20_435209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_435209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435209 prefixEnd_435209 := by exact prefixLift 435209
  have htrace : WordTrace (prefixWord ++ tailWord_435209) baseStart_435209 baseEnd_435209 := by
    simpa [prefixWord, tailWord_435209, baseEnd_435209] using wordTrace_append hprefix tailTrace_435209
  have hstable : (prefixWord ++ tailWord_435209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435209).length < 2 ^ (prefixWord ++ tailWord_435209).sum := by decide
  have hdescent : baseEnd_435209 < baseStart_435209 := by decide
  rcases family_descends (prefixWord ++ tailWord_435209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435226 : List Nat := [3, 1, 1, 3, 1, 2, 1, 5, 3]
def baseStart_435226 : Nat := 118140960795 + 435226 * 2 ^ 59
def prefixEnd_435226 : Nat := 4983230072969 + 3 ^ 40 * 435226 * 2
def baseEnd_435226 : Nat := 198649005630061697754167

theorem tailTrace_435226 : CollatzResearch.WordTrace tailWord_435226 prefixEnd_435226 198649005630061697754167 := by
  unfold tailWord_435226
  simp only [CollatzResearch.WordTrace]
  refine ⟨3968499080314501882035383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10582664214172005018761021 3968499080314501882035383)
  ·
    refine ⟨5952748620471752823053075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3968499080314501882035383 5952748620471752823053075)
    ·
      refine ⟨8929122930707629234579613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5952748620471752823053075 8929122930707629234579613)
      ·
        refine ⟨3348421099015360962967355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8929122930707629234579613 3348421099015360962967355)
        ·
          refine ⟨5022631648523041444451033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3348421099015360962967355 5022631648523041444451033)
          ·
            refine ⟨3766973736392281083338275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5022631648523041444451033 3766973736392281083338275)
            ·
              refine ⟨5650460604588421625007413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3766973736392281083338275 5650460604588421625007413)
              ·
                refine ⟨529730681680164527344445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5650460604588421625007413 529730681680164527344445)
                ·
                  refine ⟨198649005630061697754167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 529730681680164527344445 198649005630061697754167)
                  ·
                    rfl

theorem cell20_435226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_435226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435226 prefixEnd_435226 := by exact prefixLift 435226
  have htrace : WordTrace (prefixWord ++ tailWord_435226) baseStart_435226 baseEnd_435226 := by
    simpa [prefixWord, tailWord_435226, baseEnd_435226] using wordTrace_append hprefix tailTrace_435226
  have hstable : (prefixWord ++ tailWord_435226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435226).length < 2 ^ (prefixWord ++ tailWord_435226).sum := by decide
  have hdescent : baseEnd_435226 < baseStart_435226 := by decide
  rcases family_descends (prefixWord ++ tailWord_435226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435233 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 6]
def baseStart_435233 : Nat := 118140960795 + 435233 * 2 ^ 59
def prefixEnd_435233 : Nat := 4983230072969 + 3 ^ 40 * 435233 * 2
def baseEnd_435233 : Nat := 198652200620800784520805

theorem tailTrace_435233 : CollatzResearch.WordTrace tailWord_435233 prefixEnd_435233 198652200620800784520805 := by
  unfold tailWord_435233
  simp only [CollatzResearch.WordTrace]
  refine ⟨15874251632232647723646353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10582834421488431815764235 15874251632232647723646353)
  ·
    refine ⟨11905688724174485792734765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15874251632232647723646353 11905688724174485792734765)
    ·
      refine ⟨4464633271565432172275537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11905688724174485792734765 4464633271565432172275537)
      ·
        refine ⟨3348474953674074129206653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4464633271565432172275537 3348474953674074129206653)
        ·
          refine ⟨1255678107627777798452495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3348474953674074129206653 1255678107627777798452495)
          ·
            refine ⟨1883517161441666697678743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1255678107627777798452495 1883517161441666697678743)
            ·
              refine ⟨2825275742162500046518115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1883517161441666697678743 2825275742162500046518115)
              ·
                refine ⟨4237913613243750069777173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2825275742162500046518115 4237913613243750069777173)
                ·
                  refine ⟨198652200620800784520805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4237913613243750069777173 198652200620800784520805)
                  ·
                    rfl

theorem cell20_435233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_435233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435233 prefixEnd_435233 := by exact prefixLift 435233
  have htrace : WordTrace (prefixWord ++ tailWord_435233) baseStart_435233 baseEnd_435233 := by
    simpa [prefixWord, tailWord_435233, baseEnd_435233] using wordTrace_append hprefix tailTrace_435233
  have hstable : (prefixWord ++ tailWord_435233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435233).length < 2 ^ (prefixWord ++ tailWord_435233).sum := by decide
  have hdescent : baseEnd_435233 < baseStart_435233 := by decide
  rcases family_descends (prefixWord ++ tailWord_435233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435236 : List Nat := [2, 3, 1, 4, 1, 2, 3, 4]
def baseStart_435236 : Nat := 118140960795 + 435236 * 2 ^ 59
def prefixEnd_435236 : Nat := 4983230072969 + 3 ^ 40 * 435236 * 2
def baseEnd_435236 : Nat := 66217856634182035806931

theorem tailTrace_435236 : CollatzResearch.WordTrace tailWord_435236 prefixEnd_435236 66217856634182035806931 := by
  unfold tailWord_435236
  simp only [CollatzResearch.WordTrace]
  refine ⟨7937180525610889618002781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10582907367481186157337041 7937180525610889618002781)
  ·
    refine ⟨2976442697104083606751043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7937180525610889618002781 2976442697104083606751043)
    ·
      refine ⟨4464664045656125410126565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2976442697104083606751043 4464664045656125410126565)
      ·
        refine ⟨837124508560523514398731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4464664045656125410126565 837124508560523514398731)
        ·
          refine ⟨1255686762840785271598097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 837124508560523514398731 1255686762840785271598097)
          ·
            refine ⟨941765072130588953698573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1255686762840785271598097 941765072130588953698573)
            ·
              refine ⟨353161902048970857636965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 941765072130588953698573 353161902048970857636965)
              ·
                refine ⟨66217856634182035806931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 353161902048970857636965 66217856634182035806931)
                ·
                  rfl

theorem cell20_435236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 4].length) (baseStart_435236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435236 prefixEnd_435236 := by exact prefixLift 435236
  have htrace : WordTrace (prefixWord ++ tailWord_435236) baseStart_435236 baseEnd_435236 := by
    simpa [prefixWord, tailWord_435236, baseEnd_435236] using wordTrace_append hprefix tailTrace_435236
  have hstable : (prefixWord ++ tailWord_435236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435236).length < 2 ^ (prefixWord ++ tailWord_435236).sum := by decide
  have hdescent : baseEnd_435236 < baseStart_435236 := by decide
  rcases family_descends (prefixWord ++ tailWord_435236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435271 : List Nat := [1, 1, 4, 1, 3, 2, 1, 3, 4]
def baseStart_435271 : Nat := 118140960795 + 435271 * 2 ^ 59
def prefixEnd_435271 : Nat := 4983230072969 + 3 ^ 40 * 435271 * 2
def baseEnd_435271 : Nat := 198669544856241541253983

theorem tailTrace_435271 : CollatzResearch.WordTrace tailWord_435271 prefixEnd_435271 198669544856241541253983 := by
  unfold tailWord_435271
  simp only [CollatzResearch.WordTrace]
  refine ⟨15875637606094980213529667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10583758404063320142353111 15875637606094980213529667)
  ·
    refine ⟨23813456409142470320294501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15875637606094980213529667 23813456409142470320294501)
    ·
      refine ⟨4465023076714213185055219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23813456409142470320294501 4465023076714213185055219)
      ·
        refine ⟨6697534615071319777582829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4465023076714213185055219 6697534615071319777582829)
        ·
          refine ⟨2511575480651744916593561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6697534615071319777582829 2511575480651744916593561)
          ·
            refine ⟨1883681610488808687445171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2511575480651744916593561 1883681610488808687445171)
            ·
              refine ⟨2825522415733213031167757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1883681610488808687445171 2825522415733213031167757)
              ·
                refine ⟨1059570905899954886687909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2825522415733213031167757 1059570905899954886687909)
                ·
                  refine ⟨198669544856241541253983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1059570905899954886687909 198669544856241541253983)
                  ·
                    rfl

theorem cell20_435271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 4].length) (baseStart_435271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435271 prefixEnd_435271 := by exact prefixLift 435271
  have htrace : WordTrace (prefixWord ++ tailWord_435271) baseStart_435271 baseEnd_435271 := by
    simpa [prefixWord, tailWord_435271, baseEnd_435271] using wordTrace_append hprefix tailTrace_435271
  have hstable : (prefixWord ++ tailWord_435271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435271).length < 2 ^ (prefixWord ++ tailWord_435271).sum := by decide
  have hdescent : baseEnd_435271 < baseStart_435271 := by decide
  rcases family_descends (prefixWord ++ tailWord_435271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435278 : List Nat := [4, 1, 1, 1, 1, 3, 2, 7]
def baseStart_435278 : Nat := 118140960795 + 435278 * 2 ^ 59
def prefixEnd_435278 : Nat := 4983230072969 + 3 ^ 40 * 435278 * 2
def baseEnd_435278 : Nat := 66224246615660209340207

theorem tailTrace_435278 : CollatzResearch.WordTrace tailWord_435278 prefixEnd_435278 66224246615660209340207 := by
  unfold tailWord_435278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1984486614633702551129311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10583928611379746939356325 1984486614633702551129311)
  ·
    refine ⟨2976729921950553826693967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1984486614633702551129311 2976729921950553826693967)
    ·
      refine ⟨4465094882925830740040951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2976729921950553826693967 4465094882925830740040951)
      ·
        refine ⟨6697642324388746110061427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4465094882925830740040951 6697642324388746110061427)
        ·
          refine ⟨10046463486583119165092141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6697642324388746110061427 10046463486583119165092141)
          ·
            refine ⟨3767423807468669686909553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10046463486583119165092141 3767423807468669686909553)
            ·
              refine ⟨2825567855601502265182165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3767423807468669686909553 2825567855601502265182165)
              ·
                refine ⟨66224246615660209340207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2825567855601502265182165 66224246615660209340207)
                ·
                  rfl

theorem cell20_435278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_435278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435278 prefixEnd_435278 := by exact prefixLift 435278
  have htrace : WordTrace (prefixWord ++ tailWord_435278) baseStart_435278 baseEnd_435278 := by
    simpa [prefixWord, tailWord_435278, baseEnd_435278] using wordTrace_append hprefix tailTrace_435278
  have hstable : (prefixWord ++ tailWord_435278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435278).length < 2 ^ (prefixWord ++ tailWord_435278).sum := by decide
  have hdescent : baseEnd_435278 < baseStart_435278 := by decide
  rcases family_descends (prefixWord ++ tailWord_435278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435305 : List Nat := [1, 2, 1, 1, 1, 8, 1, 3, 2]
def baseStart_435305 : Nat := 118140960795 + 435305 * 2 ^ 59
def prefixEnd_435305 : Nat := 4983230072969 + 3 ^ 40 * 435305 * 2
def baseEnd_435305 : Nat := 198685063382688534120511

theorem tailTrace_435305 : CollatzResearch.WordTrace tailWord_435305 prefixEnd_435305 198685063382688534120511 := by
  unfold tailWord_435305
  simp only [CollatzResearch.WordTrace]
  refine ⟨15876877687971804020267369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10584585125314536013511579 15876877687971804020267369)
  ·
    refine ⟨11907658265978853015200527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15876877687971804020267369 11907658265978853015200527)
    ·
      refine ⟨17861487398968279522800791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11907658265978853015200527 17861487398968279522800791)
      ·
        refine ⟨26792231098452419284201187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17861487398968279522800791 26792231098452419284201187)
        ·
          refine ⟨40188346647678628926301781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26792231098452419284201187 40188346647678628926301781)
          ·
            refine ⟨470957187277483932730099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 40188346647678628926301781 470957187277483932730099)
            ·
              refine ⟨706435780916225899095149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470957187277483932730099 706435780916225899095149)
              ·
                refine ⟨264913417843584712160681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 706435780916225899095149 264913417843584712160681)
                ·
                  refine ⟨198685063382688534120511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264913417843584712160681 198685063382688534120511)
                  ·
                    rfl

theorem cell20_435305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 3, 2].length) (baseStart_435305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435305 prefixEnd_435305 := by exact prefixLift 435305
  have htrace : WordTrace (prefixWord ++ tailWord_435305) baseStart_435305 baseEnd_435305 := by
    simpa [prefixWord, tailWord_435305, baseEnd_435305] using wordTrace_append hprefix tailTrace_435305
  have hstable : (prefixWord ++ tailWord_435305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435305).length < 2 ^ (prefixWord ++ tailWord_435305).sum := by decide
  have hdescent : baseEnd_435305 < baseStart_435305 := by decide
  rcases family_descends (prefixWord ++ tailWord_435305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435333 : List Nat := [1, 3, 1, 1, 6, 1, 2, 5]
def baseStart_435333 : Nat := 118140960795 + 435333 * 2 ^ 59
def prefixEnd_435333 : Nat := 4983230072969 + 3 ^ 40 * 435333 * 2
def baseEnd_435333 : Nat := 66232614448548293729021

theorem tailTrace_435333 : CollatzResearch.WordTrace tailWord_435333 prefixEnd_435333 66232614448548293729021 := by
  unfold tailWord_435333
  simp only [CollatzResearch.WordTrace]
  refine ⟨15877898931870364802286653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10585265954580243201524435 15877898931870364802286653)
  ·
    refine ⟨5954212099451386800857495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15877898931870364802286653 5954212099451386800857495)
    ·
      refine ⟨8931318149177080201286243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5954212099451386800857495 8931318149177080201286243)
      ·
        refine ⟨13396977223765620301929365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8931318149177080201286243 13396977223765620301929365)
        ·
          refine ⟨627983307364013451652939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13396977223765620301929365 627983307364013451652939)
          ·
            refine ⟨941974961046020177479409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627983307364013451652939 941974961046020177479409)
            ·
              refine ⟨706481220784515133109557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 941974961046020177479409 706481220784515133109557)
              ·
                refine ⟨66232614448548293729021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 706481220784515133109557 66232614448548293729021)
                ·
                  rfl

theorem cell20_435333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 5].length) (baseStart_435333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435333 prefixEnd_435333 := by exact prefixLift 435333
  have htrace : WordTrace (prefixWord ++ tailWord_435333) baseStart_435333 baseEnd_435333 := by
    simpa [prefixWord, tailWord_435333, baseEnd_435333] using wordTrace_append hprefix tailTrace_435333
  have hstable : (prefixWord ++ tailWord_435333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435333).length < 2 ^ (prefixWord ++ tailWord_435333).sum := by decide
  have hdescent : baseEnd_435333 < baseStart_435333 := by decide
  rcases family_descends (prefixWord ++ tailWord_435333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435378 : List Nat := [3, 2, 1, 1, 1, 4, 1, 4, 3]
def baseStart_435378 : Nat := 118140960795 + 435378 * 2 ^ 59
def prefixEnd_435378 : Nat := 4983230072969 + 3 ^ 40 * 435378 * 2
def baseEnd_435378 : Nat := 198718382571824724686879

theorem tailTrace_435378 : CollatzResearch.WordTrace tailWord_435378 prefixEnd_435378 198718382571824724686879 := by
  unfold tailWord_435378
  simp only [CollatzResearch.WordTrace]
  refine ⟨3969885054176834371918697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10586360144471558325116525 3969885054176834371918697)
  ·
    refine ⟨2977413790632625778939023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3969885054176834371918697 2977413790632625778939023)
    ·
      refine ⟨4466120685948938668408535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2977413790632625778939023 4466120685948938668408535)
      ·
        refine ⟨6699181028923408002612803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4466120685948938668408535 6699181028923408002612803)
        ·
          refine ⟨10048771543385112003919205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6699181028923408002612803 10048771543385112003919205)
          ·
            refine ⟨1884144664384708500734851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10048771543385112003919205 1884144664384708500734851)
            ·
              refine ⟨2826216996577062751102277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1884144664384708500734851 2826216996577062751102277)
              ·
                refine ⟨529915686858199265831677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2826216996577062751102277 529915686858199265831677)
                ·
                  refine ⟨198718382571824724686879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 529915686858199265831677 198718382571824724686879)
                  ·
                    rfl

theorem cell20_435378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_435378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435378 prefixEnd_435378 := by exact prefixLift 435378
  have htrace : WordTrace (prefixWord ++ tailWord_435378) baseStart_435378 baseEnd_435378 := by
    simpa [prefixWord, tailWord_435378, baseEnd_435378] using wordTrace_append hprefix tailTrace_435378
  have hstable : (prefixWord ++ tailWord_435378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435378).length < 2 ^ (prefixWord ++ tailWord_435378).sum := by decide
  have hdescent : baseEnd_435378 < baseStart_435378 := by decide
  rcases family_descends (prefixWord ++ tailWord_435378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435464 : List Nat := [2, 1, 3, 2, 4, 2, 2, 4]
def baseStart_435464 : Nat := 118140960795 + 435464 * 2 ^ 59
def prefixEnd_435464 : Nat := 4983230072969 + 3 ^ 40 * 435464 * 2
def baseEnd_435464 : Nat := 66252545105063549273287

theorem tailTrace_435464 : CollatzResearch.WordTrace tailWord_435464 prefixEnd_435464 66252545105063549273287 := by
  unfold tailWord_435464
  simp only [CollatzResearch.WordTrace]
  refine ⟨7941338447197887087652723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10588451262930516116870297 7941338447197887087652723)
  ·
    refine ⟨11912007670796830631479085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7941338447197887087652723 11912007670796830631479085)
    ·
      refine ⟨4467002876548811486804657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11912007670796830631479085 4467002876548811486804657)
      ·
        refine ⟨3350252157411608615103493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4467002876548811486804657 3350252157411608615103493)
        ·
          refine ⟨628172279514676615331905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3350252157411608615103493 628172279514676615331905)
          ·
            refine ⟨471129209636007461498929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 628172279514676615331905 471129209636007461498929)
            ·
              refine ⟨353346907227005596124197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 471129209636007461498929 353346907227005596124197)
              ·
                refine ⟨66252545105063549273287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 353346907227005596124197 66252545105063549273287)
                ·
                  rfl

theorem cell20_435464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 4].length) (baseStart_435464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435464 prefixEnd_435464 := by exact prefixLift 435464
  have htrace : WordTrace (prefixWord ++ tailWord_435464) baseStart_435464 baseEnd_435464 := by
    simpa [prefixWord, tailWord_435464, baseEnd_435464] using wordTrace_append hprefix tailTrace_435464
  have hstable : (prefixWord ++ tailWord_435464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435464).length < 2 ^ (prefixWord ++ tailWord_435464).sum := by decide
  have hdescent : baseEnd_435464 < baseStart_435464 := by decide
  rcases family_descends (prefixWord ++ tailWord_435464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435468 : List Nat := [2, 2, 1, 2, 2, 4, 1, 6]
def baseStart_435468 : Nat := 118140960795 + 435468 * 2 ^ 59
def prefixEnd_435468 : Nat := 4983230072969 + 3 ^ 40 * 435468 * 2
def baseEnd_435468 : Nat := 66253153674728137228837

theorem tailTrace_435468 : CollatzResearch.WordTrace tailWord_435468 prefixEnd_435468 66253153674728137228837 := by
  unfold tailWord_435468
  simp only [CollatzResearch.WordTrace]
  refine ⟨7941411393190641429225529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10588548524254188572300705 7941411393190641429225529)
  ·
    refine ⟨5956058544892981071919147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7941411393190641429225529 5956058544892981071919147)
    ·
      refine ⟨8934087817339471607878721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5956058544892981071919147 8934087817339471607878721)
      ·
        refine ⟨6700565863004603705909041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8934087817339471607878721 6700565863004603705909041)
        ·
          refine ⟨5025424397253452779431781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6700565863004603705909041 5025424397253452779431781)
          ·
            refine ⟨942267074485022396143459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5025424397253452779431781 942267074485022396143459)
            ·
              refine ⟨1413400611727533594215189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 942267074485022396143459 1413400611727533594215189)
              ·
                refine ⟨66253153674728137228837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1413400611727533594215189 66253153674728137228837)
                ·
                  rfl

theorem cell20_435468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 6].length) (baseStart_435468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435468 prefixEnd_435468 := by exact prefixLift 435468
  have htrace : WordTrace (prefixWord ++ tailWord_435468) baseStart_435468 baseEnd_435468 := by
    simpa [prefixWord, tailWord_435468, baseEnd_435468] using wordTrace_append hprefix tailTrace_435468
  have hstable : (prefixWord ++ tailWord_435468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435468).length < 2 ^ (prefixWord ++ tailWord_435468).sum := by decide
  have hdescent : baseEnd_435468 < baseStart_435468 := by decide
  rcases family_descends (prefixWord ++ tailWord_435468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435485 : List Nat := [1, 4, 2, 3, 1, 3, 6]
def baseStart_435485 : Nat := 118140960795 + 435485 * 2 ^ 59
def prefixEnd_435485 : Nat := 4983230072969 + 3 ^ 40 * 435485 * 2
def baseEnd_435485 : Nat := 22085246698600878679975

theorem tailTrace_435485 : CollatzResearch.WordTrace tailWord_435485 prefixEnd_435485 22085246698600878679975 := by
  unfold tailWord_435485
  simp only [CollatzResearch.WordTrace]
  refine ⟨15883442827319694761819909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10588961884879796507879939 15883442827319694761819909)
  ·
    refine ⟨2978145530122442767841233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15883442827319694761819909 2978145530122442767841233)
    ·
      refine ⟨2233609147591832075880925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2978145530122442767841233 2233609147591832075880925)
      ·
        refine ⟨837603430346937028455347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2233609147591832075880925 837603430346937028455347)
        ·
          refine ⟨1256405145520405542683021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 837603430346937028455347 1256405145520405542683021)
          ·
            refine ⟨471151929570152078506133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1256405145520405542683021 471151929570152078506133)
            ·
              refine ⟨22085246698600878679975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 471151929570152078506133 22085246698600878679975)
              ·
                rfl

theorem cell20_435485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 6].length) (baseStart_435485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435485 prefixEnd_435485 := by exact prefixLift 435485
  have htrace : WordTrace (prefixWord ++ tailWord_435485) baseStart_435485 baseEnd_435485 := by
    simpa [prefixWord, tailWord_435485, baseEnd_435485] using wordTrace_append hprefix tailTrace_435485
  have hstable : (prefixWord ++ tailWord_435485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435485).length < 2 ^ (prefixWord ++ tailWord_435485).sum := by decide
  have hdescent : baseEnd_435485 < baseStart_435485 := by decide
  rcases family_descends (prefixWord ++ tailWord_435485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435492 : List Nat := [2, 3, 1, 3, 1, 1, 2, 4, 3]
def baseStart_435492 : Nat := 118140960795 + 435492 * 2 ^ 59
def prefixEnd_435492 : Nat := 4983230072969 + 3 ^ 40 * 435492 * 2
def baseEnd_435492 : Nat := 198770415278146994886413

theorem tailTrace_435492 : CollatzResearch.WordTrace tailWord_435492 prefixEnd_435492 198770415278146994886413 := by
  unfold tailWord_435492
  simp only [CollatzResearch.WordTrace]
  refine ⟨7941849069147167478662365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10589132092196223304883153 7941849069147167478662365)
  ·
    refine ⟨2978193400930187804498387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7941849069147167478662365 2978193400930187804498387)
    ·
      refine ⟨4467290101395281706747581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2978193400930187804498387 4467290101395281706747581)
      ·
        refine ⟨1675233788023230640030343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4467290101395281706747581 1675233788023230640030343)
        ·
          refine ⟨2512850682034845960045515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1675233788023230640030343 2512850682034845960045515)
          ·
            refine ⟨3769276023052268940068273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2512850682034845960045515 3769276023052268940068273)
            ·
              refine ⟨2826957017289201705051205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3769276023052268940068273 2826957017289201705051205)
              ·
                refine ⟨530054440741725319697101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2826957017289201705051205 530054440741725319697101)
                ·
                  refine ⟨198770415278146994886413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 530054440741725319697101 198770415278146994886413)
                  ·
                    rfl

theorem cell20_435492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_435492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435492 prefixEnd_435492 := by exact prefixLift 435492
  have htrace : WordTrace (prefixWord ++ tailWord_435492) baseStart_435492 baseEnd_435492 := by
    simpa [prefixWord, tailWord_435492, baseEnd_435492] using wordTrace_append hprefix tailTrace_435492
  have hstable : (prefixWord ++ tailWord_435492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435492).length < 2 ^ (prefixWord ++ tailWord_435492).sum := by decide
  have hdescent : baseEnd_435492 < baseStart_435492 := by decide
  rcases family_descends (prefixWord ++ tailWord_435492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435506 : List Nat := [3, 2, 1, 1, 4, 1, 1, 7]
def baseStart_435506 : Nat := 118140960795 + 435506 * 2 ^ 59
def prefixEnd_435506 : Nat := 4983230072969 + 3 ^ 40 * 435506 * 2
def baseEnd_435506 : Nat := 66258935086541722806563

theorem tailTrace_435506 : CollatzResearch.WordTrace tailWord_435506 prefixEnd_435506 66258935086541722806563 := by
  unfold tailWord_435506
  simp only [CollatzResearch.WordTrace]
  refine ⟨3971052190060903837083593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10589472506829076898889581 3971052190060903837083593)
  ·
    refine ⟨2978289142545677877812695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3971052190060903837083593 2978289142545677877812695)
    ·
      refine ⟨4467433713818516816719043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2978289142545677877812695 4467433713818516816719043)
      ·
        refine ⟨6701150570727775225078565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4467433713818516816719043 6701150570727775225078565)
        ·
          refine ⟨1256465732011457854702231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6701150570727775225078565 1256465732011457854702231)
          ·
            refine ⟨1884698598017186782053347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1256465732011457854702231 1884698598017186782053347)
            ·
              refine ⟨2827047897025780173080021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1884698598017186782053347 2827047897025780173080021)
              ·
                refine ⟨66258935086541722806563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2827047897025780173080021 66258935086541722806563)
                ·
                  rfl

theorem cell20_435506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_435506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435506 prefixEnd_435506 := by exact prefixLift 435506
  have htrace : WordTrace (prefixWord ++ tailWord_435506) baseStart_435506 baseEnd_435506 := by
    simpa [prefixWord, tailWord_435506, baseEnd_435506] using wordTrace_append hprefix tailTrace_435506
  have hstable : (prefixWord ++ tailWord_435506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435506).length < 2 ^ (prefixWord ++ tailWord_435506).sum := by decide
  have hdescent : baseEnd_435506 < baseStart_435506 := by decide
  rcases family_descends (prefixWord ++ tailWord_435506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435509 : List Nat := [1, 3, 3, 1, 2, 2, 4, 1, 3]
def baseStart_435509 : Nat := 118140960795 + 435509 * 2 ^ 59
def prefixEnd_435509 : Nat := 4983230072969 + 3 ^ 40 * 435509 * 2
def baseEnd_435509 : Nat := 198778174541370491319677

theorem tailTrace_435509 : CollatzResearch.WordTrace tailWord_435509 prefixEnd_435509 198778174541370491319677 := by
  unfold tailWord_435509
  simp only [CollatzResearch.WordTrace]
  refine ⟨15884318179232746860693581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10589545452821831240462387 15884318179232746860693581)
  ·
    refine ⟨5956619317212280072760093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15884318179232746860693581 5956619317212280072760093)
    ·
      refine ⟨2233732243954605027285035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5956619317212280072760093 2233732243954605027285035)
      ·
        refine ⟨3350598365931907540927553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2233732243954605027285035 3350598365931907540927553)
        ·
          refine ⟨2512948774448930655695665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3350598365931907540927553 2512948774448930655695665)
          ·
            refine ⟨1884711580836697991771749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2512948774448930655695665 1884711580836697991771749)
            ·
              refine ⟨353383421406880873457203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1884711580836697991771749 353383421406880873457203)
              ·
                refine ⟨530075132110321310185805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353383421406880873457203 530075132110321310185805)
                ·
                  refine ⟨198778174541370491319677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 530075132110321310185805 198778174541370491319677)
                  ·
                    rfl

theorem cell20_435509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 1, 3].length) (baseStart_435509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435509 prefixEnd_435509 := by exact prefixLift 435509
  have htrace : WordTrace (prefixWord ++ tailWord_435509) baseStart_435509 baseEnd_435509 := by
    simpa [prefixWord, tailWord_435509, baseEnd_435509] using wordTrace_append hprefix tailTrace_435509
  have hstable : (prefixWord ++ tailWord_435509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435509).length < 2 ^ (prefixWord ++ tailWord_435509).sum := by decide
  have hdescent : baseEnd_435509 < baseStart_435509 := by decide
  rcases family_descends (prefixWord ++ tailWord_435509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435520 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 6]
def baseStart_435520 : Nat := 118140960795 + 435520 * 2 ^ 59
def prefixEnd_435520 : Nat := 4983230072969 + 3 ^ 40 * 435520 * 2
def baseEnd_435520 : Nat := 198783195241103341952965

theorem tailTrace_435520 : CollatzResearch.WordTrace tailWord_435520 prefixEnd_435520 198783195241103341952965 := by
  unfold tailWord_435520
  simp only [CollatzResearch.WordTrace]
  refine ⟨7942359691096447869672007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10589812921461930492896009 7942359691096447869672007)
  ·
    refine ⟨11913539536644671804508011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7942359691096447869672007 11913539536644671804508011)
    ·
      refine ⟨17870309304967007706762017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11913539536644671804508011 17870309304967007706762017)
      ·
        refine ⟨13402731978725255780071513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17870309304967007706762017 13402731978725255780071513)
        ·
          refine ⟨10052048984043941835053635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13402731978725255780071513 10052048984043941835053635)
          ·
            refine ⟨15078073476065912752580453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10052048984043941835053635 15078073476065912752580453)
            ·
              refine ⟨2827138776762358641108835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15078073476065912752580453 2827138776762358641108835)
              ·
                refine ⟨4240708165143537961663253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2827138776762358641108835 4240708165143537961663253)
                ·
                  refine ⟨198783195241103341952965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4240708165143537961663253 198783195241103341952965)
                  ·
                    rfl

theorem cell20_435520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_435520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435520 prefixEnd_435520 := by exact prefixLift 435520
  have htrace : WordTrace (prefixWord ++ tailWord_435520) baseStart_435520 baseEnd_435520 := by
    simpa [prefixWord, tailWord_435520, baseEnd_435520] using wordTrace_append hprefix tailTrace_435520
  have hstable : (prefixWord ++ tailWord_435520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435520).length < 2 ^ (prefixWord ++ tailWord_435520).sum := by decide
  have hdescent : baseEnd_435520 < baseStart_435520 := by decide
  rcases family_descends (prefixWord ++ tailWord_435520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435542 : List Nat := [5, 2, 3, 1, 2, 1, 2, 2, 2]
def baseStart_435542 : Nat := 118140960795 + 435542 * 2 ^ 59
def prefixEnd_435542 : Nat := 4983230072969 + 3 ^ 40 * 435542 * 2
def baseEnd_435542 : Nat := 198793236640569043219543

theorem tailTrace_435542 : CollatzResearch.WordTrace tailWord_435542 prefixEnd_435542 198793236640569043219543 := by
  unfold tailWord_435542
  simp only [CollatzResearch.WordTrace]
  refine ⟨992845111757074593540305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10590347858742128997763253 992845111757074593540305)
  ·
    refine ⟨744633833817805945155229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 992845111757074593540305 744633833817805945155229)
    ·
      refine ⟨279237687681677229433211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 744633833817805945155229 279237687681677229433211)
      ·
        refine ⟨418856531522515844149817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279237687681677229433211 418856531522515844149817)
        ·
          refine ⟨314142398641886883112363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418856531522515844149817 314142398641886883112363)
          ·
            refine ⟨471213597962830324668545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314142398641886883112363 471213597962830324668545)
            ·
              refine ⟨353410198472122743501409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 471213597962830324668545 353410198472122743501409)
              ·
                refine ⟨265057648854092057626057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 353410198472122743501409 265057648854092057626057)
                ·
                  refine ⟨198793236640569043219543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 265057648854092057626057 198793236640569043219543)
                  ·
                    rfl

theorem cell20_435542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_435542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435542 prefixEnd_435542 := by exact prefixLift 435542
  have htrace : WordTrace (prefixWord ++ tailWord_435542) baseStart_435542 baseEnd_435542 := by
    simpa [prefixWord, tailWord_435542, baseEnd_435542] using wordTrace_append hprefix tailTrace_435542
  have hstable : (prefixWord ++ tailWord_435542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435542).length < 2 ^ (prefixWord ++ tailWord_435542).sum := by decide
  have hdescent : baseEnd_435542 < baseStart_435542 := by decide
  rcases family_descends (prefixWord ++ tailWord_435542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435592 : List Nat := [2, 1, 3, 3, 1, 2, 1, 5, 2]
def baseStart_435592 : Nat := 118140960795 + 435592 * 2 ^ 59
def prefixEnd_435592 : Nat := 4983230072969 + 3 ^ 40 * 435592 * 2
def baseEnd_435592 : Nat := 198816058002991091552671

theorem tailTrace_435592 : CollatzResearch.WordTrace tailWord_435592 prefixEnd_435592 198816058002991091552671 := by
  unfold tailWord_435592
  simp only [CollatzResearch.WordTrace]
  refine ⟨7943672718966026017982515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10591563625288034690643353 7943672718966026017982515)
  ·
    refine ⟨11915509078449039026973773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7943672718966026017982515 11915509078449039026973773)
    ·
      refine ⟨4468315904418389635115165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11915509078449039026973773 4468315904418389635115165)
      ·
        refine ⟨1675618464156896113168187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4468315904418389635115165 1675618464156896113168187)
        ·
          refine ⟨2513427696235344169752281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1675618464156896113168187 2513427696235344169752281)
          ·
            refine ⟨1885070772176508127314211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2513427696235344169752281 1885070772176508127314211)
            ·
              refine ⟨2827606158264762190971317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1885070772176508127314211 2827606158264762190971317)
              ·
                refine ⟨265088077337321455403561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2827606158264762190971317 265088077337321455403561)
                ·
                  refine ⟨198816058002991091552671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 265088077337321455403561 198816058002991091552671)
                  ·
                    rfl

theorem cell20_435592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 5, 2].length) (baseStart_435592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435592 prefixEnd_435592 := by exact prefixLift 435592
  have htrace : WordTrace (prefixWord ++ tailWord_435592) baseStart_435592 baseEnd_435592 := by
    simpa [prefixWord, tailWord_435592, baseEnd_435592] using wordTrace_append hprefix tailTrace_435592
  have hstable : (prefixWord ++ tailWord_435592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435592).length < 2 ^ (prefixWord ++ tailWord_435592).sum := by decide
  have hdescent : baseEnd_435592 < baseStart_435592 := by decide
  rcases family_descends (prefixWord ++ tailWord_435592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435596 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 6]
def baseStart_435596 : Nat := 118140960795 + 435596 * 2 ^ 59
def prefixEnd_435596 : Nat := 4983230072969 + 3 ^ 40 * 435596 * 2
def baseEnd_435596 : Nat := 198817883711984855419321

theorem tailTrace_435596 : CollatzResearch.WordTrace tailWord_435596 prefixEnd_435596 198817883711984855419321 := by
  unfold tailWord_435596
  simp only [CollatzResearch.WordTrace]
  refine ⟨7943745664958780359555321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10591660886611707146073761 7943745664958780359555321)
  ·
    refine ⟨5957809248719085269666491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7943745664958780359555321 5957809248719085269666491)
    ·
      refine ⟨8936713873078627904499737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5957809248719085269666491 8936713873078627904499737)
      ·
        refine ⟨6702535404808970928374803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8936713873078627904499737 6702535404808970928374803)
        ·
          refine ⟨10053803107213456392562205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6702535404808970928374803 10053803107213456392562205)
          ·
            refine ⟨3770176165205046147210827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10053803107213456392562205 3770176165205046147210827)
            ·
              refine ⟨5655264247807569220816241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3770176165205046147210827 5655264247807569220816241)
              ·
                refine ⟨4241448185855676915612181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5655264247807569220816241 4241448185855676915612181)
                ·
                  refine ⟨198817883711984855419321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4241448185855676915612181 198817883711984855419321)
                  ·
                    rfl

theorem cell20_435596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_435596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435596 prefixEnd_435596 := by exact prefixLift 435596
  have htrace : WordTrace (prefixWord ++ tailWord_435596) baseStart_435596 baseEnd_435596 := by
    simpa [prefixWord, tailWord_435596, baseEnd_435596] using wordTrace_append hprefix tailTrace_435596
  have hstable : (prefixWord ++ tailWord_435596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435596).length < 2 ^ (prefixWord ++ tailWord_435596).sum := by decide
  have hdescent : baseEnd_435596 < baseStart_435596 := by decide
  rcases family_descends (prefixWord ++ tailWord_435596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435613 : List Nat := [1, 4, 2, 1, 3, 1, 1, 3, 4]
def baseStart_435613 : Nat := 118140960795 + 435613 * 2 ^ 59
def prefixEnd_435613 : Nat := 4983230072969 + 3 ^ 40 * 435613 * 2
def baseEnd_435613 : Nat := 198825642975208351852585

theorem tailTrace_435613 : CollatzResearch.WordTrace tailWord_435613 prefixEnd_435613 198825642975208351852585 := by
  unfold tailWord_435613
  simp only [CollatzResearch.WordTrace]
  refine ⟨15888111370855972622479493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10592074247237315081652995 15888111370855972622479493)
  ·
    refine ⟨2979020882035494866714905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15888111370855972622479493 2979020882035494866714905)
    ·
      refine ⟨2234265661526621150036179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2979020882035494866714905 2234265661526621150036179)
      ·
        refine ⟨3351398492289931725054269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2234265661526621150036179 3351398492289931725054269)
        ·
          refine ⟨1256774434608724396895351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3351398492289931725054269 1256774434608724396895351)
          ·
            refine ⟨1885161651913086595343027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1256774434608724396895351 1885161651913086595343027)
            ·
              refine ⟨2827742477869629893014541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1885161651913086595343027 2827742477869629893014541)
              ·
                refine ⟨1060403429201111209880453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2827742477869629893014541 1060403429201111209880453)
                ·
                  refine ⟨198825642975208351852585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1060403429201111209880453 198825642975208351852585)
                  ·
                    rfl

theorem cell20_435613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_435613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435613 prefixEnd_435613 := by exact prefixLift 435613
  have htrace : WordTrace (prefixWord ++ tailWord_435613) baseStart_435613 baseEnd_435613 := by
    simpa [prefixWord, tailWord_435613, baseEnd_435613] using wordTrace_append hprefix tailTrace_435613
  have hstable : (prefixWord ++ tailWord_435613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435613).length < 2 ^ (prefixWord ++ tailWord_435613).sum := by decide
  have hdescent : baseEnd_435613 < baseStart_435613 := by decide
  rcases family_descends (prefixWord ++ tailWord_435613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435623 : List Nat := [1, 1, 6, 1, 1, 1, 5, 1, 3]
def baseStart_435623 : Nat := 118140960795 + 435623 * 2 ^ 59
def prefixEnd_435623 : Nat := 4983230072969 + 3 ^ 40 * 435623 * 2
def baseEnd_435623 : Nat := 198830207247692761519211

theorem tailTrace_435623 : CollatzResearch.WordTrace tailWord_435623 prefixEnd_435623 198830207247692761519211 := by
  unfold tailWord_435623
  simp only [CollatzResearch.WordTrace]
  refine ⟨15888476100819744330343523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10592317400546496220229015 15888476100819744330343523)
  ·
    refine ⟨23832714151229616495515285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15888476100819744330343523 23832714151229616495515285)
    ·
      refine ⟨1117158475838888273227279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23832714151229616495515285 1117158475838888273227279)
      ·
        refine ⟨1675737713758332409840919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1117158475838888273227279 1675737713758332409840919)
        ·
          refine ⟨2513606570637498614761379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1675737713758332409840919 2513606570637498614761379)
          ·
            refine ⟨3770409855956247922142069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2513606570637498614761379 3770409855956247922142069)
            ·
              refine ⟨353475923995898242700819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3770409855956247922142069 353475923995898242700819)
              ·
                refine ⟨530213885993847364051229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353475923995898242700819 530213885993847364051229)
                ·
                  refine ⟨198830207247692761519211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 530213885993847364051229 198830207247692761519211)
                  ·
                    rfl

theorem cell20_435623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 3].length) (baseStart_435623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435623 prefixEnd_435623 := by exact prefixLift 435623
  have htrace : WordTrace (prefixWord ++ tailWord_435623) baseStart_435623 baseEnd_435623 := by
    simpa [prefixWord, tailWord_435623, baseEnd_435623] using wordTrace_append hprefix tailTrace_435623
  have hstable : (prefixWord ++ tailWord_435623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435623).length < 2 ^ (prefixWord ++ tailWord_435623).sum := by decide
  have hdescent : baseEnd_435623 < baseStart_435623 := by decide
  rcases family_descends (prefixWord ++ tailWord_435623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435634 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 6]
def baseStart_435634 : Nat := 118140960795 + 435634 * 2 ^ 59
def prefixEnd_435634 : Nat := 4983230072969 + 3 ^ 40 * 435634 * 2
def baseEnd_435634 : Nat := 198835227947425612152499

theorem tailTrace_435634 : CollatzResearch.WordTrace tailWord_435634 prefixEnd_435634 198835227947425612152499 := by
  unfold tailWord_435634
  simp only [CollatzResearch.WordTrace]
  refine ⟨3972219325944973302248489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10592584869186595472662637 3972219325944973302248489)
  ·
    refine ⟨2979164494458729976686367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3972219325944973302248489 2979164494458729976686367)
    ·
      refine ⟨4468746741688094965029551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2979164494458729976686367 4468746741688094965029551)
      ·
        refine ⟨6703120112532142447544327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4468746741688094965029551 6703120112532142447544327)
        ·
          refine ⟨10054680168798213671316491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6703120112532142447544327 10054680168798213671316491)
          ·
            refine ⟨15082020253197320506974737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10054680168798213671316491 15082020253197320506974737)
            ·
              refine ⟨11311515189897990380231053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15082020253197320506974737 11311515189897990380231053)
              ·
                refine ⟨4241818196211746392586645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11311515189897990380231053 4241818196211746392586645)
                ·
                  refine ⟨198835227947425612152499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4241818196211746392586645 198835227947425612152499)
                  ·
                    rfl

theorem cell20_435634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_435634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435634 prefixEnd_435634 := by exact prefixLift 435634
  have htrace : WordTrace (prefixWord ++ tailWord_435634) baseStart_435634 baseEnd_435634 := by
    simpa [prefixWord, tailWord_435634, baseEnd_435634] using wordTrace_append hprefix tailTrace_435634
  have hstable : (prefixWord ++ tailWord_435634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435634).length < 2 ^ (prefixWord ++ tailWord_435634).sum := by decide
  have hdescent : baseEnd_435634 < baseStart_435634 := by decide
  rcases family_descends (prefixWord ++ tailWord_435634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435637 : List Nat := [1, 3, 3, 2, 2, 1, 4, 4]
def baseStart_435637 : Nat := 118140960795 + 435637 * 2 ^ 59
def prefixEnd_435637 : Nat := 4983230072969 + 3 ^ 40 * 435637 * 2
def baseEnd_435637 : Nat := 66278865743056978350829

theorem tailTrace_435637 : CollatzResearch.WordTrace tailWord_435637 prefixEnd_435637 66278865743056978350829 := by
  unfold tailWord_435637
  simp only [CollatzResearch.WordTrace]
  refine ⟨15888986722769024721353165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10592657815179349814235443 15888986722769024721353165)
  ·
    refine ⟨5958370021038384270507437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15888986722769024721353165 5958370021038384270507437)
    ·
      refine ⟨2234388757889394101440289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5958370021038384270507437 2234388757889394101440289)
      ·
        refine ⟨1675791568417045576080217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2234388757889394101440289 1675791568417045576080217)
        ·
          refine ⟨1256843676312784182060163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1675791568417045576080217 1256843676312784182060163)
          ·
            refine ⟨1885265514469176273090245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1256843676312784182060163 1885265514469176273090245)
            ·
              refine ⟨353487283962970551204421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1885265514469176273090245 353487283962970551204421)
              ·
                refine ⟨66278865743056978350829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 353487283962970551204421 66278865743056978350829)
                ·
                  rfl

theorem cell20_435637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 4].length) (baseStart_435637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435637 prefixEnd_435637 := by exact prefixLift 435637
  have htrace : WordTrace (prefixWord ++ tailWord_435637) baseStart_435637 baseEnd_435637 := by
    simpa [prefixWord, tailWord_435637, baseEnd_435637] using wordTrace_append hprefix tailTrace_435637
  have hstable : (prefixWord ++ tailWord_435637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435637).length < 2 ^ (prefixWord ++ tailWord_435637).sum := by decide
  have hdescent : baseEnd_435637 < baseStart_435637 := by decide
  rcases family_descends (prefixWord ++ tailWord_435637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435650 : List Nat := [3, 5, 2, 1, 1, 2, 6]
def baseStart_435650 : Nat := 118140960795 + 435650 * 2 ^ 59
def prefixEnd_435650 : Nat := 4983230072969 + 3 ^ 40 * 435650 * 2
def baseEnd_435650 : Nat := 22093614531488963068789

theorem tailTrace_435650 : CollatzResearch.WordTrace tailWord_435650 prefixEnd_435650 22093614531488963068789 := by
  unfold tailWord_435650
  simp only [CollatzResearch.WordTrace]
  refine ⟨3972365217930481985394101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10592973914481285294384269 3972365217930481985394101)
  ·
    refine ⟨372409239180982686130697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3972365217930481985394101 372409239180982686130697)
    ·
      refine ⟨279306929385737014598023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372409239180982686130697 279306929385737014598023)
      ·
        refine ⟨418960394078605521897035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279306929385737014598023 418960394078605521897035)
        ·
          refine ⟨628440591117908282845553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418960394078605521897035 628440591117908282845553)
          ·
            refine ⟨471330443338431212134165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 628440591117908282845553 471330443338431212134165)
            ·
              refine ⟨22093614531488963068789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 471330443338431212134165 22093614531488963068789)
              ·
                rfl

theorem cell20_435650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 6].length) (baseStart_435650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435650 prefixEnd_435650 := by exact prefixLift 435650
  have htrace : WordTrace (prefixWord ++ tailWord_435650) baseStart_435650 baseEnd_435650 := by
    simpa [prefixWord, tailWord_435650, baseEnd_435650] using wordTrace_append hprefix tailTrace_435650
  have hstable : (prefixWord ++ tailWord_435650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435650).length < 2 ^ (prefixWord ++ tailWord_435650).sum := by decide
  have hdescent : baseEnd_435650 < baseStart_435650 := by decide
  rcases family_descends (prefixWord ++ tailWord_435650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435658 : List Nat := [3, 1, 2, 1, 2, 5, 6]
def baseStart_435658 : Nat := 118140960795 + 435658 * 2 ^ 59
def prefixEnd_435658 : Nat := 4983230072969 + 3 ^ 40 * 435658 * 2
def baseEnd_435658 : Nat := 22094020244598688372489

theorem tailTrace_435658 : CollatzResearch.WordTrace tailWord_435658 prefixEnd_435658 22094020244598688372489 := by
  unfold tailWord_435658
  simp only [CollatzResearch.WordTrace]
  refine ⟨3972438163923236326966907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10593168437128630205245085 3972438163923236326966907)
  ·
    refine ⟨5958657245884854490450361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3972438163923236326966907 5958657245884854490450361)
    ·
      refine ⟨4468992934413640867837771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5958657245884854490450361 4468992934413640867837771)
      ·
        refine ⟨6703489401620461301756657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4468992934413640867837771 6703489401620461301756657)
        ·
          refine ⟨5027617051215345976317493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6703489401620461301756657 5027617051215345976317493)
          ·
            refine ⟨471339098551438685279765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5027617051215345976317493 471339098551438685279765)
            ·
              refine ⟨22094020244598688372489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 471339098551438685279765 22094020244598688372489)
              ·
                rfl

theorem cell20_435658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 6].length) (baseStart_435658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435658 prefixEnd_435658 := by exact prefixLift 435658
  have htrace : WordTrace (prefixWord ++ tailWord_435658) baseStart_435658 baseEnd_435658 := by
    simpa [prefixWord, tailWord_435658, baseEnd_435658] using wordTrace_append hprefix tailTrace_435658
  have hstable : (prefixWord ++ tailWord_435658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435658).length < 2 ^ (prefixWord ++ tailWord_435658).sum := by decide
  have hdescent : baseEnd_435658 < baseStart_435658 := by decide
  rcases family_descends (prefixWord ++ tailWord_435658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435772 : List Nat := [2, 2, 2, 2, 4, 1, 7]
def baseStart_435772 : Nat := 118140960795 + 435772 * 2 ^ 59
def prefixEnd_435772 : Nat := 4983230072969 + 3 ^ 40 * 435772 * 2
def baseEnd_435772 : Nat := 22099801656412273950215

theorem tailTrace_435772 : CollatzResearch.WordTrace tailWord_435772 prefixEnd_435772 22099801656412273950215 := by
  unfold tailWord_435772
  simp only [CollatzResearch.WordTrace]
  refine ⟨7946955288639971388758785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10595940384853295185011713 7946955288639971388758785)
  ·
    refine ⟨5960216466479978541569089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7946955288639971388758785 5960216466479978541569089)
    ·
      refine ⟨4470162349859983906176817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5960216466479978541569089 4470162349859983906176817)
      ·
        refine ⟨3352621762394987929632613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4470162349859983906176817 3352621762394987929632613)
        ·
          refine ⟨628616580449060236806115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3352621762394987929632613 628616580449060236806115)
          ·
            refine ⟨942924870673590355209173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 628616580449060236806115 942924870673590355209173)
            ·
              refine ⟨22099801656412273950215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 942924870673590355209173 22099801656412273950215)
              ·
                rfl

theorem cell20_435772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 7].length) (baseStart_435772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435772 prefixEnd_435772 := by exact prefixLift 435772
  have htrace : WordTrace (prefixWord ++ tailWord_435772) baseStart_435772 baseEnd_435772 := by
    simpa [prefixWord, tailWord_435772, baseEnd_435772] using wordTrace_append hprefix tailTrace_435772
  have hstable : (prefixWord ++ tailWord_435772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435772).length < 2 ^ (prefixWord ++ tailWord_435772).sum := by decide
  have hdescent : baseEnd_435772 < baseStart_435772 := by decide
  rcases family_descends (prefixWord ++ tailWord_435772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435793 : List Nat := [1, 2, 2, 1, 3, 2, 2, 7]
def baseStart_435793 : Nat := 118140960795 + 435793 * 2 ^ 59
def prefixEnd_435793 : Nat := 4983230072969 + 3 ^ 40 * 435793 * 2
def baseEnd_435793 : Nat := 66302599959975908617283

theorem tailTrace_435793 : CollatzResearch.WordTrace tailWord_435793 prefixEnd_435793 66302599959975908617283 := by
  unfold tailWord_435793
  simp only [CollatzResearch.WordTrace]
  refine ⟨15894676510203863364032033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10596451006802575576021355 15894676510203863364032033)
  ·
    refine ⟨11921007382652897523024025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15894676510203863364032033 11921007382652897523024025)
    ·
      refine ⟨8940755536989673142268019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11921007382652897523024025 8940755536989673142268019)
      ·
        refine ⟨13411133305484509713402029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8940755536989673142268019 13411133305484509713402029)
        ·
          refine ⟨5029174989556691142525761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13411133305484509713402029 5029174989556691142525761)
          ·
            refine ⟨3771881242167518356894321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5029174989556691142525761 3771881242167518356894321)
            ·
              refine ⟨2828910931625638767670741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3771881242167518356894321 2828910931625638767670741)
              ·
                refine ⟨66302599959975908617283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2828910931625638767670741 66302599959975908617283)
                ·
                  rfl

theorem cell20_435793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 7].length) (baseStart_435793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435793 prefixEnd_435793 := by exact prefixLift 435793
  have htrace : WordTrace (prefixWord ++ tailWord_435793) baseStart_435793 baseEnd_435793 := by
    simpa [prefixWord, tailWord_435793, baseEnd_435793] using wordTrace_append hprefix tailTrace_435793
  have hstable : (prefixWord ++ tailWord_435793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435793).length < 2 ^ (prefixWord ++ tailWord_435793).sum := by decide
  have hdescent : baseEnd_435793 < baseStart_435793 := by decide
  rcases family_descends (prefixWord ++ tailWord_435793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435837 : List Nat := [1, 4, 1, 1, 4, 2, 3, 2, 2]
def baseStart_435837 : Nat := 118140960795 + 435837 * 2 ^ 59
def prefixEnd_435837 : Nat := 4983230072969 + 3 ^ 40 * 435837 * 2
def baseEnd_435837 : Nat := 198927882678859128385003

theorem tailTrace_435837 : CollatzResearch.WordTrace tailWord_435837 prefixEnd_435837 198927882678859128385003 := by
  unfold tailWord_435837
  simp only [CollatzResearch.WordTrace]
  refine ⟨15896281322044458878633765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10597520881362972585755843 15896281322044458878633765)
  ·
    refine ⟨2980552747883336039743831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15896281322044458878633765 2980552747883336039743831)
    ·
      refine ⟨4470829121825004059615747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2980552747883336039743831 4470829121825004059615747)
      ·
        refine ⟨6706243682737506089423621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4470829121825004059615747 6706243682737506089423621)
        ·
          refine ⟨1257420690513282391766929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6706243682737506089423621 1257420690513282391766929)
          ·
            refine ⟨943065517884961793825197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1257420690513282391766929 943065517884961793825197)
            ·
              refine ⟨353649569206860672684449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 943065517884961793825197 353649569206860672684449)
              ·
                refine ⟨265237176905145504513337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 353649569206860672684449 265237176905145504513337)
                ·
                  refine ⟨198927882678859128385003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 265237176905145504513337 198927882678859128385003)
                  ·
                    rfl

theorem cell20_435837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_435837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435837 prefixEnd_435837 := by exact prefixLift 435837
  have htrace : WordTrace (prefixWord ++ tailWord_435837) baseStart_435837 baseEnd_435837 := by
    simpa [prefixWord, tailWord_435837, baseEnd_435837] using wordTrace_append hprefix tailTrace_435837
  have hstable : (prefixWord ++ tailWord_435837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435837).length < 2 ^ (prefixWord ++ tailWord_435837).sum := by decide
  have hdescent : baseEnd_435837 < baseStart_435837 := by decide
  rcases family_descends (prefixWord ++ tailWord_435837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435841 : List Nat := [1, 2, 4, 2, 1, 2, 3, 1, 4]
def baseStart_435841 : Nat := 118140960795 + 435841 * 2 ^ 59
def prefixEnd_435841 : Nat := 4983230072969 + 3 ^ 40 * 435841 * 2
def baseEnd_435841 : Nat := 198929708387852892251653

theorem tailTrace_435841 : CollatzResearch.WordTrace tailWord_435841 prefixEnd_435841 198929708387852892251653 := by
  unfold tailWord_435841
  simp only [CollatzResearch.WordTrace]
  refine ⟨15896427214029967561779377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10597618142686645041186251 15896427214029967561779377)
  ·
    refine ⟨11922320410522475671334533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15896427214029967561779377 11922320410522475671334533)
    ·
      refine ⟨2235435076972964188375225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11922320410522475671334533 2235435076972964188375225)
      ·
        refine ⟨1676576307729723141281419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2235435076972964188375225 1676576307729723141281419)
        ·
          refine ⟨2514864461594584711922129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1676576307729723141281419 2514864461594584711922129)
          ·
            refine ⟨1886148346195938533941597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2514864461594584711922129 1886148346195938533941597)
            ·
              refine ⟨707305629823476950228099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1886148346195938533941597 707305629823476950228099)
              ·
                refine ⟨1060958444735215425342149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 707305629823476950228099 1060958444735215425342149)
                ·
                  refine ⟨198929708387852892251653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1060958444735215425342149 198929708387852892251653)
                  ·
                    rfl

theorem cell20_435841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 4].length) (baseStart_435841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435841 prefixEnd_435841 := by exact prefixLift 435841
  have htrace : WordTrace (prefixWord ++ tailWord_435841) baseStart_435841 baseEnd_435841 := by
    simpa [prefixWord, tailWord_435841, baseEnd_435841] using wordTrace_append hprefix tailTrace_435841
  have hstable : (prefixWord ++ tailWord_435841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435841).length < 2 ^ (prefixWord ++ tailWord_435841).sum := by decide
  have hdescent : baseEnd_435841 < baseStart_435841 := by decide
  rcases family_descends (prefixWord ++ tailWord_435841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435886 : List Nat := [4, 1, 4, 1, 10]
def baseStart_435886 : Nat := 118140960795 + 435886 * 2 ^ 59
def prefixEnd_435886 : Nat := 4983230072969 + 3 ^ 40 * 435886 * 2
def baseEnd_435886 : Nat := 2456175896469539947549

theorem tailTrace_435886 : CollatzResearch.WordTrace tailWord_435886 prefixEnd_435886 2456175896469539947549 := by
  unfold tailWord_435886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1987258562358367530895939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10598712332577960164778341 1987258562358367530895939)
  ·
    refine ⟨2980887843537551296343909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1987258562358367530895939 2980887843537551296343909)
    ·
      refine ⟨558916470663290868064483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2980887843537551296343909 558916470663290868064483)
      ·
        refine ⟨838374705994936302096725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 558916470663290868064483 838374705994936302096725)
        ·
          refine ⟨2456175896469539947549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 838374705994936302096725 2456175896469539947549)
          ·
            rfl

theorem cell20_435886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 10].length) (baseStart_435886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435886 prefixEnd_435886 := by exact prefixLift 435886
  have htrace : WordTrace (prefixWord ++ tailWord_435886) baseStart_435886 baseEnd_435886 := by
    simpa [prefixWord, tailWord_435886, baseEnd_435886] using wordTrace_append hprefix tailTrace_435886
  have hstable : (prefixWord ++ tailWord_435886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435886).length < 2 ^ (prefixWord ++ tailWord_435886).sum := by decide
  have hdescent : baseEnd_435886 < baseStart_435886 := by decide
  rcases family_descends (prefixWord ++ tailWord_435886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435955 : List Nat := [1, 1, 1, 2, 2, 3, 4, 4, 2]
def baseStart_435955 : Nat := 118140960795 + 435955 * 2 ^ 59
def prefixEnd_435955 : Nat := 4983230072969 + 3 ^ 40 * 435955 * 2
def baseEnd_435955 : Nat := 198981741094175162451187

theorem tailTrace_435955 : CollatzResearch.WordTrace tailWord_435955 prefixEnd_435955 198981741094175162451187 := by
  unfold tailWord_435955
  simp only [CollatzResearch.WordTrace]
  refine ⟨15900585135616965031429319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10600390090411310020952879 15900585135616965031429319)
  ·
    refine ⟨23850877703425447547143979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15900585135616965031429319 23850877703425447547143979)
    ·
      refine ⟨35776316555138171320715969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23850877703425447547143979 35776316555138171320715969)
      ·
        refine ⟨26832237416353628490536977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35776316555138171320715969 26832237416353628490536977)
        ·
          refine ⟨20124178062265221367902733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26832237416353628490536977 20124178062265221367902733)
          ·
            refine ⟨7546566773349458012963525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20124178062265221367902733 7546566773349458012963525)
            ·
              refine ⟨1414981270003023377430661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7546566773349458012963525 1414981270003023377430661)
              ·
                refine ⟨265308988125566883268249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1414981270003023377430661 265308988125566883268249)
                ·
                  refine ⟨198981741094175162451187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 265308988125566883268249 198981741094175162451187)
                  ·
                    rfl

theorem cell20_435955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 4, 2].length) (baseStart_435955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435955 prefixEnd_435955 := by exact prefixLift 435955
  have htrace : WordTrace (prefixWord ++ tailWord_435955) baseStart_435955 baseEnd_435955 := by
    simpa [prefixWord, tailWord_435955, baseEnd_435955] using wordTrace_append hprefix tailTrace_435955
  have hstable : (prefixWord ++ tailWord_435955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435955).length < 2 ^ (prefixWord ++ tailWord_435955).sum := by decide
  have hdescent : baseEnd_435955 < baseStart_435955 := by decide
  rcases family_descends (prefixWord ++ tailWord_435955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435969 : List Nat := [1, 2, 4, 1, 1, 1, 2, 5, 3]
def baseStart_435969 : Nat := 118140960795 + 435969 * 2 ^ 59
def prefixEnd_435969 : Nat := 4983230072969 + 3 ^ 40 * 435969 * 2
def baseEnd_435969 : Nat := 198988131075653335984463

theorem tailTrace_435969 : CollatzResearch.WordTrace tailWord_435969 prefixEnd_435969 198988131075653335984463 := by
  unfold tailWord_435969
  simp only [CollatzResearch.WordTrace]
  refine ⟨15901095757566245422438961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10600730505044163614959307 15901095757566245422438961)
  ·
    refine ⟨11925821818174684066829221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15901095757566245422438961 11925821818174684066829221)
    ·
      refine ⟨2236091590907753262530479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11925821818174684066829221 2236091590907753262530479)
      ·
        refine ⟨3354137386361629893795719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2236091590907753262530479 3354137386361629893795719)
        ·
          refine ⟨5031206079542444840693579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3354137386361629893795719 5031206079542444840693579)
          ·
            refine ⟨7546809119313667261040369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5031206079542444840693579 7546809119313667261040369)
            ·
              refine ⟨5660106839485250445780277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7546809119313667261040369 5660106839485250445780277)
              ·
                refine ⟨530635016201742229291901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5660106839485250445780277 530635016201742229291901)
                ·
                  refine ⟨198988131075653335984463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 530635016201742229291901 198988131075653335984463)
                  ·
                    rfl

theorem cell20_435969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 3].length) (baseStart_435969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435969 prefixEnd_435969 := by exact prefixLift 435969
  have htrace : WordTrace (prefixWord ++ tailWord_435969) baseStart_435969 baseEnd_435969 := by
    simpa [prefixWord, tailWord_435969, baseEnd_435969] using wordTrace_append hprefix tailTrace_435969
  have hstable : (prefixWord ++ tailWord_435969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435969).length < 2 ^ (prefixWord ++ tailWord_435969).sum := by decide
  have hdescent : baseEnd_435969 < baseStart_435969 := by decide
  rcases family_descends (prefixWord ++ tailWord_435969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435976 : List Nat := [2, 1, 3, 2, 2, 1, 1, 4, 4]
def baseStart_435976 : Nat := 118140960795 + 435976 * 2 ^ 59
def prefixEnd_435976 : Nat := 4983230072969 + 3 ^ 40 * 435976 * 2
def baseEnd_435976 : Nat := 198991326066392422751101

theorem tailTrace_435976 : CollatzResearch.WordTrace tailWord_435976 prefixEnd_435976 198991326066392422751101 := by
  unfold tailWord_435976
  simp only [CollatzResearch.WordTrace]
  refine ⟨7950675534270442808971891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10600900712360590411962521 7950675534270442808971891)
  ·
    refine ⟨11926013301405664213457837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7950675534270442808971891 11926013301405664213457837)
    ·
      refine ⟨4472254988027124080046689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11926013301405664213457837 4472254988027124080046689)
      ·
        refine ⟨3354191241020343060035017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4472254988027124080046689 3354191241020343060035017)
        ·
          refine ⟨2515643430765257295026263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3354191241020343060035017 2515643430765257295026263)
          ·
            refine ⟨3773465146147885942539395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2515643430765257295026263 3773465146147885942539395)
            ·
              refine ⟨5660197719221828913809093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3773465146147885942539395 5660197719221828913809093)
              ·
                refine ⟨1061287072354092921339205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5660197719221828913809093 1061287072354092921339205)
                ·
                  refine ⟨198991326066392422751101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1061287072354092921339205 198991326066392422751101)
                  ·
                    rfl

theorem cell20_435976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_435976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435976 prefixEnd_435976 := by exact prefixLift 435976
  have htrace : WordTrace (prefixWord ++ tailWord_435976) baseStart_435976 baseEnd_435976 := by
    simpa [prefixWord, tailWord_435976, baseEnd_435976] using wordTrace_append hprefix tailTrace_435976
  have hstable : (prefixWord ++ tailWord_435976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435976).length < 2 ^ (prefixWord ++ tailWord_435976).sum := by decide
  have hdescent : baseEnd_435976 < baseStart_435976 := by decide
  rcases family_descends (prefixWord ++ tailWord_435976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435981 : List Nat := [1, 7, 2, 1, 2, 1, 1, 3, 2]
def baseStart_435981 : Nat := 118140960795 + 435981 * 2 ^ 59
def prefixEnd_435981 : Nat := 4983230072969 + 3 ^ 40 * 435981 * 2
def baseEnd_435981 : Nat := 198993608202634627584415

theorem tailTrace_435981 : CollatzResearch.WordTrace tailWord_435981 prefixEnd_435981 198993608202634627584415 := by
  unfold tailWord_435981
  simp only [CollatzResearch.WordTrace]
  refine ⟨15901533433522771471875797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10601022289015180981250531 15901533433522771471875797)
  ·
    refine ⟨372692189848189956372089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 15901533433522771471875797 372692189848189956372089)
    ·
      refine ⟨279519142386142467279067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372692189848189956372089 279519142386142467279067)
      ·
        refine ⟨419278713579213700918601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279519142386142467279067 419278713579213700918601)
        ·
          refine ⟨314459035184410275688951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 419278713579213700918601 314459035184410275688951)
          ·
            refine ⟨471688552776615413533427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314459035184410275688951 471688552776615413533427)
            ·
              refine ⟨707532829164923120300141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471688552776615413533427 707532829164923120300141)
              ·
                refine ⟨265324810936846170112553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 707532829164923120300141 265324810936846170112553)
                ·
                  refine ⟨198993608202634627584415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 265324810936846170112553 198993608202634627584415)
                  ·
                    rfl

theorem cell20_435981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_435981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435981 prefixEnd_435981 := by exact prefixLift 435981
  have htrace : WordTrace (prefixWord ++ tailWord_435981) baseStart_435981 baseEnd_435981 := by
    simpa [prefixWord, tailWord_435981, baseEnd_435981] using wordTrace_append hprefix tailTrace_435981
  have hstable : (prefixWord ++ tailWord_435981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435981).length < 2 ^ (prefixWord ++ tailWord_435981).sum := by decide
  have hdescent : baseEnd_435981 < baseStart_435981 := by decide
  rcases family_descends (prefixWord ++ tailWord_435981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435986 : List Nat := [3, 2, 4, 1, 1, 1, 1, 2, 5]
def baseStart_435986 : Nat := 118140960795 + 435986 * 2 ^ 59
def prefixEnd_435986 : Nat := 4983230072969 + 3 ^ 40 * 435986 * 2
def baseEnd_435986 : Nat := 198995890338876832417727

theorem tailTrace_435986 : CollatzResearch.WordTrace tailWord_435986 prefixEnd_435986 198995890338876832417727 := by
  unfold tailWord_435986
  simp only [CollatzResearch.WordTrace]
  refine ⟨3975428949626164331451953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10601143865669771550538541 3975428949626164331451953)
  ·
    refine ⟨2981571712219623248588965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3975428949626164331451953 2981571712219623248588965)
    ·
      refine ⟨559044696041179359110431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2981571712219623248588965 559044696041179359110431)
      ·
        refine ⟨838567044061769038665647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559044696041179359110431 838567044061769038665647)
        ·
          refine ⟨1257850566092653557998471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 838567044061769038665647 1257850566092653557998471)
          ·
            refine ⟨1886775849138980336997707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1257850566092653557998471 1886775849138980336997707)
            ·
              refine ⟨2830163773708470505496561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1886775849138980336997707 2830163773708470505496561)
              ·
                refine ⟨2122622830281352879122421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2830163773708470505496561 2122622830281352879122421)
                ·
                  refine ⟨198995890338876832417727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2122622830281352879122421 198995890338876832417727)
                  ·
                    rfl

theorem cell20_435986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_435986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_435986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_435986 prefixEnd_435986 := by exact prefixLift 435986
  have htrace : WordTrace (prefixWord ++ tailWord_435986) baseStart_435986 baseEnd_435986 := by
    simpa [prefixWord, tailWord_435986, baseEnd_435986] using wordTrace_append hprefix tailTrace_435986
  have hstable : (prefixWord ++ tailWord_435986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435986).length < 2 ^ (prefixWord ++ tailWord_435986).sum := by decide
  have hdescent : baseEnd_435986 < baseStart_435986 := by decide
  rcases family_descends (prefixWord ++ tailWord_435986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436020 : List Nat := [2, 5, 1, 1, 2, 3, 2, 1, 3]
def baseStart_436020 : Nat := 118140960795 + 436020 * 2 ^ 59
def prefixEnd_436020 : Nat := 4983230072969 + 3 ^ 40 * 436020 * 2
def baseEnd_436020 : Nat := 199011408865323825284255

theorem tailTrace_436020 : CollatzResearch.WordTrace tailWord_436020 prefixEnd_436020 199011408865323825284255 := by
  unfold tailWord_436020
  simp only [CollatzResearch.WordTrace]
  refine ⟨7951477940190740566272757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10601970586920987421697009 7951477940190740566272757)
  ·
    refine ⟨745451056892881928088071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7951477940190740566272757 745451056892881928088071)
    ·
      refine ⟨1118176585339322892132107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 745451056892881928088071 1118176585339322892132107)
      ·
        refine ⟨1677264878008984338198161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1118176585339322892132107 1677264878008984338198161)
        ·
          refine ⟨1257948658506738253648621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1677264878008984338198161 1257948658506738253648621)
          ·
            refine ⟨471730746940026845118233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1257948658506738253648621 471730746940026845118233)
            ·
              refine ⟨353798060205020133838675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 471730746940026845118233 353798060205020133838675)
              ·
                refine ⟨530697090307530200758013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353798060205020133838675 530697090307530200758013)
                ·
                  refine ⟨199011408865323825284255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 530697090307530200758013 199011408865323825284255)
                  ·
                    rfl

theorem cell20_436020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_436020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436020 prefixEnd_436020 := by exact prefixLift 436020
  have htrace : WordTrace (prefixWord ++ tailWord_436020) baseStart_436020 baseEnd_436020 := by
    simpa [prefixWord, tailWord_436020, baseEnd_436020] using wordTrace_append hprefix tailTrace_436020
  have hstable : (prefixWord ++ tailWord_436020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436020).length < 2 ^ (prefixWord ++ tailWord_436020).sum := by decide
  have hdescent : baseEnd_436020 < baseStart_436020 := by decide
  rcases family_descends (prefixWord ++ tailWord_436020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436024 : List Nat := [2, 1, 2, 1, 3, 3, 4, 1, 3]
def baseStart_436024 : Nat := 118140960795 + 436024 * 2 ^ 59
def prefixEnd_436024 : Nat := 4983230072969 + 3 ^ 40 * 436024 * 2
def baseEnd_436024 : Nat := 199013234574317589150905

theorem tailTrace_436024 : CollatzResearch.WordTrace tailWord_436024 prefixEnd_436024 199013234574317589150905 := by
  unfold tailWord_436024
  simp only [CollatzResearch.WordTrace]
  refine ⟨7951550886183494907845563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10602067848244659877127417 7951550886183494907845563)
  ·
    refine ⟨11927326329275242361768345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7951550886183494907845563 11927326329275242361768345)
    ·
      refine ⟨8945494746956431771326259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11927326329275242361768345 8945494746956431771326259)
      ·
        refine ⟨13418242120434647656989389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8945494746956431771326259 13418242120434647656989389)
        ·
          refine ⟨5031840795162992871371021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13418242120434647656989389 5031840795162992871371021)
          ·
            refine ⟨1886940298186122326764133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5031840795162992871371021 1886940298186122326764133)
            ·
              refine ⟨353801305909897936268275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1886940298186122326764133 353801305909897936268275)
              ·
                refine ⟨530701958864846904402413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353801305909897936268275 530701958864846904402413)
                ·
                  refine ⟨199013234574317589150905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 530701958864846904402413 199013234574317589150905)
                  ·
                    rfl

theorem cell20_436024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 3].length) (baseStart_436024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436024 prefixEnd_436024 := by exact prefixLift 436024
  have htrace : WordTrace (prefixWord ++ tailWord_436024) baseStart_436024 baseEnd_436024 := by
    simpa [prefixWord, tailWord_436024, baseEnd_436024] using wordTrace_append hprefix tailTrace_436024
  have hstable : (prefixWord ++ tailWord_436024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436024).length < 2 ^ (prefixWord ++ tailWord_436024).sum := by decide
  have hdescent : baseEnd_436024 < baseStart_436024 := by decide
  rcases family_descends (prefixWord ++ tailWord_436024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436073 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 8]
def baseStart_436073 : Nat := 118140960795 + 436073 * 2 ^ 59
def prefixEnd_436073 : Nat := 4983230072969 + 3 ^ 40 * 436073 * 2
def baseEnd_436073 : Nat := 199035599509491196517371

theorem tailTrace_436073 : CollatzResearch.WordTrace tailWord_436073 prefixEnd_436073 199035599509491196517371 := by
  unfold tailWord_436073
  simp only [CollatzResearch.WordTrace]
  refine ⟨15904888949189471184224873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10603259299459647456149915 15904888949189471184224873)
  ·
    refine ⟨11928666711892103388168655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15904888949189471184224873 11928666711892103388168655)
    ·
      refine ⟨17893000067838155082252983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11928666711892103388168655 17893000067838155082252983)
      ·
        refine ⟨26839500101757232623379475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17893000067838155082252983 26839500101757232623379475)
        ·
          refine ⟨40259250152635848935069213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26839500101757232623379475 40259250152635848935069213)
          ·
            refine ⟨15097218807238443350650955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40259250152635848935069213 15097218807238443350650955)
            ·
              refine ⟨22645828210857665025976433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15097218807238443350650955 22645828210857665025976433)
              ·
                refine ⟨16984371158143248769482325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22645828210857665025976433 16984371158143248769482325)
                ·
                  refine ⟨199035599509491196517371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16984371158143248769482325 199035599509491196517371)
                  ·
                    rfl

theorem cell20_436073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_436073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436073 prefixEnd_436073 := by exact prefixLift 436073
  have htrace : WordTrace (prefixWord ++ tailWord_436073) baseStart_436073 baseEnd_436073 := by
    simpa [prefixWord, tailWord_436073, baseEnd_436073] using wordTrace_append hprefix tailTrace_436073
  have hstable : (prefixWord ++ tailWord_436073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436073).length < 2 ^ (prefixWord ++ tailWord_436073).sum := by decide
  have hdescent : baseEnd_436073 < baseStart_436073 := by decide
  rcases family_descends (prefixWord ++ tailWord_436073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436076 : List Nat := [2, 2, 1, 1, 4, 4, 1, 5]
def baseStart_436076 : Nat := 118140960795 + 436076 * 2 ^ 59
def prefixEnd_436076 : Nat := 4983230072969 + 3 ^ 40 * 436076 * 2
def baseEnd_436076 : Nat := 66345656263745506472453

theorem tailTrace_436076 : CollatzResearch.WordTrace tailWord_436076 prefixEnd_436076 66345656263745506472453 := by
  unfold tailWord_436076
  simp only [CollatzResearch.WordTrace]
  refine ⟨7952499184089301348292041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10603332245452401797722721 7952499184089301348292041)
  ·
    refine ⟨5964374388066976011219031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7952499184089301348292041 5964374388066976011219031)
    ·
      refine ⟨8946561582100464016828547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5964374388066976011219031 8946561582100464016828547)
      ·
        refine ⟨13419842373150696025242821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8946561582100464016828547 13419842373150696025242821)
        ·
          refine ⟨2516220444965755504733029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13419842373150696025242821 2516220444965755504733029)
          ·
            refine ⟨471791333431079157137443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2516220444965755504733029 471791333431079157137443)
            ·
              refine ⟨707687000146618735706165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471791333431079157137443 707687000146618735706165)
              ·
                refine ⟨66345656263745506472453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 707687000146618735706165 66345656263745506472453)
                ·
                  rfl

theorem cell20_436076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 5].length) (baseStart_436076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436076 prefixEnd_436076 := by exact prefixLift 436076
  have htrace : WordTrace (prefixWord ++ tailWord_436076) baseStart_436076 baseEnd_436076 := by
    simpa [prefixWord, tailWord_436076, baseEnd_436076] using wordTrace_append hprefix tailTrace_436076
  have hstable : (prefixWord ++ tailWord_436076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436076).length < 2 ^ (prefixWord ++ tailWord_436076).sum := by decide
  have hdescent : baseEnd_436076 < baseStart_436076 := by decide
  rcases family_descends (prefixWord ++ tailWord_436076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436086 : List Nat := [5, 1, 1, 3, 2, 1, 1, 2, 4]
def baseStart_436086 : Nat := 118140960795 + 436086 * 2 ^ 59
def prefixEnd_436086 : Nat := 4983230072969 + 3 ^ 40 * 436086 * 2
def baseEnd_436086 : Nat := 199041533063720929083985

theorem tailTrace_436086 : CollatzResearch.WordTrace tailWord_436086 prefixEnd_436086 199041533063720929083985 := by
  unfold tailWord_436086
  simp only [CollatzResearch.WordTrace]
  refine ⟨994085193633898400278007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10603575398761582936298741 994085193633898400278007)
  ·
    refine ⟨1491127790450847600417011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 994085193633898400278007 1491127790450847600417011)
    ·
      refine ⟨2236691685676271400625517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1491127790450847600417011 2236691685676271400625517)
      ·
        refine ⟨838759382128601775234569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2236691685676271400625517 838759382128601775234569)
        ·
          refine ⟨629069536596451331425927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 838759382128601775234569 629069536596451331425927)
          ·
            refine ⟨943604304894676997138891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629069536596451331425927 943604304894676997138891)
            ·
              refine ⟨1415406457342015495708337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 943604304894676997138891 1415406457342015495708337)
              ·
                refine ⟨1061554843006511621781253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1415406457342015495708337 1061554843006511621781253)
                ·
                  refine ⟨199041533063720929083985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1061554843006511621781253 199041533063720929083985)
                  ·
                    rfl

theorem cell20_436086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_436086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436086 prefixEnd_436086 := by exact prefixLift 436086
  have htrace : WordTrace (prefixWord ++ tailWord_436086) baseStart_436086 baseEnd_436086 := by
    simpa [prefixWord, tailWord_436086, baseEnd_436086] using wordTrace_append hprefix tailTrace_436086
  have hstable : (prefixWord ++ tailWord_436086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436086).length < 2 ^ (prefixWord ++ tailWord_436086).sum := by decide
  have hdescent : baseEnd_436086 < baseStart_436086 := by decide
  rcases family_descends (prefixWord ++ tailWord_436086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436114 : List Nat := [3, 2, 3, 2, 1, 2, 7]
def baseStart_436114 : Nat := 118140960795 + 436114 * 2 ^ 59
def prefixEnd_436114 : Nat := 4983230072969 + 3 ^ 40 * 436114 * 2
def baseEnd_436114 : Nat := 22117145891853030683393

theorem tailTrace_436114 : CollatzResearch.WordTrace tailWord_436114 prefixEnd_436114 22117145891853030683393 := by
  unfold tailWord_436114
  simp only [CollatzResearch.WordTrace]
  refine ⟨3976596085510233796616849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10604256228027290124311597 3976596085510233796616849)
  ·
    refine ⟨2982447064132675347462637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3976596085510233796616849 2982447064132675347462637)
    ·
      refine ⟨1118417649049753255298489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2982447064132675347462637 1118417649049753255298489)
      ·
        refine ⟨838813236787314941473867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1118417649049753255298489 838813236787314941473867)
        ·
          refine ⟨1258219855180972412210801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 838813236787314941473867 1258219855180972412210801)
          ·
            refine ⟨943664891385729309158101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1258219855180972412210801 943664891385729309158101)
            ·
              refine ⟨22117145891853030683393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 943664891385729309158101 22117145891853030683393)
              ·
                rfl

theorem cell20_436114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 7].length) (baseStart_436114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436114 prefixEnd_436114 := by exact prefixLift 436114
  have htrace : WordTrace (prefixWord ++ tailWord_436114) baseStart_436114 baseEnd_436114 := by
    simpa [prefixWord, tailWord_436114, baseEnd_436114] using wordTrace_append hprefix tailTrace_436114
  have hstable : (prefixWord ++ tailWord_436114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436114).length < 2 ^ (prefixWord ++ tailWord_436114).sum := by decide
  have hdescent : baseEnd_436114 < baseStart_436114 := by decide
  rcases family_descends (prefixWord ++ tailWord_436114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436121 : List Nat := [1, 2, 1, 2, 1, 3, 5, 2, 3]
def baseStart_436121 : Nat := 118140960795 + 436121 * 2 ^ 59
def prefixEnd_436121 : Nat := 4983230072969 + 3 ^ 40 * 436121 * 2
def baseEnd_436121 : Nat := 199057508017416362917175

theorem tailTrace_436121 : CollatzResearch.WordTrace tailWord_436121 prefixEnd_436121 199057508017416362917175 := by
  unfold tailWord_436121
  simp only [CollatzResearch.WordTrace]
  refine ⟨15906639653015575381972217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10604426435343716921314811 15906639653015575381972217)
  ·
    refine ⟨11929979739761681536479163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15906639653015575381972217 11929979739761681536479163)
    ·
      refine ⟨17894969609642522304718745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11929979739761681536479163 17894969609642522304718745)
      ·
        refine ⟨13421227207231891728539059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17894969609642522304718745 13421227207231891728539059)
        ·
          refine ⟨20131840810847837592808589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13421227207231891728539059 20131840810847837592808589)
          ·
            refine ⟨7549440304067939097303221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20131840810847837592808589 7549440304067939097303221)
            ·
              refine ⟨707760028506369290372177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7549440304067939097303221 707760028506369290372177)
              ·
                refine ⟨530820021379776967779133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 707760028506369290372177 530820021379776967779133)
                ·
                  refine ⟨199057508017416362917175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 530820021379776967779133 199057508017416362917175)
                  ·
                    rfl

theorem cell20_436121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 3].length) (baseStart_436121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436121 prefixEnd_436121 := by exact prefixLift 436121
  have htrace : WordTrace (prefixWord ++ tailWord_436121) baseStart_436121 baseEnd_436121 := by
    simpa [prefixWord, tailWord_436121, baseEnd_436121] using wordTrace_append hprefix tailTrace_436121
  have hstable : (prefixWord ++ tailWord_436121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436121).length < 2 ^ (prefixWord ++ tailWord_436121).sum := by decide
  have hdescent : baseEnd_436121 < baseStart_436121 := by decide
  rcases family_descends (prefixWord ++ tailWord_436121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436124 : List Nat := [2, 2, 3, 3, 1, 1, 2, 4, 2]
def baseStart_436124 : Nat := 118140960795 + 436124 * 2 ^ 59
def prefixEnd_436124 : Nat := 4983230072969 + 3 ^ 40 * 436124 * 2
def baseEnd_436124 : Nat := 199058877299161685817163

theorem tailTrace_436124 : CollatzResearch.WordTrace tailWord_436124 prefixEnd_436124 199058877299161685817163 := by
  unfold tailWord_436124
  simp only [CollatzResearch.WordTrace]
  refine ⟨7953374536002353447165713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10604499381336471262887617 7953374536002353447165713)
  ·
    refine ⟨5965030902001765085374285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7953374536002353447165713 5965030902001765085374285)
    ·
      refine ⟨2236886588250661907015357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5965030902001765085374285 2236886588250661907015357)
      ·
        refine ⟨838832470593998215130759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2236886588250661907015357 838832470593998215130759)
        ·
          refine ⟨1258248705890997322696139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 838832470593998215130759 1258248705890997322696139)
          ·
            refine ⟨1887373058836495984044209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1258248705890997322696139 1887373058836495984044209)
            ·
              refine ⟨1415529794127371988033157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1887373058836495984044209 1415529794127371988033157)
              ·
                refine ⟨265411836398882247756217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1415529794127371988033157 265411836398882247756217)
                ·
                  refine ⟨199058877299161685817163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 265411836398882247756217 199058877299161685817163)
                  ·
                    rfl

theorem cell20_436124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 4, 2].length) (baseStart_436124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436124 prefixEnd_436124 := by exact prefixLift 436124
  have htrace : WordTrace (prefixWord ++ tailWord_436124) baseStart_436124 baseEnd_436124 := by
    simpa [prefixWord, tailWord_436124, baseEnd_436124] using wordTrace_append hprefix tailTrace_436124
  have hstable : (prefixWord ++ tailWord_436124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436124).length < 2 ^ (prefixWord ++ tailWord_436124).sum := by decide
  have hdescent : baseEnd_436124 < baseStart_436124 := by decide
  rcases family_descends (prefixWord ++ tailWord_436124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436228 : List Nat := [2, 3, 2, 4, 1, 8]
def baseStart_436228 : Nat := 118140960795 + 436228 * 2 ^ 59
def prefixEnd_436228 : Nat := 4983230072969 + 3 ^ 40 * 436228 * 2
def baseEnd_436228 : Nat := 7374309101222205420373

theorem tailTrace_436228 : CollatzResearch.WordTrace tailWord_436228 prefixEnd_436228 7374309101222205420373 := by
  unfold tailWord_436228
  simp only [CollatzResearch.WordTrace]
  refine ⟨7955271131813966328058669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10607028175751955104078225 7955271131813966328058669)
  ·
    refine ⟨2983226674430237373022001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7955271131813966328058669 2983226674430237373022001)
    ·
      refine ⟨2237420005822678029766501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2983226674430237373022001 2237420005822678029766501)
      ·
        refine ⟨419516251091752130581219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2237420005822678029766501 419516251091752130581219)
        ·
          refine ⟨629274376637628195871829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419516251091752130581219 629274376637628195871829)
          ·
            refine ⟨7374309101222205420373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 629274376637628195871829 7374309101222205420373)
            ·
              rfl

theorem cell20_436228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 8].length) (baseStart_436228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436228 prefixEnd_436228 := by exact prefixLift 436228
  have htrace : WordTrace (prefixWord ++ tailWord_436228) baseStart_436228 baseEnd_436228 := by
    simpa [prefixWord, tailWord_436228, baseEnd_436228] using wordTrace_append hprefix tailTrace_436228
  have hstable : (prefixWord ++ tailWord_436228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436228).length < 2 ^ (prefixWord ++ tailWord_436228).sum := by decide
  have hdescent : baseEnd_436228 < baseStart_436228 := by decide
  rcases family_descends (prefixWord ++ tailWord_436228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436234 : List Nat := [3, 1, 2, 2, 5, 1, 2, 2, 2]
def baseStart_436234 : Nat := 118140960795 + 436234 * 2 ^ 59
def prefixEnd_436234 : Nat := 4983230072969 + 3 ^ 40 * 436234 * 2
def baseEnd_436234 : Nat := 199109084296490192150047

theorem tailTrace_436234 : CollatzResearch.WordTrace tailWord_436234 prefixEnd_436234 199109084296490192150047 := by
  unfold tailWord_436234
  simp only [CollatzResearch.WordTrace]
  refine ⟨3977690275401548920208939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10607174067737463787223837 3977690275401548920208939)
  ·
    refine ⟨5966535413102323380313409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3977690275401548920208939 5966535413102323380313409)
    ·
      refine ⟨4474901559826742535235057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5966535413102323380313409 4474901559826742535235057)
      ·
        refine ⟨3356176169870056901426293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4474901559826742535235057 3356176169870056901426293)
        ·
          refine ⟨314641515925317834508715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3356176169870056901426293 314641515925317834508715)
          ·
            refine ⟨471962273887976751763073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314641515925317834508715 471962273887976751763073)
            ·
              refine ⟨353971705415982563822305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 471962273887976751763073 353971705415982563822305)
              ·
                refine ⟨265478779061986922866729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 353971705415982563822305 265478779061986922866729)
                ·
                  refine ⟨199109084296490192150047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 265478779061986922866729 199109084296490192150047)
                  ·
                    rfl

theorem cell20_436234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 2, 2].length) (baseStart_436234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436234 prefixEnd_436234 := by exact prefixLift 436234
  have htrace : WordTrace (prefixWord ++ tailWord_436234) baseStart_436234 baseEnd_436234 := by
    simpa [prefixWord, tailWord_436234, baseEnd_436234] using wordTrace_append hprefix tailTrace_436234
  have hstable : (prefixWord ++ tailWord_436234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436234).length < 2 ^ (prefixWord ++ tailWord_436234).sum := by decide
  have hdescent : baseEnd_436234 < baseStart_436234 := by decide
  rcases family_descends (prefixWord ++ tailWord_436234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436235 : List Nat := [1, 1, 1, 1, 6, 1, 4, 2, 3]
def baseStart_436235 : Nat := 118140960795 + 436235 * 2 ^ 59
def prefixEnd_436235 : Nat := 4983230072969 + 3 ^ 40 * 436235 * 2
def baseEnd_436235 : Nat := 199109540723738633116709

theorem tailTrace_436235 : CollatzResearch.WordTrace tailWord_436235 prefixEnd_436235 199109540723738633116709 := by
  unfold tailWord_436235
  simp only [CollatzResearch.WordTrace]
  refine ⟨15910797574602572851622159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10607198383068381901081439 15910797574602572851622159)
  ·
    refine ⟨23866196361903859277433239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15910797574602572851622159 23866196361903859277433239)
    ·
      refine ⟨35799294542855788916149859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23866196361903859277433239 35799294542855788916149859)
      ·
        refine ⟨53698941814283683374224789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35799294542855788916149859 53698941814283683374224789)
        ·
          refine ⟨2517137897544547658166787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53698941814283683374224789 2517137897544547658166787)
          ·
            refine ⟨3775706846316821487250181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2517137897544547658166787 3775706846316821487250181)
            ·
              refine ⟨707945033684404028859409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3775706846316821487250181 707945033684404028859409)
              ·
                refine ⟨530958775263303021644557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 707945033684404028859409 530958775263303021644557)
                ·
                  refine ⟨199109540723738633116709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 530958775263303021644557 199109540723738633116709)
                  ·
                    rfl

theorem cell20_436235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 3].length) (baseStart_436235 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436235 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436235 prefixEnd_436235 := by exact prefixLift 436235
  have htrace : WordTrace (prefixWord ++ tailWord_436235) baseStart_436235 baseEnd_436235 := by
    simpa [prefixWord, tailWord_436235, baseEnd_436235] using wordTrace_append hprefix tailTrace_436235
  have hstable : (prefixWord ++ tailWord_436235).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436235).length < 2 ^ (prefixWord ++ tailWord_436235).sum := by decide
  have hdescent : baseEnd_436235 < baseStart_436235 := by decide
  rcases family_descends (prefixWord ++ tailWord_436235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436245 : List Nat := [1, 3, 2, 1, 6, 1, 1, 5]
def baseStart_436245 : Nat := 118140960795 + 436245 * 2 ^ 59
def prefixEnd_436245 : Nat := 4983230072969 + 3 ^ 40 * 436245 * 2
def baseEnd_436245 : Nat := 66371368332074347594445

theorem tailTrace_436245 : CollatzResearch.WordTrace tailWord_436245 prefixEnd_436245 66371368332074347594445 := by
  unfold tailWord_436245
  simp only [CollatzResearch.WordTrace]
  refine ⟨15911162304566344559486189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10607441536377563039657459 15911162304566344559486189)
  ·
    refine ⟨5966685864212379209807321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15911162304566344559486189 5966685864212379209807321)
    ·
      refine ⟨4475014398159284407355491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5966685864212379209807321 4475014398159284407355491)
      ·
        refine ⟨6712521597238926611033237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4475014398159284407355491 6712521597238926611033237)
        ·
          refine ⟨314649449870574684892183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6712521597238926611033237 314649449870574684892183)
          ·
            refine ⟨471974174805862027338275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314649449870574684892183 471974174805862027338275)
            ·
              refine ⟨707961262208793041007413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471974174805862027338275 707961262208793041007413)
              ·
                refine ⟨66371368332074347594445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 707961262208793041007413 66371368332074347594445)
                ·
                  rfl

theorem cell20_436245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 5].length) (baseStart_436245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436245 prefixEnd_436245 := by exact prefixLift 436245
  have htrace : WordTrace (prefixWord ++ tailWord_436245) baseStart_436245 baseEnd_436245 := by
    simpa [prefixWord, tailWord_436245, baseEnd_436245] using wordTrace_append hprefix tailTrace_436245
  have hstable : (prefixWord ++ tailWord_436245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436245).length < 2 ^ (prefixWord ++ tailWord_436245).sum := by decide
  have hdescent : baseEnd_436245 < baseStart_436245 := by decide
  rcases family_descends (prefixWord ++ tailWord_436245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436286 : List Nat := [4, 2, 1, 3, 3, 1, 1, 2, 3]
def baseStart_436286 : Nat := 118140960795 + 436286 * 2 ^ 59
def prefixEnd_436286 : Nat := 4983230072969 + 3 ^ 40 * 436286 * 2
def baseEnd_436286 : Nat := 199132818513409122416501

theorem tailTrace_436286 : CollatzResearch.WordTrace tailWord_436286 prefixEnd_436286 199132818513409122416501 := by
  unfold tailWord_436286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1989082212177226070216089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10608438464945205707819141 1989082212177226070216089)
  ·
    refine ⟨1491811659132919552662067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1989082212177226070216089 1491811659132919552662067)
    ·
      refine ⟨2237717488699379328993101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1491811659132919552662067 2237717488699379328993101)
      ·
        refine ⟨839144058262267248372413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2237717488699379328993101 839144058262267248372413)
        ·
          refine ⟨314679021848350218139655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 839144058262267248372413 314679021848350218139655)
          ·
            refine ⟨472018532772525327209483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314679021848350218139655 472018532772525327209483)
            ·
              refine ⟨708027799158787990814225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472018532772525327209483 708027799158787990814225)
              ·
                refine ⟨531020849369090993110669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 708027799158787990814225 531020849369090993110669)
                ·
                  refine ⟨199132818513409122416501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 531020849369090993110669 199132818513409122416501)
                  ·
                    rfl

theorem cell20_436286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_436286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436286 prefixEnd_436286 := by exact prefixLift 436286
  have htrace : WordTrace (prefixWord ++ tailWord_436286) baseStart_436286 baseEnd_436286 := by
    simpa [prefixWord, tailWord_436286, baseEnd_436286] using wordTrace_append hprefix tailTrace_436286
  have hstable : (prefixWord ++ tailWord_436286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436286).length < 2 ^ (prefixWord ++ tailWord_436286).sum := by decide
  have hdescent : baseEnd_436286 < baseStart_436286 := by decide
  rcases family_descends (prefixWord ++ tailWord_436286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436325 : List Nat := [1, 3, 1, 3, 2, 3, 1, 6]
def baseStart_436325 : Nat := 118140960795 + 436325 * 2 ^ 59
def prefixEnd_436325 : Nat := 4983230072969 + 3 ^ 40 * 436325 * 2
def baseEnd_436325 : Nat := 66383539725366106705447

theorem tailTrace_436325 : CollatzResearch.WordTrace tailWord_436325 prefixEnd_436325 66383539725366106705447 := by
  unfold tailWord_436325
  simp only [CollatzResearch.WordTrace]
  refine ⟨15914080144276518222398429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10609386762851012148265619 15914080144276518222398429)
  ·
    refine ⟨5967780054103694333399411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15914080144276518222398429 5967780054103694333399411)
    ·
      refine ⟨8951670081155541500099117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5967780054103694333399411 8951670081155541500099117)
      ·
        refine ⟨3356876280433328062537169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8951670081155541500099117 3356876280433328062537169)
        ·
          refine ⟨2517657210324996046902877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3356876280433328062537169 2517657210324996046902877)
          ·
            refine ⟨944121453871873517588579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2517657210324996046902877 944121453871873517588579)
            ·
              refine ⟨1416182180807810276382869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 944121453871873517588579 1416182180807810276382869)
              ·
                refine ⟨66383539725366106705447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1416182180807810276382869 66383539725366106705447)
                ·
                  rfl

theorem cell20_436325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 6].length) (baseStart_436325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436325 prefixEnd_436325 := by exact prefixLift 436325
  have htrace : WordTrace (prefixWord ++ tailWord_436325) baseStart_436325 baseEnd_436325 := by
    simpa [prefixWord, tailWord_436325, baseEnd_436325] using wordTrace_append hprefix tailTrace_436325
  have hstable : (prefixWord ++ tailWord_436325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436325).length < 2 ^ (prefixWord ++ tailWord_436325).sum := by decide
  have hdescent : baseEnd_436325 < baseStart_436325 := by decide
  rcases family_descends (prefixWord ++ tailWord_436325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436332 : List Nat := [2, 2, 1, 1, 3, 3, 1, 2, 5]
def baseStart_436332 : Nat := 118140960795 + 436332 * 2 ^ 59
def prefixEnd_436332 : Nat := 4983230072969 + 3 ^ 40 * 436332 * 2
def baseEnd_436332 : Nat := 199153814166837406882979

theorem tailTrace_436332 : CollatzResearch.WordTrace tailWord_436332 prefixEnd_436332 199153814166837406882979 := by
  unfold tailWord_436332
  simp only [CollatzResearch.WordTrace]
  refine ⟨7957167727625579208951625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10609556970167438945268833 7957167727625579208951625)
  ·
    refine ⟨5967875795719184406713719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7957167727625579208951625 5967875795719184406713719)
    ·
      refine ⟨8951813693578776610070579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5967875795719184406713719 8951813693578776610070579)
      ·
        refine ⟨13427720540368164915105869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8951813693578776610070579 13427720540368164915105869)
        ·
          refine ⟨5035395202638061843164701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13427720540368164915105869 5035395202638061843164701)
          ·
            refine ⟨1888273200989273191186763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5035395202638061843164701 1888273200989273191186763)
            ·
              refine ⟨2832409801483909786780145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1888273200989273191186763 2832409801483909786780145)
              ·
                refine ⟨2124307351112932340085109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2832409801483909786780145 2124307351112932340085109)
                ·
                  refine ⟨199153814166837406882979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2124307351112932340085109 199153814166837406882979)
                  ·
                    rfl

theorem cell20_436332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_436332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436332 prefixEnd_436332 := by exact prefixLift 436332
  have htrace : WordTrace (prefixWord ++ tailWord_436332) baseStart_436332 baseEnd_436332 := by
    simpa [prefixWord, tailWord_436332, baseEnd_436332] using wordTrace_append hprefix tailTrace_436332
  have hstable : (prefixWord ++ tailWord_436332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436332).length < 2 ^ (prefixWord ++ tailWord_436332).sum := by decide
  have hdescent : baseEnd_436332 < baseStart_436332 := by decide
  rcases family_descends (prefixWord ++ tailWord_436332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436335 : List Nat := [1, 1, 2, 1, 3, 4, 3, 3, 2]
def baseStart_436335 : Nat := 118140960795 + 436335 * 2 ^ 59
def prefixEnd_436335 : Nat := 4983230072969 + 3 ^ 40 * 436335 * 2
def baseEnd_436335 : Nat := 199155183448582729782967

theorem tailTrace_436335 : CollatzResearch.WordTrace tailWord_436335 prefixEnd_436335 199155183448582729782967 := by
  unfold tailWord_436335
  simp only [CollatzResearch.WordTrace]
  refine ⟨15914444874240289930262459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10609629916160193286841639 15914444874240289930262459)
  ·
    refine ⟨23871667311360434895393689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15914444874240289930262459 23871667311360434895393689)
    ·
      refine ⟨17903750483520326171545267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23871667311360434895393689 17903750483520326171545267)
      ·
        refine ⟨26855625725280489257317901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17903750483520326171545267 26855625725280489257317901)
        ·
          refine ⟨10070859646980183471494213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26855625725280489257317901 10070859646980183471494213)
          ·
            refine ⟨1888286183808784400905165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10070859646980183471494213 1888286183808784400905165)
            ·
              refine ⟨708107318928294150339437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1888286183808784400905165 708107318928294150339437)
              ·
                refine ⟨265540244598110306377289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 708107318928294150339437 265540244598110306377289)
                ·
                  refine ⟨199155183448582729782967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 265540244598110306377289 199155183448582729782967)
                  ·
                    rfl

theorem cell20_436335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 3, 2].length) (baseStart_436335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436335 prefixEnd_436335 := by exact prefixLift 436335
  have htrace : WordTrace (prefixWord ++ tailWord_436335) baseStart_436335 baseEnd_436335 := by
    simpa [prefixWord, tailWord_436335, baseEnd_436335] using wordTrace_append hprefix tailTrace_436335
  have hstable : (prefixWord ++ tailWord_436335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436335).length < 2 ^ (prefixWord ++ tailWord_436335).sum := by decide
  have hdescent : baseEnd_436335 < baseStart_436335 := by decide
  rcases family_descends (prefixWord ++ tailWord_436335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436342 : List Nat := [5, 1, 1, 2, 1, 4, 6]
def baseStart_436342 : Nat := 118140960795 + 436342 * 2 ^ 59
def prefixEnd_436342 : Nat := 4983230072969 + 3 ^ 40 * 436342 * 2
def baseEnd_436342 : Nat := 22128708715480201838845

theorem tailTrace_436342 : CollatzResearch.WordTrace tailWord_436342 prefixEnd_436342 22128708715480201838845 := by
  unfold tailWord_436342
  simp only [CollatzResearch.WordTrace]
  refine ⟨994668761575933132860455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10609800123476620083844853 994668761575933132860455)
  ·
    refine ⟨1492003142363899699290683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 994668761575933132860455 1492003142363899699290683)
    ·
      refine ⟨2238004713545849548936025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1492003142363899699290683 2238004713545849548936025)
      ·
        refine ⟨1678503535159387161702019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2238004713545849548936025 1678503535159387161702019)
        ·
          refine ⟨2517755302739080742553029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1678503535159387161702019 2517755302739080742553029)
          ·
            refine ⟨472079119263577639228693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2517755302739080742553029 472079119263577639228693)
            ·
              refine ⟨22128708715480201838845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 472079119263577639228693 22128708715480201838845)
              ·
                rfl

theorem cell20_436342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 6].length) (baseStart_436342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436342 prefixEnd_436342 := by exact prefixLift 436342
  have htrace : WordTrace (prefixWord ++ tailWord_436342) baseStart_436342 baseEnd_436342 := by
    simpa [prefixWord, tailWord_436342, baseEnd_436342] using wordTrace_append hprefix tailTrace_436342
  have hstable : (prefixWord ++ tailWord_436342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436342).length < 2 ^ (prefixWord ++ tailWord_436342).sum := by decide
  have hdescent : baseEnd_436342 < baseStart_436342 := by decide
  rcases family_descends (prefixWord ++ tailWord_436342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436366 : List Nat := [4, 1, 1, 3, 3, 1, 1, 3, 3]
def baseStart_436366 : Nat := 118140960795 + 436366 * 2 ^ 59
def prefixEnd_436366 : Nat := 4983230072969 + 3 ^ 40 * 436366 * 2
def baseEnd_436366 : Nat := 199169332693284399749507

theorem tailTrace_436366 : CollatzResearch.WordTrace tailWord_436366 prefixEnd_436366 199169332693284399749507 := by
  unfold tailWord_436366
  simp only [CollatzResearch.WordTrace]
  refine ⟨1989446942140997778080119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10610383691418654816427301 1989446942140997778080119)
  ·
    refine ⟨2984170413211496667120179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1989446942140997778080119 2984170413211496667120179)
    ·
      refine ⟨4476255619817245000680269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2984170413211496667120179 4476255619817245000680269)
      ·
        refine ⟨1678595857431466875255101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4476255619817245000680269 1678595857431466875255101)
        ·
          refine ⟨629473446536800078220663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1678595857431466875255101 629473446536800078220663)
          ·
            refine ⟨944210169805200117330995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629473446536800078220663 944210169805200117330995)
            ·
              refine ⟨1416315254707800175996493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 944210169805200117330995 1416315254707800175996493)
              ·
                refine ⟨531118220515425065998685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1416315254707800175996493 531118220515425065998685)
                ·
                  refine ⟨199169332693284399749507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 531118220515425065998685 199169332693284399749507)
                  ·
                    rfl

theorem cell20_436366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_436366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436366 prefixEnd_436366 := by exact prefixLift 436366
  have htrace : WordTrace (prefixWord ++ tailWord_436366) baseStart_436366 baseEnd_436366 := by
    simpa [prefixWord, tailWord_436366, baseEnd_436366] using wordTrace_append hprefix tailTrace_436366
  have hstable : (prefixWord ++ tailWord_436366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436366).length < 2 ^ (prefixWord ++ tailWord_436366).sum := by decide
  have hdescent : baseEnd_436366 < baseStart_436366 := by decide
  rcases family_descends (prefixWord ++ tailWord_436366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436377 : List Nat := [1, 2, 1, 2, 1, 2, 1, 6, 4]
def baseStart_436377 : Nat := 118140960795 + 436377 * 2 ^ 59
def prefixEnd_436377 : Nat := 4983230072969 + 3 ^ 40 * 436377 * 2
def baseEnd_436377 : Nat := 199174353393017250382795

theorem tailTrace_436377 : CollatzResearch.WordTrace tailWord_436377 prefixEnd_436377 199174353393017250382795 := by
  unfold tailWord_436377
  simp only [CollatzResearch.WordTrace]
  refine ⟨15915976740088131103291385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10610651160058754068860923 15915976740088131103291385)
  ·
    refine ⟨11936982555066098327468539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15915976740088131103291385 11936982555066098327468539)
    ·
      refine ⟨17905473832599147491202809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11936982555066098327468539 17905473832599147491202809)
      ·
        refine ⟨13429105374449360618402107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17905473832599147491202809 13429105374449360618402107)
        ·
          refine ⟨20143658061674040927603161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13429105374449360618402107 20143658061674040927603161)
          ·
            refine ⟨15107743546255530695702371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20143658061674040927603161 15107743546255530695702371)
            ·
              refine ⟨22661615319383296043553557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15107743546255530695702371 22661615319383296043553557)
              ·
                refine ⟨1062263218096092002041573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22661615319383296043553557 1062263218096092002041573)
                ·
                  refine ⟨199174353393017250382795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1062263218096092002041573 199174353393017250382795)
                  ·
                    rfl

theorem cell20_436377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_436377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436377 prefixEnd_436377 := by exact prefixLift 436377
  have htrace : WordTrace (prefixWord ++ tailWord_436377) baseStart_436377 baseEnd_436377 := by
    simpa [prefixWord, tailWord_436377, baseEnd_436377] using wordTrace_append hprefix tailTrace_436377
  have hstable : (prefixWord ++ tailWord_436377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436377).length < 2 ^ (prefixWord ++ tailWord_436377).sum := by decide
  have hdescent : baseEnd_436377 < baseStart_436377 := by decide
  rcases family_descends (prefixWord ++ tailWord_436377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436401 : List Nat := [1, 2, 2, 5, 2, 8]
def baseStart_436401 : Nat := 118140960795 + 436401 * 2 ^ 59
def prefixEnd_436401 : Nat := 4983230072969 + 3 ^ 40 * 436401 * 2
def baseEnd_436401 : Nat := 7377233616554808651211

theorem tailTrace_436401 : CollatzResearch.WordTrace tailWord_436401 prefixEnd_436401 7377233616554808651211 := by
  unfold tailWord_436401
  simp only [CollatzResearch.WordTrace]
  refine ⟨15916852092001183202165057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10611234728000788801443371 15916852092001183202165057)
  ·
    refine ⟨11937639069000887401623793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15916852092001183202165057 11937639069000887401623793)
    ·
      refine ⟨8953229301750665551217845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11937639069000887401623793 8953229301750665551217845)
      ·
        refine ⟨839365247039124895426673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8953229301750665551217845 839365247039124895426673)
        ·
          refine ⟨629523935279343671570005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 839365247039124895426673 629523935279343671570005)
          ·
            refine ⟨7377233616554808651211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 629523935279343671570005 7377233616554808651211)
            ·
              rfl

theorem cell20_436401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 8].length) (baseStart_436401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436401 prefixEnd_436401 := by exact prefixLift 436401
  have htrace : WordTrace (prefixWord ++ tailWord_436401) baseStart_436401 baseEnd_436401 := by
    simpa [prefixWord, tailWord_436401, baseEnd_436401] using wordTrace_append hprefix tailTrace_436401
  have hstable : (prefixWord ++ tailWord_436401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436401).length < 2 ^ (prefixWord ++ tailWord_436401).sum := by decide
  have hdescent : baseEnd_436401 < baseStart_436401 := by decide
  rcases family_descends (prefixWord ++ tailWord_436401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436415 : List Nat := [1, 1, 2, 2, 2, 2, 1, 5, 4]
def baseStart_436415 : Nat := 118140960795 + 436415 * 2 ^ 59
def prefixEnd_436415 : Nat := 4983230072969 + 3 ^ 40 * 436415 * 2
def baseEnd_436415 : Nat := 199191697628458007115973

theorem tailTrace_436415 : CollatzResearch.WordTrace tailWord_436415 prefixEnd_436415 199191697628458007115973 := by
  unfold tailWord_436415
  simp only [CollatzResearch.WordTrace]
  refine ⟨15917362713950463593174699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10611575142633642395449799 15917362713950463593174699)
  ·
    refine ⟨23876044070925695389762049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15917362713950463593174699 23876044070925695389762049)
    ·
      refine ⟨17907033053194271542321537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23876044070925695389762049 17907033053194271542321537)
      ·
        refine ⟨13430274789895703656741153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17907033053194271542321537 13430274789895703656741153)
        ·
          refine ⟨10072706092421777742555865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13430274789895703656741153 10072706092421777742555865)
          ·
            refine ⟨7554529569316333306916899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10072706092421777742555865 7554529569316333306916899)
            ·
              refine ⟨11331794353974499960375349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7554529569316333306916899 11331794353974499960375349)
              ·
                refine ⟨1062355720685109371285189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11331794353974499960375349 1062355720685109371285189)
                ·
                  refine ⟨199191697628458007115973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1062355720685109371285189 199191697628458007115973)
                  ·
                    rfl

theorem cell20_436415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 4].length) (baseStart_436415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436415 prefixEnd_436415 := by exact prefixLift 436415
  have htrace : WordTrace (prefixWord ++ tailWord_436415) baseStart_436415 baseEnd_436415 := by
    simpa [prefixWord, tailWord_436415, baseEnd_436415] using wordTrace_append hprefix tailTrace_436415
  have hstable : (prefixWord ++ tailWord_436415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436415).length < 2 ^ (prefixWord ++ tailWord_436415).sum := by decide
  have hdescent : baseEnd_436415 < baseStart_436415 := by decide
  rcases family_descends (prefixWord ++ tailWord_436415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436449 : List Nat := [1, 2, 3, 1, 3, 1, 4, 3, 2]
def baseStart_436449 : Nat := 118140960795 + 436449 * 2 ^ 59
def prefixEnd_436449 : Nat := 4983230072969 + 3 ^ 40 * 436449 * 2
def baseEnd_436449 : Nat := 199207216154904999982501

theorem tailTrace_436449 : CollatzResearch.WordTrace tailWord_436449 prefixEnd_436449 199207216154904999982501 := by
  unfold tailWord_436449
  simp only [CollatzResearch.WordTrace]
  refine ⟨15918602795827287399912401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10612401863884858266608267 15918602795827287399912401)
  ·
    refine ⟨11938952096870465549934301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15918602795827287399912401 11938952096870465549934301)
    ·
      refine ⟨4477107036326424581225363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11938952096870465549934301 4477107036326424581225363)
      ·
        refine ⟨6715660554489636871838045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4477107036326424581225363 6715660554489636871838045)
        ·
          refine ⟨2518372707933613826939267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6715660554489636871838045 2518372707933613826939267)
          ·
            refine ⟨3777559061900420740408901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2518372707933613826939267 3777559061900420740408901)
            ·
              refine ⟨708292324106328888826669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3777559061900420740408901 708292324106328888826669)
              ·
                refine ⟨265609621539873333310001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 708292324106328888826669 265609621539873333310001)
                ·
                  refine ⟨199207216154904999982501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 265609621539873333310001 199207216154904999982501)
                  ·
                    rfl

theorem cell20_436449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 3, 2].length) (baseStart_436449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436449 prefixEnd_436449 := by exact prefixLift 436449
  have htrace : WordTrace (prefixWord ++ tailWord_436449) baseStart_436449 baseEnd_436449 := by
    simpa [prefixWord, tailWord_436449, baseEnd_436449] using wordTrace_append hprefix tailTrace_436449
  have hstable : (prefixWord ++ tailWord_436449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436449).length < 2 ^ (prefixWord ++ tailWord_436449).sum := by decide
  have hdescent : baseEnd_436449 < baseStart_436449 := by decide
  rcases family_descends (prefixWord ++ tailWord_436449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436460 : List Nat := [2, 2, 1, 1, 2, 3, 9]
def baseStart_436460 : Nat := 118140960795 + 436460 * 2 ^ 59
def prefixEnd_436460 : Nat := 4983230072969 + 3 ^ 40 * 436460 * 2
def baseEnd_436460 : Nat := 22134692983848650068421

theorem tailTrace_436460 : CollatzResearch.WordTrace tailWord_436460 prefixEnd_436460 22134692983848650068421 := by
  unfold tailWord_436460
  simp only [CollatzResearch.WordTrace]
  refine ⟨7959501999393718139281417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10612669332524957519041889 7959501999393718139281417)
  ·
    refine ⟨5969626499545288604461063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7959501999393718139281417 5969626499545288604461063)
    ·
      refine ⟨8954439749317932906691595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5969626499545288604461063 8954439749317932906691595)
      ·
        refine ⟨13431659623976899360037393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8954439749317932906691595 13431659623976899360037393)
        ·
          refine ⟨10073744717982674520028045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13431659623976899360037393 10073744717982674520028045)
          ·
            refine ⟨3777654269243502945010517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10073744717982674520028045 3777654269243502945010517)
            ·
              refine ⟨22134692983848650068421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3777654269243502945010517 22134692983848650068421)
              ·
                rfl

theorem cell20_436460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 9].length) (baseStart_436460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436460 prefixEnd_436460 := by exact prefixLift 436460
  have htrace : WordTrace (prefixWord ++ tailWord_436460) baseStart_436460 baseEnd_436460 := by
    simpa [prefixWord, tailWord_436460, baseEnd_436460] using wordTrace_append hprefix tailTrace_436460
  have hstable : (prefixWord ++ tailWord_436460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436460).length < 2 ^ (prefixWord ++ tailWord_436460).sum := by decide
  have hdescent : baseEnd_436460 < baseStart_436460 := by decide
  rcases family_descends (prefixWord ++ tailWord_436460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436463 : List Nat := [1, 1, 2, 1, 6, 1, 3, 2, 3]
def baseStart_436463 : Nat := 118140960795 + 436463 * 2 ^ 59
def prefixEnd_436463 : Nat := 4983230072969 + 3 ^ 40 * 436463 * 2
def baseEnd_436463 : Nat := 199213606136383173515777

theorem tailTrace_436463 : CollatzResearch.WordTrace tailWord_436463 prefixEnd_436463 199213606136383173515777 := by
  unfold tailWord_436463
  simp only [CollatzResearch.WordTrace]
  refine ⟨15919113417776567790922043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10612742278517711860614695 15919113417776567790922043)
  ·
    refine ⟨23878670126664851686383065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15919113417776567790922043 23878670126664851686383065)
    ·
      refine ⟨17909002594998638764787299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23878670126664851686383065 17909002594998638764787299)
      ·
        refine ⟨26863503892497958147180949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17909002594998638764787299 26863503892497958147180949)
        ·
          refine ⟨1259226744960841788149107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 26863503892497958147180949 1259226744960841788149107)
          ·
            refine ⟨1888840117441262682223661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1259226744960841788149107 1888840117441262682223661)
            ·
              refine ⟨708315044040473505833873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1888840117441262682223661 708315044040473505833873)
              ·
                refine ⟨531236283030355129375405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 708315044040473505833873 531236283030355129375405)
                ·
                  refine ⟨199213606136383173515777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 531236283030355129375405 199213606136383173515777)
                  ·
                    rfl

theorem cell20_436463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 3].length) (baseStart_436463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436463 prefixEnd_436463 := by exact prefixLift 436463
  have htrace : WordTrace (prefixWord ++ tailWord_436463) baseStart_436463 baseEnd_436463 := by
    simpa [prefixWord, tailWord_436463, baseEnd_436463] using wordTrace_append hprefix tailTrace_436463
  have hstable : (prefixWord ++ tailWord_436463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436463).length < 2 ^ (prefixWord ++ tailWord_436463).sum := by decide
  have hdescent : baseEnd_436463 < baseStart_436463 := by decide
  rcases family_descends (prefixWord ++ tailWord_436463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436470 : List Nat := [5, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_436470 : Nat := 118140960795 + 436470 * 2 ^ 59
def prefixEnd_436470 : Nat := 4983230072969 + 3 ^ 40 * 436470 * 2
def baseEnd_436470 : Nat := 199216801127122260282415

theorem tailTrace_436470 : CollatzResearch.WordTrace tailWord_436470 prefixEnd_436470 199216801127122260282415 := by
  unfold tailWord_436470
  simp only [CollatzResearch.WordTrace]
  refine ⟨994960545546950499151679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10612912485834138657617909 994960545546950499151679)
  ·
    refine ⟨1492440818320425748727519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 994960545546950499151679 1492440818320425748727519)
    ·
      refine ⟨2238661227480638623091279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1492440818320425748727519 2238661227480638623091279)
      ·
        refine ⟨3357991841220957934636919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2238661227480638623091279 3357991841220957934636919)
        ·
          refine ⟨5036987761831436901955379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3357991841220957934636919 5036987761831436901955379)
          ·
            refine ⟨7555481642747155352933069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5036987761831436901955379 7555481642747155352933069)
            ·
              refine ⟨2833305616030183257349901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7555481642747155352933069 2833305616030183257349901)
              ·
                refine ⟨1062489606011318721506213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2833305616030183257349901 1062489606011318721506213)
                ·
                  refine ⟨199216801127122260282415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1062489606011318721506213 199216801127122260282415)
                  ·
                    rfl

theorem cell20_436470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_436470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436470 prefixEnd_436470 := by exact prefixLift 436470
  have htrace : WordTrace (prefixWord ++ tailWord_436470) baseStart_436470 baseEnd_436470 := by
    simpa [prefixWord, tailWord_436470, baseEnd_436470] using wordTrace_append hprefix tailTrace_436470
  have hstable : (prefixWord ++ tailWord_436470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436470).length < 2 ^ (prefixWord ++ tailWord_436470).sum := by decide
  have hdescent : baseEnd_436470 < baseStart_436470 := by decide
  rcases family_descends (prefixWord ++ tailWord_436470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436491 : List Nat := [1, 1, 1, 1, 5, 2, 1, 4, 4]
def baseStart_436491 : Nat := 118140960795 + 436491 * 2 ^ 59
def prefixEnd_436491 : Nat := 4983230072969 + 3 ^ 40 * 436491 * 2
def baseEnd_436491 : Nat := 199226386099339520582329

theorem tailTrace_436491 : CollatzResearch.WordTrace tailWord_436491 prefixEnd_436491 199226386099339520582329 := by
  unfold tailWord_436491
  simp only [CollatzResearch.WordTrace]
  refine ⟨15920134661675128572941327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10613423107783419048627551 15920134661675128572941327)
  ·
    refine ⟨23880201992512692859411991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15920134661675128572941327 23880201992512692859411991)
    ·
      refine ⟨35820302988769039289117987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23880201992512692859411991 35820302988769039289117987)
      ·
        refine ⟨53730454483153558933676981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35820302988769039289117987 53730454483153558933676981)
        ·
          refine ⟨5037230107795646150032217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53730454483153558933676981 5037230107795646150032217)
          ·
            refine ⟨3777922580846734612524163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5037230107795646150032217 3777922580846734612524163)
            ·
              refine ⟨5666883871270101918786245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3777922580846734612524163 5666883871270101918786245)
              ·
                refine ⟨1062540725863144109772421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5666883871270101918786245 1062540725863144109772421)
                ·
                  refine ⟨199226386099339520582329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1062540725863144109772421 199226386099339520582329)
                  ·
                    rfl

theorem cell20_436491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 4].length) (baseStart_436491 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436491 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436491 prefixEnd_436491 := by exact prefixLift 436491
  have htrace : WordTrace (prefixWord ++ tailWord_436491) baseStart_436491 baseEnd_436491 := by
    simpa [prefixWord, tailWord_436491, baseEnd_436491] using wordTrace_append hprefix tailTrace_436491
  have hstable : (prefixWord ++ tailWord_436491).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436491).length < 2 ^ (prefixWord ++ tailWord_436491).sum := by decide
  have hdescent : baseEnd_436491 < baseStart_436491 := by decide
  rcases family_descends (prefixWord ++ tailWord_436491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436532 : List Nat := [2, 5, 1, 1, 1, 3, 2, 5]
def baseStart_436532 : Nat := 118140960795 + 436532 * 2 ^ 59
def prefixEnd_436532 : Nat := 4983230072969 + 3 ^ 40 * 436532 * 2
def baseEnd_436532 : Nat := 66415033205508533405165

theorem tailTrace_436532 : CollatzResearch.WordTrace tailWord_436532 prefixEnd_436532 66415033205508533405165 := by
  unfold tailWord_436532
  simp only [CollatzResearch.WordTrace]
  refine ⟨7960815027263296287591925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10614420036351061716789233 7960815027263296287591925)
  ·
    refine ⟨746326408805934026961743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7960815027263296287591925 746326408805934026961743)
    ·
      refine ⟨1119489613208901040442615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 746326408805934026961743 1119489613208901040442615)
      ·
        refine ⟨1679234419813351560663923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1119489613208901040442615 1679234419813351560663923)
        ·
          refine ⟨2518851629720027340995885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1679234419813351560663923 2518851629720027340995885)
          ·
            refine ⟨944569361145010252873457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2518851629720027340995885 944569361145010252873457)
            ·
              refine ⟨708427020858757689655093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 944569361145010252873457 708427020858757689655093)
              ·
                refine ⟨66415033205508533405165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 708427020858757689655093 66415033205508533405165)
                ·
                  rfl

theorem cell20_436532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 5].length) (baseStart_436532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436532 prefixEnd_436532 := by exact prefixLift 436532
  have htrace : WordTrace (prefixWord ++ tailWord_436532) baseStart_436532 baseEnd_436532 := by
    simpa [prefixWord, tailWord_436532, baseEnd_436532] using wordTrace_append hprefix tailTrace_436532
  have hstable : (prefixWord ++ tailWord_436532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436532).length < 2 ^ (prefixWord ++ tailWord_436532).sum := by decide
  have hdescent : baseEnd_436532 < baseStart_436532 := by decide
  rcases family_descends (prefixWord ++ tailWord_436532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436536 : List Nat := [2, 1, 2, 1, 3, 1, 3, 7]
def baseStart_436536 : Nat := 118140960795 + 436536 * 2 ^ 59
def prefixEnd_436536 : Nat := 4983230072969 + 3 ^ 40 * 436536 * 2
def baseEnd_436536 : Nat := 66415641775173121360715

theorem tailTrace_436536 : CollatzResearch.WordTrace tailWord_436536 prefixEnd_436536 66415641775173121360715 := by
  unfold tailWord_436536
  simp only [CollatzResearch.WordTrace]
  refine ⟨7960887973256050629164731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10614517297674734172219641 7960887973256050629164731)
  ·
    refine ⟨11941331959884075943747097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7960887973256050629164731 11941331959884075943747097)
    ·
      refine ⟨8955998969913056957810323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11941331959884075943747097 8955998969913056957810323)
      ·
        refine ⟨13433998454869585436715485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8955998969913056957810323 13433998454869585436715485)
        ·
          refine ⟨5037749420576094538768307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13433998454869585436715485 5037749420576094538768307)
          ·
            refine ⟨7556624130864141808152461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5037749420576094538768307 7556624130864141808152461)
            ·
              refine ⟨2833734049074053178057173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7556624130864141808152461 2833734049074053178057173)
              ·
                refine ⟨66415641775173121360715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2833734049074053178057173 66415641775173121360715)
                ·
                  rfl

theorem cell20_436536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 7].length) (baseStart_436536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436536 prefixEnd_436536 := by exact prefixLift 436536
  have htrace : WordTrace (prefixWord ++ tailWord_436536) baseStart_436536 baseEnd_436536 := by
    simpa [prefixWord, tailWord_436536, baseEnd_436536] using wordTrace_append hprefix tailTrace_436536
  have hstable : (prefixWord ++ tailWord_436536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436536).length < 2 ^ (prefixWord ++ tailWord_436536).sum := by decide
  have hdescent : baseEnd_436536 < baseStart_436536 := by decide
  rcases family_descends (prefixWord ++ tailWord_436536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436605 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 6]
def baseStart_436605 : Nat := 118140960795 + 436605 * 2 ^ 59
def prefixEnd_436605 : Nat := 4983230072969 + 3 ^ 40 * 436605 * 2
def baseEnd_436605 : Nat := 199278418805661790781863

theorem tailTrace_436605 : CollatzResearch.WordTrace tailWord_436605 prefixEnd_436605 199278418805661790781863 := by
  unfold tailWord_436605
  simp only [CollatzResearch.WordTrace]
  refine ⟨15924292583262126042591269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10616195055508084028394179 15924292583262126042591269)
  ·
    refine ⟨2985804859361648632985863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15924292583262126042591269 2985804859361648632985863)
    ·
      refine ⟨4478707289042472949478795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2985804859361648632985863 4478707289042472949478795)
      ·
        refine ⟨6718060933563709424218193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4478707289042472949478795 6718060933563709424218193)
        ·
          refine ⟨5038545700172782068163645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6718060933563709424218193 5038545700172782068163645)
          ·
            refine ⟨1889454637564793275561367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5038545700172782068163645 1889454637564793275561367)
            ·
              refine ⟨2834181956347189913342051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1889454637564793275561367 2834181956347189913342051)
              ·
                refine ⟨4251272934520784870013077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2834181956347189913342051 4251272934520784870013077)
                ·
                  refine ⟨199278418805661790781863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4251272934520784870013077 199278418805661790781863)
                  ·
                    rfl

theorem cell20_436605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_436605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436605 prefixEnd_436605 := by exact prefixLift 436605
  have htrace : WordTrace (prefixWord ++ tailWord_436605) baseStart_436605 baseEnd_436605 := by
    simpa [prefixWord, tailWord_436605, baseEnd_436605] using wordTrace_append hprefix tailTrace_436605
  have hstable : (prefixWord ++ tailWord_436605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436605).length < 2 ^ (prefixWord ++ tailWord_436605).sum := by decide
  have hdescent : baseEnd_436605 < baseStart_436605 := by decide
  rcases family_descends (prefixWord ++ tailWord_436605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436632 : List Nat := [2, 1, 2, 5, 1, 3, 1, 2, 3]
def baseStart_436632 : Nat := 118140960795 + 436632 * 2 ^ 59
def prefixEnd_436632 : Nat := 4983230072969 + 3 ^ 40 * 436632 * 2
def baseEnd_436632 : Nat := 199290742341369696881753

theorem tailTrace_436632 : CollatzResearch.WordTrace tailWord_436632 prefixEnd_436632 199290742341369696881753 := by
  unfold tailWord_436632
  simp only [CollatzResearch.WordTrace]
  refine ⟨7962638677082154826912075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10616851569442873102549433 7962638677082154826912075)
  ·
    refine ⟨11943958015623232240368113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7962638677082154826912075 11943958015623232240368113)
    ·
      refine ⟨8957968511717424180276085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11943958015623232240368113 8957968511717424180276085)
      ·
        refine ⟨839809547973508516900883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8957968511717424180276085 839809547973508516900883)
        ·
          refine ⟨1259714321960262775351325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 839809547973508516900883 1259714321960262775351325)
          ·
            refine ⟨472392870735098540756747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1259714321960262775351325 472392870735098540756747)
            ·
              refine ⟨708589306102647811135121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472392870735098540756747 708589306102647811135121)
              ·
                refine ⟨531441979576985858351341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 708589306102647811135121 531441979576985858351341)
                ·
                  refine ⟨199290742341369696881753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 531441979576985858351341 199290742341369696881753)
                  ·
                    rfl

theorem cell20_436632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 3].length) (baseStart_436632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436632 prefixEnd_436632 := by exact prefixLift 436632
  have htrace : WordTrace (prefixWord ++ tailWord_436632) baseStart_436632 baseEnd_436632 := by
    simpa [prefixWord, tailWord_436632, baseEnd_436632] using wordTrace_append hprefix tailTrace_436632
  have hstable : (prefixWord ++ tailWord_436632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436632).length < 2 ^ (prefixWord ++ tailWord_436632).sum := by decide
  have hdescent : baseEnd_436632 < baseStart_436632 := by decide
  rcases family_descends (prefixWord ++ tailWord_436632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436643 : List Nat := [1, 1, 1, 4, 1, 4, 1, 3, 4]
def baseStart_436643 : Nat := 118140960795 + 436643 * 2 ^ 59
def prefixEnd_436643 : Nat := 4983230072969 + 3 ^ 40 * 436643 * 2
def baseEnd_436643 : Nat := 199295763041102547515041

theorem tailTrace_436643 : CollatzResearch.WordTrace tailWord_436643 prefixEnd_436643 199295763041102547515041 := by
  unfold tailWord_436643
  simp only [CollatzResearch.WordTrace]
  refine ⟨15925678557124458532474583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10617119038082972354983055 15925678557124458532474583)
  ·
    refine ⟨23888517835686687798711875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15925678557124458532474583 23888517835686687798711875)
    ·
      refine ⟨35832776753530031698067813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23888517835686687798711875 35832776753530031698067813)
      ·
        refine ⟨6718645641286880943387715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35832776753530031698067813 6718645641286880943387715)
        ·
          refine ⟨10077968461930321415081573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6718645641286880943387715 10077968461930321415081573)
          ·
            refine ⟨1889619086611935265327795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10077968461930321415081573 1889619086611935265327795)
            ·
              refine ⟨2834428629917902897991693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1889619086611935265327795 2834428629917902897991693)
              ·
                refine ⟨1062910736219213586746885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2834428629917902897991693 1062910736219213586746885)
                ·
                  refine ⟨199295763041102547515041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1062910736219213586746885 199295763041102547515041)
                  ·
                    rfl

theorem cell20_436643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 4].length) (baseStart_436643 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436643 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436643 prefixEnd_436643 := by exact prefixLift 436643
  have htrace : WordTrace (prefixWord ++ tailWord_436643) baseStart_436643 baseEnd_436643 := by
    simpa [prefixWord, tailWord_436643, baseEnd_436643] using wordTrace_append hprefix tailTrace_436643
  have hstable : (prefixWord ++ tailWord_436643).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436643).length < 2 ^ (prefixWord ++ tailWord_436643).sum := by decide
  have hdescent : baseEnd_436643 < baseStart_436643 := by decide
  rcases family_descends (prefixWord ++ tailWord_436643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436684 : List Nat := [2, 2, 1, 4, 4, 1, 6]
def baseStart_436684 : Nat := 118140960795 + 436684 * 2 ^ 59
def prefixEnd_436684 : Nat := 4983230072969 + 3 ^ 40 * 436684 * 2
def baseEnd_436684 : Nat := 22146052950920958572023

theorem tailTrace_436684 : CollatzResearch.WordTrace tailWord_436684 prefixEnd_436684 22146052950920958572023 := by
  unfold tailWord_436684
  simp only [CollatzResearch.WordTrace]
  refine ⟨7963586974987961267358553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10618115966650615023144737 7963586974987961267358553)
  ·
    refine ⟨5972690231240970950518915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7963586974987961267358553 5972690231240970950518915)
    ·
      refine ⟨8959035346861456425778373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5972690231240970950518915 8959035346861456425778373)
      ·
        refine ⟨1679819127536523079833445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8959035346861456425778373 1679819127536523079833445)
        ·
          refine ⟨314966086413098077468771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1679819127536523079833445 314966086413098077468771)
          ·
            refine ⟨472449129619647116203157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314966086413098077468771 472449129619647116203157)
            ·
              refine ⟨22146052950920958572023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 472449129619647116203157 22146052950920958572023)
              ·
                rfl

theorem cell20_436684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 6].length) (baseStart_436684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436684 prefixEnd_436684 := by exact prefixLift 436684
  have htrace : WordTrace (prefixWord ++ tailWord_436684) baseStart_436684 baseEnd_436684 := by
    simpa [prefixWord, tailWord_436684, baseEnd_436684] using wordTrace_append hprefix tailTrace_436684
  have hstable : (prefixWord ++ tailWord_436684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436684).length < 2 ^ (prefixWord ++ tailWord_436684).sum := by decide
  have hdescent : baseEnd_436684 < baseStart_436684 := by decide
  rcases family_descends (prefixWord ++ tailWord_436684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436742 : List Nat := [6, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_436742 : Nat := 118140960795 + 436742 * 2 ^ 59
def prefixEnd_436742 : Nat := 4983230072969 + 3 ^ 40 * 436742 * 2
def baseEnd_436742 : Nat := 199340949338698203214637

theorem tailTrace_436742 : CollatzResearch.WordTrace tailWord_436742 prefixEnd_436742 199340949338698203214637 := by
  unfold tailWord_436742
  simp only [CollatzResearch.WordTrace]
  refine ⟨497790293242681201260265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10619526255843865626885653 497790293242681201260265)
  ·
    refine ⟨373342719932010900945199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 497790293242681201260265 373342719932010900945199)
    ·
      refine ⟨560014079898016351417799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373342719932010900945199 560014079898016351417799)
      ·
        refine ⟨840021119847024527126699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560014079898016351417799 840021119847024527126699)
        ·
          refine ⟨1260031679770536790690049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 840021119847024527126699 1260031679770536790690049)
          ·
            refine ⟨945023759827902593017537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1260031679770536790690049 945023759827902593017537)
            ·
              refine ⟨708767819870926944763153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 945023759827902593017537 708767819870926944763153)
              ·
                refine ⟨531575864903195208572365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 708767819870926944763153 531575864903195208572365)
                ·
                  refine ⟨199340949338698203214637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 531575864903195208572365 199340949338698203214637)
                  ·
                    rfl

theorem cell20_436742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_436742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436742 prefixEnd_436742 := by exact prefixLift 436742
  have htrace : WordTrace (prefixWord ++ tailWord_436742) baseStart_436742 baseEnd_436742 := by
    simpa [prefixWord, tailWord_436742, baseEnd_436742] using wordTrace_append hprefix tailTrace_436742
  have hstable : (prefixWord ++ tailWord_436742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436742).length < 2 ^ (prefixWord ++ tailWord_436742).sum := by decide
  have hdescent : baseEnd_436742 < baseStart_436742 := by decide
  rcases family_descends (prefixWord ++ tailWord_436742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436743 : List Nat := [1, 1, 4, 3, 4, 7]
def baseStart_436743 : Nat := 118140960795 + 436743 * 2 ^ 59
def prefixEnd_436743 : Nat := 4983230072969 + 3 ^ 40 * 436743 * 2
def baseEnd_436743 : Nat := 7383015028368394228937

theorem tailTrace_436743 : CollatzResearch.WordTrace tailWord_436743 prefixEnd_436743 7383015028368394228937 := by
  unfold tailWord_436743
  simp only [CollatzResearch.WordTrace]
  refine ⟨15929325856762175611114883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10619550571174783740743255 15929325856762175611114883)
  ·
    refine ⟨23893988785143263416672325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15929325856762175611114883 23893988785143263416672325)
    ·
      refine ⟨4480122897214361890626061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23893988785143263416672325 4480122897214361890626061)
      ·
        refine ⟨1680046086455385708984773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4480122897214361890626061 1680046086455385708984773)
        ·
          refine ⟨315008641210384820434645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1680046086455385708984773 315008641210384820434645)
          ·
            refine ⟨7383015028368394228937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 315008641210384820434645 7383015028368394228937)
            ·
              rfl

theorem cell20_436743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 7].length) (baseStart_436743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436743 prefixEnd_436743 := by exact prefixLift 436743
  have htrace : WordTrace (prefixWord ++ tailWord_436743) baseStart_436743 baseEnd_436743 := by
    simpa [prefixWord, tailWord_436743, baseEnd_436743] using wordTrace_append hprefix tailTrace_436743
  have hstable : (prefixWord ++ tailWord_436743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436743).length < 2 ^ (prefixWord ++ tailWord_436743).sum := by decide
  have hdescent : baseEnd_436743 < baseStart_436743 := by decide
  rcases family_descends (prefixWord ++ tailWord_436743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436749 : List Nat := [1, 7, 1, 1, 1, 2, 1, 4, 2]
def baseStart_436749 : Nat := 118140960795 + 436749 * 2 ^ 59
def prefixEnd_436749 : Nat := 4983230072969 + 3 ^ 40 * 436749 * 2
def baseEnd_436749 : Nat := 199344144329437289981275

theorem tailTrace_436749 : CollatzResearch.WordTrace tailWord_436749 prefixEnd_436749 199344144329437289981275 := by
  unfold tailWord_436749
  simp only [CollatzResearch.WordTrace]
  refine ⟨15929544694740438635833301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10619696463160292423888867 15929544694740438635833301)
  ·
    refine ⟨373348703782979030527343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 15929544694740438635833301 373348703782979030527343)
    ·
      refine ⟨560023055674468545791015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373348703782979030527343 560023055674468545791015)
      ·
        refine ⟨840034583511702818686523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560023055674468545791015 840034583511702818686523)
        ·
          refine ⟨1260051875267554228029785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 840034583511702818686523 1260051875267554228029785)
          ·
            refine ⟨945038906450665671022339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1260051875267554228029785 945038906450665671022339)
            ·
              refine ⟨1417558359675998506533509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 945038906450665671022339 1417558359675998506533509)
              ·
                refine ⟨265792192439249719975033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1417558359675998506533509 265792192439249719975033)
                ·
                  refine ⟨199344144329437289981275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 265792192439249719975033 199344144329437289981275)
                  ·
                    rfl

theorem cell20_436749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_436749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436749 prefixEnd_436749 := by exact prefixLift 436749
  have htrace : WordTrace (prefixWord ++ tailWord_436749) baseStart_436749 baseEnd_436749 := by
    simpa [prefixWord, tailWord_436749, baseEnd_436749] using wordTrace_append hprefix tailTrace_436749
  have hstable : (prefixWord ++ tailWord_436749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436749).length < 2 ^ (prefixWord ++ tailWord_436749).sum := by decide
  have hdescent : baseEnd_436749 < baseStart_436749 := by decide
  rcases family_descends (prefixWord ++ tailWord_436749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436757 : List Nat := [1, 3, 2, 1, 3, 1, 2, 3, 4]
def baseStart_436757 : Nat := 118140960795 + 436757 * 2 ^ 59
def prefixEnd_436757 : Nat := 4983230072969 + 3 ^ 40 * 436757 * 2
def baseEnd_436757 : Nat := 199347795747424817714575

theorem tailTrace_436757 : CollatzResearch.WordTrace tailWord_436757 prefixEnd_436757 199347795747424817714575 := by
  unfold tailWord_436757
  simp only [CollatzResearch.WordTrace]
  refine ⟨15929836478711456002124525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10619890985807637334749683 15929836478711456002124525)
  ·
    refine ⟨5973688679516796000796697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15929836478711456002124525 5973688679516796000796697)
    ·
      refine ⟨4480266509637597000597523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5973688679516796000796697 4480266509637597000597523)
      ·
        refine ⟨6720399764456395500896285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4480266509637597000597523 6720399764456395500896285)
        ·
          refine ⟨2520149911671148312836107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6720399764456395500896285 2520149911671148312836107)
          ·
            refine ⟨3780224867506722469254161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2520149911671148312836107 3780224867506722469254161)
            ·
              refine ⟨2835168650630041851940621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3780224867506722469254161 2835168650630041851940621)
              ·
                refine ⟨1063188243986265694477733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2835168650630041851940621 1063188243986265694477733)
                ·
                  refine ⟨199347795747424817714575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1063188243986265694477733 199347795747424817714575)
                  ·
                    rfl

theorem cell20_436757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_436757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436757 prefixEnd_436757 := by exact prefixLift 436757
  have htrace : WordTrace (prefixWord ++ tailWord_436757) baseStart_436757 baseEnd_436757 := by
    simpa [prefixWord, tailWord_436757, baseEnd_436757] using wordTrace_append hprefix tailTrace_436757
  have hstable : (prefixWord ++ tailWord_436757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436757).length < 2 ^ (prefixWord ++ tailWord_436757).sum := by decide
  have hdescent : baseEnd_436757 < baseStart_436757 := by decide
  rcases family_descends (prefixWord ++ tailWord_436757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436798 : List Nat := [4, 2, 1, 4, 1, 1, 7]
def baseStart_436798 : Nat := 118140960795 + 436798 * 2 ^ 59
def prefixEnd_436798 : Nat := 4983230072969 + 3 ^ 40 * 436798 * 2
def baseEnd_436798 : Nat := 22151834362734544149749

theorem tailTrace_436798 : CollatzResearch.WordTrace tailWord_436798 prefixEnd_436798 22151834362734544149749 := by
  unfold tailWord_436798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1991416483945365000545881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10620887914375280002911365 1991416483945365000545881)
  ·
    refine ⟨1493562362959023750409411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1991416483945365000545881 1493562362959023750409411)
    ·
      refine ⟨2240343544438535625614117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1493562362959023750409411 2240343544438535625614117)
      ·
        refine ⟨420064414582225429802647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2240343544438535625614117 420064414582225429802647)
        ·
          refine ⟨630096621873338144703971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420064414582225429802647 630096621873338144703971)
          ·
            refine ⟨945144932810007217055957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 630096621873338144703971 945144932810007217055957)
            ·
              refine ⟨22151834362734544149749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 945144932810007217055957 22151834362734544149749)
              ·
                rfl

theorem cell20_436798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 7].length) (baseStart_436798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436798 prefixEnd_436798 := by exact prefixLift 436798
  have htrace : WordTrace (prefixWord ++ tailWord_436798) baseStart_436798 baseEnd_436798 := by
    simpa [prefixWord, tailWord_436798, baseEnd_436798] using wordTrace_append hprefix tailTrace_436798
  have hstable : (prefixWord ++ tailWord_436798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436798).length < 2 ^ (prefixWord ++ tailWord_436798).sum := by decide
  have hdescent : baseEnd_436798 < baseStart_436798 := by decide
  rcases family_descends (prefixWord ++ tailWord_436798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436805 : List Nat := [1, 3, 1, 1, 1, 7, 1, 2, 3]
def baseStart_436805 : Nat := 118140960795 + 436805 * 2 ^ 59
def prefixEnd_436805 : Nat := 4983230072969 + 3 ^ 40 * 436805 * 2
def baseEnd_436805 : Nat := 199369704255349984114379

theorem tailTrace_436805 : CollatzResearch.WordTrace tailWord_436805 prefixEnd_436805 199369704255349984114379 := by
  unfold tailWord_436805
  simp only [CollatzResearch.WordTrace]
  refine ⟨15931587182537560199871869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10621058121691706799914579 15931587182537560199871869)
  ·
    refine ⟨5974345193451585074951951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15931587182537560199871869 5974345193451585074951951)
    ·
      refine ⟨8961517790177377612427927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5974345193451585074951951 8961517790177377612427927)
      ·
        refine ⟨13442276685266066418641891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8961517790177377612427927 13442276685266066418641891)
        ·
          refine ⟨20163415027899099627962837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13442276685266066418641891 20163415027899099627962837)
          ·
            refine ⟨472580039716385147530379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 20163415027899099627962837 472580039716385147530379)
            ·
              refine ⟨708870059574577721295569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472580039716385147530379 708870059574577721295569)
              ·
                refine ⟨531652544680933290971677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 708870059574577721295569 531652544680933290971677)
                ·
                  refine ⟨199369704255349984114379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 531652544680933290971677 199369704255349984114379)
                  ·
                    rfl

theorem cell20_436805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_436805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436805 prefixEnd_436805 := by exact prefixLift 436805
  have htrace : WordTrace (prefixWord ++ tailWord_436805) baseStart_436805 baseEnd_436805 := by
    simpa [prefixWord, tailWord_436805, baseEnd_436805] using wordTrace_append hprefix tailTrace_436805
  have hstable : (prefixWord ++ tailWord_436805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436805).length < 2 ^ (prefixWord ++ tailWord_436805).sum := by decide
  have hdescent : baseEnd_436805 < baseStart_436805 := by decide
  rcases family_descends (prefixWord ++ tailWord_436805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436812 : List Nat := [2, 2, 1, 3, 1, 2, 1, 6, 2]
def baseStart_436812 : Nat := 118140960795 + 436812 * 2 ^ 59
def prefixEnd_436812 : Nat := 4983230072969 + 3 ^ 40 * 436812 * 2
def baseEnd_436812 : Nat := 199372899246089070881017

theorem tailTrace_436812 : CollatzResearch.WordTrace tailWord_436812 prefixEnd_436812 199372899246089070881017 := by
  unfold tailWord_436812
  simp only [CollatzResearch.WordTrace]
  refine ⟨7965921246756100197688345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10621228329008133596917793 7965921246756100197688345)
  ·
    refine ⟨5974440935067075148266259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7965921246756100197688345 5974440935067075148266259)
    ·
      refine ⟨8961661402600612722399389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5974440935067075148266259 8961661402600612722399389)
      ·
        refine ⟨3360623025975229770899771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8961661402600612722399389 3360623025975229770899771)
        ·
          refine ⟨5040934538962844656349657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3360623025975229770899771 5040934538962844656349657)
          ·
            refine ⟨3780700904222133492262243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5040934538962844656349657 3780700904222133492262243)
            ·
              refine ⟨5671051356333200238393365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3780700904222133492262243 5671051356333200238393365)
              ·
                refine ⟨265830532328118761174689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5671051356333200238393365 265830532328118761174689)
                ·
                  refine ⟨199372899246089070881017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 265830532328118761174689 199372899246089070881017)
                  ·
                    rfl

theorem cell20_436812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 6, 2].length) (baseStart_436812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436812 prefixEnd_436812 := by exact prefixLift 436812
  have htrace : WordTrace (prefixWord ++ tailWord_436812) baseStart_436812 baseEnd_436812 := by
    simpa [prefixWord, tailWord_436812, baseEnd_436812] using wordTrace_append hprefix tailTrace_436812
  have hstable : (prefixWord ++ tailWord_436812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436812).length < 2 ^ (prefixWord ++ tailWord_436812).sum := by decide
  have hdescent : baseEnd_436812 < baseStart_436812 := by decide
  rcases family_descends (prefixWord ++ tailWord_436812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436833 : List Nat := [1, 2, 3, 1, 1, 4, 2, 2, 4]
def baseStart_436833 : Nat := 118140960795 + 436833 * 2 ^ 59
def prefixEnd_436833 : Nat := 4983230072969 + 3 ^ 40 * 436833 * 2
def baseEnd_436833 : Nat := 199382484218306331180931

theorem tailTrace_436833 : CollatzResearch.WordTrace tailWord_436833 prefixEnd_436833 199382484218306331180931 := by
  unfold tailWord_436833
  simp only [CollatzResearch.WordTrace]
  refine ⟨15932608426436120981891153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10621738950957413987927435 15932608426436120981891153)
  ·
    refine ⟨11949456319827090736418365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15932608426436120981891153 11949456319827090736418365)
    ·
      refine ⟨4481046119935159026156887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11949456319827090736418365 4481046119935159026156887)
      ·
        refine ⟨6721569179902738539235331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4481046119935159026156887 6721569179902738539235331)
        ·
          refine ⟨10082353769854107808852997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6721569179902738539235331 10082353769854107808852997)
          ·
            refine ⟨1890441331847645214159937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10082353769854107808852997 1890441331847645214159937)
            ·
              refine ⟨1417830998885733910619953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1890441331847645214159937 1417830998885733910619953)
              ·
                refine ⟨1063373249164300432964965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1417830998885733910619953 1063373249164300432964965)
                ·
                  refine ⟨199382484218306331180931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1063373249164300432964965 199382484218306331180931)
                  ·
                    rfl

theorem cell20_436833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_436833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436833 prefixEnd_436833 := by exact prefixLift 436833
  have htrace : WordTrace (prefixWord ++ tailWord_436833) baseStart_436833 baseEnd_436833 := by
    simpa [prefixWord, tailWord_436833, baseEnd_436833] using wordTrace_append hprefix tailTrace_436833
  have hstable : (prefixWord ++ tailWord_436833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436833).length < 2 ^ (prefixWord ++ tailWord_436833).sum := by decide
  have hdescent : baseEnd_436833 < baseStart_436833 := by decide
  rcases family_descends (prefixWord ++ tailWord_436833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436846 : List Nat := [4, 1, 2, 2, 2, 3, 1, 3, 2]
def baseStart_436846 : Nat := 118140960795 + 436846 * 2 ^ 59
def prefixEnd_436846 : Nat := 4983230072969 + 3 ^ 40 * 436846 * 2
def baseEnd_436846 : Nat := 199388417772536063747545

theorem tailTrace_436846 : CollatzResearch.WordTrace tailWord_436846 prefixEnd_436846 199388417772536063747545 := by
  unfold tailWord_436846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1991635321923628025264299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10622055050259349468076261 1991635321923628025264299)
  ·
    refine ⟨2987452982885442037896449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1991635321923628025264299 2987452982885442037896449)
    ·
      refine ⟨2240589737164081528422337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2987452982885442037896449 2240589737164081528422337)
      ·
        refine ⟨1680442302873061146316753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2240589737164081528422337 1680442302873061146316753)
        ·
          refine ⟨1260331727154795859737565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1680442302873061146316753 1260331727154795859737565)
          ·
            refine ⟨472624397683048447401587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1260331727154795859737565 472624397683048447401587)
            ·
              refine ⟨708936596524572671102381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472624397683048447401587 708936596524572671102381)
              ·
                refine ⟨265851223696714751663393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 708936596524572671102381 265851223696714751663393)
                ·
                  refine ⟨199388417772536063747545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 265851223696714751663393 199388417772536063747545)
                  ·
                    rfl

theorem cell20_436846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_436846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436846 prefixEnd_436846 := by exact prefixLift 436846
  have htrace : WordTrace (prefixWord ++ tailWord_436846) baseStart_436846 baseEnd_436846 := by
    simpa [prefixWord, tailWord_436846, baseEnd_436846] using wordTrace_append hprefix tailTrace_436846
  have hstable : (prefixWord ++ tailWord_436846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436846).length < 2 ^ (prefixWord ++ tailWord_436846).sum := by decide
  have hdescent : baseEnd_436846 < baseStart_436846 := by decide
  rcases family_descends (prefixWord ++ tailWord_436846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436847 : List Nat := [1, 1, 2, 1, 3, 2, 3, 2, 5]
def baseStart_436847 : Nat := 118140960795 + 436847 * 2 ^ 59
def prefixEnd_436847 : Nat := 4983230072969 + 3 ^ 40 * 436847 * 2
def baseEnd_436847 : Nat := 199388874199784504714207

theorem tailTrace_436847 : CollatzResearch.WordTrace tailWord_436847 prefixEnd_436847 199388874199784504714207 := by
  unfold tailWord_436847
  simp only [CollatzResearch.WordTrace]
  refine ⟨15933119048385401372900795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10622079365590267581933863 15933119048385401372900795)
  ·
    refine ⟨23899678572578102059351193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15933119048385401372900795 23899678572578102059351193)
    ·
      refine ⟨17924758929433576544513395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23899678572578102059351193 17924758929433576544513395)
      ·
        refine ⟨26887138394150364816770093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17924758929433576544513395 26887138394150364816770093)
        ·
          refine ⟨10082676897806386806288785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26887138394150364816770093 10082676897806386806288785)
          ·
            refine ⟨7562007673354790104716589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10082676897806386806288785 7562007673354790104716589)
            ·
              refine ⟨2835752877508046289268721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7562007673354790104716589 2835752877508046289268721)
              ·
                refine ⟨2126814658131034716951541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2835752877508046289268721 2126814658131034716951541)
                ·
                  refine ⟨199388874199784504714207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2126814658131034716951541 199388874199784504714207)
                  ·
                    rfl

theorem cell20_436847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 5].length) (baseStart_436847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436847 prefixEnd_436847 := by exact prefixLift 436847
  have htrace : WordTrace (prefixWord ++ tailWord_436847) baseStart_436847 baseEnd_436847 := by
    simpa [prefixWord, tailWord_436847, baseEnd_436847] using wordTrace_append hprefix tailTrace_436847
  have hstable : (prefixWord ++ tailWord_436847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436847).length < 2 ^ (prefixWord ++ tailWord_436847).sum := by decide
  have hdescent : baseEnd_436847 < baseStart_436847 := by decide
  rcases family_descends (prefixWord ++ tailWord_436847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436918 : List Nat := [5, 1, 3, 1, 2, 2, 2, 2, 2]
def baseStart_436918 : Nat := 118140960795 + 436918 * 2 ^ 59
def prefixEnd_436918 : Nat := 4983230072969 + 3 ^ 40 * 436918 * 2
def baseEnd_436918 : Nat := 199421280534423813347251

theorem tailTrace_436918 : CollatzResearch.WordTrace tailWord_436918 prefixEnd_436918 199421280534423813347251 := by
  unfold tailWord_436918
  simp only [CollatzResearch.WordTrace]
  refine ⟨995981789445511281170963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10623805754085453665823605 995981789445511281170963)
  ·
    refine ⟨1493972684168266921756445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 995981789445511281170963 1493972684168266921756445)
    ·
      refine ⟨560239756563100095658667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1493972684168266921756445 560239756563100095658667)
      ·
        refine ⟨840359634844650143488001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560239756563100095658667 840359634844650143488001)
        ·
          refine ⟨630269726133487607616001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 840359634844650143488001 630269726133487607616001)
          ·
            refine ⟨472702294600115705712001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 630269726133487607616001 472702294600115705712001)
            ·
              refine ⟨354526720950086779284001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 472702294600115705712001 354526720950086779284001)
              ·
                refine ⟨265895040712565084463001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 354526720950086779284001 265895040712565084463001)
                ·
                  refine ⟨199421280534423813347251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 265895040712565084463001 199421280534423813347251)
                  ·
                    rfl

theorem cell20_436918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_436918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436918 prefixEnd_436918 := by exact prefixLift 436918
  have htrace : WordTrace (prefixWord ++ tailWord_436918) baseStart_436918 baseEnd_436918 := by
    simpa [prefixWord, tailWord_436918, baseEnd_436918] using wordTrace_append hprefix tailTrace_436918
  have hstable : (prefixWord ++ tailWord_436918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436918).length < 2 ^ (prefixWord ++ tailWord_436918).sum := by decide
  have hdescent : baseEnd_436918 < baseStart_436918 := by decide
  rcases family_descends (prefixWord ++ tailWord_436918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436919 : List Nat := [1, 1, 3, 1, 6, 1, 2, 2, 3]
def baseStart_436919 : Nat := 118140960795 + 436919 * 2 ^ 59
def prefixEnd_436919 : Nat := 4983230072969 + 3 ^ 40 * 436919 * 2
def baseEnd_436919 : Nat := 199421736961672254313913

theorem tailTrace_436919 : CollatzResearch.WordTrace tailWord_436919 prefixEnd_436919 199421736961672254313913 := by
  unfold tailWord_436919
  simp only [CollatzResearch.WordTrace]
  refine ⟨15935745104124557669521811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10623830069416371779681207 15935745104124557669521811)
  ·
    refine ⟨23903617656186836504282717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15935745104124557669521811 23903617656186836504282717)
    ·
      refine ⟨8963856621070063689106019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23903617656186836504282717 8963856621070063689106019)
      ·
        refine ⟨13445784931605095533659029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8963856621070063689106019 13445784931605095533659029)
        ·
          refine ⟨630271168668988853140267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13445784931605095533659029 630271168668988853140267)
          ·
            refine ⟨945406753003483279710401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 630271168668988853140267 945406753003483279710401)
            ·
              refine ⟨709055064752612459782801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 945406753003483279710401 709055064752612459782801)
              ·
                refine ⟨531791298564459344837101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 709055064752612459782801 531791298564459344837101)
                ·
                  refine ⟨199421736961672254313913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 531791298564459344837101 199421736961672254313913)
                  ·
                    rfl

theorem cell20_436919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 3].length) (baseStart_436919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436919 prefixEnd_436919 := by exact prefixLift 436919
  have htrace : WordTrace (prefixWord ++ tailWord_436919) baseStart_436919 baseEnd_436919 := by
    simpa [prefixWord, tailWord_436919, baseEnd_436919] using wordTrace_append hprefix tailTrace_436919
  have hstable : (prefixWord ++ tailWord_436919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436919).length < 2 ^ (prefixWord ++ tailWord_436919).sum := by decide
  have hdescent : baseEnd_436919 < baseStart_436919 := by decide
  rcases family_descends (prefixWord ++ tailWord_436919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436929 : List Nat := [1, 2, 6, 2, 1, 2, 1, 5]
def baseStart_436929 : Nat := 118140960795 + 436929 * 2 ^ 59
def prefixEnd_436929 : Nat := 4983230072969 + 3 ^ 40 * 436929 * 2
def baseEnd_436929 : Nat := 66475433744718887993513

theorem tailTrace_436929 : CollatzResearch.WordTrace tailWord_436929 prefixEnd_436929 66475433744718887993513 := by
  unfold tailWord_436929
  simp only [CollatzResearch.WordTrace]
  refine ⟨15936109834088329377385841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10624073222725552918257227 15936109834088329377385841)
  ·
    refine ⟨11952082375566247033039381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15936109834088329377385841 11952082375566247033039381)
    ·
      refine ⟨560253861354667829673721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11952082375566247033039381 560253861354667829673721)
      ·
        refine ⟨420190396016000872255291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 560253861354667829673721 420190396016000872255291)
        ·
          refine ⟨630285594024001308382937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420190396016000872255291 630285594024001308382937)
          ·
            refine ⟨472714195518000981287203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 630285594024001308382937 472714195518000981287203)
            ·
              refine ⟨709071293277001471930805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472714195518000981287203 709071293277001471930805)
              ·
                refine ⟨66475433744718887993513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 709071293277001471930805 66475433744718887993513)
                ·
                  rfl

theorem cell20_436929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 5].length) (baseStart_436929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436929 prefixEnd_436929 := by exact prefixLift 436929
  have htrace : WordTrace (prefixWord ++ tailWord_436929) baseStart_436929 baseEnd_436929 := by
    simpa [prefixWord, tailWord_436929, baseEnd_436929] using wordTrace_append hprefix tailTrace_436929
  have hstable : (prefixWord ++ tailWord_436929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436929).length < 2 ^ (prefixWord ++ tailWord_436929).sum := by decide
  have hdescent : baseEnd_436929 < baseStart_436929 := by decide
  rcases family_descends (prefixWord ++ tailWord_436929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436964 : List Nat := [2, 3, 1, 1, 1, 4, 1, 5, 2]
def baseStart_436964 : Nat := 118140960795 + 436964 * 2 ^ 59
def prefixEnd_436964 : Nat := 4983230072969 + 3 ^ 40 * 436964 * 2
def baseEnd_436964 : Nat := 199442276187852097813729

theorem tailTrace_436964 : CollatzResearch.WordTrace tailWord_436964 prefixEnd_436964 199442276187852097813729 := by
  unfold tailWord_436964
  simp only [CollatzResearch.WordTrace]
  refine ⟨7968693194480765177454973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10624924259307686903273297 7968693194480765177454973)
  ·
    refine ⟨2988259947930286941545615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7968693194480765177454973 2988259947930286941545615)
    ·
      refine ⟨4482389921895430412318423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2988259947930286941545615 4482389921895430412318423)
      ·
        refine ⟨6723584882843145618477635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4482389921895430412318423 6723584882843145618477635)
        ·
          refine ⟨10085377324264718427716453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6723584882843145618477635 10085377324264718427716453)
          ·
            refine ⟨1891008248299634705196835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10085377324264718427716453 1891008248299634705196835)
            ·
              refine ⟨2836512372449452057795253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1891008248299634705196835 2836512372449452057795253)
              ·
                refine ⟨265923034917136130418305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2836512372449452057795253 265923034917136130418305)
                ·
                  refine ⟨199442276187852097813729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 265923034917136130418305 199442276187852097813729)
                  ·
                    rfl

theorem cell20_436964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_436964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436964 prefixEnd_436964 := by exact prefixLift 436964
  have htrace : WordTrace (prefixWord ++ tailWord_436964) baseStart_436964 baseEnd_436964 := by
    simpa [prefixWord, tailWord_436964, baseEnd_436964] using wordTrace_append hprefix tailTrace_436964
  have hstable : (prefixWord ++ tailWord_436964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436964).length < 2 ^ (prefixWord ++ tailWord_436964).sum := by decide
  have hdescent : baseEnd_436964 < baseStart_436964 := by decide
  rcases family_descends (prefixWord ++ tailWord_436964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436978 : List Nat := [3, 2, 1, 3, 1, 3, 1, 1, 5]
def baseStart_436978 : Nat := 118140960795 + 436978 * 2 ^ 59
def prefixEnd_436978 : Nat := 4983230072969 + 3 ^ 40 * 436978 * 2
def baseEnd_436978 : Nat := 199448666169330271347005

theorem tailTrace_436978 : CollatzResearch.WordTrace tailWord_436978 prefixEnd_436978 199448666169330271347005 := by
  unfold tailWord_436978
  simp only [CollatzResearch.WordTrace]
  refine ⟨3984474252727702686479897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10625264673940540497279725 3984474252727702686479897)
  ·
    refine ⟨2988355689545777014859923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3984474252727702686479897 2988355689545777014859923)
    ·
      refine ⟨4482533534318665522289885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2988355689545777014859923 4482533534318665522289885)
      ·
        refine ⟨1680950075369499570858707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4482533534318665522289885 1680950075369499570858707)
        ·
          refine ⟨2521425113054249356288061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1680950075369499570858707 2521425113054249356288061)
          ·
            refine ⟨945534417395343508608023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2521425113054249356288061 945534417395343508608023)
            ·
              refine ⟨1418301626093015262912035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 945534417395343508608023 1418301626093015262912035)
              ·
                refine ⟨2127452439139522894368053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1418301626093015262912035 2127452439139522894368053)
                ·
                  refine ⟨199448666169330271347005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2127452439139522894368053 199448666169330271347005)
                  ·
                    rfl

theorem cell20_436978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_436978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_436978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_436978 prefixEnd_436978 := by exact prefixLift 436978
  have htrace : WordTrace (prefixWord ++ tailWord_436978) baseStart_436978 baseEnd_436978 := by
    simpa [prefixWord, tailWord_436978, baseEnd_436978] using wordTrace_append hprefix tailTrace_436978
  have hstable : (prefixWord ++ tailWord_436978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436978).length < 2 ^ (prefixWord ++ tailWord_436978).sum := by decide
  have hdescent : baseEnd_436978 < baseStart_436978 := by decide
  rcases family_descends (prefixWord ++ tailWord_436978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437046 : List Nat := [5, 1, 2, 2, 3, 1, 2, 1, 3]
def baseStart_437046 : Nat := 118140960795 + 437046 * 2 ^ 59
def prefixEnd_437046 : Nat := 4983230072969 + 3 ^ 40 * 437046 * 2
def baseEnd_437046 : Nat := 199479703222224257080061

theorem tailTrace_437046 : CollatzResearch.WordTrace tailWord_437046 prefixEnd_437046 199479703222224257080061 := by
  unfold tailWord_437046
  simp only [CollatzResearch.WordTrace]
  refine ⟨996273573416528647462187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10626918116442972239596661 996273573416528647462187)
  ·
    refine ⟨1494410360124792971193281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 996273573416528647462187 1494410360124792971193281)
    ·
      refine ⟨1120807770093594728394961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1494410360124792971193281 1120807770093594728394961)
      ·
        refine ⟨840605827570196046296221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1120807770093594728394961 840605827570196046296221)
        ·
          refine ⟨315227185338823517361083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 840605827570196046296221 315227185338823517361083)
          ·
            refine ⟨472840778008235276041625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315227185338823517361083 472840778008235276041625)
            ·
              refine ⟨354630583506176457031219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 472840778008235276041625 354630583506176457031219)
              ·
                refine ⟨531945875259264685546829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354630583506176457031219 531945875259264685546829)
                ·
                  refine ⟨199479703222224257080061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 531945875259264685546829 199479703222224257080061)
                  ·
                    rfl

theorem cell20_437046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_437046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437046 prefixEnd_437046 := by exact prefixLift 437046
  have htrace : WordTrace (prefixWord ++ tailWord_437046) baseStart_437046 baseEnd_437046 := by
    simpa [prefixWord, tailWord_437046, baseEnd_437046] using wordTrace_append hprefix tailTrace_437046
  have hstable : (prefixWord ++ tailWord_437046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437046).length < 2 ^ (prefixWord ++ tailWord_437046).sum := by decide
  have hdescent : baseEnd_437046 < baseStart_437046 := by decide
  rcases family_descends (prefixWord ++ tailWord_437046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437050 : List Nat := [3, 1, 1, 1, 6, 2, 2, 1, 3]
def baseStart_437050 : Nat := 118140960795 + 437050 * 2 ^ 59
def prefixEnd_437050 : Nat := 4983230072969 + 3 ^ 40 * 437050 * 2
def baseEnd_437050 : Nat := 199481528931218020946711

theorem tailTrace_437050 : CollatzResearch.WordTrace tailWord_437050 prefixEnd_437050 199481528931218020946711 := by
  unfold tailWord_437050
  simp only [CollatzResearch.WordTrace]
  refine ⟨3985130766662491760635151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10627015377766644695027069 3985130766662491760635151)
  ·
    refine ⟨5977696149993737640952727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3985130766662491760635151 5977696149993737640952727)
    ·
      refine ⟨8966544224990606461429091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5977696149993737640952727 8966544224990606461429091)
      ·
        refine ⟨13449816337485909692143637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8966544224990606461429091 13449816337485909692143637)
        ·
          refine ⟨630460140819652016819233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13449816337485909692143637 630460140819652016819233)
          ·
            refine ⟨472845105614739012614425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 630460140819652016819233 472845105614739012614425)
            ·
              refine ⟨354633829211054259460819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 472845105614739012614425 354633829211054259460819)
              ·
                refine ⟨531950743816581389191229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354633829211054259460819 531950743816581389191229)
                ·
                  refine ⟨199481528931218020946711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 531950743816581389191229 199481528931218020946711)
                  ·
                    rfl

theorem cell20_437050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 3].length) (baseStart_437050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437050 prefixEnd_437050 := by exact prefixLift 437050
  have htrace : WordTrace (prefixWord ++ tailWord_437050) baseStart_437050 baseEnd_437050 := by
    simpa [prefixWord, tailWord_437050, baseEnd_437050] using wordTrace_append hprefix tailTrace_437050
  have hstable : (prefixWord ++ tailWord_437050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437050).length < 2 ^ (prefixWord ++ tailWord_437050).sum := by decide
  have hdescent : baseEnd_437050 < baseStart_437050 := by decide
  rcases family_descends (prefixWord ++ tailWord_437050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437068 : List Nat := [2, 2, 1, 3, 3, 1, 2, 6]
def baseStart_437068 : Nat := 118140960795 + 437068 * 2 ^ 59
def prefixEnd_437068 : Nat := 4983230072969 + 3 ^ 40 * 437068 * 2
def baseEnd_437068 : Nat := 66496581540563319448879

theorem tailTrace_437068 : CollatzResearch.WordTrace tailWord_437068 prefixEnd_437068 66496581540563319448879 := by
  unfold tailWord_437068
  simp only [CollatzResearch.WordTrace]
  refine ⟨7970589790292378058347929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10627453053723170744463905 7970589790292378058347929)
  ·
    refine ⟨5977942342719283543760947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7970589790292378058347929 5977942342719283543760947)
    ·
      refine ⟨8966913514078925315641421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5977942342719283543760947 8966913514078925315641421)
      ·
        refine ⟨3362592567779596993365533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8966913514078925315641421 3362592567779596993365533)
        ·
          refine ⟨1260972212917348872512075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3362592567779596993365533 1260972212917348872512075)
          ·
            refine ⟨1891458319376023308768113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1260972212917348872512075 1891458319376023308768113)
            ·
              refine ⟨1418593739532017481576085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1891458319376023308768113 1418593739532017481576085)
              ·
                refine ⟨66496581540563319448879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1418593739532017481576085 66496581540563319448879)
                ·
                  rfl

theorem cell20_437068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 6].length) (baseStart_437068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437068 prefixEnd_437068 := by exact prefixLift 437068
  have htrace : WordTrace (prefixWord ++ tailWord_437068) baseStart_437068 baseEnd_437068 := by
    simpa [prefixWord, tailWord_437068, baseEnd_437068] using wordTrace_append hprefix tailTrace_437068
  have hstable : (prefixWord ++ tailWord_437068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437068).length < 2 ^ (prefixWord ++ tailWord_437068).sum := by decide
  have hdescent : baseEnd_437068 < baseStart_437068 := by decide
  rcases family_descends (prefixWord ++ tailWord_437068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437092 : List Nat := [2, 3, 1, 1, 4, 1, 1, 4, 3]
def baseStart_437092 : Nat := 118140960795 + 437092 * 2 ^ 59
def prefixEnd_437092 : Nat := 4983230072969 + 3 ^ 40 * 437092 * 2
def baseEnd_437092 : Nat := 199500698875652541546539

theorem tailTrace_437092 : CollatzResearch.WordTrace tailWord_437092 prefixEnd_437092 199500698875652541546539 := by
  unfold tailWord_437092
  simp only [CollatzResearch.WordTrace]
  refine ⟨7971027466248904107784765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10628036621665205477046353 7971027466248904107784765)
  ·
    refine ⟨2989135299843339040419287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7971027466248904107784765 2989135299843339040419287)
    ·
      refine ⟨4483702949765008560628931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2989135299843339040419287 4483702949765008560628931)
      ·
        refine ⟨6725554424647512840943397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4483702949765008560628931 6725554424647512840943397)
        ·
          refine ⟨1261041454621408657676887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6725554424647512840943397 1261041454621408657676887)
          ·
            refine ⟨1891562181932112986515331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1261041454621408657676887 1891562181932112986515331)
            ·
              refine ⟨2837343272898169479772997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1891562181932112986515331 2837343272898169479772997)
              ·
                refine ⟨532001863668406777457437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2837343272898169479772997 532001863668406777457437)
                ·
                  refine ⟨199500698875652541546539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 532001863668406777457437 199500698875652541546539)
                  ·
                    rfl

theorem cell20_437092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_437092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437092 prefixEnd_437092 := by exact prefixLift 437092
  have htrace : WordTrace (prefixWord ++ tailWord_437092) baseStart_437092 baseEnd_437092 := by
    simpa [prefixWord, tailWord_437092, baseEnd_437092] using wordTrace_append hprefix tailTrace_437092
  have hstable : (prefixWord ++ tailWord_437092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437092).length < 2 ^ (prefixWord ++ tailWord_437092).sum := by decide
  have hdescent : baseEnd_437092 < baseStart_437092 := by decide
  rcases family_descends (prefixWord ++ tailWord_437092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437095 : List Nat := [1, 1, 5, 1, 2, 2, 4, 2, 2]
def baseStart_437095 : Nat := 118140960795 + 437095 * 2 ^ 59
def prefixEnd_437095 : Nat := 4983230072969 + 3 ^ 40 * 437095 * 2
def baseEnd_437095 : Nat := 199502068157397864446527

theorem tailTrace_437095 : CollatzResearch.WordTrace tailWord_437095 prefixEnd_437095 199502068157397864446527 := by
  unfold tailWord_437095
  simp only [CollatzResearch.WordTrace]
  refine ⟨15942164351486939727928739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10628109567657959818619159 15942164351486939727928739)
  ·
    refine ⟨23913246527230409591893109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15942164351486939727928739 23913246527230409591893109)
    ·
      refine ⟨2241866861927850899239979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23913246527230409591893109 2241866861927850899239979)
      ·
        refine ⟨3362800292891776348859969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2241866861927850899239979 3362800292891776348859969)
        ·
          refine ⟨2522100219668832261644977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3362800292891776348859969 2522100219668832261644977)
          ·
            refine ⟨1891575164751624196233733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2522100219668832261644977 1891575164751624196233733)
            ·
              refine ⟨354670343390929536793825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1891575164751624196233733 354670343390929536793825)
              ·
                refine ⟨266002757543197152595369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 354670343390929536793825 266002757543197152595369)
                ·
                  refine ⟨199502068157397864446527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 266002757543197152595369 199502068157397864446527)
                  ·
                    rfl

theorem cell20_437095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 2, 2].length) (baseStart_437095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437095 prefixEnd_437095 := by exact prefixLift 437095
  have htrace : WordTrace (prefixWord ++ tailWord_437095) baseStart_437095 baseEnd_437095 := by
    simpa [prefixWord, tailWord_437095, baseEnd_437095] using wordTrace_append hprefix tailTrace_437095
  have hstable : (prefixWord ++ tailWord_437095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437095).length < 2 ^ (prefixWord ++ tailWord_437095).sum := by decide
  have hdescent : baseEnd_437095 < baseStart_437095 := by decide
  rcases family_descends (prefixWord ++ tailWord_437095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437102 : List Nat := [4, 1, 2, 3, 2, 2, 1, 5]
def baseStart_437102 : Nat := 118140960795 + 437102 * 2 ^ 59
def prefixEnd_437102 : Nat := 4983230072969 + 3 ^ 40 * 437102 * 2
def baseEnd_437102 : Nat := 66501754382712317071055

theorem tailTrace_437102 : CollatzResearch.WordTrace tailWord_437102 prefixEnd_437102 66501754382712317071055 := by
  unfold tailWord_437102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1992802457807697490429195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10628279774974386615622373 1992802457807697490429195)
  ·
    refine ⟨2989203686711546235643793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1992802457807697490429195 2989203686711546235643793)
    ·
      refine ⟨2241902765033659676732845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2989203686711546235643793 2241902765033659676732845)
      ·
        refine ⟨840713536887622378774817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2241902765033659676732845 840713536887622378774817)
        ·
          refine ⟨630535152665716784081113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 840713536887622378774817 630535152665716784081113)
          ·
            refine ⟨472901364499287588060835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 630535152665716784081113 472901364499287588060835)
            ·
              refine ⟨709352046748931382091253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472901364499287588060835 709352046748931382091253)
              ·
                refine ⟨66501754382712317071055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 709352046748931382091253 66501754382712317071055)
                ·
                  rfl

theorem cell20_437102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_437102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437102 prefixEnd_437102 := by exact prefixLift 437102
  have htrace : WordTrace (prefixWord ++ tailWord_437102) baseStart_437102 baseEnd_437102 := by
    simpa [prefixWord, tailWord_437102, baseEnd_437102] using wordTrace_append hprefix tailTrace_437102
  have hstable : (prefixWord ++ tailWord_437102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437102).length < 2 ^ (prefixWord ++ tailWord_437102).sum := by decide
  have hdescent : baseEnd_437102 < baseStart_437102 := by decide
  rcases family_descends (prefixWord ++ tailWord_437102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437106 : List Nat := [3, 2, 1, 2, 1, 1, 5, 5]
def baseStart_437106 : Nat := 118140960795 + 437106 * 2 ^ 59
def prefixEnd_437106 : Nat := 4983230072969 + 3 ^ 40 * 437106 * 2
def baseEnd_437106 : Nat := 66502362952376905026605

theorem tailTrace_437106 : CollatzResearch.WordTrace tailWord_437106 prefixEnd_437106 66502362952376905026605 := by
  unfold tailWord_437106
  simp only [CollatzResearch.WordTrace]
  refine ⟨3985641388611772151644793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10628377036298059071052781 3985641388611772151644793)
  ·
    refine ⟨2989231041458829113733595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3985641388611772151644793 2989231041458829113733595)
    ·
      refine ⟨4483846562188243670600393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2989231041458829113733595 4483846562188243670600393)
      ·
        refine ⟨3362884921641182752950295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4483846562188243670600393 3362884921641182752950295)
        ·
          refine ⟨5044327382461774129425443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3362884921641182752950295 5044327382461774129425443)
          ·
            refine ⟨7566491073692661194138165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5044327382461774129425443 7566491073692661194138165)
            ·
              refine ⟨709358538158686986950453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7566491073692661194138165 709358538158686986950453)
              ·
                refine ⟨66502362952376905026605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 709358538158686986950453 66502362952376905026605)
                ·
                  rfl

theorem cell20_437106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_437106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437106 prefixEnd_437106 := by exact prefixLift 437106
  have htrace : WordTrace (prefixWord ++ tailWord_437106) baseStart_437106 baseEnd_437106 := by
    simpa [prefixWord, tailWord_437106, baseEnd_437106] using wordTrace_append hprefix tailTrace_437106
  have hstable : (prefixWord ++ tailWord_437106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437106).length < 2 ^ (prefixWord ++ tailWord_437106).sum := by decide
  have hdescent : baseEnd_437106 < baseStart_437106 := by decide
  rcases family_descends (prefixWord ++ tailWord_437106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437154 : List Nat := [3, 3, 1, 2, 2, 2, 2, 1, 4]
def baseStart_437154 : Nat := 118140960795 + 437154 * 2 ^ 59
def prefixEnd_437154 : Nat := 4983230072969 + 3 ^ 40 * 437154 * 2
def baseEnd_437154 : Nat := 199528997365055881479619

theorem tailTrace_437154 : CollatzResearch.WordTrace tailWord_437154 prefixEnd_437154 199528997365055881479619 := by
  unfold tailWord_437154
  simp only [CollatzResearch.WordTrace]
  refine ⟨3986079064568298201081629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10629544172182128536217677 3986079064568298201081629)
  ·
    refine ⟨1494779649213111825405611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3986079064568298201081629 1494779649213111825405611)
    ·
      refine ⟨2242169473819667738108417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1494779649213111825405611 2242169473819667738108417)
      ·
        refine ⟨1681627105364750803581313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2242169473819667738108417 1681627105364750803581313)
        ·
          refine ⟨1261220329023563102685985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1681627105364750803581313 1261220329023563102685985)
          ·
            refine ⟨945915246767672327014489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1261220329023563102685985 945915246767672327014489)
            ·
              refine ⟨709436435075754245260867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 945915246767672327014489 709436435075754245260867)
              ·
                refine ⟨1064154652613631367891301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 709436435075754245260867 1064154652613631367891301)
                ·
                  refine ⟨199528997365055881479619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1064154652613631367891301 199528997365055881479619)
                  ·
                    rfl

theorem cell20_437154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_437154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437154 prefixEnd_437154 := by exact prefixLift 437154
  have htrace : WordTrace (prefixWord ++ tailWord_437154) baseStart_437154 baseEnd_437154 := by
    simpa [prefixWord, tailWord_437154, baseEnd_437154] using wordTrace_append hprefix tailTrace_437154
  have hstable : (prefixWord ++ tailWord_437154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437154).length < 2 ^ (prefixWord ++ tailWord_437154).sum := by decide
  have hdescent : baseEnd_437154 < baseStart_437154 := by decide
  rcases family_descends (prefixWord ++ tailWord_437154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437182 : List Nat := [4, 2, 1, 1, 1, 2, 3, 6]
def baseStart_437182 : Nat := 118140960795 + 437182 * 2 ^ 59
def prefixEnd_437182 : Nat := 4983230072969 + 3 ^ 40 * 437182 * 2
def baseEnd_437182 : Nat := 66513925776004076182057

theorem tailTrace_437182 : CollatzResearch.WordTrace tailWord_437182 prefixEnd_437182 66513925776004076182057 := by
  unfold tailWord_437182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1993167187771469198293225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10630225001447835724230533 1993167187771469198293225)
  ·
    refine ⟨1494875390828601898719919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1993167187771469198293225 1494875390828601898719919)
    ·
      refine ⟨2242313086242902848079879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1494875390828601898719919 2242313086242902848079879)
      ·
        refine ⟨3363469629364354272119819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2242313086242902848079879 3363469629364354272119819)
        ·
          refine ⟨5045204444046531408179729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3363469629364354272119819 5045204444046531408179729)
          ·
            refine ⟨3783903333034898556134797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5045204444046531408179729 3783903333034898556134797)
            ·
              refine ⟨1418963749888086958550549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3783903333034898556134797 1418963749888086958550549)
              ·
                refine ⟨66513925776004076182057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1418963749888086958550549 66513925776004076182057)
                ·
                  rfl

theorem cell20_437182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_437182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437182 prefixEnd_437182 := by exact prefixLift 437182
  have htrace : WordTrace (prefixWord ++ tailWord_437182) baseStart_437182 baseEnd_437182 := by
    simpa [prefixWord, tailWord_437182, baseEnd_437182] using wordTrace_append hprefix tailTrace_437182
  have hstable : (prefixWord ++ tailWord_437182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437182).length < 2 ^ (prefixWord ++ tailWord_437182).sum := by decide
  have hdescent : baseEnd_437182 < baseStart_437182 := by decide
  rcases family_descends (prefixWord ++ tailWord_437182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437209 : List Nat := [1, 2, 1, 2, 5, 2, 3, 2, 2]
def baseStart_437209 : Nat := 118140960795 + 437209 * 2 ^ 59
def prefixEnd_437209 : Nat := 4983230072969 + 3 ^ 40 * 437209 * 2
def baseEnd_437209 : Nat := 199554100863720134646061

theorem tailTrace_437209 : CollatzResearch.WordTrace tailWord_437209 prefixEnd_437209 199554100863720134646061 := by
  unfold tailWord_437209
  simp only [CollatzResearch.WordTrace]
  refine ⟨15946322273073937197578681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10630881515382624798385787 15946322273073937197578681)
  ·
    refine ⟨11959741704805452898184011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15946322273073937197578681 11959741704805452898184011)
    ·
      refine ⟨17939612557208179347276017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11959741704805452898184011 17939612557208179347276017)
      ·
        refine ⟨13454709417906134510457013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17939612557208179347276017 13454709417906134510457013)
        ·
          refine ⟨1261379007928700110355345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13454709417906134510457013 1261379007928700110355345)
          ·
            refine ⟨946034255946525082766509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1261379007928700110355345 946034255946525082766509)
            ·
              refine ⟨354762845979946906037441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 946034255946525082766509 354762845979946906037441)
              ·
                refine ⟨266072134484960179528081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 354762845979946906037441 266072134484960179528081)
                ·
                  refine ⟨199554100863720134646061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 266072134484960179528081 199554100863720134646061)
                  ·
                    rfl

theorem cell20_437209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 2, 2].length) (baseStart_437209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437209 prefixEnd_437209 := by exact prefixLift 437209
  have htrace : WordTrace (prefixWord ++ tailWord_437209) baseStart_437209 baseEnd_437209 := by
    simpa [prefixWord, tailWord_437209, baseEnd_437209] using wordTrace_append hprefix tailTrace_437209
  have hstable : (prefixWord ++ tailWord_437209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437209).length < 2 ^ (prefixWord ++ tailWord_437209).sum := by decide
  have hdescent : baseEnd_437209 < baseStart_437209 := by decide
  rcases family_descends (prefixWord ++ tailWord_437209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437223 : List Nat := [1, 1, 5, 2, 2, 1, 4, 1, 3]
def baseStart_437223 : Nat := 118140960795 + 437223 * 2 ^ 59
def prefixEnd_437223 : Nat := 4983230072969 + 3 ^ 40 * 437223 * 2
def baseEnd_437223 : Nat := 199560490845198308179337

theorem tailTrace_437223 : CollatzResearch.WordTrace tailWord_437223 prefixEnd_437223 199560490845198308179337 := by
  unfold tailWord_437223
  simp only [CollatzResearch.WordTrace]
  refine ⟨15946832895023217588588323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10631221930015478392392215 15946832895023217588588323)
  ·
    refine ⟨23920249342534826382882485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15946832895023217588588323 23920249342534826382882485)
    ·
      refine ⟨2242523375862639973395233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23920249342534826382882485 2242523375862639973395233)
      ·
        refine ⟨1681892531896979980046425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2242523375862639973395233 1681892531896979980046425)
        ·
          refine ⟨1261419398922734985034819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1681892531896979980046425 1261419398922734985034819)
          ·
            refine ⟨1892129098384102477552229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1261419398922734985034819 1892129098384102477552229)
            ·
              refine ⟨354774205947019214541043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1892129098384102477552229 354774205947019214541043)
              ·
                refine ⟨532161308920528821811565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354774205947019214541043 532161308920528821811565)
                ·
                  refine ⟨199560490845198308179337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 532161308920528821811565 199560490845198308179337)
                  ·
                    rfl

theorem cell20_437223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 3].length) (baseStart_437223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437223 prefixEnd_437223 := by exact prefixLift 437223
  have htrace : WordTrace (prefixWord ++ tailWord_437223) baseStart_437223 baseEnd_437223 := by
    simpa [prefixWord, tailWord_437223, baseEnd_437223] using wordTrace_append hprefix tailTrace_437223
  have hstable : (prefixWord ++ tailWord_437223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437223).length < 2 ^ (prefixWord ++ tailWord_437223).sum := by decide
  have hdescent : baseEnd_437223 < baseStart_437223 := by decide
  rcases family_descends (prefixWord ++ tailWord_437223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437241 : List Nat := [1, 2, 1, 3, 1, 3, 1, 8]
def baseStart_437241 : Nat := 118140960795 + 437241 * 2 ^ 59
def prefixEnd_437241 : Nat := 4983230072969 + 3 ^ 40 * 437241 * 2
def baseEnd_437241 : Nat := 66522902178556748526421

theorem tailTrace_437241 : CollatzResearch.WordTrace tailWord_437241 prefixEnd_437241 66522902178556748526421 := by
  unfold tailWord_437241
  simp only [CollatzResearch.WordTrace]
  refine ⟨15947489408958006662743577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10631659605972004441829051 15947489408958006662743577)
  ·
    refine ⟨11960617056718504997057683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15947489408958006662743577 11960617056718504997057683)
    ·
      refine ⟨17940925585077757495586525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11960617056718504997057683 17940925585077757495586525)
      ·
        refine ⟨6727847094404159060844947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17940925585077757495586525 6727847094404159060844947)
        ·
          refine ⟨10091770641606238591267421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6727847094404159060844947 10091770641606238591267421)
          ·
            refine ⟨3784413990602339471725283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10091770641606238591267421 3784413990602339471725283)
            ·
              refine ⟨5676620985903509207587925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3784413990602339471725283 5676620985903509207587925)
              ·
                refine ⟨66522902178556748526421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5676620985903509207587925 66522902178556748526421)
                ·
                  rfl

theorem cell20_437241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 8].length) (baseStart_437241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437241 prefixEnd_437241 := by exact prefixLift 437241
  have htrace : WordTrace (prefixWord ++ tailWord_437241) baseStart_437241 baseEnd_437241 := by
    simpa [prefixWord, tailWord_437241, baseEnd_437241] using wordTrace_append hprefix tailTrace_437241
  have hstable : (prefixWord ++ tailWord_437241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437241).length < 2 ^ (prefixWord ++ tailWord_437241).sum := by decide
  have hdescent : baseEnd_437241 < baseStart_437241 := by decide
  rcases family_descends (prefixWord ++ tailWord_437241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437282 : List Nat := [3, 3, 1, 1, 1, 3, 2, 3, 3]
def baseStart_437282 : Nat := 118140960795 + 437282 * 2 ^ 59
def prefixEnd_437282 : Nat := 4983230072969 + 3 ^ 40 * 437282 * 2
def baseEnd_437282 : Nat := 199587420052856325212429

theorem tailTrace_437282 : CollatzResearch.WordTrace tailWord_437282 prefixEnd_437282 199587420052856325212429 := by
  unfold tailWord_437282
  simp only [CollatzResearch.WordTrace]
  refine ⟨3987246200452367666246525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10632656534539647109990733 3987246200452367666246525)
  ·
    refine ⟨1495217325169637874842447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3987246200452367666246525 1495217325169637874842447)
    ·
      refine ⟨2242825987754456812263671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1495217325169637874842447 2242825987754456812263671)
      ·
        refine ⟨3364238981631685218395507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2242825987754456812263671 3364238981631685218395507)
        ·
          refine ⟨5046358472447527827593261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3364238981631685218395507 5046358472447527827593261)
          ·
            refine ⟨1892384427167822935347473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5046358472447527827593261 1892384427167822935347473)
            ·
              refine ⟨1419288320375867201510605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1892384427167822935347473 1419288320375867201510605)
              ·
                refine ⟨532233120140950200566477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1419288320375867201510605 532233120140950200566477)
                ·
                  refine ⟨199587420052856325212429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 532233120140950200566477 199587420052856325212429)
                  ·
                    rfl

theorem cell20_437282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_437282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437282 prefixEnd_437282 := by exact prefixLift 437282
  have htrace : WordTrace (prefixWord ++ tailWord_437282) baseStart_437282 baseEnd_437282 := by
    simpa [prefixWord, tailWord_437282, baseEnd_437282] using wordTrace_append hprefix tailTrace_437282
  have hstable : (prefixWord ++ tailWord_437282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437282).length < 2 ^ (prefixWord ++ tailWord_437282).sum := by decide
  have hdescent : baseEnd_437282 < baseStart_437282 := by decide
  rcases family_descends (prefixWord ++ tailWord_437282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437296 : List Nat := [2, 1, 1, 1, 2, 4, 5, 4]
def baseStart_437296 : Nat := 118140960795 + 437296 * 2 ^ 59
def prefixEnd_437296 : Nat := 4983230072969 + 3 ^ 40 * 437296 * 2
def baseEnd_437296 : Nat := 66531270011444832915235

theorem tailTrace_437296 : CollatzResearch.WordTrace tailWord_437296 prefixEnd_437296 66531270011444832915235 := by
  unfold tailWord_437296
  simp only [CollatzResearch.WordTrace]
  refine ⟨7974747711879375527997871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10632996949172500703997161 7974747711879375527997871)
  ·
    refine ⟨11962121567819063291996807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7974747711879375527997871 11962121567819063291996807)
    ·
      refine ⟨17943182351728594937995211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11962121567819063291996807 17943182351728594937995211)
      ·
        refine ⟨26914773527592892406992817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17943182351728594937995211 26914773527592892406992817)
        ·
          refine ⟨20186080145694669305244613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26914773527592892406992817 20186080145694669305244613)
          ·
            refine ⟨3784890027317750494733365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20186080145694669305244613 3784890027317750494733365)
            ·
              refine ⟨354833440061039108881253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3784890027317750494733365 354833440061039108881253)
              ·
                refine ⟨66531270011444832915235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 354833440061039108881253 66531270011444832915235)
                ·
                  rfl

theorem cell20_437296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 4].length) (baseStart_437296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437296 prefixEnd_437296 := by exact prefixLift 437296
  have htrace : WordTrace (prefixWord ++ tailWord_437296) baseStart_437296 baseEnd_437296 := by
    simpa [prefixWord, tailWord_437296, baseEnd_437296] using wordTrace_append hprefix tailTrace_437296
  have hstable : (prefixWord ++ tailWord_437296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437296).length < 2 ^ (prefixWord ++ tailWord_437296).sum := by decide
  have hdescent : baseEnd_437296 < baseStart_437296 := by decide
  rcases family_descends (prefixWord ++ tailWord_437296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437351 : List Nat := [1, 1, 5, 1, 1, 5, 2, 4]
def baseStart_437351 : Nat := 118140960795 + 437351 * 2 ^ 59
def prefixEnd_437351 : Nat := 4983230072969 + 3 ^ 40 * 437351 * 2
def baseEnd_437351 : Nat := 66539637844332917304049

theorem tailTrace_437351 : CollatzResearch.WordTrace tailWord_437351 prefixEnd_437351 66539637844332917304049 := by
  unfold tailWord_437351
  simp only [CollatzResearch.WordTrace]
  refine ⟨15951501438559495449247907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10634334292372996966165271 15951501438559495449247907)
  ·
    refine ⟨23927252157839243173871861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15951501438559495449247907 23927252157839243173871861)
    ·
      refine ⟨2243179889797429047550487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23927252157839243173871861 2243179889797429047550487)
      ·
        refine ⟨3364769834696143571325731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2243179889797429047550487 3364769834696143571325731)
        ·
          refine ⟨5047154752044215356988597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3364769834696143571325731 5047154752044215356988597)
          ·
            refine ⟨473170758004145189717681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5047154752044215356988597 473170758004145189717681)
            ·
              refine ⟨354878068503108892288261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 473170758004145189717681 354878068503108892288261)
              ·
                refine ⟨66539637844332917304049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 354878068503108892288261 66539637844332917304049)
                ·
                  rfl

theorem cell20_437351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 4].length) (baseStart_437351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437351 prefixEnd_437351 := by exact prefixLift 437351
  have htrace : WordTrace (prefixWord ++ tailWord_437351) baseStart_437351 baseEnd_437351 := by
    simpa [prefixWord, tailWord_437351, baseEnd_437351] using wordTrace_append hprefix tailTrace_437351
  have hstable : (prefixWord ++ tailWord_437351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437351).length < 2 ^ (prefixWord ++ tailWord_437351).sum := by decide
  have hdescent : baseEnd_437351 < baseStart_437351 := by decide
  rcases family_descends (prefixWord ++ tailWord_437351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437374 : List Nat := [4, 2, 4, 1, 1, 1, 3, 2, 2]
def baseStart_437374 : Nat := 118140960795 + 437374 * 2 ^ 59
def prefixEnd_437374 : Nat := 4983230072969 + 3 ^ 40 * 437374 * 2
def baseEnd_437374 : Nat := 199629411359712894145387

theorem tailTrace_437374 : CollatzResearch.WordTrace tailWord_437374 prefixEnd_437374 199629411359712894145387 := by
  unfold tailWord_437374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1994042539684521297166897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10634893544984113584890117 1994042539684521297166897)
  ·
    refine ⟨1495531904763390972875173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1994042539684521297166897 1495531904763390972875173)
    ·
      refine ⟨280412232143135807414095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1495531904763390972875173 280412232143135807414095)
      ·
        refine ⟨420618348214703711121143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280412232143135807414095 420618348214703711121143)
        ·
          refine ⟨630927522322055566681715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420618348214703711121143 630927522322055566681715)
          ·
            refine ⟨946391283483083350022573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 630927522322055566681715 946391283483083350022573)
            ·
              refine ⟨354896731306156256258465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 946391283483083350022573 354896731306156256258465)
              ·
                refine ⟨266172548479617192193849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 354896731306156256258465 266172548479617192193849)
                ·
                  refine ⟨199629411359712894145387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 266172548479617192193849 199629411359712894145387)
                  ·
                    rfl

theorem cell20_437374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_437374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437374 prefixEnd_437374 := by exact prefixLift 437374
  have htrace : WordTrace (prefixWord ++ tailWord_437374) baseStart_437374 baseEnd_437374 := by
    simpa [prefixWord, tailWord_437374, baseEnd_437374] using wordTrace_append hprefix tailTrace_437374
  have hstable : (prefixWord ++ tailWord_437374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437374).length < 2 ^ (prefixWord ++ tailWord_437374).sum := by decide
  have hdescent : baseEnd_437374 < baseStart_437374 := by decide
  rcases family_descends (prefixWord ++ tailWord_437374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437379 : List Nat := [1, 1, 1, 3, 3, 2, 2, 4, 3]
def baseStart_437379 : Nat := 118140960795 + 437379 * 2 ^ 59
def prefixEnd_437379 : Nat := 4983230072969 + 3 ^ 40 * 437379 * 2
def baseEnd_437379 : Nat := 199631693495955098978699

theorem tailTrace_437379 : CollatzResearch.WordTrace tailWord_437379 prefixEnd_437379 199631693495955098978699 := by
  unfold tailWord_437379
  simp only [CollatzResearch.WordTrace]
  refine ⟨15952522682458056231267191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10635015121638704154178127 15952522682458056231267191)
  ·
    refine ⟨23928784023687084346900787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15952522682458056231267191 23928784023687084346900787)
    ·
      refine ⟨35893176035530626520351181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23928784023687084346900787 35893176035530626520351181)
      ·
        refine ⟨13459941013323984945131693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35893176035530626520351181 13459941013323984945131693)
        ·
          refine ⟨5047477879996494354424385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13459941013323984945131693 5047477879996494354424385)
          ·
            refine ⟨3785608409997370765818289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5047477879996494354424385 3785608409997370765818289)
            ·
              refine ⟨2839206307498028074363717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3785608409997370765818289 2839206307498028074363717)
              ·
                refine ⟨532351182655880263943197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2839206307498028074363717 532351182655880263943197)
                ·
                  refine ⟨199631693495955098978699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 532351182655880263943197 199631693495955098978699)
                  ·
                    rfl

theorem cell20_437379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 3].length) (baseStart_437379 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437379 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437379 prefixEnd_437379 := by exact prefixLift 437379
  have htrace : WordTrace (prefixWord ++ tailWord_437379) baseStart_437379 baseEnd_437379 := by
    simpa [prefixWord, tailWord_437379, baseEnd_437379] using wordTrace_append hprefix tailTrace_437379
  have hstable : (prefixWord ++ tailWord_437379).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437379).length < 2 ^ (prefixWord ++ tailWord_437379).sum := by decide
  have hdescent : baseEnd_437379 < baseStart_437379 := by decide
  rcases family_descends (prefixWord ++ tailWord_437379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437444 : List Nat := [2, 3, 3, 1, 4, 1, 1, 5]
def baseStart_437444 : Nat := 118140960795 + 437444 * 2 ^ 59
def prefixEnd_437444 : Nat := 4983230072969 + 3 ^ 40 * 437444 * 2
def baseEnd_437444 : Nat := 66553787089034587270589

theorem tailTrace_437444 : CollatzResearch.WordTrace tailWord_437444 prefixEnd_437444 66553787089034587270589 := by
  unfold tailWord_437444
  simp only [CollatzResearch.WordTrace]
  refine ⟨7977446713611286166191693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10636595618148381554922257 7977446713611286166191693)
  ·
    refine ⟨2991542517604232312321885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7977446713611286166191693 2991542517604232312321885)
    ·
      refine ⟨1121828444101587117120707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2991542517604232312321885 1121828444101587117120707)
      ·
        refine ⟨1682742666152380675681061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1121828444101587117120707 1682742666152380675681061)
        ·
          refine ⟨315514249903571376690199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1682742666152380675681061 315514249903571376690199)
          ·
            refine ⟨473271374855357065035299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315514249903571376690199 473271374855357065035299)
            ·
              refine ⟨709907062283035597552949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473271374855357065035299 709907062283035597552949)
              ·
                refine ⟨66553787089034587270589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 709907062283035597552949 66553787089034587270589)
                ·
                  rfl

theorem cell20_437444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 5].length) (baseStart_437444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437444 prefixEnd_437444 := by exact prefixLift 437444
  have htrace : WordTrace (prefixWord ++ tailWord_437444) baseStart_437444 baseEnd_437444 := by
    simpa [prefixWord, tailWord_437444, baseEnd_437444] using wordTrace_append hprefix tailTrace_437444
  have hstable : (prefixWord ++ tailWord_437444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437444).length < 2 ^ (prefixWord ++ tailWord_437444).sum := by decide
  have hdescent : baseEnd_437444 < baseStart_437444 := by decide
  rcases family_descends (prefixWord ++ tailWord_437444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437492 : List Nat := [2, 6, 1, 2, 1, 1, 2, 1, 4]
def baseStart_437492 : Nat := 118140960795 + 437492 * 2 ^ 59
def prefixEnd_437492 : Nat := 4983230072969 + 3 ^ 40 * 437492 * 2
def baseEnd_437492 : Nat := 199683269775028928211571

theorem tailTrace_437492 : CollatzResearch.WordTrace tailWord_437492 prefixEnd_437492 199683269775028928211571 := by
  unfold tailWord_437492
  simp only [CollatzResearch.WordTrace]
  refine ⟨7978322065524338265065365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10637762754032451020087153 7978322065524338265065365)
  ·
    refine ⟨373983846821453356174939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7978322065524338265065365 373983846821453356174939)
    ·
      refine ⟨560975770232180034262409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373983846821453356174939 560975770232180034262409)
      ·
        refine ⟨420731827674135025696807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 560975770232180034262409 420731827674135025696807)
        ·
          refine ⟨631097741511202538545211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420731827674135025696807 631097741511202538545211)
          ·
            refine ⟨946646612266803807817817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631097741511202538545211 946646612266803807817817)
            ·
              refine ⟨709984959200102855863363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 946646612266803807817817 709984959200102855863363)
              ·
                refine ⟨1064977438800154283795045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 709984959200102855863363 1064977438800154283795045)
                ·
                  refine ⟨199683269775028928211571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1064977438800154283795045 199683269775028928211571)
                  ·
                    rfl

theorem cell20_437492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_437492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437492 prefixEnd_437492 := by exact prefixLift 437492
  have htrace : WordTrace (prefixWord ++ tailWord_437492) baseStart_437492 baseEnd_437492 := by
    simpa [prefixWord, tailWord_437492, baseEnd_437492] using wordTrace_append hprefix tailTrace_437492
  have hstable : (prefixWord ++ tailWord_437492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437492).length < 2 ^ (prefixWord ++ tailWord_437492).sum := by decide
  have hdescent : baseEnd_437492 < baseStart_437492 := by decide
  rcases family_descends (prefixWord ++ tailWord_437492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437506 : List Nat := [3, 4, 1, 1, 3, 1, 3, 1, 3]
def baseStart_437506 : Nat := 118140960795 + 437506 * 2 ^ 59
def prefixEnd_437506 : Nat := 4983230072969 + 3 ^ 40 * 437506 * 2
def baseEnd_437506 : Nat := 199689659756507101744847

theorem tailTrace_437506 : CollatzResearch.WordTrace tailWord_437506 prefixEnd_437506 199689659756507101744847 := by
  unfold tailWord_437506
  simp only [CollatzResearch.WordTrace]
  refine ⟨3989288688249489230285093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10638103168665304614093581 3989288688249489230285093)
  ·
    refine ⟨747991629046779230678455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3989288688249489230285093 747991629046779230678455)
    ·
      refine ⟨1121987443570168846017683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 747991629046779230678455 1121987443570168846017683)
      ·
        refine ⟨1682981165355253269026525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1121987443570168846017683 1682981165355253269026525)
        ·
          refine ⟨631117937008219975884947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1682981165355253269026525 631117937008219975884947)
          ·
            refine ⟨946676905512329963827421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631117937008219975884947 946676905512329963827421)
            ·
              refine ⟨355003839567123736435283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 946676905512329963827421 355003839567123736435283)
              ·
                refine ⟨532505759350685604652925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355003839567123736435283 532505759350685604652925)
                ·
                  refine ⟨199689659756507101744847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 532505759350685604652925 199689659756507101744847)
                  ·
                    rfl

theorem cell20_437506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_437506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437506 prefixEnd_437506 := by exact prefixLift 437506
  have htrace : WordTrace (prefixWord ++ tailWord_437506) baseStart_437506 baseEnd_437506 := by
    simpa [prefixWord, tailWord_437506, baseEnd_437506] using wordTrace_append hprefix tailTrace_437506
  have hstable : (prefixWord ++ tailWord_437506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437506).length < 2 ^ (prefixWord ++ tailWord_437506).sum := by decide
  have hdescent : baseEnd_437506 < baseStart_437506 := by decide
  rcases family_descends (prefixWord ++ tailWord_437506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437552 : List Nat := [2, 1, 1, 1, 2, 2, 3, 3, 5]
def baseStart_437552 : Nat := 118140960795 + 437552 * 2 ^ 59
def prefixEnd_437552 : Nat := 4983230072969 + 3 ^ 40 * 437552 * 2
def baseEnd_437552 : Nat := 199710655409935386211325

theorem tailTrace_437552 : CollatzResearch.WordTrace tailWord_437552 prefixEnd_437552 199710655409935386211325 := by
  unfold tailWord_437552
  simp only [CollatzResearch.WordTrace]
  refine ⟨7979416255415653388657455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10639221673887537851543273 7979416255415653388657455)
  ·
    refine ⟨11969124383123480082986183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7979416255415653388657455 11969124383123480082986183)
    ·
      refine ⟨17953686574685220124479275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11969124383123480082986183 17953686574685220124479275)
      ·
        refine ⟨26930529862027830186718913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17953686574685220124479275 26930529862027830186718913)
        ·
          refine ⟨20197897396520872640039185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26930529862027830186718913 20197897396520872640039185)
          ·
            refine ⟨15148423047390654480029389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20197897396520872640039185 15148423047390654480029389)
            ·
              refine ⟨5680658642771495430011021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15148423047390654480029389 5680658642771495430011021)
              ·
                refine ⟨2130246991039310786254133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5680658642771495430011021 2130246991039310786254133)
                ·
                  refine ⟨199710655409935386211325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2130246991039310786254133 199710655409935386211325)
                  ·
                    rfl

theorem cell20_437552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_437552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437552 prefixEnd_437552 := by exact prefixLift 437552
  have htrace : WordTrace (prefixWord ++ tailWord_437552) baseStart_437552 baseEnd_437552 := by
    simpa [prefixWord, tailWord_437552, baseEnd_437552] using wordTrace_append hprefix tailTrace_437552
  have hstable : (prefixWord ++ tailWord_437552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437552).length < 2 ^ (prefixWord ++ tailWord_437552).sum := by decide
  have hdescent : baseEnd_437552 < baseStart_437552 := by decide
  rcases family_descends (prefixWord ++ tailWord_437552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437555 : List Nat := [1, 1, 1, 2, 5, 4, 1, 1, 4]
def baseStart_437555 : Nat := 118140960795 + 437555 * 2 ^ 59
def prefixEnd_437555 : Nat := 4983230072969 + 3 ^ 40 * 437555 * 2
def baseEnd_437555 : Nat := 199712024691680709111313

theorem tailTrace_437555 : CollatzResearch.WordTrace tailWord_437555 prefixEnd_437555 199712024691680709111313 := by
  unfold tailWord_437555
  simp only [CollatzResearch.WordTrace]
  refine ⟨15958941929820438289674119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10639294619880292193116079 15958941929820438289674119)
  ·
    refine ⟨23938412894730657434511179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15958941929820438289674119 23938412894730657434511179)
    ·
      refine ⟨35907619342095986151766769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23938412894730657434511179 35907619342095986151766769)
      ·
        refine ⟨26930714506571989613825077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35907619342095986151766769 26930714506571989613825077)
        ·
          refine ⟨2524754484991124026296101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26930714506571989613825077 2524754484991124026296101)
          ·
            refine ⟨473391465935835754930519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2524754484991124026296101 473391465935835754930519)
            ·
              refine ⟨710087198903753632395779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473391465935835754930519 710087198903753632395779)
              ·
                refine ⟨1065130798355630448593669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 710087198903753632395779 1065130798355630448593669)
                ·
                  refine ⟨199712024691680709111313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1065130798355630448593669 199712024691680709111313)
                  ·
                    rfl

theorem cell20_437555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 4].length) (baseStart_437555 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437555 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437555 prefixEnd_437555 := by exact prefixLift 437555
  have htrace : WordTrace (prefixWord ++ tailWord_437555) baseStart_437555 baseEnd_437555 := by
    simpa [prefixWord, tailWord_437555, baseEnd_437555] using wordTrace_append hprefix tailTrace_437555
  have hstable : (prefixWord ++ tailWord_437555).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437555).length < 2 ^ (prefixWord ++ tailWord_437555).sum := by decide
  have hdescent : baseEnd_437555 < baseStart_437555 := by decide
  rcases family_descends (prefixWord ++ tailWord_437555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437558 : List Nat := [5, 1, 2, 3, 1, 1, 2, 5]
def baseStart_437558 : Nat := 118140960795 + 437558 * 2 ^ 59
def prefixEnd_437558 : Nat := 4983230072969 + 3 ^ 40 * 437558 * 2
def baseEnd_437558 : Nat := 66571131324475344003767

theorem tailTrace_437558 : CollatzResearch.WordTrace tailWord_437558 prefixEnd_437558 66571131324475344003767 := by
  unfold tailWord_437558
  simp only [CollatzResearch.WordTrace]
  refine ⟨997440709300598112627083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10639367565873046534688885 997440709300598112627083)
  ·
    refine ⟨1496161063950897168940625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 997440709300598112627083 1496161063950897168940625)
    ·
      refine ⟨1122120797963172876705469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1496161063950897168940625 1122120797963172876705469)
      ·
        refine ⟨420795299236189828764551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1122120797963172876705469 420795299236189828764551)
        ·
          refine ⟨631192948854284743146827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420795299236189828764551 631192948854284743146827)
          ·
            refine ⟨946789423281427114720241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631192948854284743146827 946789423281427114720241)
            ·
              refine ⟨710092067461070336040181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 946789423281427114720241 710092067461070336040181)
              ·
                refine ⟨66571131324475344003767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 710092067461070336040181 66571131324475344003767)
                ·
                  rfl

theorem cell20_437558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_437558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437558 prefixEnd_437558 := by exact prefixLift 437558
  have htrace : WordTrace (prefixWord ++ tailWord_437558) baseStart_437558 baseEnd_437558 := by
    simpa [prefixWord, tailWord_437558, baseEnd_437558] using wordTrace_append hprefix tailTrace_437558
  have hstable : (prefixWord ++ tailWord_437558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437558).length < 2 ^ (prefixWord ++ tailWord_437558).sum := by decide
  have hdescent : baseEnd_437558 < baseStart_437558 := by decide
  rcases family_descends (prefixWord ++ tailWord_437558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437565 : List Nat := [1, 4, 1, 5, 1, 1, 1, 3, 3]
def baseStart_437565 : Nat := 118140960795 + 437565 * 2 ^ 59
def prefixEnd_437565 : Nat := 4983230072969 + 3 ^ 40 * 437565 * 2
def baseEnd_437565 : Nat := 199716588964165118777939

theorem tailTrace_437565 : CollatzResearch.WordTrace tailWord_437565 prefixEnd_437565 199716588964165118777939 := by
  unfold tailWord_437565
  simp only [CollatzResearch.WordTrace]
  refine ⟨15959306659784209997538149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10639537773189473331692099 15959306659784209997538149)
  ·
    refine ⟨2992369998709539374538403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15959306659784209997538149 2992369998709539374538403)
    ·
      refine ⟨4488554998064309061807605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2992369998709539374538403 4488554998064309061807605)
      ·
        refine ⟨420802031068528974544463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4488554998064309061807605 420802031068528974544463)
        ·
          refine ⟨631203046602793461816695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420802031068528974544463 631203046602793461816695)
          ·
            refine ⟨946804569904190192725043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631203046602793461816695 946804569904190192725043)
            ·
              refine ⟨1420206854856285289087565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 946804569904190192725043 1420206854856285289087565)
              ·
                refine ⟨532577570571106983407837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1420206854856285289087565 532577570571106983407837)
                ·
                  refine ⟨199716588964165118777939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 532577570571106983407837 199716588964165118777939)
                  ·
                    rfl

theorem cell20_437565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_437565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437565 prefixEnd_437565 := by exact prefixLift 437565
  have htrace : WordTrace (prefixWord ++ tailWord_437565) baseStart_437565 baseEnd_437565 := by
    simpa [prefixWord, tailWord_437565, baseEnd_437565] using wordTrace_append hprefix tailTrace_437565
  have hstable : (prefixWord ++ tailWord_437565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437565).length < 2 ^ (prefixWord ++ tailWord_437565).sum := by decide
  have hdescent : baseEnd_437565 < baseStart_437565 := by decide
  rcases family_descends (prefixWord ++ tailWord_437565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437634 : List Nat := [3, 4, 2, 1, 1, 2, 3, 4]
def baseStart_437634 : Nat := 118140960795 + 437634 * 2 ^ 59
def prefixEnd_437634 : Nat := 4983230072969 + 3 ^ 40 * 437634 * 2
def baseEnd_437634 : Nat := 66582694148102515159219

theorem tailTrace_437634 : CollatzResearch.WordTrace tailWord_437634 prefixEnd_437634 66582694148102515159219 := by
  unfold tailWord_437634
  simp only [CollatzResearch.WordTrace]
  refine ⟨3990455824133558695449989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10641215531022823187866637 3990455824133558695449989)
  ·
    refine ⟨748210467025042255396873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3990455824133558695449989 748210467025042255396873)
    ·
      refine ⟨561157850268781691547655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 748210467025042255396873 561157850268781691547655)
      ·
        refine ⟨841736775403172537321483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561157850268781691547655 841736775403172537321483)
        ·
          refine ⟨1262605163104758805982225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 841736775403172537321483 1262605163104758805982225)
          ·
            refine ⟨946953872328569104486669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1262605163104758805982225 946953872328569104486669)
            ·
              refine ⟨355107702123213414182501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 946953872328569104486669 355107702123213414182501)
              ·
                refine ⟨66582694148102515159219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 355107702123213414182501 66582694148102515159219)
                ·
                  rfl

theorem cell20_437634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_437634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437634 prefixEnd_437634 := by exact prefixLift 437634
  have htrace : WordTrace (prefixWord ++ tailWord_437634) baseStart_437634 baseEnd_437634 := by
    simpa [prefixWord, tailWord_437634, baseEnd_437634] using wordTrace_append hprefix tailTrace_437634
  have hstable : (prefixWord ++ tailWord_437634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437634).length < 2 ^ (prefixWord ++ tailWord_437634).sum := by decide
  have hdescent : baseEnd_437634 < baseStart_437634 := by decide
  rcases family_descends (prefixWord ++ tailWord_437634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437704 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 7]
def baseStart_437704 : Nat := 118140960795 + 437704 * 2 ^ 59
def prefixEnd_437704 : Nat := 4983230072969 + 3 ^ 40 * 437704 * 2
def baseEnd_437704 : Nat := 199780032351698413144037

theorem tailTrace_437704 : CollatzResearch.WordTrace tailWord_437704 prefixEnd_437704 199780032351698413144037 := by
  unfold tailWord_437704
  simp only [CollatzResearch.WordTrace]
  refine ⟨7982188203140318368424083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10642917604187091157898777 7982188203140318368424083)
  ·
    refine ⟨11973282304710477552636125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7982188203140318368424083 11973282304710477552636125)
    ·
      refine ⟨4489980864266429082238547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11973282304710477552636125 4489980864266429082238547)
      ·
        refine ⟨6734971296399643623357821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4489980864266429082238547 6734971296399643623357821)
        ·
          refine ⟨2525614236149866358759183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6734971296399643623357821 2525614236149866358759183)
          ·
            refine ⟨3788421354224799538138775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2525614236149866358759183 3788421354224799538138775)
            ·
              refine ⟨5682632031337199307208163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3788421354224799538138775 5682632031337199307208163)
              ·
                refine ⟨8523948047005798960812245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5682632031337199307208163 8523948047005798960812245)
                ·
                  refine ⟨199780032351698413144037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8523948047005798960812245 199780032351698413144037)
                  ·
                    rfl

theorem cell20_437704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_437704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437704 prefixEnd_437704 := by exact prefixLift 437704
  have htrace : WordTrace (prefixWord ++ tailWord_437704) baseStart_437704 baseEnd_437704 := by
    simpa [prefixWord, tailWord_437704, baseEnd_437704] using wordTrace_append hprefix tailTrace_437704
  have hstable : (prefixWord ++ tailWord_437704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437704).length < 2 ^ (prefixWord ++ tailWord_437704).sum := by decide
  have hdescent : baseEnd_437704 < baseStart_437704 := by decide
  rcases family_descends (prefixWord ++ tailWord_437704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437707 : List Nat := [1, 1, 1, 1, 3, 3, 5, 3, 2]
def baseStart_437707 : Nat := 118140960795 + 437707 * 2 ^ 59
def prefixEnd_437707 : Nat := 4983230072969 + 3 ^ 40 * 437707 * 2
def baseEnd_437707 : Nat := 199781401633443736044025

theorem tailTrace_437707 : CollatzResearch.WordTrace tailWord_437707 prefixEnd_437707 199781401633443736044025 := by
  unfold tailWord_437707
  simp only [CollatzResearch.WordTrace]
  refine ⟨15964485825269768249207375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10642990550179845499471583 15964485825269768249207375)
  ·
    refine ⟨23946728737904652373811063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15964485825269768249207375 23946728737904652373811063)
    ·
      refine ⟨35920093106856978560716595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23946728737904652373811063 35920093106856978560716595)
      ·
        refine ⟨53880139660285467841074893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35920093106856978560716595 53880139660285467841074893)
        ·
          refine ⟨20205052372607050440403085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53880139660285467841074893 20205052372607050440403085)
          ·
            refine ⟨7576894639727643915151157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20205052372607050440403085 7576894639727643915151157)
            ·
              refine ⟨710333872474466617045421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7576894639727643915151157 710333872474466617045421)
              ·
                refine ⟨266375202177924981392033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 710333872474466617045421 266375202177924981392033)
                ·
                  refine ⟨199781401633443736044025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 266375202177924981392033 199781401633443736044025)
                  ·
                    rfl

theorem cell20_437707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 3, 2].length) (baseStart_437707 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437707 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437707 prefixEnd_437707 := by exact prefixLift 437707
  have htrace : WordTrace (prefixWord ++ tailWord_437707) baseStart_437707 baseEnd_437707 := by
    simpa [prefixWord, tailWord_437707, baseEnd_437707] using wordTrace_append hprefix tailTrace_437707
  have hstable : (prefixWord ++ tailWord_437707).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437707).length < 2 ^ (prefixWord ++ tailWord_437707).sum := by decide
  have hdescent : baseEnd_437707 < baseStart_437707 := by decide
  rcases family_descends (prefixWord ++ tailWord_437707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437711 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 6]
def baseStart_437711 : Nat := 118140960795 + 437711 * 2 ^ 59
def prefixEnd_437711 : Nat := 4983230072969 + 3 ^ 40 * 437711 * 2
def baseEnd_437711 : Nat := 199783227342437499910675

theorem tailTrace_437711 : CollatzResearch.WordTrace tailWord_437711 prefixEnd_437711 199783227342437499910675 := by
  unfold tailWord_437711
  simp only [CollatzResearch.WordTrace]
  refine ⟨15964631717255276932352987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10643087811503517954901991 15964631717255276932352987)
  ·
    refine ⟨23946947575882915398529481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15964631717255276932352987 23946947575882915398529481)
    ·
      refine ⟨17960210681912186548897111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23946947575882915398529481 17960210681912186548897111)
      ·
        refine ⟨26940316022868279823345667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17960210681912186548897111 26940316022868279823345667)
        ·
          refine ⟨40410474034302419735018501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26940316022868279823345667 40410474034302419735018501)
          ·
            refine ⟨7576963881431703700315969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40410474034302419735018501 7576963881431703700315969)
            ·
              refine ⟨5682722911073777775236977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7576963881431703700315969 5682722911073777775236977)
              ·
                refine ⟨4262042183305333331427733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5682722911073777775236977 4262042183305333331427733)
                ·
                  refine ⟨199783227342437499910675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4262042183305333331427733 199783227342437499910675)
                  ·
                    rfl

theorem cell20_437711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 6].length) (baseStart_437711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437711 prefixEnd_437711 := by exact prefixLift 437711
  have htrace : WordTrace (prefixWord ++ tailWord_437711) baseStart_437711 baseEnd_437711 := by
    simpa [prefixWord, tailWord_437711, baseEnd_437711] using wordTrace_append hprefix tailTrace_437711
  have hstable : (prefixWord ++ tailWord_437711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437711).length < 2 ^ (prefixWord ++ tailWord_437711).sum := by decide
  have hdescent : baseEnd_437711 < baseStart_437711 := by decide
  rcases family_descends (prefixWord ++ tailWord_437711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437735 : List Nat := [1, 1, 5, 2, 1, 2, 1, 7]
def baseStart_437735 : Nat := 118140960795 + 437735 * 2 ^ 59
def prefixEnd_437735 : Nat := 4983230072969 + 3 ^ 40 * 437735 * 2
def baseEnd_437735 : Nat := 66598060532133361036859

theorem tailTrace_437735 : CollatzResearch.WordTrace tailWord_437735 prefixEnd_437735 66598060532133361036859 := by
  unfold tailWord_437735
  simp only [CollatzResearch.WordTrace]
  refine ⟨15965507069168329031226659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10643671379445552687484439 15965507069168329031226659)
  ·
    refine ⟨23948260603752493546839989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15965507069168329031226659 23948260603752493546839989)
    ·
      refine ⟨2245149431601796270016249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23948260603752493546839989 2245149431601796270016249)
      ·
        refine ⟨1683862073701347202512187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2245149431601796270016249 1683862073701347202512187)
        ·
          refine ⟨2525793110552020803768281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1683862073701347202512187 2525793110552020803768281)
          ·
            refine ⟨1894344832914015602826211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2525793110552020803768281 1894344832914015602826211)
            ·
              refine ⟨2841517249371023404239317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1894344832914015602826211 2841517249371023404239317)
              ·
                refine ⟨66598060532133361036859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2841517249371023404239317 66598060532133361036859)
                ·
                  rfl

theorem cell20_437735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 7].length) (baseStart_437735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437735 prefixEnd_437735 := by exact prefixLift 437735
  have htrace : WordTrace (prefixWord ++ tailWord_437735) baseStart_437735 baseEnd_437735 := by
    simpa [prefixWord, tailWord_437735, baseEnd_437735] using wordTrace_append hprefix tailTrace_437735
  have hstable : (prefixWord ++ tailWord_437735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437735).length < 2 ^ (prefixWord ++ tailWord_437735).sum := by decide
  have hdescent : baseEnd_437735 < baseStart_437735 := by decide
  rcases family_descends (prefixWord ++ tailWord_437735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437738 : List Nat := [3, 1, 3, 1, 4, 1, 1, 3, 3]
def baseStart_437738 : Nat := 118140960795 + 437738 * 2 ^ 59
def prefixEnd_437738 : Nat := 4983230072969 + 3 ^ 40 * 437738 * 2
def baseEnd_437738 : Nat := 199795550878145406010565

theorem tailTrace_437738 : CollatzResearch.WordTrace tailWord_437738 prefixEnd_437738 199795550878145406010565 := by
  unfold tailWord_437738
  simp only [CollatzResearch.WordTrace]
  refine ⟨3991404122039365135896467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10643744325438307029057245 3991404122039365135896467)
  ·
    refine ⟨5987106183059047703844701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3991404122039365135896467 5987106183059047703844701)
    ·
      refine ⟨2245164818647142888941763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5987106183059047703844701 2245164818647142888941763)
      ·
        refine ⟨3367747227970714333412645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2245164818647142888941763 3367747227970714333412645)
        ·
          refine ⟨631452605244508937514871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3367747227970714333412645 631452605244508937514871)
          ·
            refine ⟨947178907866763406272307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631452605244508937514871 947178907866763406272307)
            ·
              refine ⟨1420768361800145109408461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 947178907866763406272307 1420768361800145109408461)
              ·
                refine ⟨532788135675054416028173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1420768361800145109408461 532788135675054416028173)
                ·
                  refine ⟨199795550878145406010565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 532788135675054416028173 199795550878145406010565)
                  ·
                    rfl

theorem cell20_437738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_437738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437738 prefixEnd_437738 := by exact prefixLift 437738
  have htrace : WordTrace (prefixWord ++ tailWord_437738) baseStart_437738 baseEnd_437738 := by
    simpa [prefixWord, tailWord_437738, baseEnd_437738] using wordTrace_append hprefix tailTrace_437738
  have hstable : (prefixWord ++ tailWord_437738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437738).length < 2 ^ (prefixWord ++ tailWord_437738).sum := by decide
  have hdescent : baseEnd_437738 < baseStart_437738 := by decide
  rcases family_descends (prefixWord ++ tailWord_437738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437818 : List Nat := [3, 1, 1, 1, 3, 2, 2, 2, 5]
def baseStart_437818 : Nat := 118140960795 + 437818 * 2 ^ 59
def prefixEnd_437818 : Nat := 4983230072969 + 3 ^ 40 * 437818 * 2
def baseEnd_437818 : Nat := 199832065058020683343571

theorem tailTrace_437818 : CollatzResearch.WordTrace tailWord_437818 prefixEnd_437818 199832065058020683343571 := by
  unfold tailWord_437818
  simp only [CollatzResearch.WordTrace]
  refine ⟨3992133581966908551624527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10645689551911756137665405 3992133581966908551624527)
  ·
    refine ⟨5988200372950362827436791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3992133581966908551624527 5988200372950362827436791)
    ·
      refine ⟨8982300559425544241155187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5988200372950362827436791 8982300559425544241155187)
      ·
        refine ⟨13473450839138316361732781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8982300559425544241155187 13473450839138316361732781)
        ·
          refine ⟨5052544064676868635649793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13473450839138316361732781 5052544064676868635649793)
          ·
            refine ⟨3789408048507651476737345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5052544064676868635649793 3789408048507651476737345)
            ·
              refine ⟨2842056036380738607553009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3789408048507651476737345 2842056036380738607553009)
              ·
                refine ⟨2131542027285553955664757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2842056036380738607553009 2131542027285553955664757)
                ·
                  refine ⟨199832065058020683343571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2131542027285553955664757 199832065058020683343571)
                  ·
                    rfl

theorem cell20_437818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_437818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437818 prefixEnd_437818 := by exact prefixLift 437818
  have htrace : WordTrace (prefixWord ++ tailWord_437818) baseStart_437818 baseEnd_437818 := by
    simpa [prefixWord, tailWord_437818, baseEnd_437818] using wordTrace_append hprefix tailTrace_437818
  have hstable : (prefixWord ++ tailWord_437818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437818).length < 2 ^ (prefixWord ++ tailWord_437818).sum := by decide
  have hdescent : baseEnd_437818 < baseStart_437818 := by decide
  rcases family_descends (prefixWord ++ tailWord_437818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437831 : List Nat := [1, 1, 4, 1, 6, 1, 1, 2, 3]
def baseStart_437831 : Nat := 118140960795 + 437831 * 2 ^ 59
def prefixEnd_437831 : Nat := 4983230072969 + 3 ^ 40 * 437831 * 2
def baseEnd_437831 : Nat := 199837998612250415910185

theorem tailTrace_437831 : CollatzResearch.WordTrace tailWord_437831 prefixEnd_437831 199837998612250415910185 := by
  unfold tailWord_437831
  simp only [CollatzResearch.WordTrace]
  refine ⟨15969008476820537426721347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10646005651213691617814231 15969008476820537426721347)
  ·
    refine ⟨23953512715230806140082021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15969008476820537426721347 23953512715230806140082021)
    ·
      refine ⟨4491283634105776151265379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23953512715230806140082021 4491283634105776151265379)
      ·
        refine ⟨6736925451158664226898069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4491283634105776151265379 6736925451158664226898069)
        ·
          refine ⟨315793380523062385635847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6736925451158664226898069 315793380523062385635847)
          ·
            refine ⟨473690070784593578453771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315793380523062385635847 473690070784593578453771)
            ·
              refine ⟨710535106176890367680657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473690070784593578453771 710535106176890367680657)
              ·
                refine ⟨532901329632667775760493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 710535106176890367680657 532901329632667775760493)
                ·
                  refine ⟨199837998612250415910185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 532901329632667775760493 199837998612250415910185)
                  ·
                    rfl

theorem cell20_437831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 3].length) (baseStart_437831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437831 prefixEnd_437831 := by exact prefixLift 437831
  have htrace : WordTrace (prefixWord ++ tailWord_437831) baseStart_437831 baseEnd_437831 := by
    simpa [prefixWord, tailWord_437831, baseEnd_437831] using wordTrace_append hprefix tailTrace_437831
  have hstable : (prefixWord ++ tailWord_437831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437831).length < 2 ^ (prefixWord ++ tailWord_437831).sum := by decide
  have hdescent : baseEnd_437831 < baseStart_437831 := by decide
  rcases family_descends (prefixWord ++ tailWord_437831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437842 : List Nat := [3, 2, 2, 1, 2, 2, 1, 3, 4]
def baseStart_437842 : Nat := 118140960795 + 437842 * 2 ^ 59
def prefixEnd_437842 : Nat := 4983230072969 + 3 ^ 40 * 437842 * 2
def baseEnd_437842 : Nat := 199843019311983266543473

theorem tailTrace_437842 : CollatzResearch.WordTrace tailWord_437842 prefixEnd_437842 199843019311983266543473 := by
  unfold tailWord_437842
  simp only [CollatzResearch.WordTrace]
  refine ⟨3992352419945171576342945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10646273119853790870247853 3992352419945171576342945)
  ·
    refine ⟨2994264314958878682257209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3992352419945171576342945 2994264314958878682257209)
    ·
      refine ⟨2245698236219159011692907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2994264314958878682257209 2245698236219159011692907)
      ·
        refine ⟨3368547354328738517539361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2245698236219159011692907 3368547354328738517539361)
        ·
          refine ⟨2526410515746553888154521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3368547354328738517539361 2526410515746553888154521)
          ·
            refine ⟨1894807886809915416115891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2526410515746553888154521 1894807886809915416115891)
            ·
              refine ⟨2842211830214873124173837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1894807886809915416115891 2842211830214873124173837)
              ·
                refine ⟨1065829436330577421565189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2842211830214873124173837 1065829436330577421565189)
                ·
                  refine ⟨199843019311983266543473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1065829436330577421565189 199843019311983266543473)
                  ·
                    rfl

theorem cell20_437842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_437842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437842 prefixEnd_437842 := by exact prefixLift 437842
  have htrace : WordTrace (prefixWord ++ tailWord_437842) baseStart_437842 baseEnd_437842 := by
    simpa [prefixWord, tailWord_437842, baseEnd_437842] using wordTrace_append hprefix tailTrace_437842
  have hstable : (prefixWord ++ tailWord_437842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437842).length < 2 ^ (prefixWord ++ tailWord_437842).sum := by decide
  have hdescent : baseEnd_437842 < baseStart_437842 := by decide
  rcases family_descends (prefixWord ++ tailWord_437842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437866 : List Nat := [3, 1, 3, 2, 1, 2, 4, 4]
def baseStart_437866 : Nat := 118140960795 + 437866 * 2 ^ 59
def prefixEnd_437866 : Nat := 4983230072969 + 3 ^ 40 * 437866 * 2
def baseEnd_437866 : Nat := 66617991188648616581125

theorem tailTrace_437866 : CollatzResearch.WordTrace tailWord_437866 prefixEnd_437866 66617991188648616581125 := by
  unfold tailWord_437866
  simp only [CollatzResearch.WordTrace]
  refine ⟨3992571257923434601061363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10646856687795825602830301 3992571257923434601061363)
  ·
    refine ⟨5988856886885151901592045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3992571257923434601061363 5988856886885151901592045)
    ·
      refine ⟨2245821332581931963097017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5988856886885151901592045 2245821332581931963097017)
      ·
        refine ⟨1684365999436448972322763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2245821332581931963097017 1684365999436448972322763)
        ·
          refine ⟨2526548999154673458484145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1684365999436448972322763 2526548999154673458484145)
          ·
            refine ⟨1894911749366005093863109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2526548999154673458484145 1894911749366005093863109)
            ·
              refine ⟨355295953006125955099333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1894911749366005093863109 355295953006125955099333)
              ·
                refine ⟨66617991188648616581125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 355295953006125955099333 66617991188648616581125)
                ·
                  rfl

theorem cell20_437866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_437866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437866 prefixEnd_437866 := by exact prefixLift 437866
  have htrace : WordTrace (prefixWord ++ tailWord_437866) baseStart_437866 baseEnd_437866 := by
    simpa [prefixWord, tailWord_437866, baseEnd_437866] using wordTrace_append hprefix tailTrace_437866
  have hstable : (prefixWord ++ tailWord_437866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437866).length < 2 ^ (prefixWord ++ tailWord_437866).sum := by decide
  have hdescent : baseEnd_437866 < baseStart_437866 := by decide
  rcases family_descends (prefixWord ++ tailWord_437866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437911 : List Nat := [1, 1, 3, 3, 2, 3, 1, 3, 3]
def baseStart_437911 : Nat := 118140960795 + 437911 * 2 ^ 59
def prefixEnd_437911 : Nat := 4983230072969 + 3 ^ 40 * 437911 * 2
def baseEnd_437911 : Nat := 199874512792125693243191

theorem tailTrace_437911 : CollatzResearch.WordTrace tailWord_437911 prefixEnd_437911 199874512792125693243191 := by
  unfold tailWord_437911
  simp only [CollatzResearch.WordTrace]
  refine ⟨15971926316530711089633587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10647950877687140726422391 15971926316530711089633587)
  ·
    refine ⟨23957889474796066634450381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15971926316530711089633587 23957889474796066634450381)
    ·
      refine ⟨8984208553048524987918893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23957889474796066634450381 8984208553048524987918893)
      ·
        refine ⟨3369078207393196870469585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8984208553048524987918893 3369078207393196870469585)
        ·
          refine ⟨2526808655544897652852189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3369078207393196870469585 2526808655544897652852189)
          ·
            refine ⟨947553245829336619819571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2526808655544897652852189 947553245829336619819571)
            ·
              refine ⟨1421329868744004929729357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 947553245829336619819571 1421329868744004929729357)
              ·
                refine ⟨532998700779001848648509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1421329868744004929729357 532998700779001848648509)
                ·
                  refine ⟨199874512792125693243191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 532998700779001848648509 199874512792125693243191)
                  ·
                    rfl

theorem cell20_437911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 3].length) (baseStart_437911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437911 prefixEnd_437911 := by exact prefixLift 437911
  have htrace : WordTrace (prefixWord ++ tailWord_437911) baseStart_437911 baseEnd_437911 := by
    simpa [prefixWord, tailWord_437911, baseEnd_437911] using wordTrace_append hprefix tailTrace_437911
  have hstable : (prefixWord ++ tailWord_437911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437911).length < 2 ^ (prefixWord ++ tailWord_437911).sum := by decide
  have hdescent : baseEnd_437911 < baseStart_437911 := by decide
  rcases family_descends (prefixWord ++ tailWord_437911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437942 : List Nat := [5, 1, 3, 1, 1, 9]
def baseStart_437942 : Nat := 118140960795 + 437942 * 2 ^ 59
def prefixEnd_437942 : Nat := 4983230072969 + 3 ^ 40 * 437942 * 2
def baseEnd_437942 : Nat := 7403283779141754192953

theorem tailTrace_437942 : CollatzResearch.WordTrace tailWord_437942 prefixEnd_437942 7403283779141754192953 := by
  unfold tailWord_437942
  simp only [CollatzResearch.WordTrace]
  refine ⟨998316061213650211500755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10648704652945602256008053 998316061213650211500755)
  ·
    refine ⟨1497474091820475317251133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 998316061213650211500755 1497474091820475317251133)
    ·
      refine ⟨561552784432678243969175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1497474091820475317251133 561552784432678243969175)
      ·
        refine ⟨842329176649017365953763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561552784432678243969175 842329176649017365953763)
        ·
          refine ⟨1263493764973526048930645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 842329176649017365953763 1263493764973526048930645)
          ·
            refine ⟨7403283779141754192953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1263493764973526048930645 7403283779141754192953)
            ·
              rfl

theorem cell20_437942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 9].length) (baseStart_437942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437942 prefixEnd_437942 := by exact prefixLift 437942
  have htrace : WordTrace (prefixWord ++ tailWord_437942) baseStart_437942 baseEnd_437942 := by
    simpa [prefixWord, tailWord_437942, baseEnd_437942] using wordTrace_append hprefix tailTrace_437942
  have hstable : (prefixWord ++ tailWord_437942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437942).length < 2 ^ (prefixWord ++ tailWord_437942).sum := by decide
  have hdescent : baseEnd_437942 < baseStart_437942 := by decide
  rcases family_descends (prefixWord ++ tailWord_437942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437946 : List Nat := [3, 1, 1, 1, 2, 12]
def baseStart_437946 : Nat := 118140960795 + 437946 * 2 ^ 59
def prefixEnd_437946 : Nat := 4983230072969 + 3 ^ 40 * 437946 * 2
def baseEnd_437946 : Nat := 7403351397993375076903

theorem tailTrace_437946 : CollatzResearch.WordTrace tailWord_437946 prefixEnd_437946 7403351397993375076903 := by
  unfold tailWord_437946
  simp only [CollatzResearch.WordTrace]
  refine ⟨3993300717850978016789423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10648801914269274711438461 3993300717850978016789423)
  ·
    refine ⟨5989951076776467025184135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3993300717850978016789423 5989951076776467025184135)
    ·
      refine ⟨8984926615164700537776203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5989951076776467025184135 8984926615164700537776203)
      ·
        refine ⟨13477389922747050806664305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8984926615164700537776203 13477389922747050806664305)
        ·
          refine ⟨10108042442060288104998229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13477389922747050806664305 10108042442060288104998229)
          ·
            refine ⟨7403351397993375076903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 10108042442060288104998229 7403351397993375076903)
            ·
              rfl

theorem cell20_437946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 12].length) (baseStart_437946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437946 prefixEnd_437946 := by exact prefixLift 437946
  have htrace : WordTrace (prefixWord ++ tailWord_437946) baseStart_437946 baseEnd_437946 := by
    simpa [prefixWord, tailWord_437946, baseEnd_437946] using wordTrace_append hprefix tailTrace_437946
  have hstable : (prefixWord ++ tailWord_437946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437946).length < 2 ^ (prefixWord ++ tailWord_437946).sum := by decide
  have hdescent : baseEnd_437946 < baseStart_437946 := by decide
  rcases family_descends (prefixWord ++ tailWord_437946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437949 : List Nat := [1, 4, 1, 2, 1, 2, 4, 2, 3]
def baseStart_437949 : Nat := 118140960795 + 437949 * 2 ^ 59
def prefixEnd_437949 : Nat := 4983230072969 + 3 ^ 40 * 437949 * 2
def baseEnd_437949 : Nat := 199891857027566449976369

theorem tailTrace_437949 : CollatzResearch.WordTrace tailWord_437949 prefixEnd_437949 199891857027566449976369 := by
  unfold tailWord_437949
  simp only [CollatzResearch.WordTrace]
  refine ⟨15973312290393043579516901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10648874860262029053011267 15973312290393043579516901)
  ·
    refine ⟨2994996054448695671159419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15973312290393043579516901 2994996054448695671159419)
    ·
      refine ⟨4492494081673043506739129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2994996054448695671159419 4492494081673043506739129)
      ·
        refine ⟨3369370561254782630054347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4492494081673043506739129 3369370561254782630054347)
        ·
          refine ⟨5054055841882173945081521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3369370561254782630054347 5054055841882173945081521)
          ·
            refine ⟨3790541881411630458811141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5054055841882173945081521 3790541881411630458811141)
            ·
              refine ⟨710726602764680711027089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3790541881411630458811141 710726602764680711027089)
              ·
                refine ⟨533044952073510533270317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 710726602764680711027089 533044952073510533270317)
                ·
                  refine ⟨199891857027566449976369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 533044952073510533270317 199891857027566449976369)
                  ·
                    rfl

theorem cell20_437949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_437949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437949 prefixEnd_437949 := by exact prefixLift 437949
  have htrace : WordTrace (prefixWord ++ tailWord_437949) baseStart_437949 baseEnd_437949 := by
    simpa [prefixWord, tailWord_437949, baseEnd_437949] using wordTrace_append hprefix tailTrace_437949
  have hstable : (prefixWord ++ tailWord_437949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437949).length < 2 ^ (prefixWord ++ tailWord_437949).sum := by decide
  have hdescent : baseEnd_437949 < baseStart_437949 := by decide
  rcases family_descends (prefixWord ++ tailWord_437949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437956 : List Nat := [2, 3, 3, 1, 1, 1, 2, 3, 4]
def baseStart_437956 : Nat := 118140960795 + 437956 * 2 ^ 59
def prefixEnd_437956 : Nat := 4983230072969 + 3 ^ 40 * 437956 * 2
def baseEnd_437956 : Nat := 199895052018305536743007

theorem tailTrace_437956 : CollatzResearch.WordTrace tailWord_437956 prefixEnd_437956 199895052018305536743007 := by
  unfold tailWord_437956
  simp only [CollatzResearch.WordTrace]
  refine ⟨7986783800683841887510861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10649045067578455850014481 7986783800683841887510861)
  ·
    refine ⟨2995043925256440707816573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7986783800683841887510861 2995043925256440707816573)
    ·
      refine ⟨1123141471971165265431215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2995043925256440707816573 1123141471971165265431215)
      ·
        refine ⟨1684712207956747898146823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1123141471971165265431215 1684712207956747898146823)
        ·
          refine ⟨2527068311935121847220235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1684712207956747898146823 2527068311935121847220235)
          ·
            refine ⟨3790602467902682770830353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2527068311935121847220235 3790602467902682770830353)
            ·
              refine ⟨2842951850927012078122765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3790602467902682770830353 2842951850927012078122765)
              ·
                refine ⟨1066106944097629529296037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2842951850927012078122765 1066106944097629529296037)
                ·
                  refine ⟨199895052018305536743007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1066106944097629529296037 199895052018305536743007)
                  ·
                    rfl

theorem cell20_437956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_437956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437956 prefixEnd_437956 := by exact prefixLift 437956
  have htrace : WordTrace (prefixWord ++ tailWord_437956) baseStart_437956 baseEnd_437956 := by
    simpa [prefixWord, tailWord_437956, baseEnd_437956] using wordTrace_append hprefix tailTrace_437956
  have hstable : (prefixWord ++ tailWord_437956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437956).length < 2 ^ (prefixWord ++ tailWord_437956).sum := by decide
  have hdescent : baseEnd_437956 < baseStart_437956 := by decide
  rcases family_descends (prefixWord ++ tailWord_437956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437977 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 6]
def baseStart_437977 : Nat := 118140960795 + 437977 * 2 ^ 59
def prefixEnd_437977 : Nat := 4983230072969 + 3 ^ 40 * 437977 * 2
def baseEnd_437977 : Nat := 199904636990522797042921

theorem tailTrace_437977 : CollatzResearch.WordTrace tailWord_437977 prefixEnd_437977 199904636990522797042921 := by
  unfold tailWord_437977
  simp only [CollatzResearch.WordTrace]
  refine ⟨15974333534291604361536185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10649555689527736241024123 15974333534291604361536185)
  ·
    refine ⟨11980750150718703271152139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15974333534291604361536185 11980750150718703271152139)
    ·
      refine ⟨17971125226078054906728209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11980750150718703271152139 17971125226078054906728209)
      ·
        refine ⟨13478343919558541180046157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17971125226078054906728209 13478343919558541180046157)
        ·
          refine ⟨5054378969834452942517309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13478343919558541180046157 5054378969834452942517309)
          ·
            refine ⟨1895392113687919853443991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5054378969834452942517309 1895392113687919853443991)
            ·
              refine ⟨2843088170531879780165987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1895392113687919853443991 2843088170531879780165987)
              ·
                refine ⟨4264632255797819670248981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2843088170531879780165987 4264632255797819670248981)
                ·
                  refine ⟨199904636990522797042921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4264632255797819670248981 199904636990522797042921)
                  ·
                    rfl

theorem cell20_437977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_437977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_437977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_437977 prefixEnd_437977 := by exact prefixLift 437977
  have htrace : WordTrace (prefixWord ++ tailWord_437977) baseStart_437977 baseEnd_437977 := by
    simpa [prefixWord, tailWord_437977, baseEnd_437977] using wordTrace_append hprefix tailTrace_437977
  have hstable : (prefixWord ++ tailWord_437977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437977).length < 2 ^ (prefixWord ++ tailWord_437977).sum := by decide
  have hdescent : baseEnd_437977 < baseStart_437977 := by decide
  rcases family_descends (prefixWord ++ tailWord_437977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
