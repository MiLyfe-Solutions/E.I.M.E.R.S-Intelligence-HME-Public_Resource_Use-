import V185TrunkScan23Chunk0154

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_916277 : List Nat := [1, 3, 3, 1, 3, 2, 3, 1, 1, 5]
def baseStart_916277 : Nat := 118140960795 + 916277 * 2 ^ 59
def prefixEnd_916277 : Nat := 4983230072969 + 3 ^ 40 * 916277 * 2
def baseEnd_916277 : Nat := 156830171219938931907875

theorem tailTrace_916277 : CollatzResearch.WordTrace tailWord_916277 prefixEnd_916277 156830171219938931907875 := by
  unfold tailWord_916277
  simp only [CollatzResearch.WordTrace]
  refine ⟨33419367701492391498091085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22279578467661594332060723 33419367701492391498091085)
  ·
    refine ⟨12532262888059646811784157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33419367701492391498091085 12532262888059646811784157)
    ·
      refine ⟨4699598583022367554419059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12532262888059646811784157 4699598583022367554419059)
      ·
        refine ⟨7049397874533551331628589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4699598583022367554419059 7049397874533551331628589)
        ·
          refine ⟨2643524202950081749360721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7049397874533551331628589 2643524202950081749360721)
          ·
            refine ⟨1982643152212561312020541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2643524202950081749360721 1982643152212561312020541)
            ·
              refine ⟨743491182079710492007703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1982643152212561312020541 743491182079710492007703)
              ·
                refine ⟨1115236773119565738011555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 743491182079710492007703 1115236773119565738011555)
                ·
                  refine ⟨1672855159679348607017333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1115236773119565738011555 1672855159679348607017333)
                  ·
                    refine ⟨156830171219938931907875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1672855159679348607017333 156830171219938931907875)
                    ·
                      rfl

theorem cell23_916277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_916277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916277 prefixEnd_916277 := by exact prefixLift 916277
  have htrace : WordTrace (prefixWord ++ tailWord_916277) baseStart_916277 baseEnd_916277 := by
    simpa [prefixWord, tailWord_916277, baseEnd_916277] using wordTrace_append hprefix tailTrace_916277
  have hstable : (prefixWord ++ tailWord_916277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916277).length < 2 ^ (prefixWord ++ tailWord_916277).sum := by decide
  have hdescent : baseEnd_916277 < baseStart_916277 := by decide
  rcases family_descends (prefixWord ++ tailWord_916277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916300 : List Nat := [2, 2, 1, 3, 3, 1, 1, 2, 3, 2, 3]
def baseStart_916300 : Nat := 118140960795 + 916300 * 2 ^ 59
def prefixEnd_916300 : Nat := 4983230072969 + 3 ^ 40 * 916300 * 2
def baseEnd_916300 : Nat := 470502323714870205736019

theorem tailTrace_916300 : CollatzResearch.WordTrace tailWord_916300 prefixEnd_916300 470502323714870205736019 := by
  unfold tailWord_916300
  simp only [CollatzResearch.WordTrace]
  refine ⟨16710103290204533213089177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22280137720272710950785569 16710103290204533213089177)
  ·
    refine ⟨12532577467653399909816883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16710103290204533213089177 12532577467653399909816883)
    ·
      refine ⟨18798866201480099864725325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12532577467653399909816883 18798866201480099864725325)
      ·
        refine ⟨7049574825555037449271997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18798866201480099864725325 7049574825555037449271997)
        ·
          refine ⟨2643590559583139043476999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7049574825555037449271997 2643590559583139043476999)
          ·
            refine ⟨3965385839374708565215499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2643590559583139043476999 3965385839374708565215499)
            ·
              refine ⟨5948078759062062847823249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3965385839374708565215499 5948078759062062847823249)
              ·
                refine ⟨4461059069296547135867437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5948078759062062847823249 4461059069296547135867437)
                ·
                  refine ⟨1672897150986205175950289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4461059069296547135867437 1672897150986205175950289)
                  ·
                    refine ⟨1254672863239653881962717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1672897150986205175950289 1254672863239653881962717)
                    ·
                      refine ⟨470502323714870205736019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1254672863239653881962717 470502323714870205736019)
                      ·
                        rfl

theorem cell23_916300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_916300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916300 prefixEnd_916300 := by exact prefixLift 916300
  have htrace : WordTrace (prefixWord ++ tailWord_916300) baseStart_916300 baseEnd_916300 := by
    simpa [prefixWord, tailWord_916300, baseEnd_916300] using wordTrace_append hprefix tailTrace_916300
  have hstable : (prefixWord ++ tailWord_916300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916300).length < 2 ^ (prefixWord ++ tailWord_916300).sum := by decide
  have hdescent : baseEnd_916300 < baseStart_916300 := by decide
  rcases family_descends (prefixWord ++ tailWord_916300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916334 : List Nat := [4, 1, 2, 3, 2, 1, 1, 3, 1, 2, 3]
def baseStart_916334 : Nat := 118140960795 + 916334 * 2 ^ 59
def prefixEnd_916334 : Nat := 4983230072969 + 3 ^ 40 * 916334 * 2
def baseEnd_916334 : Nat := 470519782057123072710863

theorem tailTrace_916334 : CollatzResearch.WordTrace tailWord_916334 prefixEnd_916334 470519782057123072710863 := by
  unfold tailWord_916334
  simp only [CollatzResearch.WordTrace]
  refine ⟨4177680832785736279114507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22280964441523926821944037 4177680832785736279114507)
  ·
    refine ⟨6266521249178604418671761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4177680832785736279114507 6266521249178604418671761)
    ·
      refine ⟨4699890936883953314003821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6266521249178604418671761 4699890936883953314003821)
      ·
        refine ⟨1762459101331482492751433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4699890936883953314003821 1762459101331482492751433)
        ·
          refine ⟨1321844325998611869563575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1762459101331482492751433 1321844325998611869563575)
          ·
            refine ⟨1982766488997917804345363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1321844325998611869563575 1982766488997917804345363)
            ·
              refine ⟨2974149733496876706518045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1982766488997917804345363 2974149733496876706518045)
              ·
                refine ⟨1115306150061328764944267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2974149733496876706518045 1115306150061328764944267)
                ·
                  refine ⟨1672959225091993147416401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1115306150061328764944267 1672959225091993147416401)
                  ·
                    refine ⟨1254719418818994860562301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1672959225091993147416401 1254719418818994860562301)
                    ·
                      refine ⟨470519782057123072710863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1254719418818994860562301 470519782057123072710863)
                      ·
                        rfl

theorem cell23_916334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_916334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916334 prefixEnd_916334 := by exact prefixLift 916334
  have htrace : WordTrace (prefixWord ++ tailWord_916334) baseStart_916334 baseEnd_916334 := by
    simpa [prefixWord, tailWord_916334, baseEnd_916334] using wordTrace_append hprefix tailTrace_916334
  have hstable : (prefixWord ++ tailWord_916334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916334).length < 2 ^ (prefixWord ++ tailWord_916334).sum := by decide
  have hdescent : baseEnd_916334 < baseStart_916334 := by decide
  rcases family_descends (prefixWord ++ tailWord_916334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916347 : List Nat := [1, 1, 1, 1, 1, 5, 5, 2, 2, 1, 3]
def baseStart_916347 : Nat := 118140960795 + 916347 * 2 ^ 59
def prefixEnd_916347 : Nat := 4983230072969 + 3 ^ 40 * 916347 * 2
def baseEnd_916347 : Nat := 470526457305631521848303

theorem tailTrace_916347 : CollatzResearch.WordTrace tailWord_916347 prefixEnd_916347 470526457305631521848303 := by
  unfold tailWord_916347
  simp only [CollatzResearch.WordTrace]
  refine ⟨33421920811238793453139295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22281280540825862302092863 33421920811238793453139295)
  ·
    refine ⟨50132881216858190179708943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33421920811238793453139295 50132881216858190179708943)
    ·
      refine ⟨75199321825287285269563415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50132881216858190179708943 75199321825287285269563415)
      ·
        refine ⟨112798982737930927904345123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75199321825287285269563415 112798982737930927904345123)
        ·
          refine ⟨169198474106896391856517685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112798982737930927904345123 169198474106896391856517685)
          ·
            refine ⟨15862356947521536736548533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 169198474106896391856517685 15862356947521536736548533)
            ·
              refine ⟨1487095963830144069051425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15862356947521536736548533 1487095963830144069051425)
              ·
                refine ⟨1115321972872608051788569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1487095963830144069051425 1115321972872608051788569)
                ·
                  refine ⟨836491479654456038841427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1115321972872608051788569 836491479654456038841427)
                  ·
                    refine ⟨1254737219481684058262141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 836491479654456038841427 1254737219481684058262141)
                    ·
                      refine ⟨470526457305631521848303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1254737219481684058262141 470526457305631521848303)
                      ·
                        rfl

theorem cell23_916347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 2, 1, 3].length) (baseStart_916347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916347 prefixEnd_916347 := by exact prefixLift 916347
  have htrace : WordTrace (prefixWord ++ tailWord_916347) baseStart_916347 baseEnd_916347 := by
    simpa [prefixWord, tailWord_916347, baseEnd_916347] using wordTrace_append hprefix tailTrace_916347
  have hstable : (prefixWord ++ tailWord_916347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916347).length < 2 ^ (prefixWord ++ tailWord_916347).sum := by decide
  have hdescent : baseEnd_916347 < baseStart_916347 := by decide
  rcases family_descends (prefixWord ++ tailWord_916347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916363 : List Nat := [1, 1, 1, 1, 4, 2, 4, 1, 2, 6]
def baseStart_916363 : Nat := 118140960795 + 916363 * 2 ^ 59
def prefixEnd_916363 : Nat := 4983230072969 + 3 ^ 40 * 916363 * 2
def baseEnd_916363 : Nat := 156844890998701153082743

theorem tailTrace_916363 : CollatzResearch.WordTrace tailWord_916363 prefixEnd_916363 156844890998701153082743 := by
  unfold tailWord_916363
  simp only [CollatzResearch.WordTrace]
  refine ⟨33422504379180828185721743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22281669586120552123814495 33422504379180828185721743)
  ·
    refine ⟨50133756568771242278582615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33422504379180828185721743 50133756568771242278582615)
    ·
      refine ⟨75200634853156863417873923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50133756568771242278582615 75200634853156863417873923)
      ·
        refine ⟨112800952279735295126810885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75200634853156863417873923 112800952279735295126810885)
        ·
          refine ⟨21150178552450367836277041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112800952279735295126810885 21150178552450367836277041)
          ·
            refine ⟨15862633914337775877207781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21150178552450367836277041 15862633914337775877207781)
            ·
              refine ⟨2974243858938332976976459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15862633914337775877207781 2974243858938332976976459)
              ·
                refine ⟨4461365788407499465464689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2974243858938332976976459 4461365788407499465464689)
                ·
                  refine ⟨3346024341305624599098517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4461365788407499465464689 3346024341305624599098517)
                  ·
                    refine ⟨156844890998701153082743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3346024341305624599098517 156844890998701153082743)
                    ·
                      rfl

theorem cell23_916363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 6].length) (baseStart_916363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916363 prefixEnd_916363 := by exact prefixLift 916363
  have htrace : WordTrace (prefixWord ++ tailWord_916363) baseStart_916363 baseEnd_916363 := by
    simpa [prefixWord, tailWord_916363, baseEnd_916363] using wordTrace_append hprefix tailTrace_916363
  have hstable : (prefixWord ++ tailWord_916363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916363).length < 2 ^ (prefixWord ++ tailWord_916363).sum := by decide
  have hdescent : baseEnd_916363 < baseStart_916363 := by decide
  rcases family_descends (prefixWord ++ tailWord_916363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916387 : List Nat := [1, 1, 1, 4, 1, 2, 3, 2, 4, 2, 2]
def baseStart_916387 : Nat := 118140960795 + 916387 * 2 ^ 59
def prefixEnd_916387 : Nat := 4983230072969 + 3 ^ 40 * 916387 * 2
def baseEnd_916387 : Nat := 470546996531811365348119

theorem tailTrace_916387 : CollatzResearch.WordTrace tailWord_916387 prefixEnd_916387 470546996531811365348119 := by
  unfold tailWord_916387
  simp only [CollatzResearch.WordTrace]
  refine ⟨33423379731093880284595415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22282253154062586856396943 33423379731093880284595415)
  ·
    refine ⟨50135069596640820426893123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33423379731093880284595415 50135069596640820426893123)
    ·
      refine ⟨75202604394961230640339685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50135069596640820426893123 75202604394961230640339685)
      ·
        refine ⟨14100488324055230745063691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75202604394961230640339685 14100488324055230745063691)
        ·
          refine ⟨21150732486082846117595537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14100488324055230745063691 21150732486082846117595537)
          ·
            refine ⟨15863049364562134588196653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21150732486082846117595537 15863049364562134588196653)
            ·
              refine ⟨5948643511710800470573745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15863049364562134588196653 5948643511710800470573745)
              ·
                refine ⟨4461482633783100352930309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5948643511710800470573745 4461482633783100352930309)
                ·
                  refine ⟨836527993834331316174433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4461482633783100352930309 836527993834331316174433)
                  ·
                    refine ⟨627395995375748487130825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 836527993834331316174433 627395995375748487130825)
                    ·
                      refine ⟨470546996531811365348119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 627395995375748487130825 470546996531811365348119)
                      ·
                        rfl

theorem cell23_916387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 4, 2, 2].length) (baseStart_916387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916387 prefixEnd_916387 := by exact prefixLift 916387
  have htrace : WordTrace (prefixWord ++ tailWord_916387) baseStart_916387 baseEnd_916387 := by
    simpa [prefixWord, tailWord_916387, baseEnd_916387] using wordTrace_append hprefix tailTrace_916387
  have hstable : (prefixWord ++ tailWord_916387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916387).length < 2 ^ (prefixWord ++ tailWord_916387).sum := by decide
  have hdescent : baseEnd_916387 < baseStart_916387 := by decide
  rcases family_descends (prefixWord ++ tailWord_916387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916423 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 3, 7]
def baseStart_916423 : Nat := 118140960795 + 916423 * 2 ^ 59
def prefixEnd_916423 : Nat := 4983230072969 + 3 ^ 40 * 916423 * 2
def baseEnd_916423 : Nat := 156855160611791074832651

theorem tailTrace_916423 : CollatzResearch.WordTrace tailWord_916423 prefixEnd_916423 156855160611791074832651 := by
  unfold tailWord_916423
  simp only [CollatzResearch.WordTrace]
  refine ⟨33424692758963458432905923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22283128505975638955270615 33424692758963458432905923)
  ·
    refine ⟨50137039138445187649358885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33424692758963458432905923 50137039138445187649358885)
    ·
      refine ⟨9400694838458472684254791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50137039138445187649358885 9400694838458472684254791)
      ·
        refine ⟨14101042257687709026382187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9400694838458472684254791 14101042257687709026382187)
        ·
          refine ⟨21151563386531563539573281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14101042257687709026382187 21151563386531563539573281)
          ·
            refine ⟨15863672539898672654679961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21151563386531563539573281 15863672539898672654679961)
            ·
              refine ⟨11897754404924004491009971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15863672539898672654679961 11897754404924004491009971)
              ·
                refine ⟨17846631607386006736514957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11897754404924004491009971 17846631607386006736514957)
                ·
                  refine ⟨6692486852769752526193109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17846631607386006736514957 6692486852769752526193109)
                  ·
                    refine ⟨156855160611791074832651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6692486852769752526193109 156855160611791074832651)
                    ·
                      rfl

theorem cell23_916423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_916423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916423 prefixEnd_916423 := by exact prefixLift 916423
  have htrace : WordTrace (prefixWord ++ tailWord_916423) baseStart_916423 baseEnd_916423 := by
    simpa [prefixWord, tailWord_916423, baseEnd_916423] using wordTrace_append hprefix tailTrace_916423
  have hstable : (prefixWord ++ tailWord_916423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916423).length < 2 ^ (prefixWord ++ tailWord_916423).sum := by decide
  have hdescent : baseEnd_916423 < baseStart_916423 := by decide
  rcases family_descends (prefixWord ++ tailWord_916423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916433 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 1, 1, 7]
def baseStart_916433 : Nat := 118140960795 + 916433 * 2 ^ 59
def prefixEnd_916433 : Nat := 4983230072969 + 3 ^ 40 * 916433 * 2
def baseEnd_916433 : Nat := 470570616641918185372907

theorem tailTrace_916433 : CollatzResearch.WordTrace tailWord_916433 prefixEnd_916433 470570616641918185372907 := by
  unfold tailWord_916433
  simp only [CollatzResearch.WordTrace]
  refine ⟨33425057488927230140769953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22283371659284820093846635 33425057488927230140769953)
  ·
    refine ⟨25068793116695422605577465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33425057488927230140769953 25068793116695422605577465)
    ·
      refine ⟨18801594837521566954183099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25068793116695422605577465 18801594837521566954183099)
      ·
        refine ⟨28202392256282350431274649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18801594837521566954183099 28202392256282350431274649)
        ·
          refine ⟨21151794192211762823455987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28202392256282350431274649 21151794192211762823455987)
          ·
            refine ⟨31727691288317644235183981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21151794192211762823455987 31727691288317644235183981)
            ·
              refine ⟨11897884233119116588193993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31727691288317644235183981 11897884233119116588193993)
              ·
                refine ⟨8923413174839337441145495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11897884233119116588193993 8923413174839337441145495)
                ·
                  refine ⟨13385119762259006161718243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8923413174839337441145495 13385119762259006161718243)
                  ·
                    refine ⟨20077679643388509242577365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13385119762259006161718243 20077679643388509242577365)
                    ·
                      refine ⟨470570616641918185372907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 20077679643388509242577365 470570616641918185372907)
                      ·
                        rfl

theorem cell23_916433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_916433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916433 prefixEnd_916433 := by exact prefixLift 916433
  have htrace : WordTrace (prefixWord ++ tailWord_916433) baseStart_916433 baseEnd_916433 := by
    simpa [prefixWord, tailWord_916433, baseEnd_916433] using wordTrace_append hprefix tailTrace_916433
  have hstable : (prefixWord ++ tailWord_916433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916433).length < 2 ^ (prefixWord ++ tailWord_916433).sum := by decide
  have hdescent : baseEnd_916433 < baseStart_916433 := by decide
  rcases family_descends (prefixWord ++ tailWord_916433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916440 : List Nat := [2, 1, 2, 2, 2, 3, 1, 3, 2, 5]
def baseStart_916440 : Nat := 118140960795 + 916440 * 2 ^ 59
def prefixEnd_916440 : Nat := 4983230072969 + 3 ^ 40 * 916440 * 2
def baseEnd_916440 : Nat := 156858070335499885995125

theorem tailTrace_916440 : CollatzResearch.WordTrace tailWord_916440 prefixEnd_916440 156858070335499885995125 := by
  unfold tailWord_916440
  simp only [CollatzResearch.WordTrace]
  refine ⟨16712656399950935168137387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22283541866601246890849849 16712656399950935168137387)
  ·
    refine ⟨25068984599926402752206081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16712656399950935168137387 25068984599926402752206081)
    ·
      refine ⟨18801738449944802064154561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25068984599926402752206081 18801738449944802064154561)
      ·
        refine ⟨14101303837458601548115921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18801738449944802064154561 14101303837458601548115921)
        ·
          refine ⟨10575977878093951161086941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14101303837458601548115921 10575977878093951161086941)
          ·
            refine ⟨3965991704285231685407603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10575977878093951161086941 3965991704285231685407603)
            ·
              refine ⟨5948987556427847528111405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3965991704285231685407603 5948987556427847528111405)
              ·
                refine ⟨2230870333660442823041777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5948987556427847528111405 2230870333660442823041777)
                ·
                  refine ⟨1673152750245332117281333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2230870333660442823041777 1673152750245332117281333)
                  ·
                    refine ⟨156858070335499885995125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1673152750245332117281333 156858070335499885995125)
                    ·
                      rfl

theorem cell23_916440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 2, 5].length) (baseStart_916440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916440 prefixEnd_916440 := by exact prefixLift 916440
  have htrace : WordTrace (prefixWord ++ tailWord_916440) baseStart_916440 baseEnd_916440 := by
    simpa [prefixWord, tailWord_916440, baseEnd_916440] using wordTrace_append hprefix tailTrace_916440
  have hstable : (prefixWord ++ tailWord_916440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916440).length < 2 ^ (prefixWord ++ tailWord_916440).sum := by decide
  have hdescent : baseEnd_916440 < baseStart_916440 := by decide
  rcases family_descends (prefixWord ++ tailWord_916440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916443 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 4]
def baseStart_916443 : Nat := 118140960795 + 916443 * 2 ^ 59
def prefixEnd_916443 : Nat := 4983230072969 + 3 ^ 40 * 916443 * 2
def baseEnd_916443 : Nat := 470575751448463146247861

theorem tailTrace_916443 : CollatzResearch.WordTrace tailWord_916443 prefixEnd_916443 470575751448463146247861 := by
  unfold tailWord_916443
  simp only [CollatzResearch.WordTrace]
  refine ⟨33425422218891001848633983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22283614812594001232422655 33425422218891001848633983)
  ·
    refine ⟨50138133328336502772950975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33425422218891001848633983 50138133328336502772950975)
    ·
      refine ⟨75207199992504754159426463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50138133328336502772950975 75207199992504754159426463)
      ·
        refine ⟨112810799988757131239139695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75207199992504754159426463 112810799988757131239139695)
        ·
          refine ⟨169216199983135696858709543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112810799988757131239139695 169216199983135696858709543)
          ·
            refine ⟨253824299974703545288064315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169216199983135696858709543 253824299974703545288064315)
            ·
              refine ⟨380736449962055317932096473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253824299974703545288064315 380736449962055317932096473)
              ·
                refine ⟨285552337471541488449072355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 380736449962055317932096473 285552337471541488449072355)
                ·
                  refine ⟨428328506207312232673608533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 285552337471541488449072355 428328506207312232673608533)
                  ·
                    refine ⟨2509737341058470113321925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 428328506207312232673608533 2509737341058470113321925)
                    ·
                      refine ⟨470575751448463146247861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2509737341058470113321925 470575751448463146247861)
                      ·
                        rfl

theorem cell23_916443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 4].length) (baseStart_916443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916443 prefixEnd_916443 := by exact prefixLift 916443
  have htrace : WordTrace (prefixWord ++ tailWord_916443) baseStart_916443 baseEnd_916443 := by
    simpa [prefixWord, tailWord_916443, baseEnd_916443] using wordTrace_append hprefix tailTrace_916443
  have hstable : (prefixWord ++ tailWord_916443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916443).length < 2 ^ (prefixWord ++ tailWord_916443).sum := by decide
  have hdescent : baseEnd_916443 < baseStart_916443 := by decide
  rcases family_descends (prefixWord ++ tailWord_916443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916468 : List Nat := [2, 6, 2, 1, 1, 1, 1, 1, 2, 2, 4]
def baseStart_916468 : Nat := 118140960795 + 916468 * 2 ^ 59
def prefixEnd_916468 : Nat := 4983230072969 + 3 ^ 40 * 916468 * 2
def baseEnd_916468 : Nat := 470588588464825548435247

theorem tailTrace_916468 : CollatzResearch.WordTrace tailWord_916468 prefixEnd_916468 470588588464825548435247 := by
  unfold tailWord_916468
  simp only [CollatzResearch.WordTrace]
  refine ⟨16713167021900215559147029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22284222695866954078862705 16713167021900215559147029)
  ·
    refine ⟨783429704151572604335017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16713167021900215559147029 783429704151572604335017)
    ·
      refine ⟨587572278113679453251263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 783429704151572604335017 587572278113679453251263)
      ·
        refine ⟨881358417170519179876895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 587572278113679453251263 881358417170519179876895)
        ·
          refine ⟨1322037625755778769815343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 881358417170519179876895 1322037625755778769815343)
          ·
            refine ⟨1983056438633668154723015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1322037625755778769815343 1983056438633668154723015)
            ·
              refine ⟨2974584657950502232084523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1983056438633668154723015 2974584657950502232084523)
              ·
                refine ⟨4461876986925753348126785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2974584657950502232084523 4461876986925753348126785)
                ·
                  refine ⟨3346407740194315011095089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4461876986925753348126785 3346407740194315011095089)
                  ·
                    refine ⟨2509805805145736258321317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3346407740194315011095089 2509805805145736258321317)
                    ·
                      refine ⟨470588588464825548435247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2509805805145736258321317 470588588464825548435247)
                      ·
                        rfl

theorem cell23_916468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_916468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916468 prefixEnd_916468 := by exact prefixLift 916468
  have htrace : WordTrace (prefixWord ++ tailWord_916468) baseStart_916468 baseEnd_916468 := by
    simpa [prefixWord, tailWord_916468, baseEnd_916468] using wordTrace_append hprefix tailTrace_916468
  have hstable : (prefixWord ++ tailWord_916468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916468).length < 2 ^ (prefixWord ++ tailWord_916468).sum := by decide
  have hdescent : baseEnd_916468 < baseStart_916468 := by decide
  rcases family_descends (prefixWord ++ tailWord_916468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916483 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 12]
def baseStart_916483 : Nat := 118140960795 + 916483 * 2 ^ 59
def prefixEnd_916483 : Nat := 4983230072969 + 3 ^ 40 * 916483 * 2
def baseEnd_916483 : Nat := 52288476741626998860853

theorem tailTrace_916483 : CollatzResearch.WordTrace tailWord_916483 prefixEnd_916483 52288476741626998860853 := by
  unfold tailWord_916483
  simp only [CollatzResearch.WordTrace]
  refine ⟨33426881138746088680090103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22284587425830725786726735 33426881138746088680090103)
  ·
    refine ⟨50140321708119133020135155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33426881138746088680090103 50140321708119133020135155)
    ·
      refine ⟨75210482562178699530202733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50140321708119133020135155 75210482562178699530202733)
      ·
        refine ⟨28203930960817012323826025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75210482562178699530202733 28203930960817012323826025)
        ·
          refine ⟨21152948220612759242869519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28203930960817012323826025 21152948220612759242869519)
          ·
            refine ⟨31729422330919138864304279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21152948220612759242869519 31729422330919138864304279)
            ·
              refine ⟨47594133496378708296456419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31729422330919138864304279 47594133496378708296456419)
              ·
                refine ⟨71391200244568062444684629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47594133496378708296456419 71391200244568062444684629)
                ·
                  refine ⟨52288476741626998860853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 71391200244568062444684629 52288476741626998860853)
                  ·
                    rfl

theorem cell23_916483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 12].length) (baseStart_916483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916483 prefixEnd_916483 := by exact prefixLift 916483
  have htrace : WordTrace (prefixWord ++ tailWord_916483) baseStart_916483 baseEnd_916483 := by
    simpa [prefixWord, tailWord_916483, baseEnd_916483] using wordTrace_append hprefix tailTrace_916483
  have hstable : (prefixWord ++ tailWord_916483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916483).length < 2 ^ (prefixWord ++ tailWord_916483).sum := by decide
  have hdescent : baseEnd_916483 < baseStart_916483 := by decide
  rcases family_descends (prefixWord ++ tailWord_916483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916487 : List Nat := [1, 1, 4, 3, 1, 1, 3, 2, 3, 4]
def baseStart_916487 : Nat := 118140960795 + 916487 * 2 ^ 59
def prefixEnd_916487 : Nat := 4983230072969 + 3 ^ 40 * 916487 * 2
def baseEnd_916487 : Nat := 156866114865753658032553

theorem tailTrace_916487 : CollatzResearch.WordTrace tailWord_916487 prefixEnd_916487 156866114865753658032553 := by
  unfold tailWord_916487
  simp only [CollatzResearch.WordTrace]
  refine ⟨33427027030731597363235715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22284684687154398242157143 33427027030731597363235715)
  ·
    refine ⟨50140540546097396044853573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33427027030731597363235715 50140540546097396044853573)
    ·
      refine ⟨9401351352393261758410045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50140540546097396044853573 9401351352393261758410045)
      ·
        refine ⟨3525506757147473159403767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9401351352393261758410045 3525506757147473159403767)
        ·
          refine ⟨5288260135721209739105651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3525506757147473159403767 5288260135721209739105651)
          ·
            refine ⟨7932390203581814608658477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5288260135721209739105651 7932390203581814608658477)
            ·
              refine ⟨2974646326343180478246929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7932390203581814608658477 2974646326343180478246929)
              ·
                refine ⟨2230984744757385358685197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2974646326343180478246929 2230984744757385358685197)
                ·
                  refine ⟨836619279284019509506949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2230984744757385358685197 836619279284019509506949)
                  ·
                    refine ⟨156866114865753658032553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 836619279284019509506949 156866114865753658032553)
                    ·
                      rfl

theorem cell23_916487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_916487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916487 prefixEnd_916487 := by exact prefixLift 916487
  have htrace : WordTrace (prefixWord ++ tailWord_916487) baseStart_916487 baseEnd_916487 := by
    simpa [prefixWord, tailWord_916487, baseEnd_916487] using wordTrace_append hprefix tailTrace_916487
  have hstable : (prefixWord ++ tailWord_916487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916487).length < 2 ^ (prefixWord ++ tailWord_916487).sum := by decide
  have hdescent : baseEnd_916487 < baseStart_916487 := by decide
  rcases family_descends (prefixWord ++ tailWord_916487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916494 : List Nat := [4, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4]
def baseStart_916494 : Nat := 118140960795 + 916494 * 2 ^ 59
def prefixEnd_916494 : Nat := 4983230072969 + 3 ^ 40 * 916494 * 2
def baseEnd_916494 : Nat := 470601938961842446710127

theorem tailTrace_916494 : CollatzResearch.WordTrace tailWord_916494 prefixEnd_916494 470601938961842446710127 := by
  unfold tailWord_916494
  simp only [CollatzResearch.WordTrace]
  refine ⟨4178410292713279694842567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22284854894470825039160357 4178410292713279694842567)
  ·
    refine ⟨6267615439069919542263851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4178410292713279694842567 6267615439069919542263851)
    ·
      refine ⟨9401423158604879313395777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6267615439069919542263851 9401423158604879313395777)
      ·
        refine ⟨7051067368953659485046833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9401423158604879313395777 7051067368953659485046833)
        ·
          refine ⟨5288300526715244613785125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7051067368953659485046833 5288300526715244613785125)
          ·
            refine ⟨991556348759108365084711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5288300526715244613785125 991556348759108365084711)
            ·
              refine ⟨1487334523138662547627067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 991556348759108365084711 1487334523138662547627067)
              ·
                refine ⟨2231001784707993821440601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1487334523138662547627067 2231001784707993821440601)
                ·
                  refine ⟨1673251338530995366080451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2231001784707993821440601 1673251338530995366080451)
                  ·
                    refine ⟨2509877007796493049120677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1673251338530995366080451 2509877007796493049120677)
                    ·
                      refine ⟨470601938961842446710127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2509877007796493049120677 470601938961842446710127)
                      ·
                        rfl

theorem cell23_916494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_916494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916494 prefixEnd_916494 := by exact prefixLift 916494
  have htrace : WordTrace (prefixWord ++ tailWord_916494) baseStart_916494 baseEnd_916494 := by
    simpa [prefixWord, tailWord_916494, baseEnd_916494] using wordTrace_append hprefix tailTrace_916494
  have hstable : (prefixWord ++ tailWord_916494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916494).length < 2 ^ (prefixWord ++ tailWord_916494).sum := by decide
  have hdescent : baseEnd_916494 < baseStart_916494 := by decide
  rcases family_descends (prefixWord ++ tailWord_916494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916504 : List Nat := [2, 1, 2, 3, 2, 2, 1, 5, 1, 4]
def baseStart_916504 : Nat := 118140960795 + 916504 * 2 ^ 59
def prefixEnd_916504 : Nat := 4983230072969 + 3 ^ 40 * 916504 * 2
def baseEnd_916504 : Nat := 156869024589462469195027

theorem tailTrace_916504 : CollatzResearch.WordTrace tailWord_916504 prefixEnd_916504 156869024589462469195027 := by
  unfold tailWord_916504
  simp only [CollatzResearch.WordTrace]
  refine ⟨16713823535835004633302283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22285098047780006177736377 16713823535835004633302283)
  ·
    refine ⟨25070735303752506949953425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16713823535835004633302283 25070735303752506949953425)
    ·
      refine ⟨18803051477814380212465069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25070735303752506949953425 18803051477814380212465069)
      ·
        refine ⟨7051144304180392579674401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18803051477814380212465069 7051144304180392579674401)
        ·
          refine ⟨5288358228135294434755801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7051144304180392579674401 5288358228135294434755801)
          ·
            refine ⟨3966268671101470826066851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5288358228135294434755801 3966268671101470826066851)
            ·
              refine ⟨5949403006652206239100277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3966268671101470826066851 5949403006652206239100277)
              ·
                refine ⟨557756531873644334915651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5949403006652206239100277 557756531873644334915651)
                ·
                  refine ⟨836634797810466502373477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 557756531873644334915651 836634797810466502373477)
                  ·
                    refine ⟨156869024589462469195027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 836634797810466502373477 156869024589462469195027)
                    ·
                      rfl

theorem cell23_916504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 5, 1, 4].length) (baseStart_916504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916504 prefixEnd_916504 := by exact prefixLift 916504
  have htrace : WordTrace (prefixWord ++ tailWord_916504) baseStart_916504 baseEnd_916504 := by
    simpa [prefixWord, tailWord_916504, baseEnd_916504] using wordTrace_append hprefix tailTrace_916504
  have hstable : (prefixWord ++ tailWord_916504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916504).length < 2 ^ (prefixWord ++ tailWord_916504).sum := by decide
  have hdescent : baseEnd_916504 < baseStart_916504 := by decide
  rcases family_descends (prefixWord ++ tailWord_916504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916547 : List Nat := [1, 1, 1, 3, 1, 2, 6, 2, 1, 5]
def baseStart_916547 : Nat := 118140960795 + 916547 * 2 ^ 59
def prefixEnd_916547 : Nat := 4983230072969 + 3 ^ 40 * 916547 * 2
def baseEnd_916547 : Nat := 156876384478843579782461

theorem tailTrace_916547 : CollatzResearch.WordTrace tailWord_916547 prefixEnd_916547 156876384478843579782461 := by
  unfold tailWord_916547
  simp only [CollatzResearch.WordTrace]
  refine ⟨33429215410514227610419895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22286143607009485073613263 33429215410514227610419895)
  ·
    refine ⟨50143823115771341415629843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33429215410514227610419895 50143823115771341415629843)
    ·
      refine ⟨75215734673657012123444765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50143823115771341415629843 75215734673657012123444765)
      ·
        refine ⟨28205900502621379546291787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75215734673657012123444765 28205900502621379546291787)
        ·
          refine ⟨42308850753932069319437681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28205900502621379546291787 42308850753932069319437681)
          ·
            refine ⟨31731638065449051989578261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42308850753932069319437681 31731638065449051989578261)
            ·
              refine ⟨1487420534317924312011481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31731638065449051989578261 1487420534317924312011481)
              ·
                refine ⟨1115565400738443234008611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1487420534317924312011481 1115565400738443234008611)
                ·
                  refine ⟨1673348101107664851012917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1115565400738443234008611 1673348101107664851012917)
                  ·
                    refine ⟨156876384478843579782461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1673348101107664851012917 156876384478843579782461)
                    ·
                      rfl

theorem cell23_916547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 5].length) (baseStart_916547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916547 prefixEnd_916547 := by exact prefixLift 916547
  have htrace : WordTrace (prefixWord ++ tailWord_916547) baseStart_916547 baseEnd_916547 := by
    simpa [prefixWord, tailWord_916547, baseEnd_916547] using wordTrace_append hprefix tailTrace_916547
  have hstable : (prefixWord ++ tailWord_916547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916547).length < 2 ^ (prefixWord ++ tailWord_916547).sum := by decide
  have hdescent : baseEnd_916547 < baseStart_916547 := by decide
  rcases family_descends (prefixWord ++ tailWord_916547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916560 : List Nat := [2, 1, 1, 1, 1, 3, 1, 6, 1, 6]
def baseStart_916560 : Nat := 118140960795 + 916560 * 2 ^ 59
def prefixEnd_916560 : Nat := 4983230072969 + 3 ^ 40 * 916560 * 2
def baseEnd_916560 : Nat := 156878609561679729494941

theorem tailTrace_916560 : CollatzResearch.WordTrace tailWord_916560 prefixEnd_916560 156878609561679729494941 := by
  unfold tailWord_916560
  simp only [CollatzResearch.WordTrace]
  refine ⟨16714844779733565415321567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22286459706311420553762089 16714844779733565415321567)
  ·
    refine ⟨25072267169600348122982351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16714844779733565415321567 25072267169600348122982351)
    ·
      refine ⟨37608400754400522184473527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25072267169600348122982351 37608400754400522184473527)
      ·
        refine ⟨56412601131600783276710291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37608400754400522184473527 56412601131600783276710291)
        ·
          refine ⟨84618901697401174915065437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56412601131600783276710291 84618901697401174915065437)
          ·
            refine ⟨31732088136525440593149539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84618901697401174915065437 31732088136525440593149539)
            ·
              refine ⟨47598132204788160889724309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31732088136525440593149539 47598132204788160889724309)
              ·
                refine ⟨2231162447099445041705827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47598132204788160889724309 2231162447099445041705827)
                ·
                  refine ⟨3346743670649167562558741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2231162447099445041705827 3346743670649167562558741)
                  ·
                    refine ⟨156878609561679729494941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3346743670649167562558741 156878609561679729494941)
                    ·
                      rfl

theorem cell23_916560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 1, 6].length) (baseStart_916560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916560 prefixEnd_916560 := by exact prefixLift 916560
  have htrace : WordTrace (prefixWord ++ tailWord_916560) baseStart_916560 baseEnd_916560 := by
    simpa [prefixWord, tailWord_916560, baseEnd_916560] using wordTrace_append hprefix tailTrace_916560
  have hstable : (prefixWord ++ tailWord_916560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916560).length < 2 ^ (prefixWord ++ tailWord_916560).sum := by decide
  have hdescent : baseEnd_916560 < baseStart_916560 := by decide
  rcases family_descends (prefixWord ++ tailWord_916560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916561 : List Nat := [1, 2, 2, 1, 3, 1, 5, 3, 1, 1, 3]
def baseStart_916561 : Nat := 118140960795 + 916561 * 2 ^ 59
def prefixEnd_916561 : Nat := 4983230072969 + 3 ^ 40 * 916561 * 2
def baseEnd_916561 : Nat := 470636342165693684572319

theorem tailTrace_916561 : CollatzResearch.WordTrace tailWord_916561 prefixEnd_916561 470636342165693684572319 := by
  unfold tailWord_916561
  simp only [CollatzResearch.WordTrace]
  refine ⟨33429726032463508001429537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22286484021642338667619691 33429726032463508001429537)
  ·
    refine ⟨25072294524347631001072153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33429726032463508001429537 25072294524347631001072153)
    ·
      refine ⟨18804220893260723250804115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25072294524347631001072153 18804220893260723250804115)
      ·
        refine ⟨28206331339891084876206173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18804220893260723250804115 28206331339891084876206173)
        ·
          refine ⟨10577374252459156828577315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28206331339891084876206173 10577374252459156828577315)
          ·
            refine ⟨15866061378688735242865973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10577374252459156828577315 15866061378688735242865973)
            ·
              refine ⟨1487443254252068929018685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15866061378688735242865973 1487443254252068929018685)
              ·
                refine ⟨557791220344525848382007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1487443254252068929018685 557791220344525848382007)
                ·
                  refine ⟨836686830516788772573011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 557791220344525848382007 836686830516788772573011)
                  ·
                    refine ⟨1255030245775183158859517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 836686830516788772573011 1255030245775183158859517)
                    ·
                      refine ⟨470636342165693684572319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1255030245775183158859517 470636342165693684572319)
                      ·
                        rfl

theorem cell23_916561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 3, 1, 1, 3].length) (baseStart_916561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916561 prefixEnd_916561 := by exact prefixLift 916561
  have htrace : WordTrace (prefixWord ++ tailWord_916561) baseStart_916561 baseEnd_916561 := by
    simpa [prefixWord, tailWord_916561, baseEnd_916561] using wordTrace_append hprefix tailTrace_916561
  have hstable : (prefixWord ++ tailWord_916561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916561).length < 2 ^ (prefixWord ++ tailWord_916561).sum := by decide
  have hdescent : baseEnd_916561 < baseStart_916561 := by decide
  rcases family_descends (prefixWord ++ tailWord_916561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916577 : List Nat := [1, 2, 3, 1, 1, 2, 4, 1, 4, 4]
def baseStart_916577 : Nat := 118140960795 + 916577 * 2 ^ 59
def prefixEnd_916577 : Nat := 4983230072969 + 3 ^ 40 * 916577 * 2
def baseEnd_916577 : Nat := 156881519285388540657415

theorem tailTrace_916577 : CollatzResearch.WordTrace tailWord_916577 prefixEnd_916577 156881519285388540657415 := by
  unfold tailWord_916577
  simp only [CollatzResearch.WordTrace]
  refine ⟨33430309600405542734011985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22286873066937028489341323 33430309600405542734011985)
  ·
    refine ⟨25072732200304157050508989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33430309600405542734011985 25072732200304157050508989)
    ·
      refine ⟨9402274575114058893940871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25072732200304157050508989 9402274575114058893940871)
      ·
        refine ⟨14103411862671088340911307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9402274575114058893940871 14103411862671088340911307)
        ·
          refine ⟨21155117794006632511366961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14103411862671088340911307 21155117794006632511366961)
          ·
            refine ⟨15866338345504974383525221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21155117794006632511366961 15866338345504974383525221)
            ·
              refine ⟨2974938439782182696910979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15866338345504974383525221 2974938439782182696910979)
              ·
                refine ⟨4462407659673274045366469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2974938439782182696910979 4462407659673274045366469)
                ·
                  refine ⟨836701436188738883506213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4462407659673274045366469 836701436188738883506213)
                  ·
                    refine ⟨156881519285388540657415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 836701436188738883506213 156881519285388540657415)
                    ·
                      rfl

theorem cell23_916577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_916577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916577 prefixEnd_916577 := by exact prefixLift 916577
  have htrace : WordTrace (prefixWord ++ tailWord_916577) baseStart_916577 baseEnd_916577 := by
    simpa [prefixWord, tailWord_916577, baseEnd_916577] using wordTrace_append hprefix tailTrace_916577
  have hstable : (prefixWord ++ tailWord_916577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916577).length < 2 ^ (prefixWord ++ tailWord_916577).sum := by decide
  have hdescent : baseEnd_916577 < baseStart_916577 := by decide
  rcases family_descends (prefixWord ++ tailWord_916577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916578 : List Nat := [3, 3, 2, 2, 1, 3, 1, 1, 3, 1, 3]
def baseStart_916578 : Nat := 118140960795 + 916578 * 2 ^ 59
def prefixEnd_916578 : Nat := 4983230072969 + 3 ^ 40 * 916578 * 2
def baseEnd_916578 : Nat := 470645071336820118059741

theorem tailTrace_916578 : CollatzResearch.WordTrace tailWord_916578 prefixEnd_916578 470645071336820118059741 := by
  unfold tailWord_916578
  simp only [CollatzResearch.WordTrace]
  refine ⟨8357586518350479976199597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22286897382267946603198925 8357586518350479976199597)
  ·
    refine ⟨3134094944381429991074849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8357586518350479976199597 3134094944381429991074849)
    ·
      refine ⟨2350571208286072493306137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3134094944381429991074849 2350571208286072493306137)
      ·
        refine ⟨1762928406214554369979603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2350571208286072493306137 1762928406214554369979603)
        ·
          refine ⟨2644392609321831554969405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1762928406214554369979603 2644392609321831554969405)
          ·
            refine ⟨991647228495686833113527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2644392609321831554969405 991647228495686833113527)
            ·
              refine ⟨1487470842743530249670291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 991647228495686833113527 1487470842743530249670291)
              ·
                refine ⟨2231206264115295374505437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1487470842743530249670291 2231206264115295374505437)
                ·
                  refine ⟨836702349043235765439539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2231206264115295374505437 836702349043235765439539)
                  ·
                    refine ⟨1255053523564853648159309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 836702349043235765439539 1255053523564853648159309)
                    ·
                      refine ⟨470645071336820118059741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1255053523564853648159309 470645071336820118059741)
                      ·
                        rfl

theorem cell23_916578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_916578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916578 prefixEnd_916578 := by exact prefixLift 916578
  have htrace : WordTrace (prefixWord ++ tailWord_916578) baseStart_916578 baseEnd_916578 := by
    simpa [prefixWord, tailWord_916578, baseEnd_916578] using wordTrace_append hprefix tailTrace_916578
  have hstable : (prefixWord ++ tailWord_916578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916578).length < 2 ^ (prefixWord ++ tailWord_916578).sum := by decide
  have hdescent : baseEnd_916578 < baseStart_916578 := by decide
  rcases family_descends (prefixWord ++ tailWord_916578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916594 : List Nat := [3, 2, 1, 2, 2, 1, 3, 3, 2, 4]
def baseStart_916594 : Nat := 118140960795 + 916594 * 2 ^ 59
def prefixEnd_916594 : Nat := 4983230072969 + 3 ^ 40 * 916594 * 2
def baseEnd_916594 : Nat := 156884429009097351819889

theorem tailTrace_916594 : CollatzResearch.WordTrace tailWord_916594 prefixEnd_916594 156884429009097351819889 := by
  unfold tailWord_916594
  simp only [CollatzResearch.WordTrace]
  refine ⟨8357732410335988659345209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22287286427562636424920557 8357732410335988659345209)
  ·
    refine ⟨6268299307751991494508907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8357732410335988659345209 6268299307751991494508907)
    ·
      refine ⟨9402448961627987241763361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6268299307751991494508907 9402448961627987241763361)
      ·
        refine ⟨7051836721220990431322521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9402448961627987241763361 7051836721220990431322521)
        ·
          refine ⟨5288877540915742823491891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7051836721220990431322521 5288877540915742823491891)
          ·
            refine ⟨7933316311373614235237837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5288877540915742823491891 7933316311373614235237837)
            ·
              refine ⟨2974993616765105338214189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7933316311373614235237837 2974993616765105338214189)
              ·
                refine ⟨1115622606286914501830321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2974993616765105338214189 1115622606286914501830321)
                ·
                  refine ⟨836716954715185876372741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1115622606286914501830321 836716954715185876372741)
                  ·
                    refine ⟨156884429009097351819889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 836716954715185876372741 156884429009097351819889)
                    ·
                      rfl

theorem cell23_916594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_916594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916594 prefixEnd_916594 := by exact prefixLift 916594
  have htrace : WordTrace (prefixWord ++ tailWord_916594) baseStart_916594 baseEnd_916594 := by
    simpa [prefixWord, tailWord_916594, baseEnd_916594] using wordTrace_append hprefix tailTrace_916594
  have hstable : (prefixWord ++ tailWord_916594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916594).length < 2 ^ (prefixWord ++ tailWord_916594).sum := by decide
  have hdescent : baseEnd_916594 < baseStart_916594 := by decide
  rcases family_descends (prefixWord ++ tailWord_916594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916601 : List Nat := [1, 2, 1, 3, 5, 2, 1, 2, 1, 1, 4]
def baseStart_916601 : Nat := 118140960795 + 916601 * 2 ^ 59
def prefixEnd_916601 : Nat := 4983230072969 + 3 ^ 40 * 916601 * 2
def baseEnd_916601 : Nat := 470656881391873528072135

theorem tailTrace_916601 : CollatzResearch.WordTrace tailWord_916601 prefixEnd_916601 470656881391873528072135 := by
  unfold tailWord_916601
  simp only [CollatzResearch.WordTrace]
  refine ⟨33431184952318594832885657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22287456634879063221923771 33431184952318594832885657)
  ·
    refine ⟨25073388714238946124664243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33431184952318594832885657 25073388714238946124664243)
    ·
      refine ⟨37610083071358419186996365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25073388714238946124664243 37610083071358419186996365)
      ·
        refine ⟨14103781151759407195123637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37610083071358419186996365 14103781151759407195123637)
        ·
          refine ⟨1322229482977444424542841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14103781151759407195123637 1322229482977444424542841)
          ·
            refine ⟨991672112233083318407131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1322229482977444424542841 991672112233083318407131)
            ·
              refine ⟨1487508168349624977610697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 991672112233083318407131 1487508168349624977610697)
              ·
                refine ⟨1115631126262218733208023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1487508168349624977610697 1115631126262218733208023)
                ·
                  refine ⟨1673446689393328099812035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1115631126262218733208023 1673446689393328099812035)
                  ·
                    refine ⟨2510170034089992149718053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1673446689393328099812035 2510170034089992149718053)
                    ·
                      refine ⟨470656881391873528072135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2510170034089992149718053 470656881391873528072135)
                      ·
                        rfl

theorem cell23_916601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_916601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916601 prefixEnd_916601 := by exact prefixLift 916601
  have htrace : WordTrace (prefixWord ++ tailWord_916601) baseStart_916601 baseEnd_916601 := by
    simpa [prefixWord, tailWord_916601, baseEnd_916601] using wordTrace_append hprefix tailTrace_916601
  have hstable : (prefixWord ++ tailWord_916601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916601).length < 2 ^ (prefixWord ++ tailWord_916601).sum := by decide
  have hdescent : baseEnd_916601 < baseStart_916601 := by decide
  rcases family_descends (prefixWord ++ tailWord_916601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916617 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 3, 3, 3]
def baseStart_916617 : Nat := 118140960795 + 916617 * 2 ^ 59
def prefixEnd_916617 : Nat := 4983230072969 + 3 ^ 40 * 916617 * 2
def baseEnd_916617 : Nat := 470665097082345465472061

theorem tailTrace_916617 : CollatzResearch.WordTrace tailWord_916617 prefixEnd_916617 470665097082345465472061 := by
  unfold tailWord_916617
  simp only [CollatzResearch.WordTrace]
  refine ⟨33431768520260629565468105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22287845680173753043645403 33431768520260629565468105)
  ·
    refine ⟨25073826390195472174101079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33431768520260629565468105 25073826390195472174101079)
    ·
      refine ⟨37610739585293208261151619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25073826390195472174101079 37610739585293208261151619)
      ·
        refine ⟨56416109377939812391727429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37610739585293208261151619 56416109377939812391727429)
        ·
          refine ⟨10578020508363714823448893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56416109377939812391727429 10578020508363714823448893)
          ·
            refine ⟨3966757690636393058793335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10578020508363714823448893 3966757690636393058793335)
            ·
              refine ⟨5950136535954589588190003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3966757690636393058793335 5950136535954589588190003)
              ·
                refine ⟨8925204803931884382285005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5950136535954589588190003 8925204803931884382285005)
                ·
                  refine ⟨3346951801474456643356877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8925204803931884382285005 3346951801474456643356877)
                  ·
                    refine ⟨1255106925552921241258829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3346951801474456643356877 1255106925552921241258829)
                    ·
                      refine ⟨470665097082345465472061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1255106925552921241258829 470665097082345465472061)
                      ·
                        rfl

theorem cell23_916617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 3, 3].length) (baseStart_916617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916617 prefixEnd_916617 := by exact prefixLift 916617
  have htrace : WordTrace (prefixWord ++ tailWord_916617) baseStart_916617 baseEnd_916617 := by
    simpa [prefixWord, tailWord_916617, baseEnd_916617] using wordTrace_append hprefix tailTrace_916617
  have hstable : (prefixWord ++ tailWord_916617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916617).length < 2 ^ (prefixWord ++ tailWord_916617).sum := by decide
  have hdescent : baseEnd_916617 < baseStart_916617 := by decide
  rcases family_descends (prefixWord ++ tailWord_916617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916618 : List Nat := [3, 1, 2, 3, 1, 1, 2, 5, 1, 2, 2]
def baseStart_916618 : Nat := 118140960795 + 916618 * 2 ^ 59
def prefixEnd_916618 : Nat := 4983230072969 + 3 ^ 40 * 916618 * 2
def baseEnd_916618 : Nat := 470665610562999961559557

theorem tailTrace_916618 : CollatzResearch.WordTrace tailWord_916618 prefixEnd_916618 470665610562999961559557 := by
  unfold tailWord_916618
  simp only [CollatzResearch.WordTrace]
  refine ⟨8357951248314251684063627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22287869995504671157503005 8357951248314251684063627)
  ·
    refine ⟨12536926872471377526095441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8357951248314251684063627 12536926872471377526095441)
    ·
      refine ⟨9402695154353533144571581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12536926872471377526095441 9402695154353533144571581)
      ·
        refine ⟨3526010682882574929214343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9402695154353533144571581 3526010682882574929214343)
        ·
          refine ⟨5289016024323862393821515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3526010682882574929214343 5289016024323862393821515)
          ·
            refine ⟨7933524036485793590732273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5289016024323862393821515 7933524036485793590732273)
            ·
              refine ⟨5950143027364345193049205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7933524036485793590732273 5950143027364345193049205)
              ·
                refine ⟨557825908815407361848363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5950143027364345193049205 557825908815407361848363)
                ·
                  refine ⟨836738863223111042772545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 557825908815407361848363 836738863223111042772545)
                  ·
                    refine ⟨627554147417333282079409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 836738863223111042772545 627554147417333282079409)
                    ·
                      refine ⟨470665610562999961559557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 627554147417333282079409 470665610562999961559557)
                      ·
                        rfl

theorem cell23_916618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_916618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916618 prefixEnd_916618 := by exact prefixLift 916618
  have htrace : WordTrace (prefixWord ++ tailWord_916618) baseStart_916618 baseEnd_916618 := by
    simpa [prefixWord, tailWord_916618, baseEnd_916618] using wordTrace_append hprefix tailTrace_916618
  have hstable : (prefixWord ++ tailWord_916618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916618).length < 2 ^ (prefixWord ++ tailWord_916618).sum := by decide
  have hdescent : baseEnd_916618 < baseStart_916618 := by decide
  rcases family_descends (prefixWord ++ tailWord_916618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916620 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 4, 7]
def baseStart_916620 : Nat := 118140960795 + 916620 * 2 ^ 59
def prefixEnd_916620 : Nat := 4983230072969 + 3 ^ 40 * 916620 * 2
def baseEnd_916620 : Nat := 156888879174769651244849

theorem tailTrace_916620 : CollatzResearch.WordTrace tailWord_916620 prefixEnd_916620 156888879174769651244849 := by
  unfold tailWord_916620
  simp only [CollatzResearch.WordTrace]
  refine ⟨16715938969624880538913657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22287918626166507385218209 16715938969624880538913657)
  ·
    refine ⟨12536954227218660404185243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16715938969624880538913657 12536954227218660404185243)
    ·
      refine ⟨18805431340827990606277865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12536954227218660404185243 18805431340827990606277865)
      ·
        refine ⟨14104073505620992954708399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18805431340827990606277865 14104073505620992954708399)
        ·
          refine ⟨21156110258431489432062599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14104073505620992954708399 21156110258431489432062599)
          ·
            refine ⟨31734165387647234148093899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21156110258431489432062599 31734165387647234148093899)
            ·
              refine ⟨47601248081470851222140849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31734165387647234148093899 47601248081470851222140849)
              ·
                refine ⟨35700936061103138416605637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47601248081470851222140849 35700936061103138416605637)
                ·
                  refine ⟨6693925511456838453113557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35700936061103138416605637 6693925511456838453113557)
                  ·
                    refine ⟨156888879174769651244849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6693925511456838453113557 156888879174769651244849)
                    ·
                      rfl

theorem cell23_916620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 7].length) (baseStart_916620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916620 prefixEnd_916620 := by exact prefixLift 916620
  have htrace : WordTrace (prefixWord ++ tailWord_916620) baseStart_916620 baseEnd_916620 := by
    simpa [prefixWord, tailWord_916620, baseEnd_916620] using wordTrace_append hprefix tailTrace_916620
  have hstable : (prefixWord ++ tailWord_916620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916620).length < 2 ^ (prefixWord ++ tailWord_916620).sum := by decide
  have hdescent : baseEnd_916620 < baseStart_916620 := by decide
  rcases family_descends (prefixWord ++ tailWord_916620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916685 : List Nat := [1, 6, 2, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_916685 : Nat := 118140960795 + 916685 * 2 ^ 59
def prefixEnd_916685 : Nat := 4983230072969 + 3 ^ 40 * 916685 * 2
def baseEnd_916685 : Nat := 470700013766851199421749

theorem tailTrace_916685 : CollatzResearch.WordTrace tailWord_916685 prefixEnd_916685 470700013766851199421749 := by
  unfold tailWord_916685
  simp only [CollatzResearch.WordTrace]
  refine ⟨33434248684014277178943509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22289499122676184785962339 33434248684014277178943509)
  ·
    refine ⟨1567230407063169242762977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33434248684014277178943509 1567230407063169242762977)
    ·
      refine ⟨1175422805297376932072233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1567230407063169242762977 1175422805297376932072233)
      ·
        refine ⟨881567103973032699054175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1175422805297376932072233 881567103973032699054175)
        ·
          refine ⟨1322350655959549048581263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 881567103973032699054175 1322350655959549048581263)
          ·
            refine ⟨1983525983939323572871895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1322350655959549048581263 1983525983939323572871895)
            ·
              refine ⟨2975288975908985359307843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1983525983939323572871895 2975288975908985359307843)
              ·
                refine ⟨4462933463863478038961765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2975288975908985359307843 4462933463863478038961765)
                ·
                  refine ⟨836800024474402132305331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4462933463863478038961765 836800024474402132305331)
                  ·
                    refine ⟨1255200036711603198457997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 836800024474402132305331 1255200036711603198457997)
                    ·
                      refine ⟨470700013766851199421749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1255200036711603198457997 470700013766851199421749)
                      ·
                        rfl

theorem cell23_916685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_916685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916685 prefixEnd_916685 := by exact prefixLift 916685
  have htrace : WordTrace (prefixWord ++ tailWord_916685) baseStart_916685 baseEnd_916685 := by
    simpa [prefixWord, tailWord_916685, baseEnd_916685] using wordTrace_append hprefix tailTrace_916685
  have hstable : (prefixWord ++ tailWord_916685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916685).length < 2 ^ (prefixWord ++ tailWord_916685).sum := by decide
  have hdescent : baseEnd_916685 < baseStart_916685 := by decide
  rcases family_descends (prefixWord ++ tailWord_916685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916841 : List Nat := [1, 2, 1, 1, 1, 3, 2, 5, 2, 3, 2]
def baseStart_916841 : Nat := 118140960795 + 916841 * 2 ^ 59
def prefixEnd_916841 : Nat := 4983230072969 + 3 ^ 40 * 916841 * 2
def baseEnd_916841 : Nat := 470780116748952589071031

theorem tailTrace_916841 : CollatzResearch.WordTrace tailWord_916841 prefixEnd_916841 470780116748952589071031 := by
  unfold tailWord_916841
  simp only [CollatzResearch.WordTrace]
  refine ⟨33439938471449115821622377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22293292314299410547748251 33439938471449115821622377)
  ·
    refine ⟨25079953853586836866216783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33439938471449115821622377 25079953853586836866216783)
    ·
      refine ⟨37619930780380255299325175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25079953853586836866216783 37619930780380255299325175)
      ·
        refine ⟨56429896170570382948987763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37619930780380255299325175 56429896170570382948987763)
        ·
          refine ⟨84644844255855574423481645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56429896170570382948987763 84644844255855574423481645)
          ·
            refine ⟨31741816595945840408805617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84644844255855574423481645 31741816595945840408805617)
            ·
              refine ⟨23806362446959380306604213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31741816595945840408805617 23806362446959380306604213)
              ·
                refine ⟨2231846479402441903744145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23806362446959380306604213 2231846479402441903744145)
                ·
                  refine ⟨1673884859551831427808109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2231846479402441903744145 1673884859551831427808109)
                  ·
                    refine ⟨627706822331936785428041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1673884859551831427808109 627706822331936785428041)
                    ·
                      refine ⟨470780116748952589071031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 627706822331936785428041 470780116748952589071031)
                      ·
                        rfl

theorem cell23_916841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 3, 2].length) (baseStart_916841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916841 prefixEnd_916841 := by exact prefixLift 916841
  have htrace : WordTrace (prefixWord ++ tailWord_916841) baseStart_916841 baseEnd_916841 := by
    simpa [prefixWord, tailWord_916841, baseEnd_916841] using wordTrace_append hprefix tailTrace_916841
  have hstable : (prefixWord ++ tailWord_916841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916841).length < 2 ^ (prefixWord ++ tailWord_916841).sum := by decide
  have hdescent : baseEnd_916841 < baseStart_916841 := by decide
  rcases family_descends (prefixWord ++ tailWord_916841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916865 : List Nat := [1, 2, 4, 3, 2, 1, 2, 1, 3, 1, 3]
def baseStart_916865 : Nat := 118140960795 + 916865 * 2 ^ 59
def prefixEnd_916865 : Nat := 4983230072969 + 3 ^ 40 * 916865 * 2
def baseEnd_916865 : Nat := 470792440284660495170921

theorem tailTrace_916865 : CollatzResearch.WordTrace tailWord_916865 prefixEnd_916865 470792440284660495170921 := by
  unfold tailWord_916865
  simp only [CollatzResearch.WordTrace]
  refine ⟨33440813823362167920496049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22293875882241445280330699 33440813823362167920496049)
  ·
    refine ⟨25080610367521625940372037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33440813823362167920496049 25080610367521625940372037)
    ·
      refine ⟨4702614443910304863819757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25080610367521625940372037 4702614443910304863819757)
      ·
        refine ⟨1763480416466364323932409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4702614443910304863819757 1763480416466364323932409)
        ·
          refine ⟨1322610312349773242949307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1763480416466364323932409 1322610312349773242949307)
          ·
            refine ⟨1983915468524659864423961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1322610312349773242949307 1983915468524659864423961)
            ·
              refine ⟨1487936601393494898317971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1983915468524659864423961 1487936601393494898317971)
              ·
                refine ⟨2231904902090242347476957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1487936601393494898317971 2231904902090242347476957)
                ·
                  refine ⟨836964338283840880303859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2231904902090242347476957 836964338283840880303859)
                  ·
                    refine ⟨1255446507425761320455789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 836964338283840880303859 1255446507425761320455789)
                    ·
                      refine ⟨470792440284660495170921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1255446507425761320455789 470792440284660495170921)
                      ·
                        rfl

theorem cell23_916865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_916865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916865 prefixEnd_916865 := by exact prefixLift 916865
  have htrace : WordTrace (prefixWord ++ tailWord_916865) baseStart_916865 baseEnd_916865 := by
    simpa [prefixWord, tailWord_916865, baseEnd_916865] using wordTrace_append hprefix tailTrace_916865
  have hstable : (prefixWord ++ tailWord_916865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916865).length < 2 ^ (prefixWord ++ tailWord_916865).sum := by decide
  have hdescent : baseEnd_916865 < baseStart_916865 := by decide
  rcases family_descends (prefixWord ++ tailWord_916865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916932 : List Nat := [2, 3, 3, 2, 1, 3, 2, 1, 2, 4]
def baseStart_916932 : Nat := 118140960795 + 916932 * 2 ^ 59
def prefixEnd_916932 : Nat := 4983230072969 + 3 ^ 40 * 916932 * 2
def baseEnd_916932 : Nat := 156942281162837244344371

theorem tailTrace_916932 : CollatzResearch.WordTrace tailWord_916932 prefixEnd_916932 156942281162837244344371 := by
  unfold tailWord_916932
  simp only [CollatzResearch.WordTrace]
  refine ⟨16721628757059719181592525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22295505009412958908790033 16721628757059719181592525)
  ·
    refine ⟨6270610783897394693097197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16721628757059719181592525 6270610783897394693097197)
    ·
      refine ⟨2351479043961523009911449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6270610783897394693097197 2351479043961523009911449)
      ·
        refine ⟨1763609282971142257433587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2351479043961523009911449 1763609282971142257433587)
        ·
          refine ⟨2645413924456713386150381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1763609282971142257433587 2645413924456713386150381)
          ·
            refine ⟨992030221671267519806393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2645413924456713386150381 992030221671267519806393)
            ·
              refine ⟨744022666253450639854795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 992030221671267519806393 744022666253450639854795)
              ·
                refine ⟨1116033999380175959782193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 744022666253450639854795 1116033999380175959782193)
                ·
                  refine ⟨837025499535131969836645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1116033999380175959782193 837025499535131969836645)
                  ·
                    refine ⟨156942281162837244344371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 837025499535131969836645 156942281162837244344371)
                    ·
                      rfl

theorem cell23_916932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_916932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916932 prefixEnd_916932 := by exact prefixLift 916932
  have htrace : WordTrace (prefixWord ++ tailWord_916932) baseStart_916932 baseEnd_916932 := by
    simpa [prefixWord, tailWord_916932, baseEnd_916932] using wordTrace_append hprefix tailTrace_916932
  have hstable : (prefixWord ++ tailWord_916932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916932).length < 2 ^ (prefixWord ++ tailWord_916932).sum := by decide
  have hdescent : baseEnd_916932 < baseStart_916932 := by decide
  rcases family_descends (prefixWord ++ tailWord_916932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916944 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 4]
def baseStart_916944 : Nat := 118140960795 + 916944 * 2 ^ 59
def prefixEnd_916944 : Nat := 4983230072969 + 3 ^ 40 * 916944 * 2
def baseEnd_916944 : Nat := 470833005256365686083057

theorem tailTrace_916944 : CollatzResearch.WordTrace tailWord_916944 prefixEnd_916944 470833005256365686083057 := by
  unfold tailWord_916944
  simp only [CollatzResearch.WordTrace]
  refine ⟨16721847595037982206310943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22295796793383976275081257 16721847595037982206310943)
  ·
    refine ⟨25082771392556973309466415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16721847595037982206310943 25082771392556973309466415)
    ·
      refine ⟨37624157088835459964199623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25082771392556973309466415 37624157088835459964199623)
      ·
        refine ⟨56436235633253189946299435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37624157088835459964199623 56436235633253189946299435)
        ·
          refine ⟨84654353449879784919449153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56436235633253189946299435 84654353449879784919449153)
          ·
            refine ⟨63490765087409838689586865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84654353449879784919449153 63490765087409838689586865)
            ·
              refine ⟨47618073815557379017190149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63490765087409838689586865 47618073815557379017190149)
              ·
                refine ⟨8928388840417008565723153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47618073815557379017190149 8928388840417008565723153)
                ·
                  refine ⟨6696291630312756424292365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8928388840417008565723153 6696291630312756424292365)
                  ·
                    refine ⟨2511109361367283659109637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6696291630312756424292365 2511109361367283659109637)
                    ·
                      refine ⟨470833005256365686083057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2511109361367283659109637 470833005256365686083057)
                      ·
                        rfl

theorem cell23_916944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 4].length) (baseStart_916944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916944 prefixEnd_916944 := by exact prefixLift 916944
  have htrace : WordTrace (prefixWord ++ tailWord_916944) baseStart_916944 baseEnd_916944 := by
    simpa [prefixWord, tailWord_916944, baseEnd_916944] using wordTrace_append hprefix tailTrace_916944
  have hstable : (prefixWord ++ tailWord_916944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916944).length < 2 ^ (prefixWord ++ tailWord_916944).sum := by decide
  have hdescent : baseEnd_916944 < baseStart_916944 := by decide
  rcases family_descends (prefixWord ++ tailWord_916944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916973 : List Nat := [1, 5, 1, 3, 3, 1, 2, 2, 1, 2, 2]
def baseStart_916973 : Nat := 118140960795 + 916973 * 2 ^ 59
def prefixEnd_916973 : Nat := 4983230072969 + 3 ^ 40 * 916973 * 2
def baseEnd_916973 : Nat := 470847896195346072620425

theorem tailTrace_916973 : CollatzResearch.WordTrace tailWord_916973 prefixEnd_916973 470847896195346072620425 := by
  unfold tailWord_916973
  simp only [CollatzResearch.WordTrace]
  refine ⟨33444752906970902365427573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22296501937980601576951715 33444752906970902365427573)
  ·
    refine ⟨3135445585028522096758835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33444752906970902365427573 3135445585028522096758835)
    ·
      refine ⟨4703168377542783145138253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3135445585028522096758835 4703168377542783145138253)
      ·
        refine ⟨1763688141578543679426845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4703168377542783145138253 1763688141578543679426845)
        ·
          refine ⟨661383053091953879785067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1763688141578543679426845 661383053091953879785067)
          ·
            refine ⟨992074579637930819677601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 661383053091953879785067 992074579637930819677601)
            ·
              refine ⟨744055934728448114758201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 992074579637930819677601 744055934728448114758201)
              ·
                refine ⟨558041951046336086068651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 744055934728448114758201 558041951046336086068651)
                ·
                  refine ⟨837062926569504129102977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 558041951046336086068651 837062926569504129102977)
                  ·
                    refine ⟨627797194927128096827233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 837062926569504129102977 627797194927128096827233)
                    ·
                      refine ⟨470847896195346072620425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 627797194927128096827233 470847896195346072620425)
                      ·
                        rfl

theorem cell23_916973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_916973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_916973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_916973 prefixEnd_916973 := by exact prefixLift 916973
  have htrace : WordTrace (prefixWord ++ tailWord_916973) baseStart_916973 baseEnd_916973 := by
    simpa [prefixWord, tailWord_916973, baseEnd_916973] using wordTrace_append hprefix tailTrace_916973
  have hstable : (prefixWord ++ tailWord_916973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916973).length < 2 ^ (prefixWord ++ tailWord_916973).sum := by decide
  have hdescent : baseEnd_916973 < baseStart_916973 := by decide
  rcases family_descends (prefixWord ++ tailWord_916973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917046 : List Nat := [5, 1, 2, 1, 3, 1, 3, 1, 2, 2, 2]
def baseStart_917046 : Nat := 118140960795 + 917046 * 2 ^ 59
def prefixEnd_917046 : Nat := 4983230072969 + 3 ^ 40 * 917046 * 2
def baseEnd_917046 : Nat := 470885380283124287007589

theorem tailTrace_917046 : CollatzResearch.WordTrace tailWord_917046 prefixEnd_917046 470885380283124287007589 := by
  unfold tailWord_917046
  simp only [CollatzResearch.WordTrace]
  refine ⟨2090463464731652239552187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22298276957137623888556661 2090463464731652239552187)
  ·
    refine ⟨3135695197097478359328281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2090463464731652239552187 3135695197097478359328281)
    ·
      refine ⟨2351771397823108769496211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3135695197097478359328281 2351771397823108769496211)
      ·
        refine ⟨3527657096734663154244317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2351771397823108769496211 3527657096734663154244317)
        ·
          refine ⟨1322871411275498682841619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3527657096734663154244317 1322871411275498682841619)
          ·
            refine ⟨1984307116913248024262429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1322871411275498682841619 1984307116913248024262429)
            ·
              refine ⟨744115168842468009098411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1984307116913248024262429 744115168842468009098411)
              ·
                refine ⟨1116172753263702013647617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 744115168842468009098411 1116172753263702013647617)
                ·
                  refine ⟨837129564947776510235713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1116172753263702013647617 837129564947776510235713)
                  ·
                    refine ⟨627847173710832382676785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 837129564947776510235713 627847173710832382676785)
                    ·
                      refine ⟨470885380283124287007589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 627847173710832382676785 470885380283124287007589)
                      ·
                        rfl

theorem cell23_917046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_917046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917046 prefixEnd_917046 := by exact prefixLift 917046
  have htrace : WordTrace (prefixWord ++ tailWord_917046) baseStart_917046 baseEnd_917046 := by
    simpa [prefixWord, tailWord_917046, baseEnd_917046] using wordTrace_append hprefix tailTrace_917046
  have hstable : (prefixWord ++ tailWord_917046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917046).length < 2 ^ (prefixWord ++ tailWord_917046).sum := by decide
  have hdescent : baseEnd_917046 < baseStart_917046 := by decide
  rcases family_descends (prefixWord ++ tailWord_917046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917069 : List Nat := [1, 6, 1, 1, 4, 1, 1, 3, 5]
def baseStart_917069 : Nat := 118140960795 + 917069 * 2 ^ 59
def prefixEnd_917069 : Nat := 4983230072969 + 3 ^ 40 * 917069 * 2
def baseEnd_917069 : Nat := 52321910037575299668887

theorem tailTrace_917069 : CollatzResearch.WordTrace tailWord_917069 prefixEnd_917069 52321910037575299668887 := by
  unfold tailWord_917069
  simp only [CollatzResearch.WordTrace]
  refine ⟨33448254314623110760922261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22298836209748740507281507 33448254314623110760922261)
  ·
    refine ⟨1567886920997958316918231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33448254314623110760922261 1567886920997958316918231)
    ·
      refine ⟨2351830381496937475377347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1567886920997958316918231 2351830381496937475377347)
      ·
        refine ⟨3527745572245406213066021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2351830381496937475377347 3527745572245406213066021)
        ·
          refine ⟨661452294796013664949879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3527745572245406213066021 661452294796013664949879)
          ·
            refine ⟨992178442194020497424819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 661452294796013664949879 992178442194020497424819)
            ·
              refine ⟨1488267663291030746137229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 992178442194020497424819 1488267663291030746137229)
              ·
                refine ⟨558100373734136529801461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1488267663291030746137229 558100373734136529801461)
                ·
                  refine ⟨52321910037575299668887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 558100373734136529801461 52321910037575299668887)
                  ·
                    rfl

theorem cell23_917069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_917069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917069 prefixEnd_917069 := by exact prefixLift 917069
  have htrace : WordTrace (prefixWord ++ tailWord_917069) baseStart_917069 baseEnd_917069 := by
    simpa [prefixWord, tailWord_917069, baseEnd_917069] using wordTrace_append hprefix tailTrace_917069
  have hstable : (prefixWord ++ tailWord_917069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917069).length < 2 ^ (prefixWord ++ tailWord_917069).sum := by decide
  have hdescent : baseEnd_917069 < baseStart_917069 := by decide
  rcases family_descends (prefixWord ++ tailWord_917069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917091 : List Nat := [1, 1, 1, 5, 1, 3, 2, 1, 8]
def baseStart_917091 : Nat := 118140960795 + 917091 * 2 ^ 59
def prefixEnd_917091 : Nat := 4983230072969 + 3 ^ 40 * 917091 * 2
def baseEnd_917091 : Nat := 52323165212508512327209

theorem tailTrace_917091 : CollatzResearch.WordTrace tailWord_917091 prefixEnd_917091 52323165212508512327209 := by
  unfold tailWord_917091
  simp only [CollatzResearch.WordTrace]
  refine ⟨33449056720543408518223127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22299371147028939012148751 33449056720543408518223127)
  ·
    refine ⟨50173585080815112777334691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33449056720543408518223127 50173585080815112777334691)
    ·
      refine ⟨75260377621222669166002037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50173585080815112777334691 75260377621222669166002037)
      ·
        refine ⟨7055660401989625234312691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75260377621222669166002037 7055660401989625234312691)
        ·
          refine ⟨10583490602984437851469037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7055660401989625234312691 10583490602984437851469037)
          ·
            refine ⟨3968808976119164194300889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10583490602984437851469037 3968808976119164194300889)
            ·
              refine ⟨2976606732089373145725667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3968808976119164194300889 2976606732089373145725667)
              ·
                refine ⟨4464910098134059718588501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2976606732089373145725667 4464910098134059718588501)
                ·
                  refine ⟨52323165212508512327209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4464910098134059718588501 52323165212508512327209)
                  ·
                    rfl

theorem cell23_917091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 8].length) (baseStart_917091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917091 prefixEnd_917091 := by exact prefixLift 917091
  have htrace : WordTrace (prefixWord ++ tailWord_917091) baseStart_917091 baseEnd_917091 := by
    simpa [prefixWord, tailWord_917091, baseEnd_917091] using wordTrace_append hprefix tailTrace_917091
  have hstable : (prefixWord ++ tailWord_917091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917091).length < 2 ^ (prefixWord ++ tailWord_917091).sum := by decide
  have hdescent : baseEnd_917091 < baseStart_917091 := by decide
  rcases family_descends (prefixWord ++ tailWord_917091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917095 : List Nat := [1, 1, 5, 1, 1, 1, 2, 6, 1, 4]
def baseStart_917095 : Nat := 118140960795 + 917095 * 2 ^ 59
def prefixEnd_917095 : Nat := 4983230072969 + 3 ^ 40 * 917095 * 2
def baseEnd_917095 : Nat := 156970180278398198431621

theorem tailTrace_917095 : CollatzResearch.WordTrace tailWord_917095 prefixEnd_917095 156970180278398198431621 := by
  unfold tailWord_917095
  simp only [CollatzResearch.WordTrace]
  refine ⟨33449202612528917201368739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22299468408352611467579159 33449202612528917201368739)
  ·
    refine ⟨50173803918793375802053109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33449202612528917201368739 50173803918793375802053109)
    ·
      refine ⟨4703794117386878981442479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50173803918793375802053109 4703794117386878981442479)
      ·
        refine ⟨7055691176080318472163719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4703794117386878981442479 7055691176080318472163719)
        ·
          refine ⟨10583536764120477708245579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7055691176080318472163719 10583536764120477708245579)
          ·
            refine ⟨15875305146180716562368369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10583536764120477708245579 15875305146180716562368369)
            ·
              refine ⟨11906478859635537421776277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15875305146180716562368369 11906478859635537421776277)
              ·
                refine ⟨558116196545415816645763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11906478859635537421776277 558116196545415816645763)
                ·
                  refine ⟨837174294818123724968645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 558116196545415816645763 837174294818123724968645)
                  ·
                    refine ⟨156970180278398198431621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 837174294818123724968645 156970180278398198431621)
                    ·
                      rfl

theorem cell23_917095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_917095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917095 prefixEnd_917095 := by exact prefixLift 917095
  have htrace : WordTrace (prefixWord ++ tailWord_917095) baseStart_917095 baseEnd_917095 := by
    simpa [prefixWord, tailWord_917095, baseEnd_917095] using wordTrace_append hprefix tailTrace_917095
  have hstable : (prefixWord ++ tailWord_917095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917095).length < 2 ^ (prefixWord ++ tailWord_917095).sum := by decide
  have hdescent : baseEnd_917095 < baseStart_917095 := by decide
  rcases family_descends (prefixWord ++ tailWord_917095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917202 : List Nat := [3, 2, 2, 2, 2, 1, 3, 2, 2, 4]
def baseStart_917202 : Nat := 118140960795 + 917202 * 2 ^ 59
def prefixEnd_917202 : Nat := 4983230072969 + 3 ^ 40 * 917202 * 2
def baseEnd_917202 : Nat := 156988494421741892218957

theorem tailTrace_917202 : CollatzResearch.WordTrace tailWord_917202 prefixEnd_917202 156988494421741892218957 := by
  unfold tailWord_917202
  simp only [CollatzResearch.WordTrace]
  refine ⟨8363276305785318618878465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22302070148760849650342573 8363276305785318618878465)
  ·
    refine ⟨6272457229338988964158849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8363276305785318618878465 6272457229338988964158849)
    ·
      refine ⟨4704342922004241723119137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6272457229338988964158849 4704342922004241723119137)
      ·
        refine ⟨3528257191503181292339353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4704342922004241723119137 3528257191503181292339353)
        ·
          refine ⟨2646192893627385969254515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3528257191503181292339353 2646192893627385969254515)
          ·
            refine ⟨3969289340441078953881773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2646192893627385969254515 3969289340441078953881773)
            ·
              refine ⟨1488483502665404607705665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3969289340441078953881773 1488483502665404607705665)
              ·
                refine ⟨1116362626999053455779249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1488483502665404607705665 1116362626999053455779249)
                ·
                  refine ⟨837271970249290091834437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1116362626999053455779249 837271970249290091834437)
                  ·
                    refine ⟨156988494421741892218957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 837271970249290091834437 156988494421741892218957)
                    ·
                      rfl

theorem cell23_917202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_917202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917202 prefixEnd_917202 := by exact prefixLift 917202
  have htrace : WordTrace (prefixWord ++ tailWord_917202) baseStart_917202 baseEnd_917202 := by
    simpa [prefixWord, tailWord_917202, baseEnd_917202] using wordTrace_append hprefix tailTrace_917202
  have hstable : (prefixWord ++ tailWord_917202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917202).length < 2 ^ (prefixWord ++ tailWord_917202).sum := by decide
  have hdescent : baseEnd_917202 < baseStart_917202 := by decide
  rcases family_descends (prefixWord ++ tailWord_917202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917209 : List Nat := [1, 2, 1, 2, 3, 3, 2, 4, 1, 2, 2]
def baseStart_917209 : Nat := 118140960795 + 917209 * 2 ^ 59
def prefixEnd_917209 : Nat := 4983230072969 + 3 ^ 40 * 917209 * 2
def baseEnd_917209 : Nat := 470969077629807149269339

theorem tailTrace_917209 : CollatzResearch.WordTrace tailWord_917209 prefixEnd_917209 470969077629807149269339 := by
  unfold tailWord_917209
  simp only [CollatzResearch.WordTrace]
  refine ⟨33453360534115914671018681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22302240356077276447345787 33453360534115914671018681)
  ·
    refine ⟨25090020400586936003264011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33453360534115914671018681 25090020400586936003264011)
    ·
      refine ⟨37635030600880404004896017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25090020400586936003264011 37635030600880404004896017)
      ·
        refine ⟨28226272950660303003672013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37635030600880404004896017 28226272950660303003672013)
        ·
          refine ⟨10584852356497613626377005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28226272950660303003672013 10584852356497613626377005)
          ·
            refine ⟨3969319633686605109891377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10584852356497613626377005 3969319633686605109891377)
            ·
              refine ⟨2976989725264953832418533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3969319633686605109891377 2976989725264953832418533)
              ·
                refine ⟨558185573487178843578475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2976989725264953832418533 558185573487178843578475)
                ·
                  refine ⟨837278360230768265367713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 558185573487178843578475 837278360230768265367713)
                  ·
                    refine ⟨627958770173076199025785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 837278360230768265367713 627958770173076199025785)
                    ·
                      refine ⟨470969077629807149269339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 627958770173076199025785 470969077629807149269339)
                      ·
                        rfl

theorem cell23_917209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 4, 1, 2, 2].length) (baseStart_917209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917209 prefixEnd_917209 := by exact prefixLift 917209
  have htrace : WordTrace (prefixWord ++ tailWord_917209) baseStart_917209 baseEnd_917209 := by
    simpa [prefixWord, tailWord_917209, baseEnd_917209] using wordTrace_append hprefix tailTrace_917209
  have hstable : (prefixWord ++ tailWord_917209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917209).length < 2 ^ (prefixWord ++ tailWord_917209).sum := by decide
  have hdescent : baseEnd_917209 < baseStart_917209 := by decide
  rcases family_descends (prefixWord ++ tailWord_917209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917212 : List Nat := [2, 2, 5, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_917212 : Nat := 118140960795 + 917212 * 2 ^ 59
def prefixEnd_917212 : Nat := 4983230072969 + 3 ^ 40 * 917212 * 2
def baseEnd_917212 : Nat := 470970618071770637531825

theorem tailTrace_917212 : CollatzResearch.WordTrace tailWord_917212 prefixEnd_917212 470970618071770637531825 := by
  unfold tailWord_917212
  simp only [CollatzResearch.WordTrace]
  refine ⟨16726734976552523091688945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22302313302070030788918593 16726734976552523091688945)
  ·
    refine ⟨12545051232414392318766709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16726734976552523091688945 12545051232414392318766709)
    ·
      refine ⟨1176098553038849279884379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12545051232414392318766709 1176098553038849279884379)
      ·
        refine ⟨1764147829558273919826569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1176098553038849279884379 1764147829558273919826569)
        ·
          refine ⟨1323110872168705439869927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1764147829558273919826569 1323110872168705439869927)
          ·
            refine ⟨1984666308253058159804891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1323110872168705439869927 1984666308253058159804891)
            ·
              refine ⟨2976999462379587239707337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1984666308253058159804891 2976999462379587239707337)
              ·
                refine ⟨2232749596784690429780503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2976999462379587239707337 2232749596784690429780503)
                ·
                  refine ⟨3349124395177035644670755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2232749596784690429780503 3349124395177035644670755)
                  ·
                    refine ⟨5023686592765553467006133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3349124395177035644670755 5023686592765553467006133)
                    ·
                      refine ⟨470970618071770637531825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5023686592765553467006133 470970618071770637531825)
                      ·
                        rfl

theorem cell23_917212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_917212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917212 prefixEnd_917212 := by exact prefixLift 917212
  have htrace : WordTrace (prefixWord ++ tailWord_917212) baseStart_917212 baseEnd_917212 := by
    simpa [prefixWord, tailWord_917212, baseEnd_917212] using wordTrace_append hprefix tailTrace_917212
  have hstable : (prefixWord ++ tailWord_917212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917212).length < 2 ^ (prefixWord ++ tailWord_917212).sum := by decide
  have hdescent : baseEnd_917212 < baseStart_917212 := by decide
  rcases family_descends (prefixWord ++ tailWord_917212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917219 : List Nat := [1, 1, 1, 7, 2, 1, 3, 1, 2, 4]
def baseStart_917219 : Nat := 118140960795 + 917219 * 2 ^ 59
def prefixEnd_917219 : Nat := 4983230072969 + 3 ^ 40 * 917219 * 2
def baseEnd_917219 : Nat := 156991404145450703381431

theorem tailTrace_917219 : CollatzResearch.WordTrace tailWord_917219 prefixEnd_917219 156991404145450703381431 := by
  unfold tailWord_917219
  simp only [CollatzResearch.WordTrace]
  refine ⟨33453725264079686378882711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22302483509386457585921807 33453725264079686378882711)
  ·
    refine ⟨50180587896119529568324067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33453725264079686378882711 50180587896119529568324067)
    ·
      refine ⟨75270881844179294352486101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50180587896119529568324067 75270881844179294352486101)
      ·
        refine ⟨1764161293222952211386393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 75270881844179294352486101 1764161293222952211386393)
        ·
          refine ⟨1323120969917214158539795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1764161293222952211386393 1323120969917214158539795)
          ·
            refine ⟨1984681454875821237809693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1323120969917214158539795 1984681454875821237809693)
            ·
              refine ⟨744255545578432964178635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1984681454875821237809693 744255545578432964178635)
              ·
                refine ⟨1116383318367649446267953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 744255545578432964178635 1116383318367649446267953)
                ·
                  refine ⟨837287488775737084700965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1116383318367649446267953 837287488775737084700965)
                  ·
                    refine ⟨156991404145450703381431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 837287488775737084700965 156991404145450703381431)
                    ·
                      rfl

theorem cell23_917219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 2, 4].length) (baseStart_917219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917219 prefixEnd_917219 := by exact prefixLift 917219
  have htrace : WordTrace (prefixWord ++ tailWord_917219) baseStart_917219 baseEnd_917219 := by
    simpa [prefixWord, tailWord_917219, baseEnd_917219] using wordTrace_append hprefix tailTrace_917219
  have hstable : (prefixWord ++ tailWord_917219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917219).length < 2 ^ (prefixWord ++ tailWord_917219).sum := by decide
  have hdescent : baseEnd_917219 < baseStart_917219 := by decide
  rcases family_descends (prefixWord ++ tailWord_917219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917235 : List Nat := [1, 1, 1, 2, 2, 3, 2, 3, 3, 3, 2]
def baseStart_917235 : Nat := 118140960795 + 917235 * 2 ^ 59
def prefixEnd_917235 : Nat := 4983230072969 + 3 ^ 40 * 917235 * 2
def baseEnd_917235 : Nat := 470982428126824047544219

theorem tailTrace_917235 : CollatzResearch.WordTrace tailWord_917235 prefixEnd_917235 470982428126824047544219 := by
  unfold tailWord_917235
  simp only [CollatzResearch.WordTrace]
  refine ⟨33454308832021721111465159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22302872554681147407643439 33454308832021721111465159)
  ·
    refine ⟨50181463248032581667197739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33454308832021721111465159 50181463248032581667197739)
    ·
      refine ⟨75272194872048872500796609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50181463248032581667197739 75272194872048872500796609)
      ·
        refine ⟨56454146154036654375597457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75272194872048872500796609 56454146154036654375597457)
        ·
          refine ⟨42340609615527490781698093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56454146154036654375597457 42340609615527490781698093)
          ·
            refine ⟨15877728605822809043136785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42340609615527490781698093 15877728605822809043136785)
            ·
              refine ⟨11908296454367106782352589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15877728605822809043136785 11908296454367106782352589)
              ·
                refine ⟨4465611170387665043382221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11908296454367106782352589 4465611170387665043382221)
                ·
                  refine ⟨1674604188895374391268333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4465611170387665043382221 1674604188895374391268333)
                  ·
                    refine ⟨627976570835765396725625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1674604188895374391268333 627976570835765396725625)
                    ·
                      refine ⟨470982428126824047544219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 627976570835765396725625 470982428126824047544219)
                      ·
                        rfl

theorem cell23_917235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 3, 2].length) (baseStart_917235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917235 prefixEnd_917235 := by exact prefixLift 917235
  have htrace : WordTrace (prefixWord ++ tailWord_917235) baseStart_917235 baseEnd_917235 := by
    simpa [prefixWord, tailWord_917235, baseEnd_917235] using wordTrace_append hprefix tailTrace_917235
  have hstable : (prefixWord ++ tailWord_917235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917235).length < 2 ^ (prefixWord ++ tailWord_917235).sum := by decide
  have hdescent : baseEnd_917235 < baseStart_917235 := by decide
  rcases family_descends (prefixWord ++ tailWord_917235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917254 : List Nat := [6, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3]
def baseStart_917254 : Nat := 118140960795 + 917254 * 2 ^ 59
def prefixEnd_917254 : Nat := 4983230072969 + 3 ^ 40 * 917254 * 2
def baseEnd_917254 : Nat := 470992184259259473206633

theorem tailTrace_917254 : CollatzResearch.WordTrace tailWord_917254 prefixEnd_917254 470992184259259473206633 := by
  unfold tailWord_917254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1045468806842277729887713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22303334545968591570937877 1045468806842277729887713)
  ·
    refine ⟨784101605131708297415785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1045468806842277729887713 784101605131708297415785)
    ·
      refine ⟨588076203848781223061839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 784101605131708297415785 588076203848781223061839)
      ·
        refine ⟨882114305773171834592759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588076203848781223061839 882114305773171834592759)
        ·
          refine ⟨1323171458659757751889139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 882114305773171834592759 1323171458659757751889139)
          ·
            refine ⟨1984757187989636627833709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1323171458659757751889139 1984757187989636627833709)
            ·
              refine ⟨744283945496113735437641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1984757187989636627833709 744283945496113735437641)
              ·
                refine ⟨558212959122085301578231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 744283945496113735437641 558212959122085301578231)
                ·
                  refine ⟨837319438683127952367347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 558212959122085301578231 837319438683127952367347)
                  ·
                    refine ⟨1255979158024691928551021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 837319438683127952367347 1255979158024691928551021)
                    ·
                      refine ⟨470992184259259473206633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1255979158024691928551021 470992184259259473206633)
                      ·
                        rfl

theorem cell23_917254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_917254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917254 prefixEnd_917254 := by exact prefixLift 917254
  have htrace : WordTrace (prefixWord ++ tailWord_917254) baseStart_917254 baseEnd_917254 := by
    simpa [prefixWord, tailWord_917254, baseEnd_917254] using wordTrace_append hprefix tailTrace_917254
  have hstable : (prefixWord ++ tailWord_917254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917254).length < 2 ^ (prefixWord ++ tailWord_917254).sum := by decide
  have hdescent : baseEnd_917254 < baseStart_917254 := by decide
  rcases family_descends (prefixWord ++ tailWord_917254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917282 : List Nat := [3, 3, 1, 1, 2, 1, 2, 3, 1, 4, 2]
def baseStart_917282 : Nat := 118140960795 + 917282 * 2 ^ 59
def prefixEnd_917282 : Nat := 4983230072969 + 3 ^ 40 * 917282 * 2
def baseEnd_917282 : Nat := 471006561717585363656503

theorem tailTrace_917282 : CollatzResearch.WordTrace tailWord_917282 prefixEnd_917282 471006561717585363656503 := by
  unfold tailWord_917282
  simp only [CollatzResearch.WordTrace]
  refine ⟨8364005765712862034606525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22304015375234298758950733 8364005765712862034606525)
  ·
    refine ⟨3136502162142323262977447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8364005765712862034606525 3136502162142323262977447)
    ·
      refine ⟨4704753243213484894466171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3136502162142323262977447 4704753243213484894466171)
      ·
        refine ⟨7057129864820227341699257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4704753243213484894466171 7057129864820227341699257)
        ·
          refine ⟨5292847398615170506274443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7057129864820227341699257 5292847398615170506274443)
          ·
            refine ⟨7939271097922755759411665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5292847398615170506274443 7939271097922755759411665)
            ·
              refine ⟨5954453323442066819558749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7939271097922755759411665 5954453323442066819558749)
              ·
                refine ⟨2232919996290775057334531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5954453323442066819558749 2232919996290775057334531)
                ·
                  refine ⟨3349379994436162586001797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2232919996290775057334531 3349379994436162586001797)
                  ·
                    refine ⟨628008748956780484875337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3349379994436162586001797 628008748956780484875337)
                    ·
                      refine ⟨471006561717585363656503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 628008748956780484875337 471006561717585363656503)
                      ·
                        rfl

theorem cell23_917282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_917282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917282 prefixEnd_917282 := by exact prefixLift 917282
  have htrace : WordTrace (prefixWord ++ tailWord_917282) baseStart_917282 baseEnd_917282 := by
    simpa [prefixWord, tailWord_917282, baseEnd_917282] using wordTrace_append hprefix tailTrace_917282
  have hstable : (prefixWord ++ tailWord_917282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917282).length < 2 ^ (prefixWord ++ tailWord_917282).sum := by decide
  have hdescent : baseEnd_917282 < baseStart_917282 := by decide
  rcases family_descends (prefixWord ++ tailWord_917282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917302 : List Nat := [5, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_917302 : Nat := 118140960795 + 917302 * 2 ^ 59
def prefixEnd_917302 : Nat := 4983230072969 + 3 ^ 40 * 917302 * 2
def baseEnd_917302 : Nat := 471016831330675285406411

theorem tailTrace_917302 : CollatzResearch.WordTrace tailWord_917302 prefixEnd_917302 471016831330675285406411 := by
  unfold tailWord_917302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2091047032673686972134635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22304501681852661036102773 2091047032673686972134635)
  ·
    refine ⟨3136570549010530458201953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2091047032673686972134635 3136570549010530458201953)
    ·
      refine ⟨2352427911757897843651465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3136570549010530458201953 2352427911757897843651465)
      ·
        refine ⟨1764320933818423382738599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2352427911757897843651465 1764320933818423382738599)
        ·
          refine ⟨2646481400727635074107899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1764320933818423382738599 2646481400727635074107899)
          ·
            refine ⟨3969722101091452611161849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2646481400727635074107899 3969722101091452611161849)
            ·
              refine ⟨2977291575818589458371387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3969722101091452611161849 2977291575818589458371387)
              ·
                refine ⟨4465937363727884187557081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2977291575818589458371387 4465937363727884187557081)
                ·
                  refine ⟨3349453022795913140667811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4465937363727884187557081 3349453022795913140667811)
                  ·
                    refine ⟨5024179534193869711001717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3349453022795913140667811 5024179534193869711001717)
                    ·
                      refine ⟨471016831330675285406411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5024179534193869711001717 471016831330675285406411)
                      ·
                        rfl

theorem cell23_917302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_917302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917302 prefixEnd_917302 := by exact prefixLift 917302
  have htrace : WordTrace (prefixWord ++ tailWord_917302) baseStart_917302 baseEnd_917302 := by
    simpa [prefixWord, tailWord_917302, baseEnd_917302] using wordTrace_append hprefix tailTrace_917302
  have hstable : (prefixWord ++ tailWord_917302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917302).length < 2 ^ (prefixWord ++ tailWord_917302).sum := by decide
  have hdescent : baseEnd_917302 < baseStart_917302 := by decide
  rcases family_descends (prefixWord ++ tailWord_917302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917332 : List Nat := [2, 4, 1, 1, 3, 2, 1, 1, 2, 3, 3]
def baseStart_917332 : Nat := 118140960795 + 917332 * 2 ^ 59
def prefixEnd_917332 : Nat := 4983230072969 + 3 ^ 40 * 917332 * 2
def baseEnd_917332 : Nat := 471032235750310168031273

theorem tailTrace_917332 : CollatzResearch.WordTrace tailWord_917332 prefixEnd_917332 471032235750310168031273 := by
  unfold tailWord_917332
  simp only [CollatzResearch.WordTrace]
  refine ⟨16728923356335153338873125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22305231141780204451830833 16728923356335153338873125)
  ·
    refine ⟨3136673129312841251038711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16728923356335153338873125 3136673129312841251038711)
    ·
      refine ⟨4705009693969261876558067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3136673129312841251038711 4705009693969261876558067)
      ·
        refine ⟨7057514540953892814837101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4705009693969261876558067 7057514540953892814837101)
        ·
          refine ⟨2646567952857709805563913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7057514540953892814837101 2646567952857709805563913)
          ·
            refine ⟨1984925964643282354172935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2646567952857709805563913 1984925964643282354172935)
            ·
              refine ⟨2977388946964923531259403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1984925964643282354172935 2977388946964923531259403)
              ·
                refine ⟨4466083420447385296889105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2977388946964923531259403 4466083420447385296889105)
                ·
                  refine ⟨3349562565335538972666829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4466083420447385296889105 3349562565335538972666829)
                  ·
                    refine ⟨1256085962000827114750061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3349562565335538972666829 1256085962000827114750061)
                    ·
                      refine ⟨471032235750310168031273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1256085962000827114750061 471032235750310168031273)
                      ·
                        rfl

theorem cell23_917332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_917332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917332 prefixEnd_917332 := by exact prefixLift 917332
  have htrace : WordTrace (prefixWord ++ tailWord_917332) baseStart_917332 baseEnd_917332 := by
    simpa [prefixWord, tailWord_917332, baseEnd_917332] using wordTrace_append hprefix tailTrace_917332
  have hstable : (prefixWord ++ tailWord_917332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917332).length < 2 ^ (prefixWord ++ tailWord_917332).sum := by decide
  have hdescent : baseEnd_917332 < baseStart_917332 := by decide
  rcases family_descends (prefixWord ++ tailWord_917332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917355 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 3, 6, 2]
def baseStart_917355 : Nat := 118140960795 + 917355 * 2 ^ 59
def prefixEnd_917355 : Nat := 4983230072969 + 3 ^ 40 * 917355 * 2
def baseEnd_917355 : Nat := 471044045805363578043667

theorem tailTrace_917355 : CollatzResearch.WordTrace tailWord_917355 prefixEnd_917355 471044045805363578043667 := by
  unfold tailWord_917355
  simp only [CollatzResearch.WordTrace]
  refine ⟨33458685591586981605833519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22305790394391321070555679 33458685591586981605833519)
  ·
    refine ⟨50188028387380472408750279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33458685591586981605833519 50188028387380472408750279)
    ·
      refine ⟨75282042581070708613125419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50188028387380472408750279 75282042581070708613125419)
      ·
        refine ⟨112923063871606062919688129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75282042581070708613125419 112923063871606062919688129)
        ·
          refine ⟨84692297903704547189766097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112923063871606062919688129 84692297903704547189766097)
          ·
            refine ⟨63519223427778410392324573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84692297903704547189766097 63519223427778410392324573)
            ·
              refine ⟨23819708785416903897121715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63519223427778410392324573 23819708785416903897121715)
              ·
                refine ⟨35729563178125355845682573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23819708785416903897121715 35729563178125355845682573)
                ·
                  refine ⟨13398586191797008442130965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35729563178125355845682573 13398586191797008442130965)
                  ·
                    refine ⟨628058727740484770724889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13398586191797008442130965 628058727740484770724889)
                    ·
                      refine ⟨471044045805363578043667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 628058727740484770724889 471044045805363578043667)
                      ·
                        rfl

theorem cell23_917355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 6, 2].length) (baseStart_917355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917355 prefixEnd_917355 := by exact prefixLift 917355
  have htrace : WordTrace (prefixWord ++ tailWord_917355) baseStart_917355 baseEnd_917355 := by
    simpa [prefixWord, tailWord_917355, baseEnd_917355] using wordTrace_append hprefix tailTrace_917355
  have hstable : (prefixWord ++ tailWord_917355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917355).length < 2 ^ (prefixWord ++ tailWord_917355).sum := by decide
  have hdescent : baseEnd_917355 < baseStart_917355 := by decide
  rcases family_descends (prefixWord ++ tailWord_917355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917375 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 4, 2, 3]
def baseStart_917375 : Nat := 118140960795 + 917375 * 2 ^ 59
def prefixEnd_917375 : Nat := 4983230072969 + 3 ^ 40 * 917375 * 2
def baseEnd_917375 : Nat := 471054315418453499793575

theorem tailTrace_917375 : CollatzResearch.WordTrace tailWord_917375 prefixEnd_917375 471054315418453499793575 := by
  unfold tailWord_917375
  simp only [CollatzResearch.WordTrace]
  refine ⟨33459415051514525021561579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22306276701009683347707719 33459415051514525021561579)
  ·
    refine ⟨50189122577271787532342369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33459415051514525021561579 50189122577271787532342369)
    ·
      refine ⟨37641841932953840649256777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50189122577271787532342369 37641841932953840649256777)
      ·
        refine ⟨28231381449715380486942583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37641841932953840649256777 28231381449715380486942583)
        ·
          refine ⟨42347072174573070730413875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28231381449715380486942583 42347072174573070730413875)
          ·
            refine ⟨63520608261859606095620813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42347072174573070730413875 63520608261859606095620813)
            ·
              refine ⟨23820228098197352285857805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63520608261859606095620813 23820228098197352285857805)
              ·
                refine ⟨8932585536824007107196677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23820228098197352285857805 8932585536824007107196677)
                ·
                  refine ⟨1674859788154501332599377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8932585536824007107196677 1674859788154501332599377)
                  ·
                    refine ⟨1256144841115875999449533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1674859788154501332599377 1256144841115875999449533)
                    ·
                      refine ⟨471054315418453499793575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1256144841115875999449533 471054315418453499793575)
                      ·
                        rfl

theorem cell23_917375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 2, 3].length) (baseStart_917375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917375 prefixEnd_917375 := by exact prefixLift 917375
  have htrace : WordTrace (prefixWord ++ tailWord_917375) baseStart_917375 baseEnd_917375 := by
    simpa [prefixWord, tailWord_917375, baseEnd_917375] using wordTrace_append hprefix tailTrace_917375
  have hstable : (prefixWord ++ tailWord_917375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917375).length < 2 ^ (prefixWord ++ tailWord_917375).sum := by decide
  have hdescent : baseEnd_917375 < baseStart_917375 := by decide
  rcases family_descends (prefixWord ++ tailWord_917375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917455 : List Nat := [1, 1, 2, 1, 1, 5, 2, 3, 1, 6]
def baseStart_917455 : Nat := 118140960795 + 917455 * 2 ^ 59
def prefixEnd_917455 : Nat := 4983230072969 + 3 ^ 40 * 917455 * 2
def baseEnd_917455 : Nat := 157031797956937728931069

theorem tailTrace_917455 : CollatzResearch.WordTrace tailWord_917455 prefixEnd_917455 157031797956937728931069 := by
  unfold tailWord_917455
  simp only [CollatzResearch.WordTrace]
  refine ⟨33462332891224698684473819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22308221927483132456315879 33462332891224698684473819)
  ·
    refine ⟨50193499336837048026710729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33462332891224698684473819 50193499336837048026710729)
    ·
      refine ⟨37645124502627786020033047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50193499336837048026710729 37645124502627786020033047)
      ·
        refine ⟨56467686753941679030049571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37645124502627786020033047 56467686753941679030049571)
        ·
          refine ⟨84701530130912518545074357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56467686753941679030049571 84701530130912518545074357)
          ·
            refine ⟨7940768449773048613600721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84701530130912518545074357 7940768449773048613600721)
            ·
              refine ⟨5955576337329786460200541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7940768449773048613600721 5955576337329786460200541)
              ·
                refine ⟨2233341126498669922575203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5955576337329786460200541 2233341126498669922575203)
                ·
                  refine ⟨3350011689748004883862805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2233341126498669922575203 3350011689748004883862805)
                  ·
                    refine ⟨157031797956937728931069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3350011689748004883862805 157031797956937728931069)
                    ·
                      rfl

theorem cell23_917455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 6].length) (baseStart_917455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917455 prefixEnd_917455 := by exact prefixLift 917455
  have htrace : WordTrace (prefixWord ++ tailWord_917455) baseStart_917455 baseEnd_917455 := by
    simpa [prefixWord, tailWord_917455, baseEnd_917455] using wordTrace_append hprefix tailTrace_917455
  have hstable : (prefixWord ++ tailWord_917455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917455).length < 2 ^ (prefixWord ++ tailWord_917455).sum := by decide
  have hdescent : baseEnd_917455 < baseStart_917455 := by decide
  rcases family_descends (prefixWord ++ tailWord_917455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917466 : List Nat := [3, 1, 1, 2, 5, 1, 2, 1, 2, 3, 2]
def baseStart_917466 : Nat := 118140960795 + 917466 * 2 ^ 59
def prefixEnd_917466 : Nat := 4983230072969 + 3 ^ 40 * 917466 * 2
def baseEnd_917466 : Nat := 471101042158012643755657

theorem tailTrace_917466 : CollatzResearch.WordTrace tailWord_917466 prefixEnd_917466 471101042158012643755657 := by
  unfold tailWord_917466
  simp only [CollatzResearch.WordTrace]
  refine ⟨8365683523546211890781063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22308489396123231708749501 8365683523546211890781063)
  ·
    refine ⟨12548525285319317836171595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8365683523546211890781063 12548525285319317836171595)
    ·
      refine ⟨18822787927978976754257393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12548525285319317836171595 18822787927978976754257393)
      ·
        refine ⟨14117090945984232565693045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18822787927978976754257393 14117090945984232565693045)
        ·
          refine ⟨1323477276186021803033723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14117090945984232565693045 1323477276186021803033723)
          ·
            refine ⟨1985215914279032704550585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1323477276186021803033723 1985215914279032704550585)
            ·
              refine ⟨1488911935709274528412939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1985215914279032704550585 1488911935709274528412939)
              ·
                refine ⟨2233367903563911792619409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1488911935709274528412939 2233367903563911792619409)
                ·
                  refine ⟨1675025927672933844464557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2233367903563911792619409 1675025927672933844464557)
                  ·
                    refine ⟨628134722877350191674209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1675025927672933844464557 628134722877350191674209)
                    ·
                      refine ⟨471101042158012643755657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 628134722877350191674209 471101042158012643755657)
                      ·
                        rfl

theorem cell23_917466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 2, 3, 2].length) (baseStart_917466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917466 prefixEnd_917466 := by exact prefixLift 917466
  have htrace : WordTrace (prefixWord ++ tailWord_917466) baseStart_917466 baseEnd_917466 := by
    simpa [prefixWord, tailWord_917466, baseEnd_917466] using wordTrace_append hprefix tailTrace_917466
  have hstable : (prefixWord ++ tailWord_917466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917466).length < 2 ^ (prefixWord ++ tailWord_917466).sum := by decide
  have hdescent : baseEnd_917466 < baseStart_917466 := by decide
  rcases family_descends (prefixWord ++ tailWord_917466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917515 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 2, 7]
def baseStart_917515 : Nat := 118140960795 + 917515 * 2 ^ 59
def prefixEnd_917515 : Nat := 4983230072969 + 3 ^ 40 * 917515 * 2
def baseEnd_917515 : Nat := 157042067570027650680977

theorem tailTrace_917515 : CollatzResearch.WordTrace tailWord_917515 prefixEnd_917515 157042067570027650680977 := by
  unfold tailWord_917515
  simp only [CollatzResearch.WordTrace]
  refine ⟨33464521271007328931657999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22309680847338219287771999 33464521271007328931657999)
  ·
    refine ⟨50196781906510993397486999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33464521271007328931657999 50196781906510993397486999)
    ·
      refine ⟨75295172859766490096230499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50196781906510993397486999 75295172859766490096230499)
      ·
        refine ⟨112942759289649735144345749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75295172859766490096230499 112942759289649735144345749)
        ·
          refine ⟨5294191841702331334891207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 112942759289649735144345749 5294191841702331334891207)
          ·
            refine ⟨7941287762553497002336811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5294191841702331334891207 7941287762553497002336811)
            ·
              refine ⟨11911931643830245503505217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7941287762553497002336811 11911931643830245503505217)
              ·
                refine ⟨8933948732872684127628913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11911931643830245503505217 8933948732872684127628913)
                ·
                  refine ⟨6700461549654513095721685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8933948732872684127628913 6700461549654513095721685)
                  ·
                    refine ⟨157042067570027650680977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6700461549654513095721685 157042067570027650680977)
                    ·
                      rfl

theorem cell23_917515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 7].length) (baseStart_917515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917515 prefixEnd_917515 := by exact prefixLift 917515
  have htrace : WordTrace (prefixWord ++ tailWord_917515) baseStart_917515 baseEnd_917515 := by
    simpa [prefixWord, tailWord_917515, baseEnd_917515] using wordTrace_append hprefix tailTrace_917515
  have hstable : (prefixWord ++ tailWord_917515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917515).length < 2 ^ (prefixWord ++ tailWord_917515).sum := by decide
  have hdescent : baseEnd_917515 < baseStart_917515 := by decide
  rcases family_descends (prefixWord ++ tailWord_917515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917517 : List Nat := [1, 7, 1, 2, 1, 2, 1, 1, 2, 3, 2]
def baseStart_917517 : Nat := 118140960795 + 917517 * 2 ^ 59
def prefixEnd_917517 : Nat := 4983230072969 + 3 ^ 40 * 917517 * 2
def baseEnd_917517 : Nat := 471127229671391944217923

theorem tailTrace_917517 : CollatzResearch.WordTrace tailWord_917517 prefixEnd_917517 471127229671391944217923 := by
  unfold tailWord_917517
  simp only [CollatzResearch.WordTrace]
  refine ⟨33464594217000083273230805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22309729478000055515487203 33464594217000083273230805)
  ·
    refine ⟨784326426960939451716347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 33464594217000083273230805 784326426960939451716347)
    ·
      refine ⟨1176489640441409177574521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 784326426960939451716347 1176489640441409177574521)
      ·
        refine ⟨882367230331056883180891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1176489640441409177574521 882367230331056883180891)
        ·
          refine ⟨1323550845496585324771337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 882367230331056883180891 1323550845496585324771337)
          ·
            refine ⟨992663134122438993578503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1323550845496585324771337 992663134122438993578503)
            ·
              refine ⟨1488994701183658490367755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 992663134122438993578503 1488994701183658490367755)
              ·
                refine ⟨2233492051775487735551633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1488994701183658490367755 2233492051775487735551633)
                ·
                  refine ⟨1675119038831615801663725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2233492051775487735551633 1675119038831615801663725)
                  ·
                    refine ⟨628169639561855925623897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1675119038831615801663725 628169639561855925623897)
                    ·
                      refine ⟨471127229671391944217923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 628169639561855925623897 471127229671391944217923)
                      ·
                        rfl

theorem cell23_917517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_917517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917517 prefixEnd_917517 := by exact prefixLift 917517
  have htrace : WordTrace (prefixWord ++ tailWord_917517) baseStart_917517 baseEnd_917517 := by
    simpa [prefixWord, tailWord_917517, baseEnd_917517] using wordTrace_append hprefix tailTrace_917517
  have hstable : (prefixWord ++ tailWord_917517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917517).length < 2 ^ (prefixWord ++ tailWord_917517).sum := by decide
  have hdescent : baseEnd_917517 < baseStart_917517 := by decide
  rcases family_descends (prefixWord ++ tailWord_917517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917533 : List Nat := [1, 4, 2, 2, 2, 3, 2, 1, 1, 2, 3]
def baseStart_917533 : Nat := 118140960795 + 917533 * 2 ^ 59
def prefixEnd_917533 : Nat := 4983230072969 + 3 ^ 40 * 917533 * 2
def baseEnd_917533 : Nat := 471135445361863881617849

theorem tailTrace_917533 : CollatzResearch.WordTrace tailWord_917533 prefixEnd_917533 471135445361863881617849 := by
  unfold tailWord_917533
  simp only [CollatzResearch.WordTrace]
  refine ⟨33465177784942118005813253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22310118523294745337208835 33465177784942118005813253)
  ·
    refine ⟨6274720834676647126089985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33465177784942118005813253 6274720834676647126089985)
    ·
      refine ⟨4706040626007485344567489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6274720834676647126089985 4706040626007485344567489)
      ·
        refine ⟨3529530469505614008425617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4706040626007485344567489 3529530469505614008425617)
        ·
          refine ⟨2647147852129210506319213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3529530469505614008425617 2647147852129210506319213)
          ·
            refine ⟨992680444548453939869705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2647147852129210506319213 992680444548453939869705)
            ·
              refine ⟨744510333411340454902279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 992680444548453939869705 744510333411340454902279)
              ·
                refine ⟨1116765500117010682353419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 744510333411340454902279 1116765500117010682353419)
                ·
                  refine ⟨1675148250175516023530129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1116765500117010682353419 1675148250175516023530129)
                  ·
                    refine ⟨1256361187631637017647597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1675148250175516023530129 1256361187631637017647597)
                    ·
                      refine ⟨471135445361863881617849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1256361187631637017647597 471135445361863881617849)
                      ·
                        rfl

theorem cell23_917533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_917533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917533 prefixEnd_917533 := by exact prefixLift 917533
  have htrace : WordTrace (prefixWord ++ tailWord_917533) baseStart_917533 baseEnd_917533 := by
    simpa [prefixWord, tailWord_917533, baseEnd_917533] using wordTrace_append hprefix tailTrace_917533
  have hstable : (prefixWord ++ tailWord_917533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917533).length < 2 ^ (prefixWord ++ tailWord_917533).sum := by decide
  have hdescent : baseEnd_917533 < baseStart_917533 := by decide
  rcases family_descends (prefixWord ++ tailWord_917533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917546 : List Nat := [3, 1, 4, 1, 2, 2, 1, 1, 4, 1, 3]
def baseStart_917546 : Nat := 118140960795 + 917546 * 2 ^ 59
def prefixEnd_917546 : Nat := 4983230072969 + 3 ^ 40 * 917546 * 2
def baseEnd_917546 : Nat := 471142120610372330755289

theorem tailTrace_917546 : CollatzResearch.WordTrace tailWord_917546 prefixEnd_917546 471142120610372330755289 := by
  unfold tailWord_917546
  simp only [CollatzResearch.WordTrace]
  refine ⟨8366412983473755306509123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22310434622596680817357661 8366412983473755306509123)
  ·
    refine ⟨12549619475210632959763685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8366412983473755306509123 12549619475210632959763685)
    ·
      refine ⟨2353053651601993679955691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12549619475210632959763685 2353053651601993679955691)
      ·
        refine ⟨3529580477402990519933537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2353053651601993679955691 3529580477402990519933537)
        ·
          refine ⟨2647185358052242889950153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3529580477402990519933537 2647185358052242889950153)
          ·
            refine ⟨1985389018539182167462615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2647185358052242889950153 1985389018539182167462615)
            ·
              refine ⟨2978083527808773251193923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1985389018539182167462615 2978083527808773251193923)
              ·
                refine ⟨4467125291713159876790885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2978083527808773251193923 4467125291713159876790885)
                ·
                  refine ⟨837585992196217476898291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4467125291713159876790885 837585992196217476898291)
                  ·
                    refine ⟨1256378988294326215347437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 837585992196217476898291 1256378988294326215347437)
                    ·
                      refine ⟨471142120610372330755289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1256378988294326215347437 471142120610372330755289)
                      ·
                        rfl

theorem cell23_917546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_917546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917546 prefixEnd_917546 := by exact prefixLift 917546
  have htrace : WordTrace (prefixWord ++ tailWord_917546) baseStart_917546 baseEnd_917546 := by
    simpa [prefixWord, tailWord_917546, baseEnd_917546] using wordTrace_append hprefix tailTrace_917546
  have hstable : (prefixWord ++ tailWord_917546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917546).length < 2 ^ (prefixWord ++ tailWord_917546).sum := by decide
  have hdescent : baseEnd_917546 < baseStart_917546 := by decide
  rcases family_descends (prefixWord ++ tailWord_917546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917590 : List Nat := [5, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2]
def baseStart_917590 : Nat := 118140960795 + 917590 * 2 ^ 59
def prefixEnd_917590 : Nat := 4983230072969 + 3 ^ 40 * 917590 * 2
def baseEnd_917590 : Nat := 471164713759170158605087

theorem tailTrace_917590 : CollatzResearch.WordTrace tailWord_917590 prefixEnd_917590 471164713759170158605087 := by
  unfold tailWord_917590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2091703546608476046289889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22311504497157077827092149 2091703546608476046289889)
  ·
    refine ⟨1568777659956357034717417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2091703546608476046289889 1568777659956357034717417)
    ·
      refine ⟨1176583244967267776038063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1568777659956357034717417 1176583244967267776038063)
      ·
        refine ⟨1764874867450901664057095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1176583244967267776038063 1764874867450901664057095)
        ·
          refine ⟨2647312301176352496085643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1764874867450901664057095 2647312301176352496085643)
          ·
            refine ⟨3970968451764528744128465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2647312301176352496085643 3970968451764528744128465)
            ·
              refine ⟨2978226338823396558096349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3970968451764528744128465 2978226338823396558096349)
              ·
                refine ⟨1116834877058773709286131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2978226338823396558096349 1116834877058773709286131)
                ·
                  refine ⟨1675252315588160563929197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1116834877058773709286131 1675252315588160563929197)
                  ·
                    refine ⟨628219618345560211473449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1675252315588160563929197 628219618345560211473449)
                    ·
                      refine ⟨471164713759170158605087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 628219618345560211473449 471164713759170158605087)
                      ·
                        rfl

theorem cell23_917590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_917590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917590 prefixEnd_917590 := by exact prefixLift 917590
  have htrace : WordTrace (prefixWord ++ tailWord_917590) baseStart_917590 baseEnd_917590 := by
    simpa [prefixWord, tailWord_917590, baseEnd_917590] using wordTrace_append hprefix tailTrace_917590
  have hstable : (prefixWord ++ tailWord_917590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917590).length < 2 ^ (prefixWord ++ tailWord_917590).sum := by decide
  have hdescent : baseEnd_917590 < baseStart_917590 := by decide
  rcases family_descends (prefixWord ++ tailWord_917590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917669 : List Nat := [1, 3, 1, 2, 1, 3, 2, 3, 3, 4]
def baseStart_917669 : Nat := 118140960795 + 917669 * 2 ^ 59
def prefixEnd_917669 : Nat := 4983230072969 + 3 ^ 40 * 917669 * 2
def baseEnd_917669 : Nat := 157068426243625116505741

theorem tailTrace_917669 : CollatzResearch.WordTrace tailWord_917669 prefixEnd_917669 157068426243625116505741 := by
  unfold tailWord_917669
  simp only [CollatzResearch.WordTrace]
  refine ⟨33470138112449413232764061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22313425408299608821842707 33470138112449413232764061)
  ·
    refine ⟨12551301792168529962286523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33470138112449413232764061 12551301792168529962286523)
    ·
      refine ⟨18826952688252794943429785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12551301792168529962286523 18826952688252794943429785)
      ·
        refine ⟨14120214516189596207572339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18826952688252794943429785 14120214516189596207572339)
        ·
          refine ⟨21180321774284394311358509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14120214516189596207572339 21180321774284394311358509)
          ·
            refine ⟨7942620665356647866759441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21180321774284394311358509 7942620665356647866759441)
            ·
              refine ⟨5956965499017485900069581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7942620665356647866759441 5956965499017485900069581)
              ·
                refine ⟨2233862062131557212526093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5956965499017485900069581 2233862062131557212526093)
                ·
                  refine ⟨837698273299333954697285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2233862062131557212526093 837698273299333954697285)
                  ·
                    refine ⟨157068426243625116505741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 837698273299333954697285 157068426243625116505741)
                    ·
                      rfl

theorem cell23_917669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 3, 4].length) (baseStart_917669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917669 prefixEnd_917669 := by exact prefixLift 917669
  have htrace : WordTrace (prefixWord ++ tailWord_917669) baseStart_917669 baseEnd_917669 := by
    simpa [prefixWord, tailWord_917669, baseEnd_917669] using wordTrace_append hprefix tailTrace_917669
  have hstable : (prefixWord ++ tailWord_917669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917669).length < 2 ^ (prefixWord ++ tailWord_917669).sum := by decide
  have hdescent : baseEnd_917669 < baseStart_917669 := by decide
  rcases family_descends (prefixWord ++ tailWord_917669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917696 : List Nat := [2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 3]
def baseStart_917696 : Nat := 118140960795 + 917696 * 2 ^ 59
def prefixEnd_917696 : Nat := 4983230072969 + 3 ^ 40 * 917696 * 2
def baseEnd_917696 : Nat := 471219142708546743879599

theorem tailTrace_917696 : CollatzResearch.WordTrace tailWord_917696 prefixEnd_917696 471219142708546743879599 := by
  unfold tailWord_917696
  simp only [CollatzResearch.WordTrace]
  refine ⟨16735561441675798421998471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22314081922234397895997961 16735561441675798421998471)
  ·
    refine ⟨25103342162513697632997707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16735561441675798421998471 25103342162513697632997707)
    ·
      refine ⟨37655013243770546449496561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25103342162513697632997707 37655013243770546449496561)
      ·
        refine ⟨28241259932827909837122421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37655013243770546449496561 28241259932827909837122421)
        ·
          refine ⟨2647618118702616547230227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28241259932827909837122421 2647618118702616547230227)
          ·
            refine ⟨3971427178053924820845341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2647618118702616547230227 3971427178053924820845341)
            ·
              refine ⟨1489285191770221807817003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3971427178053924820845341 1489285191770221807817003)
              ·
                refine ⟨2233927787655332711725505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1489285191770221807817003 2233927787655332711725505)
                ·
                  refine ⟨1675445840741499533794129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2233927787655332711725505 1675445840741499533794129)
                  ·
                    refine ⟨1256584380556124650345597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1675445840741499533794129 1256584380556124650345597)
                    ·
                      refine ⟨471219142708546743879599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1256584380556124650345597 471219142708546743879599)
                      ·
                        rfl

theorem cell23_917696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 3].length) (baseStart_917696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917696 prefixEnd_917696 := by exact prefixLift 917696
  have htrace : WordTrace (prefixWord ++ tailWord_917696) baseStart_917696 baseEnd_917696 := by
    simpa [prefixWord, tailWord_917696, baseEnd_917696] using wordTrace_append hprefix tailTrace_917696
  have hstable : (prefixWord ++ tailWord_917696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917696).length < 2 ^ (prefixWord ++ tailWord_917696).sum := by decide
  have hdescent : baseEnd_917696 < baseStart_917696 := by decide
  rcases family_descends (prefixWord ++ tailWord_917696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917736 : List Nat := [2, 1, 4, 1, 2, 2, 1, 2, 1, 5, 2]
def baseStart_917736 : Nat := 118140960795 + 917736 * 2 ^ 59
def prefixEnd_917736 : Nat := 4983230072969 + 3 ^ 40 * 917736 * 2
def baseEnd_917736 : Nat := 471239681934726587379415

theorem tailTrace_917736 : CollatzResearch.WordTrace tailWord_917736 prefixEnd_917736 471239681934726587379415 := by
  unfold tailWord_917736
  simp only [CollatzResearch.WordTrace]
  refine ⟨16736290901603341837726531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22315054535471122450302041 16736290901603341837726531)
  ·
    refine ⟨25104436352405012756589797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16736290901603341837726531 25104436352405012756589797)
    ·
      refine ⟨4707081816075939891860587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25104436352405012756589797 4707081816075939891860587)
      ·
        refine ⟨7060622724113909837790881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4707081816075939891860587 7060622724113909837790881)
        ·
          refine ⟨5295467043085432378343161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7060622724113909837790881 5295467043085432378343161)
          ·
            refine ⟨3971600282314074283757371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5295467043085432378343161 3971600282314074283757371)
            ·
              refine ⟨5957400423471111425636057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3971600282314074283757371 5957400423471111425636057)
              ·
                refine ⟨4468050317603333569227043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5957400423471111425636057 4468050317603333569227043)
                ·
                  refine ⟨6702075476405000353840565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4468050317603333569227043 6702075476405000353840565)
                  ·
                    refine ⟨628319575912968783172553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6702075476405000353840565 628319575912968783172553)
                    ·
                      refine ⟨471239681934726587379415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 628319575912968783172553 471239681934726587379415)
                      ·
                        rfl

theorem cell23_917736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_917736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917736 prefixEnd_917736 := by exact prefixLift 917736
  have htrace : WordTrace (prefixWord ++ tailWord_917736) baseStart_917736 baseEnd_917736 := by
    simpa [prefixWord, tailWord_917736, baseEnd_917736] using wordTrace_append hprefix tailTrace_917736
  have hstable : (prefixWord ++ tailWord_917736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917736).length < 2 ^ (prefixWord ++ tailWord_917736).sum := by decide
  have hdescent : baseEnd_917736 < baseStart_917736 := by decide
  rcases family_descends (prefixWord ++ tailWord_917736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917746 : List Nat := [3, 2, 1, 3, 2, 1, 1, 4, 1, 5]
def baseStart_917746 : Nat := 118140960795 + 917746 * 2 ^ 59
def prefixEnd_917746 : Nat := 4983230072969 + 3 ^ 40 * 917746 * 2
def baseEnd_917746 : Nat := 157081605580423849418123

theorem tailTrace_917746 : CollatzResearch.WordTrace tailWord_917746 prefixEnd_917746 157081605580423849418123 := by
  unfold tailWord_917746
  simp only [CollatzResearch.WordTrace]
  refine ⟨8368236633292613845829273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22315297688780303588878061 8368236633292613845829273)
  ·
    refine ⟨6276177474969460384371955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8368236633292613845829273 6276177474969460384371955)
    ·
      refine ⟨9414266212454190576557933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6276177474969460384371955 9414266212454190576557933)
      ·
        refine ⟨3530349829670321466209225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9414266212454190576557933 3530349829670321466209225)
        ·
          refine ⟨2647762372252741099656919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3530349829670321466209225 2647762372252741099656919)
          ·
            refine ⟨3971643558379111649485379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2647762372252741099656919 3971643558379111649485379)
            ·
              refine ⟨5957465337568667474228069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3971643558379111649485379 5957465337568667474228069)
              ·
                refine ⟨1117024750794125151417763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5957465337568667474228069 1117024750794125151417763)
                ·
                  refine ⟨1675537126191187727126645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1117024750794125151417763 1675537126191187727126645)
                  ·
                    refine ⟨157081605580423849418123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1675537126191187727126645 157081605580423849418123)
                    ·
                      rfl

theorem cell23_917746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_917746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917746 prefixEnd_917746 := by exact prefixLift 917746
  have htrace : WordTrace (prefixWord ++ tailWord_917746) baseStart_917746 baseEnd_917746 := by
    simpa [prefixWord, tailWord_917746, baseEnd_917746] using wordTrace_append hprefix tailTrace_917746
  have hstable : (prefixWord ++ tailWord_917746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917746).length < 2 ^ (prefixWord ++ tailWord_917746).sum := by decide
  have hdescent : baseEnd_917746 < baseStart_917746 := by decide
  rcases family_descends (prefixWord ++ tailWord_917746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917759 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 6, 4]
def baseStart_917759 : Nat := 118140960795 + 917759 * 2 ^ 59
def prefixEnd_917759 : Nat := 4983230072969 + 3 ^ 40 * 917759 * 2
def baseEnd_917759 : Nat := 157083830663259999130603

theorem tailTrace_917759 : CollatzResearch.WordTrace tailWord_917759 prefixEnd_917759 157083830663259999130603 := by
  unfold tailWord_917759
  simp only [CollatzResearch.WordTrace]
  refine ⟨33473420682123358603540331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22315613788082239069026887 33473420682123358603540331)
  ·
    refine ⟨50210131023185037905310497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33473420682123358603540331 50210131023185037905310497)
    ·
      refine ⟨37657598267388778428982873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50210131023185037905310497 37657598267388778428982873)
      ·
        refine ⟨28243198700541583821737155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37657598267388778428982873 28243198700541583821737155)
        ·
          refine ⟨42364798050812375732605733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28243198700541583821737155 42364798050812375732605733)
          ·
            refine ⟨7943399634527320449863575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42364798050812375732605733 7943399634527320449863575)
            ·
              refine ⟨11915099451790980674795363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7943399634527320449863575 11915099451790980674795363)
              ·
                refine ⟨17872649177686471012193045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11915099451790980674795363 17872649177686471012193045)
                ·
                  refine ⟨837780430204053328696549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17872649177686471012193045 837780430204053328696549)
                  ·
                    refine ⟨157083830663259999130603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 837780430204053328696549 157083830663259999130603)
                    ·
                      rfl

theorem cell23_917759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 6, 4].length) (baseStart_917759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917759 prefixEnd_917759 := by exact prefixLift 917759
  have htrace : WordTrace (prefixWord ++ tailWord_917759) baseStart_917759 baseEnd_917759 := by
    simpa [prefixWord, tailWord_917759, baseEnd_917759] using wordTrace_append hprefix tailTrace_917759
  have hstable : (prefixWord ++ tailWord_917759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917759).length < 2 ^ (prefixWord ++ tailWord_917759).sum := by decide
  have hdescent : baseEnd_917759 < baseStart_917759 := by decide
  rcases family_descends (prefixWord ++ tailWord_917759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917769 : List Nat := [1, 2, 1, 1, 3, 4, 1, 3, 1, 1, 5]
def baseStart_917769 : Nat := 118140960795 + 917769 * 2 ^ 59
def prefixEnd_917769 : Nat := 4983230072969 + 3 ^ 40 * 917769 * 2
def baseEnd_917769 : Nat := 471256626796324958266763

theorem tailTrace_917769 : CollatzResearch.WordTrace tailWord_917769 prefixEnd_917769 471256626796324958266763 := by
  unfold tailWord_917769
  simp only [CollatzResearch.WordTrace]
  refine ⟨33473785412087130311404361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22315856941391420207602907 33473785412087130311404361)
  ·
    refine ⟨25105339059065347733553271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33473785412087130311404361 25105339059065347733553271)
    ·
      refine ⟨37658008588598021600329907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25105339059065347733553271 37658008588598021600329907)
      ·
        refine ⟨56487012882897032400494861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37658008588598021600329907 56487012882897032400494861)
        ·
          refine ⟨21182629831086387150185573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56487012882897032400494861 21182629831086387150185573)
          ·
            refine ⟨3971743093328697590659795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21182629831086387150185573 3971743093328697590659795)
            ·
              refine ⟨5957614639993046385989693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3971743093328697590659795 5957614639993046385989693)
              ·
                refine ⟨2234105489997392394746135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5957614639993046385989693 2234105489997392394746135)
                ·
                  refine ⟨3351158234996088592119203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2234105489997392394746135 3351158234996088592119203)
                  ·
                    refine ⟨5026737352494132888178805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3351158234996088592119203 5026737352494132888178805)
                    ·
                      refine ⟨471256626796324958266763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5026737352494132888178805 471256626796324958266763)
                      ·
                        rfl

theorem cell23_917769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 1, 5].length) (baseStart_917769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917769 prefixEnd_917769 := by exact prefixLift 917769
  have htrace : WordTrace (prefixWord ++ tailWord_917769) baseStart_917769 baseEnd_917769 := by
    simpa [prefixWord, tailWord_917769, baseEnd_917769] using wordTrace_append hprefix tailTrace_917769
  have hstable : (prefixWord ++ tailWord_917769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917769).length < 2 ^ (prefixWord ++ tailWord_917769).sum := by decide
  have hdescent : baseEnd_917769 < baseStart_917769 := by decide
  rcases family_descends (prefixWord ++ tailWord_917769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917793 : List Nat := [1, 2, 3, 2, 1, 1, 6, 1, 2, 4]
def baseStart_917793 : Nat := 118140960795 + 917793 * 2 ^ 59
def prefixEnd_917793 : Nat := 4983230072969 + 3 ^ 40 * 917793 * 2
def baseEnd_917793 : Nat := 157089650110677621455551

theorem tailTrace_917793 : CollatzResearch.WordTrace tailWord_917793 prefixEnd_917793 157089650110677621455551 := by
  unfold tailWord_917793
  simp only [CollatzResearch.WordTrace]
  refine ⟨33474660764000182410278033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22316440509333454940185355 33474660764000182410278033)
  ·
    refine ⟨25105995573000136807708525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33474660764000182410278033 25105995573000136807708525)
    ·
      refine ⟨9414748339875051302890697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25105995573000136807708525 9414748339875051302890697)
      ·
        refine ⟨7061061254906288477168023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9414748339875051302890697 7061061254906288477168023)
        ·
          refine ⟨10591591882359432715752035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7061061254906288477168023 10591591882359432715752035)
          ·
            refine ⟨15887387823539149073628053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10591591882359432715752035 15887387823539149073628053)
            ·
              refine ⟨744721304228397612826315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15887387823539149073628053 744721304228397612826315)
              ·
                refine ⟨1117081956342596419239473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 744721304228397612826315 1117081956342596419239473)
                ·
                  refine ⟨837811467256947314429605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1117081956342596419239473 837811467256947314429605)
                  ·
                    refine ⟨157089650110677621455551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 837811467256947314429605 157089650110677621455551)
                    ·
                      rfl

theorem cell23_917793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_917793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917793 prefixEnd_917793 := by exact prefixLift 917793
  have htrace : WordTrace (prefixWord ++ tailWord_917793) baseStart_917793 baseEnd_917793 := by
    simpa [prefixWord, tailWord_917793, baseEnd_917793] using wordTrace_append hprefix tailTrace_917793
  have hstable : (prefixWord ++ tailWord_917793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917793).length < 2 ^ (prefixWord ++ tailWord_917793).sum := by decide
  have hdescent : baseEnd_917793 < baseStart_917793 := by decide
  rcases family_descends (prefixWord ++ tailWord_917793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917800 : List Nat := [2, 1, 5, 1, 3, 2, 1, 2, 1, 1, 4]
def baseStart_917800 : Nat := 118140960795 + 917800 * 2 ^ 59
def prefixEnd_917800 : Nat := 4983230072969 + 3 ^ 40 * 917800 * 2
def baseEnd_917800 : Nat := 471272544696614336979121

theorem tailTrace_917800 : CollatzResearch.WordTrace tailWord_917800 prefixEnd_917800 471272544696614336979121 := by
  unfold tailWord_917800
  simp only [CollatzResearch.WordTrace]
  refine ⟨16737458037487411302891427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22316610716649881737188569 16737458037487411302891427)
  ·
    refine ⟨25106187056231116954337141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16737458037487411302891427 25106187056231116954337141)
    ·
      refine ⟨2353705036521667214469107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25106187056231116954337141 2353705036521667214469107)
      ·
        refine ⟨3530557554782500821703661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2353705036521667214469107 3530557554782500821703661)
        ·
          refine ⟨1323959083043437808138873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3530557554782500821703661 1323959083043437808138873)
          ·
            refine ⟨992969312282578356104155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1323959083043437808138873 992969312282578356104155)
            ·
              refine ⟨1489453968423867534156233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 992969312282578356104155 1489453968423867534156233)
              ·
                refine ⟨1117090476317900650617175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1489453968423867534156233 1117090476317900650617175)
                ·
                  refine ⟨1675635714476850975925763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1117090476317900650617175 1675635714476850975925763)
                  ·
                    refine ⟨2513453571715276463888645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1675635714476850975925763 2513453571715276463888645)
                    ·
                      refine ⟨471272544696614336979121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2513453571715276463888645 471272544696614336979121)
                      ·
                        rfl

theorem cell23_917800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_917800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917800 prefixEnd_917800 := by exact prefixLift 917800
  have htrace : WordTrace (prefixWord ++ tailWord_917800) baseStart_917800 baseEnd_917800 := by
    simpa [prefixWord, tailWord_917800, baseEnd_917800] using wordTrace_append hprefix tailTrace_917800
  have hstable : (prefixWord ++ tailWord_917800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917800).length < 2 ^ (prefixWord ++ tailWord_917800).sum := by decide
  have hdescent : baseEnd_917800 < baseStart_917800 := by decide
  rcases family_descends (prefixWord ++ tailWord_917800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917816 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 6, 1, 3]
def baseStart_917816 : Nat := 118140960795 + 917816 * 2 ^ 59
def prefixEnd_917816 : Nat := 4983230072969 + 3 ^ 40 * 917816 * 2
def baseEnd_917816 : Nat := 471280760387086274379047

theorem tailTrace_917816 : CollatzResearch.WordTrace tailWord_917816 prefixEnd_917816 471280760387086274379047 := by
  unfold tailWord_917816
  simp only [CollatzResearch.WordTrace]
  refine ⟨16737749821458428669182651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22316999761944571558910201 16737749821458428669182651)
  ·
    refine ⟨25106624732187643003773977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16737749821458428669182651 25106624732187643003773977)
    ·
      refine ⟨18829968549140732252830483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25106624732187643003773977 18829968549140732252830483)
      ·
        refine ⟨28244952823711098379245725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18829968549140732252830483 28244952823711098379245725)
        ·
          refine ⟨10591857308891661892217147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28244952823711098379245725 10591857308891661892217147)
          ·
            refine ⟨15887785963337492838325721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10591857308891661892217147 15887785963337492838325721)
            ·
              refine ⟨11915839472503119628744291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15887785963337492838325721 11915839472503119628744291)
              ·
                refine ⟨17873759208754679443116437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11915839472503119628744291 17873759208754679443116437)
                ·
                  refine ⟨837832462910375598896083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17873759208754679443116437 837832462910375598896083)
                  ·
                    refine ⟨1256748694365563398344125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 837832462910375598896083 1256748694365563398344125)
                    ·
                      refine ⟨471280760387086274379047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1256748694365563398344125 471280760387086274379047)
                      ·
                        rfl

theorem cell23_917816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 6, 1, 3].length) (baseStart_917816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917816 prefixEnd_917816 := by exact prefixLift 917816
  have htrace : WordTrace (prefixWord ++ tailWord_917816) baseStart_917816 baseEnd_917816 := by
    simpa [prefixWord, tailWord_917816, baseEnd_917816] using wordTrace_append hprefix tailTrace_917816
  have hstable : (prefixWord ++ tailWord_917816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917816).length < 2 ^ (prefixWord ++ tailWord_917816).sum := by decide
  have hdescent : baseEnd_917816 < baseStart_917816 := by decide
  rcases family_descends (prefixWord ++ tailWord_917816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917873 : List Nat := [1, 2, 2, 2, 1, 2, 1, 4, 4, 2, 2]
def baseStart_917873 : Nat := 118140960795 + 917873 * 2 ^ 59
def prefixEnd_917873 : Nat := 4983230072969 + 3 ^ 40 * 917873 * 2
def baseEnd_917873 : Nat := 471310028784392551366285

theorem tailTrace_917873 : CollatzResearch.WordTrace tailWord_917873 prefixEnd_917873 471310028784392551366285 := by
  unfold tailWord_917873
  simp only [CollatzResearch.WordTrace]
  refine ⟨33477578603710356073190273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22318385735806904048793515 33477578603710356073190273)
  ·
    refine ⟨25108183952782767054892705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33477578603710356073190273 25108183952782767054892705)
    ·
      refine ⟨18831137964587075291169529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25108183952782767054892705 18831137964587075291169529)
      ·
        refine ⟨14123353473440306468377147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18831137964587075291169529 14123353473440306468377147)
        ·
          refine ⟨21185030210160459702565721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14123353473440306468377147 21185030210160459702565721)
          ·
            refine ⟨15888772657620344776924291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21185030210160459702565721 15888772657620344776924291)
            ·
              refine ⟨23833158986430517165386437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15888772657620344776924291 23833158986430517165386437)
              ·
                refine ⟨4468717309955721968509957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23833158986430517165386437 4468717309955721968509957)
                ·
                  refine ⟨837884495616697869095617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4468717309955721968509957 837884495616697869095617)
                  ·
                    refine ⟨628413371712523401821713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 837884495616697869095617 628413371712523401821713)
                    ·
                      refine ⟨471310028784392551366285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 628413371712523401821713 471310028784392551366285)
                      ·
                        rfl

theorem cell23_917873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 4, 2, 2].length) (baseStart_917873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917873 prefixEnd_917873 := by exact prefixLift 917873
  have htrace : WordTrace (prefixWord ++ tailWord_917873) baseStart_917873 baseEnd_917873 := by
    simpa [prefixWord, tailWord_917873, baseEnd_917873] using wordTrace_append hprefix tailTrace_917873
  have hstable : (prefixWord ++ tailWord_917873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917873).length < 2 ^ (prefixWord ++ tailWord_917873).sum := by decide
  have hdescent : baseEnd_917873 < baseStart_917873 := by decide
  rcases family_descends (prefixWord ++ tailWord_917873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917877 : List Nat := [1, 3, 4, 1, 2, 1, 4, 1, 1, 3, 2]
def baseStart_917877 : Nat := 118140960795 + 917877 * 2 ^ 59
def prefixEnd_917877 : Nat := 4983230072969 + 3 ^ 40 * 917877 * 2
def baseEnd_917877 : Nat := 471312082707010535716267

theorem tailTrace_917877 : CollatzResearch.WordTrace tailWord_917877 prefixEnd_917877 471312082707010535716267 := by
  unfold tailWord_917877
  simp only [CollatzResearch.WordTrace]
  refine ⟨33477724495695864756335885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22318482997130576504223923 33477724495695864756335885)
  ·
    refine ⟨12554146685885949283625957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33477724495695864756335885 12554146685885949283625957)
    ·
      refine ⟨2353902503603615490679867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12554146685885949283625957 2353902503603615490679867)
      ·
        refine ⟨3530853755405423236019801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2353902503603615490679867 3530853755405423236019801)
        ·
          refine ⟨2648140316554067427014851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3530853755405423236019801 2648140316554067427014851)
          ·
            refine ⟨3972210474831101140522277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2648140316554067427014851 3972210474831101140522277)
            ·
              refine ⟨744789464030831463847927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3972210474831101140522277 744789464030831463847927)
              ·
                refine ⟨1117184196046247195771891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 744789464030831463847927 1117184196046247195771891)
                ·
                  refine ⟨1675776294069370793657837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1117184196046247195771891 1675776294069370793657837)
                  ·
                    refine ⟨628416110276014047621689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1675776294069370793657837 628416110276014047621689)
                    ·
                      refine ⟨471312082707010535716267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 628416110276014047621689 471312082707010535716267)
                      ·
                        rfl

theorem cell23_917877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_917877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917877 prefixEnd_917877 := by exact prefixLift 917877
  have htrace : WordTrace (prefixWord ++ tailWord_917877) baseStart_917877 baseEnd_917877 := by
    simpa [prefixWord, tailWord_917877, baseEnd_917877] using wordTrace_append hprefix tailTrace_917877
  have hstable : (prefixWord ++ tailWord_917877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917877).length < 2 ^ (prefixWord ++ tailWord_917877).sum := by decide
  have hdescent : baseEnd_917877 < baseStart_917877 := by decide
  rcases family_descends (prefixWord ++ tailWord_917877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917896 : List Nat := [2, 1, 3, 3, 1, 1, 4, 1, 7]
def baseStart_917896 : Nat := 118140960795 + 917896 * 2 ^ 59
def prefixEnd_917896 : Nat := 4983230072969 + 3 ^ 40 * 917896 * 2
def baseEnd_917896 : Nat := 52369093204382884597631

theorem tailTrace_917896 : CollatzResearch.WordTrace tailWord_917896 prefixEnd_917896 52369093204382884597631 := by
  unfold tailWord_917896
  simp only [CollatzResearch.WordTrace]
  refine ⟨16739208741313515500638771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22318944988418020667518361 16739208741313515500638771)
  ·
    refine ⟨25108813111970273250958157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16739208741313515500638771 25108813111970273250958157)
    ·
      refine ⟨9415804916988852469109309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25108813111970273250958157 9415804916988852469109309)
      ·
        refine ⟨3530926843870819675915991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9415804916988852469109309 3530926843870819675915991)
        ·
          refine ⟨5296390265806229513873987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3530926843870819675915991 5296390265806229513873987)
          ·
            refine ⟨7944585398709344270810981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5296390265806229513873987 7944585398709344270810981)
            ·
              refine ⟨1489609762258002050777059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7944585398709344270810981 1489609762258002050777059)
              ·
                refine ⟨2234414643387003076165589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1489609762258002050777059 2234414643387003076165589)
                ·
                  refine ⟨52369093204382884597631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2234414643387003076165589 52369093204382884597631)
                  ·
                    rfl

theorem cell23_917896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 7].length) (baseStart_917896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917896 prefixEnd_917896 := by exact prefixLift 917896
  have htrace : WordTrace (prefixWord ++ tailWord_917896) baseStart_917896 baseEnd_917896 := by
    simpa [prefixWord, tailWord_917896, baseEnd_917896] using wordTrace_append hprefix tailTrace_917896
  have hstable : (prefixWord ++ tailWord_917896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917896).length < 2 ^ (prefixWord ++ tailWord_917896).sum := by decide
  have hdescent : baseEnd_917896 < baseStart_917896 := by decide
  rcases family_descends (prefixWord ++ tailWord_917896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917983 : List Nat := [1, 1, 2, 3, 3, 2, 1, 3, 2, 2, 3]
def baseStart_917983 : Nat := 118140960795 + 917983 * 2 ^ 59
def prefixEnd_917983 : Nat := 4983230072969 + 3 ^ 40 * 917983 * 2
def baseEnd_917983 : Nat := 471366511656387120990779

theorem tailTrace_917983 : CollatzResearch.WordTrace tailWord_917983 prefixEnd_917983 471366511656387120990779 := by
  unfold tailWord_917983
  simp only [CollatzResearch.WordTrace]
  refine ⟨33481590633311844859694603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22321060422207896573129735 33481590633311844859694603)
  ·
    refine ⟨50222385949967767289541905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33481590633311844859694603 50222385949967767289541905)
    ·
      refine ⟨37666789462475825467156429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50222385949967767289541905 37666789462475825467156429)
      ·
        refine ⟨14125046048428434550183661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37666789462475825467156429 14125046048428434550183661)
        ·
          refine ⟨5296892268160662956318873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14125046048428434550183661 5296892268160662956318873)
          ·
            refine ⟨3972669201120497217239155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5296892268160662956318873 3972669201120497217239155)
            ·
              refine ⟨5959003801680745825858733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3972669201120497217239155 5959003801680745825858733)
              ·
                refine ⟨2234626425630279684697025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5959003801680745825858733 2234626425630279684697025)
                ·
                  refine ⟨1675969819222709763522769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2234626425630279684697025 1675969819222709763522769)
                  ·
                    refine ⟨1256977364417032322642077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1675969819222709763522769 1256977364417032322642077)
                    ·
                      refine ⟨471366511656387120990779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1256977364417032322642077 471366511656387120990779)
                      ·
                        rfl

theorem cell23_917983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_917983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_917983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_917983 prefixEnd_917983 := by exact prefixLift 917983
  have htrace : WordTrace (prefixWord ++ tailWord_917983) baseStart_917983 baseEnd_917983 := by
    simpa [prefixWord, tailWord_917983, baseEnd_917983] using wordTrace_append hprefix tailTrace_917983
  have hstable : (prefixWord ++ tailWord_917983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917983).length < 2 ^ (prefixWord ++ tailWord_917983).sum := by decide
  have hdescent : baseEnd_917983 < baseStart_917983 := by decide
  rcases family_descends (prefixWord ++ tailWord_917983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918026 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 2, 1, 7]
def baseStart_918026 : Nat := 118140960795 + 918026 * 2 ^ 59
def prefixEnd_918026 : Nat := 4983230072969 + 3 ^ 40 * 918026 * 2
def baseEnd_918026 : Nat := 471388591324530452753081

theorem tailTrace_918026 : CollatzResearch.WordTrace tailWord_918026 prefixEnd_918026 471388591324530452753081 := by
  unfold tailWord_918026
  simp only [CollatzResearch.WordTrace]
  refine ⟨8370789743039015800877483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22322105981437375469006621 8370789743039015800877483)
  ·
    refine ⟨12556184614558523701316225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8370789743039015800877483 12556184614558523701316225)
    ·
      refine ⟨9417138460918892775987169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12556184614558523701316225 9417138460918892775987169)
      ·
        refine ⟨7062853845689169581990377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9417138460918892775987169 7062853845689169581990377)
        ·
          refine ⟨5297140384266877186492783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7062853845689169581990377 5297140384266877186492783)
          ·
            refine ⟨7945710576400315779739175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5297140384266877186492783 7945710576400315779739175)
            ·
              refine ⟨11918565864600473669608763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7945710576400315779739175 11918565864600473669608763)
              ·
                refine ⟨17877848796900710504413145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11918565864600473669608763 17877848796900710504413145)
                ·
                  refine ⟨13408386597675532878309859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17877848796900710504413145 13408386597675532878309859)
                  ·
                    refine ⟨20112579896513299317464789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13408386597675532878309859 20112579896513299317464789)
                    ·
                      refine ⟨471388591324530452753081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 20112579896513299317464789 471388591324530452753081)
                      ·
                        rfl

theorem cell23_918026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_918026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918026 prefixEnd_918026 := by exact prefixLift 918026
  have htrace : WordTrace (prefixWord ++ tailWord_918026) baseStart_918026 baseEnd_918026 := by
    simpa [prefixWord, tailWord_918026, baseEnd_918026] using wordTrace_append hprefix tailTrace_918026
  have hstable : (prefixWord ++ tailWord_918026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918026).length < 2 ^ (prefixWord ++ tailWord_918026).sum := by decide
  have hdescent : baseEnd_918026 < baseStart_918026 := by decide
  rcases family_descends (prefixWord ++ tailWord_918026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918030 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3]
def baseStart_918030 : Nat := 118140960795 + 918030 * 2 ^ 59
def prefixEnd_918030 : Nat := 4983230072969 + 3 ^ 40 * 918030 * 2
def baseEnd_918030 : Nat := 471390645247148437103063

theorem tailTrace_918030 : CollatzResearch.WordTrace tailWord_918030 prefixEnd_918030 471390645247148437103063 := by
  unfold tailWord_918030
  simp only [CollatzResearch.WordTrace]
  refine ⟨4185413108017696485831943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22322203242761047924437029 4185413108017696485831943)
  ·
    refine ⟨6278119662026544728747915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4185413108017696485831943 6278119662026544728747915)
    ·
      refine ⟨9417179493039817093121873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6278119662026544728747915 9417179493039817093121873)
      ·
        refine ⟨7062884619779862819841405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9417179493039817093121873 7062884619779862819841405)
        ·
          refine ⟨2648581732417448557440527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7062884619779862819841405 2648581732417448557440527)
          ·
            refine ⟨3972872598626172836160791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2648581732417448557440527 3972872598626172836160791)
            ·
              refine ⟨5959308897939259254241187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3972872598626172836160791 5959308897939259254241187)
              ·
                refine ⟨8938963346908888881361781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5959308897939259254241187 8938963346908888881361781)
                ·
                  refine ⟨838027813772708332627667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8938963346908888881361781 838027813772708332627667)
                  ·
                    refine ⟨1257041720659062498941501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 838027813772708332627667 1257041720659062498941501)
                    ·
                      refine ⟨471390645247148437103063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1257041720659062498941501 471390645247148437103063)
                      ·
                        rfl

theorem cell23_918030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_918030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918030 prefixEnd_918030 := by exact prefixLift 918030
  have htrace : WordTrace (prefixWord ++ tailWord_918030) baseStart_918030 baseEnd_918030 := by
    simpa [prefixWord, tailWord_918030, baseEnd_918030] using wordTrace_append hprefix tailTrace_918030
  have hstable : (prefixWord ++ tailWord_918030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918030).length < 2 ^ (prefixWord ++ tailWord_918030).sum := by decide
  have hdescent : baseEnd_918030 < baseStart_918030 := by decide
  rcases family_descends (prefixWord ++ tailWord_918030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918040 : List Nat := [2, 1, 2, 3, 3, 2, 1, 1, 1, 5, 2]
def baseStart_918040 : Nat := 118140960795 + 918040 * 2 ^ 59
def prefixEnd_918040 : Nat := 4983230072969 + 3 ^ 40 * 918040 * 2
def baseEnd_918040 : Nat := 471395780053693397978017

theorem tailTrace_918040 : CollatzResearch.WordTrace tailWord_918040 prefixEnd_918040 471395780053693397978017 := by
  unfold tailWord_918040
  simp only [CollatzResearch.WordTrace]
  refine ⟨16741834797052671797259787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22322446396070229063013049 16741834797052671797259787)
  ·
    refine ⟨25112752195579007695889681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16741834797052671797259787 25112752195579007695889681)
    ·
      refine ⟨18834564146684255771917261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25112752195579007695889681 18834564146684255771917261)
      ·
        refine ⟨7062961555006595914468973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18834564146684255771917261 7062961555006595914468973)
        ·
          refine ⟨2648610583127473467925865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7062961555006595914468973 2648610583127473467925865)
          ·
            refine ⟨1986457937345605100944399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2648610583127473467925865 1986457937345605100944399)
            ·
              refine ⟨2979686906018407651416599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1986457937345605100944399 2979686906018407651416599)
              ·
                refine ⟨4469530359027611477124899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2979686906018407651416599 4469530359027611477124899)
                ·
                  refine ⟨6704295538541417215687349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4469530359027611477124899 6704295538541417215687349)
                  ·
                    refine ⟨628527706738257863970689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6704295538541417215687349 628527706738257863970689)
                    ·
                      refine ⟨471395780053693397978017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 628527706738257863970689 471395780053693397978017)
                      ·
                        rfl

theorem cell23_918040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_918040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918040 prefixEnd_918040 := by exact prefixLift 918040
  have htrace : WordTrace (prefixWord ++ tailWord_918040) baseStart_918040 baseEnd_918040 := by
    simpa [prefixWord, tailWord_918040, baseEnd_918040] using wordTrace_append hprefix tailTrace_918040
  have hstable : (prefixWord ++ tailWord_918040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918040).length < 2 ^ (prefixWord ++ tailWord_918040).sum := by decide
  have hdescent : baseEnd_918040 < baseStart_918040 := by decide
  rcases family_descends (prefixWord ++ tailWord_918040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918073 : List Nat := [1, 2, 1, 5, 1, 1, 3, 2, 1, 1, 5]
def baseStart_918073 : Nat := 118140960795 + 918073 * 2 ^ 59
def prefixEnd_918073 : Nat := 4983230072969 + 3 ^ 40 * 918073 * 2
def baseEnd_918073 : Nat := 471412724915291768865365

theorem tailTrace_918073 : CollatzResearch.WordTrace tailWord_918073 prefixEnd_918073 471412724915291768865365 := by
  unfold tailWord_918073
  simp only [CollatzResearch.WordTrace]
  refine ⟨33484873202985790230470873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22323248801990526820313915 33484873202985790230470873)
  ·
    refine ⟨25113654902239342672853155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33484873202985790230470873 25113654902239342672853155)
    ·
      refine ⟨37670482353359014009279733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25113654902239342672853155 37670482353359014009279733)
      ·
        refine ⟨3531607720627407563369975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37670482353359014009279733 3531607720627407563369975)
        ·
          refine ⟨5297411580941111345054963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3531607720627407563369975 5297411580941111345054963)
          ·
            refine ⟨7946117371411667017582445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5297411580941111345054963 7946117371411667017582445)
            ·
              refine ⟨2979794014279375131593417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7946117371411667017582445 2979794014279375131593417)
              ·
                refine ⟨2234845510709531348695063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2979794014279375131593417 2234845510709531348695063)
                ·
                  refine ⟨3352268266064297023042595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2234845510709531348695063 3352268266064297023042595)
                  ·
                    refine ⟨5028402399096445534563893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3352268266064297023042595 5028402399096445534563893)
                    ·
                      refine ⟨471412724915291768865365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5028402399096445534563893 471412724915291768865365)
                      ·
                        rfl

theorem cell23_918073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_918073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918073 prefixEnd_918073 := by exact prefixLift 918073
  have htrace : WordTrace (prefixWord ++ tailWord_918073) baseStart_918073 baseEnd_918073 := by
    simpa [prefixWord, tailWord_918073, baseEnd_918073] using wordTrace_append hprefix tailTrace_918073
  have hstable : (prefixWord ++ tailWord_918073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918073).length < 2 ^ (prefixWord ++ tailWord_918073).sum := by decide
  have hdescent : baseEnd_918073 < baseStart_918073 := by decide
  rcases family_descends (prefixWord ++ tailWord_918073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918087 : List Nat := [1, 1, 4, 1, 4, 1, 2, 2, 3, 2, 2]
def baseStart_918087 : Nat := 118140960795 + 918087 * 2 ^ 59
def prefixEnd_918087 : Nat := 4983230072969 + 3 ^ 40 * 918087 * 2
def baseEnd_918087 : Nat := 471419913644454714090301

theorem tailTrace_918087 : CollatzResearch.WordTrace tailWord_918087 prefixEnd_918087 471419913644454714090301 := by
  unfold tailWord_918087
  simp only [CollatzResearch.WordTrace]
  refine ⟨33485383824935070621480515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22323589216623380414320343 33485383824935070621480515)
  ·
    refine ⟨50228075737402605932220773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33485383824935070621480515 50228075737402605932220773)
    ·
      refine ⟨9417764200762988612291395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50228075737402605932220773 9417764200762988612291395)
      ·
        refine ⟨14126646301144482918437093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9417764200762988612291395 14126646301144482918437093)
        ·
          refine ⟨2648746181464590547206955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14126646301144482918437093 2648746181464590547206955)
          ·
            refine ⟨3973119272196885820810433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2648746181464590547206955 3973119272196885820810433)
            ·
              refine ⟨2979839454147664365607825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3973119272196885820810433 2979839454147664365607825)
              ·
                refine ⟨2234879590610748274205869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2979839454147664365607825 2234879590610748274205869)
                ·
                  refine ⟨838079846479030602827201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2234879590610748274205869 838079846479030602827201)
                  ·
                    refine ⟨628559884859272952120401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 838079846479030602827201 628559884859272952120401)
                    ·
                      refine ⟨471419913644454714090301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 628559884859272952120401 471419913644454714090301)
                      ·
                        rfl

theorem cell23_918087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 3, 2, 2].length) (baseStart_918087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918087 prefixEnd_918087 := by exact prefixLift 918087
  have htrace : WordTrace (prefixWord ++ tailWord_918087) baseStart_918087 baseEnd_918087 := by
    simpa [prefixWord, tailWord_918087, baseEnd_918087] using wordTrace_append hprefix tailTrace_918087
  have hstable : (prefixWord ++ tailWord_918087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918087).length < 2 ^ (prefixWord ++ tailWord_918087).sum := by decide
  have hdescent : baseEnd_918087 < baseStart_918087 := by decide
  rcases family_descends (prefixWord ++ tailWord_918087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918090 : List Nat := [3, 1, 2, 1, 1, 4, 1, 4, 1, 2, 3]
def baseStart_918090 : Nat := 118140960795 + 918090 * 2 ^ 59
def prefixEnd_918090 : Nat := 4983230072969 + 3 ^ 40 * 918090 * 2
def baseEnd_918090 : Nat := 471421454086418202352787

theorem tailTrace_918090 : CollatzResearch.WordTrace tailWord_918090 prefixEnd_918090 471421454086418202352787 := by
  unfold tailWord_918090
  simp only [CollatzResearch.WordTrace]
  refine ⟨8371373310981050533459931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22323662162616134755893149 8371373310981050533459931)
  ·
    refine ⟨12557059966471575800189897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8371373310981050533459931 12557059966471575800189897)
    ·
      refine ⟨9417794974853681850142423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12557059966471575800189897 9417794974853681850142423)
      ·
        refine ⟨14126692462280522775213635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9417794974853681850142423 14126692462280522775213635)
        ·
          refine ⟨21190038693420784162820453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14126692462280522775213635 21190038693420784162820453)
          ·
            refine ⟨3973132255016397030528835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21190038693420784162820453 3973132255016397030528835)
            ·
              refine ⟨5959698382524595545793253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3973132255016397030528835 5959698382524595545793253)
              ·
                refine ⟨1117443446723361664836235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5959698382524595545793253 1117443446723361664836235)
                ·
                  refine ⟨1676165170085042497254353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1117443446723361664836235 1676165170085042497254353)
                  ·
                    refine ⟨1257123877563781872940765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1676165170085042497254353 1257123877563781872940765)
                    ·
                      refine ⟨471421454086418202352787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1257123877563781872940765 471421454086418202352787)
                      ·
                        rfl

theorem cell23_918090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_918090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918090 prefixEnd_918090 := by exact prefixLift 918090
  have htrace : WordTrace (prefixWord ++ tailWord_918090) baseStart_918090 baseEnd_918090 := by
    simpa [prefixWord, tailWord_918090, baseEnd_918090] using wordTrace_append hprefix tailTrace_918090
  have hstable : (prefixWord ++ tailWord_918090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918090).length < 2 ^ (prefixWord ++ tailWord_918090).sum := by decide
  have hdescent : baseEnd_918090 < baseStart_918090 := by decide
  rcases family_descends (prefixWord ++ tailWord_918090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918103 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 3, 3, 3]
def baseStart_918103 : Nat := 118140960795 + 918103 * 2 ^ 59
def prefixEnd_918103 : Nat := 4983230072969 + 3 ^ 40 * 918103 * 2
def baseEnd_918103 : Nat := 471428129334926651490227

theorem tailTrace_918103 : CollatzResearch.WordTrace tailWord_918103 prefixEnd_918103 471428129334926651490227 := by
  unfold tailWord_918103
  simp only [CollatzResearch.WordTrace]
  refine ⟨33485967392877105354062963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22323978261918070236041975 33485967392877105354062963)
  ·
    refine ⟨50228951089315658031094445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33485967392877105354062963 50228951089315658031094445)
    ·
      refine ⟨18835856658493371761660417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50228951089315658031094445 18835856658493371761660417)
      ·
        refine ⟨14126892493870028821245313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18835856658493371761660417 14126892493870028821245313)
        ·
          refine ⟨10595169370402521615933985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14126892493870028821245313 10595169370402521615933985)
          ·
            refine ⟨7946377027801891211950489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10595169370402521615933985 7946377027801891211950489)
            ·
              refine ⟨5959782770851418408962867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7946377027801891211950489 5959782770851418408962867)
              ·
                refine ⟨8939674156277127613444301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5959782770851418408962867 8939674156277127613444301)
                ·
                  refine ⟨3352377808603922855041613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8939674156277127613444301 3352377808603922855041613)
                  ·
                    refine ⟨1257141678226471070640605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3352377808603922855041613 1257141678226471070640605)
                    ·
                      refine ⟨471428129334926651490227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1257141678226471070640605 471428129334926651490227)
                      ·
                        rfl

theorem cell23_918103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_918103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918103 prefixEnd_918103 := by exact prefixLift 918103
  have htrace : WordTrace (prefixWord ++ tailWord_918103) baseStart_918103 baseEnd_918103 := by
    simpa [prefixWord, tailWord_918103, baseEnd_918103] using wordTrace_append hprefix tailTrace_918103
  have hstable : (prefixWord ++ tailWord_918103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918103).length < 2 ^ (prefixWord ++ tailWord_918103).sum := by decide
  have hdescent : baseEnd_918103 < baseStart_918103 := by decide
  rcases family_descends (prefixWord ++ tailWord_918103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918104 : List Nat := [2, 1, 2, 2, 1, 2, 5, 3, 1, 2, 2]
def baseStart_918104 : Nat := 118140960795 + 918104 * 2 ^ 59
def prefixEnd_918104 : Nat := 4983230072969 + 3 ^ 40 * 918104 * 2
def baseEnd_918104 : Nat := 471428642815581147577723

theorem tailTrace_918104 : CollatzResearch.WordTrace tailWord_918104 prefixEnd_918104 471428642815581147577723 := by
  unfold tailWord_918104
  simp only [CollatzResearch.WordTrace]
  refine ⟨16743001932936741262424683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22324002577248988349899577 16743001932936741262424683)
  ·
    refine ⟨25114502899405111893637025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16743001932936741262424683 25114502899405111893637025)
    ·
      refine ⟨18835877174553833920227769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25114502899405111893637025 18835877174553833920227769)
      ·
        refine ⟨14126907880915375440170827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18835877174553833920227769 14126907880915375440170827)
        ·
          refine ⟨21190361821373063160256241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14126907880915375440170827 21190361821373063160256241)
          ·
            refine ⟨15892771366029797370192181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21190361821373063160256241 15892771366029797370192181)
            ·
              refine ⟨1489947315565293503455517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15892771366029797370192181 1489947315565293503455517)
              ·
                refine ⟨558730243336985063795819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1489947315565293503455517 558730243336985063795819)
                ·
                  refine ⟨838095365005477595693729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 558730243336985063795819 838095365005477595693729)
                  ·
                    refine ⟨628571523754108196770297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 838095365005477595693729 628571523754108196770297)
                    ·
                      refine ⟨471428642815581147577723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 628571523754108196770297 471428642815581147577723)
                      ·
                        rfl

theorem cell23_918104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 3, 1, 2, 2].length) (baseStart_918104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918104 prefixEnd_918104 := by exact prefixLift 918104
  have htrace : WordTrace (prefixWord ++ tailWord_918104) baseStart_918104 baseEnd_918104 := by
    simpa [prefixWord, tailWord_918104, baseEnd_918104] using wordTrace_append hprefix tailTrace_918104
  have hstable : (prefixWord ++ tailWord_918104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918104).length < 2 ^ (prefixWord ++ tailWord_918104).sum := by decide
  have hdescent : baseEnd_918104 < baseStart_918104 := by decide
  rcases family_descends (prefixWord ++ tailWord_918104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918106 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 3, 9]
def baseStart_918106 : Nat := 118140960795 + 918106 * 2 ^ 59
def prefixEnd_918106 : Nat := 4983230072969 + 3 ^ 40 * 918106 * 2
def baseEnd_918106 : Nat := 157143223258963379917571

theorem tailTrace_918106 : CollatzResearch.WordTrace tailWord_918106 prefixEnd_918106 157143223258963379917571 := by
  unfold tailWord_918106
  simp only [CollatzResearch.WordTrace]
  refine ⟨8371519202966559216605543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22324051207910824577614781 8371519202966559216605543)
  ·
    refine ⟨12557278804449838824908315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8371519202966559216605543 12557278804449838824908315)
    ·
      refine ⟨18835918206674758237362473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12557278804449838824908315 18835918206674758237362473)
      ·
        refine ⟨14126938655006068678021855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18835918206674758237362473 14126938655006068678021855)
        ·
          refine ⟨21190407982509103017032783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14126938655006068678021855 21190407982509103017032783)
          ·
            refine ⟨31785611973763654525549175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21190407982509103017032783 31785611973763654525549175)
            ·
              refine ⟨47678417960645481788323763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31785611973763654525549175 47678417960645481788323763)
              ·
                refine ⟨71517626940968222682485645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47678417960645481788323763 71517626940968222682485645)
                ·
                  refine ⟨26819110102863083505932117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71517626940968222682485645 26819110102863083505932117)
                  ·
                    refine ⟨157143223258963379917571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 26819110102863083505932117 157143223258963379917571)
                    ·
                      rfl

theorem cell23_918106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 3, 9].length) (baseStart_918106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918106 prefixEnd_918106 := by exact prefixLift 918106
  have htrace : WordTrace (prefixWord ++ tailWord_918106) baseStart_918106 baseEnd_918106 := by
    simpa [prefixWord, tailWord_918106, baseEnd_918106] using wordTrace_append hprefix tailTrace_918106
  have hstable : (prefixWord ++ tailWord_918106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918106).length < 2 ^ (prefixWord ++ tailWord_918106).sum := by decide
  have hdescent : baseEnd_918106 < baseStart_918106 := by decide
  rcases family_descends (prefixWord ++ tailWord_918106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918137 : List Nat := [1, 2, 1, 3, 3, 3, 1, 3, 2, 1, 3]
def baseStart_918137 : Nat := 118140960795 + 918137 * 2 ^ 59
def prefixEnd_918137 : Nat := 4983230072969 + 3 ^ 40 * 918137 * 2
def baseEnd_918137 : Nat := 471445587677179518465071

theorem tailTrace_918137 : CollatzResearch.WordTrace tailWord_918137 prefixEnd_918137 471445587677179518465071 := by
  unfold tailWord_918137
  simp only [CollatzResearch.WordTrace]
  refine ⟨33487207474753929160800665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22324804983169286107200443 33487207474753929160800665)
  ·
    refine ⟨25115405606065446870600499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33487207474753929160800665 25115405606065446870600499)
    ·
      refine ⟨37673108409098170305900749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25115405606065446870600499 37673108409098170305900749)
      ·
        refine ⟨14127415653411813864712781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37673108409098170305900749 14127415653411813864712781)
        ·
          refine ⟨5297780870029430199267293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14127415653411813864712781 5297780870029430199267293)
          ·
            refine ⟨1986667826261036324725235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5297780870029430199267293 1986667826261036324725235)
            ·
              refine ⟨2980001739391554487087853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1986667826261036324725235 2980001739391554487087853)
              ·
                refine ⟨1117500652271832932657945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2980001739391554487087853 1117500652271832932657945)
                ·
                  refine ⟨838125489203874699493459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1117500652271832932657945 838125489203874699493459)
                  ·
                    refine ⟨1257188233805812049240189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 838125489203874699493459 1257188233805812049240189)
                    ·
                      refine ⟨471445587677179518465071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1257188233805812049240189 471445587677179518465071)
                      ·
                        rfl

theorem cell23_918137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 2, 1, 3].length) (baseStart_918137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918137 prefixEnd_918137 := by exact prefixLift 918137
  have htrace : WordTrace (prefixWord ++ tailWord_918137) baseStart_918137 baseEnd_918137 := by
    simpa [prefixWord, tailWord_918137, baseEnd_918137] using wordTrace_append hprefix tailTrace_918137
  have hstable : (prefixWord ++ tailWord_918137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918137).length < 2 ^ (prefixWord ++ tailWord_918137).sum := by decide
  have hdescent : baseEnd_918137 < baseStart_918137 := by decide
  rcases family_descends (prefixWord ++ tailWord_918137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918147 : List Nat := [1, 1, 1, 3, 3, 1, 5, 2, 1, 3, 2]
def baseStart_918147 : Nat := 118140960795 + 918147 * 2 ^ 59
def prefixEnd_918147 : Nat := 4983230072969 + 3 ^ 40 * 918147 * 2
def baseEnd_918147 : Nat := 471450722483724479340025

theorem tailTrace_918147 : CollatzResearch.WordTrace tailWord_918147 prefixEnd_918147 471450722483724479340025 := by
  unfold tailWord_918147
  simp only [CollatzResearch.WordTrace]
  refine ⟨33487572204717700868664695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22325048136478467245776463 33487572204717700868664695)
  ·
    refine ⟨50231358307076551302997043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33487572204717700868664695 50231358307076551302997043)
    ·
      refine ⟨75347037460614826954495565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50231358307076551302997043 75347037460614826954495565)
      ·
        refine ⟨28255139047730560107935837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75347037460614826954495565 28255139047730560107935837)
        ·
          refine ⟨10595677142898960040475939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28255139047730560107935837 10595677142898960040475939)
          ·
            refine ⟨15893515714348440060713909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10595677142898960040475939 15893515714348440060713909)
            ·
              refine ⟨1490017098220166255691929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15893515714348440060713909 1490017098220166255691929)
              ·
                refine ⟨1117512823665124691768947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1490017098220166255691929 1117512823665124691768947)
                ·
                  refine ⟨1676269235497687037653421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1117512823665124691768947 1676269235497687037653421)
                  ·
                    refine ⟨628600963311632639120033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1676269235497687037653421 628600963311632639120033)
                    ·
                      refine ⟨471450722483724479340025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 628600963311632639120033 471450722483724479340025)
                      ·
                        rfl

theorem cell23_918147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 3, 2].length) (baseStart_918147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918147 prefixEnd_918147 := by exact prefixLift 918147
  have htrace : WordTrace (prefixWord ++ tailWord_918147) baseStart_918147 baseEnd_918147 := by
    simpa [prefixWord, tailWord_918147, baseEnd_918147] using wordTrace_append hprefix tailTrace_918147
  have hstable : (prefixWord ++ tailWord_918147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918147).length < 2 ^ (prefixWord ++ tailWord_918147).sum := by decide
  have hdescent : baseEnd_918147 < baseStart_918147 := by decide
  rcases family_descends (prefixWord ++ tailWord_918147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918228 : List Nat := [2, 4, 1, 3, 2, 2, 1, 2, 2, 2, 2]
def baseStart_918228 : Nat := 118140960795 + 918228 * 2 ^ 59
def prefixEnd_918228 : Nat := 4983230072969 + 3 ^ 40 * 918228 * 2
def baseEnd_918228 : Nat := 471492314416738662427153

theorem tailTrace_918228 : CollatzResearch.WordTrace tailWord_918228 prefixEnd_918228 471492314416738662427153 := by
  unfold tailWord_918228
  simp only [CollatzResearch.WordTrace]
  refine ⟨16745263258712125851181669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22327017678282834468242225 16745263258712125851181669)
  ·
    refine ⟨3139736861008523597096563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16745263258712125851181669 3139736861008523597096563)
    ·
      refine ⟨4709605291512785395644845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3139736861008523597096563 4709605291512785395644845)
      ·
        refine ⟨1766101984317294523366817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4709605291512785395644845 1766101984317294523366817)
        ·
          refine ⟨1324576488237970892525113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1766101984317294523366817 1324576488237970892525113)
          ·
            refine ⟨993432366178478169393835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1324576488237970892525113 993432366178478169393835)
            ·
              refine ⟨1490148549267717254090753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 993432366178478169393835 1490148549267717254090753)
              ·
                refine ⟨1117611411950787940568065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1490148549267717254090753 1117611411950787940568065)
                ·
                  refine ⟨838208558963090955426049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1117611411950787940568065 838208558963090955426049)
                  ·
                    refine ⟨628656419222318216569537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 838208558963090955426049 628656419222318216569537)
                    ·
                      refine ⟨471492314416738662427153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 628656419222318216569537 471492314416738662427153)
                      ·
                        rfl

theorem cell23_918228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_918228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918228 prefixEnd_918228 := by exact prefixLift 918228
  have htrace : WordTrace (prefixWord ++ tailWord_918228) baseStart_918228 baseEnd_918228 := by
    simpa [prefixWord, tailWord_918228, baseEnd_918228] using wordTrace_append hprefix tailTrace_918228
  have hstable : (prefixWord ++ tailWord_918228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918228).length < 2 ^ (prefixWord ++ tailWord_918228).sum := by decide
  have hdescent : baseEnd_918228 < baseStart_918228 := by decide
  rcases family_descends (prefixWord ++ tailWord_918228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918263 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 4]
def baseStart_918263 : Nat := 118140960795 + 918263 * 2 ^ 59
def prefixEnd_918263 : Nat := 4983230072969 + 3 ^ 40 * 918263 * 2
def baseEnd_918263 : Nat := 471510286239646025489491

theorem tailTrace_918263 : CollatzResearch.WordTrace tailWord_918263 prefixEnd_918263 471510286239646025489491 := by
  unfold tailWord_918263
  simp only [CollatzResearch.WordTrace]
  refine ⟨33491803072297452679887443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22327868714864968453258295 33491803072297452679887443)
  ·
    refine ⟨50237704608446179019831165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33491803072297452679887443 50237704608446179019831165)
    ·
      refine ⟨18839139228167317132436687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50237704608446179019831165 18839139228167317132436687)
      ·
        refine ⟨28258708842250975698655031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18839139228167317132436687 28258708842250975698655031)
        ·
          refine ⟨42388063263376463547982547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28258708842250975698655031 42388063263376463547982547)
          ·
            refine ⟨63582094895064695321973821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42388063263376463547982547 63582094895064695321973821)
            ·
              refine ⟨23843285585649260745740183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63582094895064695321973821 23843285585649260745740183)
              ·
                refine ⟨35764928378473891118610275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23843285585649260745740183 35764928378473891118610275)
                ·
                  refine ⟨53647392567710836677915413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35764928378473891118610275 53647392567710836677915413)
                  ·
                    refine ⟨2514721526611445469277285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 53647392567710836677915413 2514721526611445469277285)
                    ·
                      refine ⟨471510286239646025489491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2514721526611445469277285 471510286239646025489491)
                      ·
                        rfl

theorem cell23_918263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_918263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918263 prefixEnd_918263 := by exact prefixLift 918263
  have htrace : WordTrace (prefixWord ++ tailWord_918263) baseStart_918263 baseEnd_918263 := by
    simpa [prefixWord, tailWord_918263, baseEnd_918263] using wordTrace_append hprefix tailTrace_918263
  have hstable : (prefixWord ++ tailWord_918263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918263).length < 2 ^ (prefixWord ++ tailWord_918263).sum := by decide
  have hdescent : baseEnd_918263 < baseStart_918263 := by decide
  rcases family_descends (prefixWord ++ tailWord_918263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918313 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 2, 1, 7]
def baseStart_918313 : Nat := 118140960795 + 918313 * 2 ^ 59
def prefixEnd_918313 : Nat := 4983230072969 + 3 ^ 40 * 918313 * 2
def baseEnd_918313 : Nat := 471535960272370829864261

theorem tailTrace_918313 : CollatzResearch.WordTrace tailWord_918313 prefixEnd_918313 471535960272370829864261 := by
  unfold tailWord_918313
  simp only [CollatzResearch.WordTrace]
  refine ⟨33493626722116311219207593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22329084481410874146138395 33493626722116311219207593)
  ·
    refine ⟨25120220041587233414405695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33493626722116311219207593 25120220041587233414405695)
    ·
      refine ⟨37680330062380850121608543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25120220041587233414405695 37680330062380850121608543)
      ·
        refine ⟨56520495093571275182412815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37680330062380850121608543 56520495093571275182412815)
        ·
          refine ⟨84780742640356912773619223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56520495093571275182412815 84780742640356912773619223)
          ·
            refine ⟨127171113960535369160428835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84780742640356912773619223 127171113960535369160428835)
            ·
              refine ⟨190756670940803053740643253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127171113960535369160428835 190756670940803053740643253)
              ·
                refine ⟨17883437900700286288185305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190756670940803053740643253 17883437900700286288185305)
                ·
                  refine ⟨13412578425525214716138979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17883437900700286288185305 13412578425525214716138979)
                  ·
                    refine ⟨20118867638287822074208469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13412578425525214716138979 20118867638287822074208469)
                    ·
                      refine ⟨471535960272370829864261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 20118867638287822074208469 471535960272370829864261)
                      ·
                        rfl

theorem cell23_918313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 1, 7].length) (baseStart_918313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918313 prefixEnd_918313 := by exact prefixLift 918313
  have htrace : WordTrace (prefixWord ++ tailWord_918313) baseStart_918313 baseEnd_918313 := by
    simpa [prefixWord, tailWord_918313, baseEnd_918313] using wordTrace_append hprefix tailTrace_918313
  have hstable : (prefixWord ++ tailWord_918313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918313).length < 2 ^ (prefixWord ++ tailWord_918313).sum := by decide
  have hdescent : baseEnd_918313 < baseStart_918313 := by decide
  rcases family_descends (prefixWord ++ tailWord_918313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918360 : List Nat := [2, 1, 2, 2, 1, 1, 1, 6, 1, 1, 5]
def baseStart_918360 : Nat := 118140960795 + 918360 * 2 ^ 59
def prefixEnd_918360 : Nat := 4983230072969 + 3 ^ 40 * 918360 * 2
def baseEnd_918360 : Nat := 471560093863132145976545

theorem tailTrace_918360 : CollatzResearch.WordTrace tailWord_918360 prefixEnd_918360 471560093863132145976545 := by
  unfold tailWord_918360
  simp only [CollatzResearch.WordTrace]
  refine ⟨16747670476473019123084267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22330227301964025497445689 16747670476473019123084267)
  ·
    refine ⟨25121505714709528684626401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16747670476473019123084267 25121505714709528684626401)
    ·
      refine ⟨18841129286032146513469801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25121505714709528684626401 18841129286032146513469801)
      ·
        refine ⟨14130846964524109885102351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18841129286032146513469801 14130846964524109885102351)
        ·
          refine ⟨21196270446786164827653527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14130846964524109885102351 21196270446786164827653527)
          ·
            refine ⟨31794405670179247241480291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21196270446786164827653527 31794405670179247241480291)
            ·
              refine ⟨47691608505268870862220437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31794405670179247241480291 47691608505268870862220437)
              ·
                refine ⟨2235544148684478321666583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47691608505268870862220437 2235544148684478321666583)
                ·
                  refine ⟨3353316223026717482499875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2235544148684478321666583 3353316223026717482499875)
                  ·
                    refine ⟨5029974334540076223749813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3353316223026717482499875 5029974334540076223749813)
                    ·
                      refine ⟨471560093863132145976545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5029974334540076223749813 471560093863132145976545)
                      ·
                        rfl

theorem cell23_918360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_918360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918360 prefixEnd_918360 := by exact prefixLift 918360
  have htrace : WordTrace (prefixWord ++ tailWord_918360) baseStart_918360 baseEnd_918360 := by
    simpa [prefixWord, tailWord_918360, baseEnd_918360] using wordTrace_append hprefix tailTrace_918360
  have hstable : (prefixWord ++ tailWord_918360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918360).length < 2 ^ (prefixWord ++ tailWord_918360).sum := by decide
  have hdescent : baseEnd_918360 < baseStart_918360 := by decide
  rcases family_descends (prefixWord ++ tailWord_918360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918367 : List Nat := [1, 1, 2, 3, 1, 3, 1, 5, 2, 4]
def baseStart_918367 : Nat := 118140960795 + 918367 * 2 ^ 59
def prefixEnd_918367 : Nat := 4983230072969 + 3 ^ 40 * 918367 * 2
def baseEnd_918367 : Nat := 157187896075904539529671

theorem tailTrace_918367 : CollatzResearch.WordTrace tailWord_918367 prefixEnd_918367 157187896075904539529671 := by
  unfold tailWord_918367
  simp only [CollatzResearch.WordTrace]
  refine ⟨33495596263920678441673355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22330397509280452294448903 33495596263920678441673355)
  ·
    refine ⟨50243394395881017662510033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33495596263920678441673355 50243394395881017662510033)
    ·
      refine ⟨37682545796910763246882525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50243394395881017662510033 37682545796910763246882525)
      ·
        refine ⟨14130954673841536217580947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37682545796910763246882525 14130954673841536217580947)
        ·
          refine ⟨21196432010762304326371421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14130954673841536217580947 21196432010762304326371421)
          ·
            refine ⟨7948662004035864122389283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21196432010762304326371421 7948662004035864122389283)
            ·
              refine ⟨11922993006053796183583925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7948662004035864122389283 11922993006053796183583925)
              ·
                refine ⟨1117780594317543392210993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11922993006053796183583925 1117780594317543392210993)
                ·
                  refine ⟨838335445738157544158245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1117780594317543392210993 838335445738157544158245)
                  ·
                    refine ⟨157187896075904539529671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 838335445738157544158245 157187896075904539529671)
                    ·
                      rfl

theorem cell23_918367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 2, 4].length) (baseStart_918367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918367 prefixEnd_918367 := by exact prefixLift 918367
  have htrace : WordTrace (prefixWord ++ tailWord_918367) baseStart_918367 baseEnd_918367 := by
    simpa [prefixWord, tailWord_918367, baseEnd_918367] using wordTrace_append hprefix tailTrace_918367
  have hstable : (prefixWord ++ tailWord_918367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918367).length < 2 ^ (prefixWord ++ tailWord_918367).sum := by decide
  have hdescent : baseEnd_918367 < baseStart_918367 := by decide
  rcases family_descends (prefixWord ++ tailWord_918367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918408 : List Nat := [2, 1, 3, 3, 2, 1, 2, 4, 1, 2, 2]
def baseStart_918408 : Nat := 118140960795 + 918408 * 2 ^ 59
def prefixEnd_918408 : Nat := 4983230072969 + 3 ^ 40 * 918408 * 2
def baseEnd_918408 : Nat := 471584740934547958176325

theorem tailTrace_918408 : CollatzResearch.WordTrace tailWord_918408 prefixEnd_918408 471584740934547958176325 := by
  unfold tailWord_918408
  simp only [CollatzResearch.WordTrace]
  refine ⟨16748545828386071221957939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22331394437848094962610585 16748545828386071221957939)
  ·
    refine ⟨25122818742579106832936909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16748545828386071221957939 25122818742579106832936909)
    ·
      refine ⟨9421057028467165062351341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25122818742579106832936909 9421057028467165062351341)
      ·
        refine ⟨3532896385675186898381753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9421057028467165062351341 3532896385675186898381753)
        ·
          refine ⟨2649672289256390173786315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3532896385675186898381753 2649672289256390173786315)
          ·
            refine ⟨3974508433884585260679473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2649672289256390173786315 3974508433884585260679473)
            ·
              refine ⟨2980881325413438945509605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3974508433884585260679473 2980881325413438945509605)
              ·
                refine ⟨558915248515019802283051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2980881325413438945509605 558915248515019802283051)
                ·
                  refine ⟨838372872772529703424577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 558915248515019802283051 838372872772529703424577)
                  ·
                    refine ⟨628779654579397277568433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 838372872772529703424577 628779654579397277568433)
                    ·
                      refine ⟨471584740934547958176325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 628779654579397277568433 471584740934547958176325)
                      ·
                        rfl

theorem cell23_918408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_918408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918408 prefixEnd_918408 := by exact prefixLift 918408
  have htrace : WordTrace (prefixWord ++ tailWord_918408) baseStart_918408 baseEnd_918408 := by
    simpa [prefixWord, tailWord_918408, baseEnd_918408] using wordTrace_append hprefix tailTrace_918408
  have hstable : (prefixWord ++ tailWord_918408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918408).length < 2 ^ (prefixWord ++ tailWord_918408).sum := by decide
  have hdescent : baseEnd_918408 < baseStart_918408 := by decide
  rcases family_descends (prefixWord ++ tailWord_918408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918418 : List Nat := [3, 2, 3, 2, 2, 1, 3, 1, 2, 4]
def baseStart_918418 : Nat := 118140960795 + 918418 * 2 ^ 59
def prefixEnd_918418 : Nat := 4983230072969 + 3 ^ 40 * 918418 * 2
def baseEnd_918418 : Nat := 157196625247030973017093

theorem tailTrace_918418 : CollatzResearch.WordTrace tailWord_918418 prefixEnd_918418 157196625247030973017093 := by
  unfold tailWord_918418
  simp only [CollatzResearch.WordTrace]
  refine ⟨8374364096683978537944977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22331637591157276101186605 8374364096683978537944977)
  ·
    refine ⟨6280773072512983903458733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8374364096683978537944977 6280773072512983903458733)
    ·
      refine ⟨2355289902192368963797025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6280773072512983903458733 2355289902192368963797025)
      ·
        refine ⟨1766467426644276722847769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2355289902192368963797025 1766467426644276722847769)
        ·
          refine ⟨1324850569983207542135827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1766467426644276722847769 1324850569983207542135827)
          ·
            refine ⟨1987275854974811313203741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1324850569983207542135827 1987275854974811313203741)
            ·
              refine ⟨745228445615554242451403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1987275854974811313203741 745228445615554242451403)
              ·
                refine ⟨1117842668423331363677105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 745228445615554242451403 1117842668423331363677105)
                ·
                  refine ⟨838382001317498522757829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1117842668423331363677105 838382001317498522757829)
                  ·
                    refine ⟨157196625247030973017093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 838382001317498522757829 157196625247030973017093)
                    ·
                      rfl

theorem cell23_918418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_918418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918418 prefixEnd_918418 := by exact prefixLift 918418
  have htrace : WordTrace (prefixWord ++ tailWord_918418) baseStart_918418 baseEnd_918418 := by
    simpa [prefixWord, tailWord_918418, baseEnd_918418] using wordTrace_append hprefix tailTrace_918418
  have hstable : (prefixWord ++ tailWord_918418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918418).length < 2 ^ (prefixWord ++ tailWord_918418).sum := by decide
  have hdescent : baseEnd_918418 < baseStart_918418 := by decide
  rcases family_descends (prefixWord ++ tailWord_918418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918481 : List Nat := [1, 2, 2, 1, 2, 1, 5, 3, 2, 2, 2]
def baseStart_918481 : Nat := 118140960795 + 918481 * 2 ^ 59
def prefixEnd_918481 : Nat := 4983230072969 + 3 ^ 40 * 918481 * 2
def baseEnd_918481 : Nat := 471622225022326172563489

theorem tailTrace_918481 : CollatzResearch.WordTrace tailWord_918481 prefixEnd_918481 471622225022326172563489 := by
  unfold tailWord_918481
  simp only [CollatzResearch.WordTrace]
  refine ⟨33499754185507675911323297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22333169457005117274215531 33499754185507675911323297)
  ·
    refine ⟨25124815639130756933492473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33499754185507675911323297 25124815639130756933492473)
    ·
      refine ⟨18843611729348067700119355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25124815639130756933492473 18843611729348067700119355)
      ·
        refine ⟨28265417594022101550179033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18843611729348067700119355 28265417594022101550179033)
        ·
          refine ⟨21199063195516576162634275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28265417594022101550179033 21199063195516576162634275)
          ·
            refine ⟨31798594793274864243951413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21199063195516576162634275 31798594793274864243951413)
            ·
              refine ⟨2981118261869518522870445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31798594793274864243951413 2981118261869518522870445)
              ·
                refine ⟨1117919348201069446076417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2981118261869518522870445 1117919348201069446076417)
                ·
                  refine ⟨838439511150802084557313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1117919348201069446076417 838439511150802084557313)
                  ·
                    refine ⟨628829633363101563417985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 838439511150802084557313 628829633363101563417985)
                    ·
                      refine ⟨471622225022326172563489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 628829633363101563417985 471622225022326172563489)
                      ·
                        rfl

theorem cell23_918481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 2, 2, 2].length) (baseStart_918481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918481 prefixEnd_918481 := by exact prefixLift 918481
  have htrace : WordTrace (prefixWord ++ tailWord_918481) baseStart_918481 baseEnd_918481 := by
    simpa [prefixWord, tailWord_918481, baseEnd_918481] using wordTrace_append hprefix tailTrace_918481
  have hstable : (prefixWord ++ tailWord_918481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918481).length < 2 ^ (prefixWord ++ tailWord_918481).sum := by decide
  have hdescent : baseEnd_918481 < baseStart_918481 := by decide
  rcases family_descends (prefixWord ++ tailWord_918481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918485 : List Nat := [1, 3, 2, 3, 4, 1, 1, 2, 1, 3, 2]
def baseStart_918485 : Nat := 118140960795 + 918485 * 2 ^ 59
def prefixEnd_918485 : Nat := 4983230072969 + 3 ^ 40 * 918485 * 2
def baseEnd_918485 : Nat := 471624278944944156913471

theorem tailTrace_918485 : CollatzResearch.WordTrace tailWord_918485 prefixEnd_918485 471624278944944156913471 := by
  unfold tailWord_918485
  simp only [CollatzResearch.WordTrace]
  refine ⟨33499900077493184594468909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22333266718328789729645939 33499900077493184594468909)
  ·
    refine ⟨12562462529059944222925841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33499900077493184594468909 12562462529059944222925841)
    ·
      refine ⟨9421846896794958167194381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12562462529059944222925841 9421846896794958167194381)
      ·
        refine ⟨3533192586298109312697893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9421846896794958167194381 3533192586298109312697893)
        ·
          refine ⟨662473609930895496130855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3533192586298109312697893 662473609930895496130855)
          ·
            refine ⟨993710414896343244196283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662473609930895496130855 993710414896343244196283)
            ·
              refine ⟨1490565622344514866294425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 993710414896343244196283 1490565622344514866294425)
              ·
                refine ⟨1117924216758386149720819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1490565622344514866294425 1117924216758386149720819)
                ·
                  refine ⟨1676886325137579224581229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1117924216758386149720819 1676886325137579224581229)
                  ·
                    refine ⟨628832371926592209217961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1676886325137579224581229 628832371926592209217961)
                    ·
                      refine ⟨471624278944944156913471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 628832371926592209217961 471624278944944156913471)
                      ·
                        rfl

theorem cell23_918485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_918485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918485 prefixEnd_918485 := by exact prefixLift 918485
  have htrace : WordTrace (prefixWord ++ tailWord_918485) baseStart_918485 baseEnd_918485 := by
    simpa [prefixWord, tailWord_918485, baseEnd_918485] using wordTrace_append hprefix tailTrace_918485
  have hstable : (prefixWord ++ tailWord_918485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918485).length < 2 ^ (prefixWord ++ tailWord_918485).sum := by decide
  have hdescent : baseEnd_918485 < baseStart_918485 := by decide
  rcases family_descends (prefixWord ++ tailWord_918485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918497 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 4, 3, 3]
def baseStart_918497 : Nat := 118140960795 + 918497 * 2 ^ 59
def prefixEnd_918497 : Nat := 4983230072969 + 3 ^ 40 * 918497 * 2
def baseEnd_918497 : Nat := 471630440712798109963415

theorem tailTrace_918497 : CollatzResearch.WordTrace tailWord_918497 prefixEnd_918497 471630440712798109963415 := by
  unfold tailWord_918497
  simp only [CollatzResearch.WordTrace]
  refine ⟨33500337753449710643905745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22333558502299807095937163 33500337753449710643905745)
  ·
    refine ⟨25125253315087282982929309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33500337753449710643905745 25125253315087282982929309)
    ·
      refine ⟨9421969993157731118598491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25125253315087282982929309 9421969993157731118598491)
      ·
        refine ⟨14132954989736596677897737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9421969993157731118598491 14132954989736596677897737)
        ·
          refine ⟨10599716242302447508423303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14132954989736596677897737 10599716242302447508423303)
          ·
            refine ⟨15899574363453671262634955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10599716242302447508423303 15899574363453671262634955)
            ·
              refine ⟨23849361545180506893952433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15899574363453671262634955 23849361545180506893952433)
              ·
                refine ⟨17887021158885380170464325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23849361545180506893952433 17887021158885380170464325)
                ·
                  refine ⟨3353816467291008781962061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17887021158885380170464325 3353816467291008781962061)
                  ·
                    refine ⟨1257681175234128293235773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3353816467291008781962061 1257681175234128293235773)
                    ·
                      refine ⟨471630440712798109963415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1257681175234128293235773 471630440712798109963415)
                      ·
                        rfl

theorem cell23_918497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_918497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918497 prefixEnd_918497 := by exact prefixLift 918497
  have htrace : WordTrace (prefixWord ++ tailWord_918497) baseStart_918497 baseEnd_918497 := by
    simpa [prefixWord, tailWord_918497, baseEnd_918497] using wordTrace_append hprefix tailTrace_918497
  have hstable : (prefixWord ++ tailWord_918497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918497).length < 2 ^ (prefixWord ++ tailWord_918497).sum := by decide
  have hdescent : baseEnd_918497 < baseStart_918497 := by decide
  rcases family_descends (prefixWord ++ tailWord_918497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918498 : List Nat := [3, 3, 3, 1, 1, 2, 1, 2, 1, 4, 2]
def baseStart_918498 : Nat := 118140960795 + 918498 * 2 ^ 59
def prefixEnd_918498 : Nat := 4983230072969 + 3 ^ 40 * 918498 * 2
def baseEnd_918498 : Nat := 471630954193452606050911

theorem tailTrace_918498 : CollatzResearch.WordTrace tailWord_918498 prefixEnd_918498 471630954193452606050911 := by
  unfold tailWord_918498
  simp only [CollatzResearch.WordTrace]
  refine ⟨8375093556611521953673037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22333582817630725209794765 8375093556611521953673037)
  ·
    refine ⟨3140660083729320732627389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8375093556611521953673037 3140660083729320732627389)
    ·
      refine ⟨1177747531398495274735271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3140660083729320732627389 1177747531398495274735271)
      ·
        refine ⟨1766621297097742912102907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1177747531398495274735271 1766621297097742912102907)
        ·
          refine ⟨2649931945646614368154361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1766621297097742912102907 2649931945646614368154361)
          ·
            refine ⟨1987448959234960776115771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2649931945646614368154361 1987448959234960776115771)
            ·
              refine ⟨2981173438852441164173657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1987448959234960776115771 2981173438852441164173657)
              ·
                refine ⟨2235880079139330873130243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2981173438852441164173657 2235880079139330873130243)
                ·
                  refine ⟨3353820118708996309695365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2235880079139330873130243 3353820118708996309695365)
                  ·
                    refine ⟨628841272257936808067881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3353820118708996309695365 628841272257936808067881)
                    ·
                      refine ⟨471630954193452606050911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 628841272257936808067881 471630954193452606050911)
                      ·
                        rfl

theorem cell23_918498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_918498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918498 prefixEnd_918498 := by exact prefixLift 918498
  have htrace : WordTrace (prefixWord ++ tailWord_918498) baseStart_918498 baseEnd_918498 := by
    simpa [prefixWord, tailWord_918498, baseEnd_918498] using wordTrace_append hprefix tailTrace_918498
  have hstable : (prefixWord ++ tailWord_918498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918498).length < 2 ^ (prefixWord ++ tailWord_918498).sum := by decide
  have hdescent : baseEnd_918498 < baseStart_918498 := by decide
  rcases family_descends (prefixWord ++ tailWord_918498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918524 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 2, 5, 2]
def baseStart_918524 : Nat := 118140960795 + 918524 * 2 ^ 59
def prefixEnd_918524 : Nat := 4983230072969 + 3 ^ 40 * 918524 * 2
def baseEnd_918524 : Nat := 471644304690469504325791

theorem tailTrace_918524 : CollatzResearch.WordTrace tailWord_918524 prefixEnd_918524 471644304690469504325791 := by
  unfold tailWord_918524
  simp only [CollatzResearch.WordTrace]
  refine ⟨16750661262175947127569313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22334215016234596170092417 16750661262175947127569313)
  ·
    refine ⟨12562995946631960345676985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16750661262175947127569313 12562995946631960345676985)
    ·
      refine ⟨9422246959973970259257739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12562995946631960345676985 9422246959973970259257739)
      ·
        refine ⟨14133370439960955388886609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9422246959973970259257739 14133370439960955388886609)
        ·
          refine ⟨10600027829970716541664957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14133370439960955388886609 10600027829970716541664957)
          ·
            refine ⟨3975010436239018703124359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10600027829970716541664957 3975010436239018703124359)
            ·
              refine ⟨5962515654358528054686539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3975010436239018703124359 5962515654358528054686539)
              ·
                refine ⟨8943773481537792082029809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5962515654358528054686539 8943773481537792082029809)
                ·
                  refine ⟨6707830111153344061522357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8943773481537792082029809 6707830111153344061522357)
                  ·
                    refine ⟨628859072920626005767721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6707830111153344061522357 628859072920626005767721)
                    ·
                      refine ⟨471644304690469504325791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 628859072920626005767721 471644304690469504325791)
                      ·
                        rfl

theorem cell23_918524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 2, 5, 2].length) (baseStart_918524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918524 prefixEnd_918524 := by exact prefixLift 918524
  have htrace : WordTrace (prefixWord ++ tailWord_918524) baseStart_918524 baseEnd_918524 := by
    simpa [prefixWord, tailWord_918524, baseEnd_918524] using wordTrace_append hprefix tailTrace_918524
  have hstable : (prefixWord ++ tailWord_918524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918524).length < 2 ^ (prefixWord ++ tailWord_918524).sum := by decide
  have hdescent : baseEnd_918524 < baseStart_918524 := by decide
  rcases family_descends (prefixWord ++ tailWord_918524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918537 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 4, 1, 4]
def baseStart_918537 : Nat := 118140960795 + 918537 * 2 ^ 59
def prefixEnd_918537 : Nat := 4983230072969 + 3 ^ 40 * 918537 * 2
def baseEnd_918537 : Nat := 471650979938977953463231

theorem tailTrace_918537 : CollatzResearch.WordTrace tailWord_918537 prefixEnd_918537 471650979938977953463231 := by
  unfold tailWord_918537
  simp only [CollatzResearch.WordTrace]
  refine ⟨33501796673304797475361865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22334531115536531650241243 33501796673304797475361865)
  ·
    refine ⟨25126347504978598106521399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33501796673304797475361865 25126347504978598106521399)
    ·
      refine ⟨37689521257467897159782099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25126347504978598106521399 37689521257467897159782099)
      ·
        refine ⟨56534281886201845739673149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37689521257467897159782099 56534281886201845739673149)
        ·
          refine ⟨21200355707325692152377431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56534281886201845739673149 21200355707325692152377431)
          ·
            refine ⟨31800533560988538228566147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21200355707325692152377431 31800533560988538228566147)
            ·
              refine ⟨47700800341482807342849221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31800533560988538228566147 47700800341482807342849221)
              ·
                refine ⟨8943900064028026376784229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47700800341482807342849221 8943900064028026376784229)
                ·
                  refine ⟨1676981262005254945647043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8943900064028026376784229 1676981262005254945647043)
                  ·
                    refine ⟨2515471893007882418470565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1676981262005254945647043 2515471893007882418470565)
                    ·
                      refine ⟨471650979938977953463231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2515471893007882418470565 471650979938977953463231)
                      ·
                        rfl

theorem cell23_918537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 1, 4].length) (baseStart_918537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918537 prefixEnd_918537 := by exact prefixLift 918537
  have htrace : WordTrace (prefixWord ++ tailWord_918537) baseStart_918537 baseEnd_918537 := by
    simpa [prefixWord, tailWord_918537, baseEnd_918537] using wordTrace_append hprefix tailTrace_918537
  have hstable : (prefixWord ++ tailWord_918537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918537).length < 2 ^ (prefixWord ++ tailWord_918537).sum := by decide
  have hdescent : baseEnd_918537 < baseStart_918537 := by decide
  rcases family_descends (prefixWord ++ tailWord_918537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918551 : List Nat := [1, 1, 3, 5, 1, 3, 1, 1, 2, 5]
def baseStart_918551 : Nat := 118140960795 + 918551 * 2 ^ 59
def prefixEnd_918551 : Nat := 4983230072969 + 3 ^ 40 * 918551 * 2
def baseEnd_918551 : Nat := 157219389556046966229389

theorem tailTrace_918551 : CollatzResearch.WordTrace tailWord_918551 prefixEnd_918551 157219389556046966229389 := by
  unfold tailWord_918551
  simp only [CollatzResearch.WordTrace]
  refine ⟨33502307295254077866371507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22334871530169385244247671 33502307295254077866371507)
  ·
    refine ⟨50253460942881116799557261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33502307295254077866371507 50253460942881116799557261)
    ·
      refine ⟨18845047853580418799833973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50253460942881116799557261 18845047853580418799833973)
      ·
        refine ⟨1766723236273164262484435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18845047853580418799833973 1766723236273164262484435)
        ·
          refine ⟨2650084854409746393726653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1766723236273164262484435 2650084854409746393726653)
          ·
            refine ⟨993781820403654897647495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2650084854409746393726653 993781820403654897647495)
            ·
              refine ⟨1490672730605482346471243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 993781820403654897647495 1490672730605482346471243)
              ·
                refine ⟨2236009095908223519706865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1490672730605482346471243 2236009095908223519706865)
                ·
                  refine ⟨1677006821931167639780149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2236009095908223519706865 1677006821931167639780149)
                  ·
                    refine ⟨157219389556046966229389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1677006821931167639780149 157219389556046966229389)
                    ·
                      rfl

theorem cell23_918551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 5].length) (baseStart_918551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918551 prefixEnd_918551 := by exact prefixLift 918551
  have htrace : WordTrace (prefixWord ++ tailWord_918551) baseStart_918551 baseEnd_918551 := by
    simpa [prefixWord, tailWord_918551, baseEnd_918551] using wordTrace_append hprefix tailTrace_918551
  have hstable : (prefixWord ++ tailWord_918551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918551).length < 2 ^ (prefixWord ++ tailWord_918551).sum := by decide
  have hdescent : baseEnd_918551 < baseStart_918551 := by decide
  rcases family_descends (prefixWord ++ tailWord_918551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918554 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 1, 6, 2]
def baseStart_918554 : Nat := 118140960795 + 918554 * 2 ^ 59
def prefixEnd_918554 : Nat := 4983230072969 + 3 ^ 40 * 918554 * 2
def baseEnd_918554 : Nat := 471659709110104386950653

theorem tailTrace_918554 : CollatzResearch.WordTrace tailWord_918554 prefixEnd_918554 471659709110104386950653 := by
  unfold tailWord_918554
  simp only [CollatzResearch.WordTrace]
  refine ⟨8375604178560802344682679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22334944476162139585820477 8375604178560802344682679)
  ·
    refine ⟨12563406267841203517024019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8375604178560802344682679 12563406267841203517024019)
    ·
      refine ⟨18845109401761805275536029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12563406267841203517024019 18845109401761805275536029)
      ·
        refine ⟨7066916025660676978326011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18845109401761805275536029 7066916025660676978326011)
        ·
          refine ⟨10600374038491015467489017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7066916025660676978326011 10600374038491015467489017)
          ·
            refine ⟨7950280528868261600616763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10600374038491015467489017 7950280528868261600616763)
            ·
              refine ⟨11925420793302392400925145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7950280528868261600616763 11925420793302392400925145)
              ·
                refine ⟨8944065594976794300693859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11925420793302392400925145 8944065594976794300693859)
                ·
                  refine ⟨13416098392465191451040789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8944065594976794300693859 13416098392465191451040789)
                  ·
                    refine ⟨628879612146805849267537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13416098392465191451040789 628879612146805849267537)
                    ·
                      refine ⟨471659709110104386950653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 628879612146805849267537 471659709110104386950653)
                      ·
                        rfl

theorem cell23_918554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_918554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918554 prefixEnd_918554 := by exact prefixLift 918554
  have htrace : WordTrace (prefixWord ++ tailWord_918554) baseStart_918554 baseEnd_918554 := by
    simpa [prefixWord, tailWord_918554, baseEnd_918554] using wordTrace_append hprefix tailTrace_918554
  have hstable : (prefixWord ++ tailWord_918554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918554).length < 2 ^ (prefixWord ++ tailWord_918554).sum := by decide
  have hdescent : baseEnd_918554 < baseStart_918554 := by decide
  rcases family_descends (prefixWord ++ tailWord_918554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918577 : List Nat := [1, 2, 2, 3, 1, 2, 3, 1, 8]
def baseStart_918577 : Nat := 118140960795 + 918577 * 2 ^ 59
def prefixEnd_918577 : Nat := 4983230072969 + 3 ^ 40 * 918577 * 2
def baseEnd_918577 : Nat := 52407946573906421884783

theorem tailTrace_918577 : CollatzResearch.WordTrace tailWord_918577 prefixEnd_918577 52407946573906421884783 := by
  unfold tailWord_918577
  simp only [CollatzResearch.WordTrace]
  refine ⟨33503255593159884306817985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22335503728773256204545323 33503255593159884306817985)
  ·
    refine ⟨25127441694869913230113489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33503255593159884306817985 25127441694869913230113489)
    ·
      refine ⟨18845581271152434922585117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25127441694869913230113489 18845581271152434922585117)
      ·
        refine ⟨7067092976682163095969419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18845581271152434922585117 7067092976682163095969419)
        ·
          refine ⟨10600639465023244643954129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7067092976682163095969419 10600639465023244643954129)
          ·
            refine ⟨7950479598767433482965597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10600639465023244643954129 7950479598767433482965597)
            ·
              refine ⟨2981429849537787556112099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7950479598767433482965597 2981429849537787556112099)
              ·
                refine ⟨4472144774306681334168149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2981429849537787556112099 4472144774306681334168149)
                ·
                  refine ⟨52407946573906421884783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4472144774306681334168149 52407946573906421884783)
                  ·
                    rfl

theorem cell23_918577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 8].length) (baseStart_918577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918577 prefixEnd_918577 := by exact prefixLift 918577
  have htrace : WordTrace (prefixWord ++ tailWord_918577) baseStart_918577 baseEnd_918577 := by
    simpa [prefixWord, tailWord_918577, baseEnd_918577] using wordTrace_append hprefix tailTrace_918577
  have hstable : (prefixWord ++ tailWord_918577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918577).length < 2 ^ (prefixWord ++ tailWord_918577).sum := by decide
  have hdescent : baseEnd_918577 < baseStart_918577 := by decide
  rcases family_descends (prefixWord ++ tailWord_918577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918587 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 4, 5, 3]
def baseStart_918587 : Nat := 118140960795 + 918587 * 2 ^ 59
def prefixEnd_918587 : Nat := 4983230072969 + 3 ^ 40 * 918587 * 2
def baseEnd_918587 : Nat := 471676653971702757838001

theorem tailTrace_918587 : CollatzResearch.WordTrace tailWord_918587 prefixEnd_918587 471676653971702757838001 := by
  unfold tailWord_918587
  simp only [CollatzResearch.WordTrace]
  refine ⟨33503620323123656014682015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22335746882082437343121343 33503620323123656014682015)
  ·
    refine ⟨50255430484685484022023023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33503620323123656014682015 50255430484685484022023023)
    ·
      refine ⟨75383145727028226033034535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50255430484685484022023023 75383145727028226033034535)
      ·
        refine ⟨113074718590542339049551803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75383145727028226033034535 113074718590542339049551803)
        ·
          refine ⟨169612077885813508574327705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113074718590542339049551803 169612077885813508574327705)
          ·
            refine ⟨127209058414360131430745779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169612077885813508574327705 127209058414360131430745779)
            ·
              refine ⟨190813587621540197146118669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127209058414360131430745779 190813587621540197146118669)
              ·
                refine ⟨71555095358077573929794501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190813587621540197146118669 71555095358077573929794501)
                ·
                  refine ⟨13416580379639545111836469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71555095358077573929794501 13416580379639545111836469)
                  ·
                    refine ⟨1257804410591207354234669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13416580379639545111836469 1257804410591207354234669)
                    ·
                      refine ⟨471676653971702757838001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1257804410591207354234669 471676653971702757838001)
                      ·
                        rfl

theorem cell23_918587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 5, 3].length) (baseStart_918587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918587 prefixEnd_918587 := by exact prefixLift 918587
  have htrace : WordTrace (prefixWord ++ tailWord_918587) baseStart_918587 baseEnd_918587 := by
    simpa [prefixWord, tailWord_918587, baseEnd_918587] using wordTrace_append hprefix tailTrace_918587
  have hstable : (prefixWord ++ tailWord_918587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918587).length < 2 ^ (prefixWord ++ tailWord_918587).sum := by decide
  have hdescent : baseEnd_918587 < baseStart_918587 := by decide
  rcases family_descends (prefixWord ++ tailWord_918587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918598 : List Nat := [6, 1, 1, 1, 1, 2, 2, 2, 3, 4]
def baseStart_918598 : Nat := 118140960795 + 918598 * 2 ^ 59
def prefixEnd_918598 : Nat := 4983230072969 + 3 ^ 40 * 918598 * 2
def baseEnd_918598 : Nat := 157227434086300738266817

theorem tailTrace_918598 : CollatzResearch.WordTrace tailWord_918598 prefixEnd_918598 157227434086300738266817 := by
  unfold tailWord_918598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1047000672690118902916639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22336014350722536595554965 1047000672690118902916639)
  ·
    refine ⟨1570501009035178354374959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1047000672690118902916639 1570501009035178354374959)
    ·
      refine ⟨2355751513552767531562439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1570501009035178354374959 2355751513552767531562439)
      ·
        refine ⟨3533627270329151297343659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2355751513552767531562439 3533627270329151297343659)
        ·
          refine ⟨5300440905493726946015489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3533627270329151297343659 5300440905493726946015489)
          ·
            refine ⟨3975330679120295209511617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5300440905493726946015489 3975330679120295209511617)
            ·
              refine ⟨2981498009340221407133713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3975330679120295209511617 2981498009340221407133713)
              ·
                refine ⟨2236123507005166055350285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2981498009340221407133713 2236123507005166055350285)
                ·
                  refine ⟨838546315126937270756357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2236123507005166055350285 838546315126937270756357)
                  ·
                    refine ⟨157227434086300738266817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 838546315126937270756357 157227434086300738266817)
                    ·
                      rfl

theorem cell23_918598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_918598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918598 prefixEnd_918598 := by exact prefixLift 918598
  have htrace : WordTrace (prefixWord ++ tailWord_918598) baseStart_918598 baseEnd_918598 := by
    simpa [prefixWord, tailWord_918598, baseEnd_918598] using wordTrace_append hprefix tailTrace_918598
  have hstable : (prefixWord ++ tailWord_918598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918598).length < 2 ^ (prefixWord ++ tailWord_918598).sum := by decide
  have hdescent : baseEnd_918598 < baseStart_918598 := by decide
  rcases family_descends (prefixWord ++ tailWord_918598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918624 : List Nat := [2, 1, 1, 3, 2, 2, 1, 5, 1, 5]
def baseStart_918624 : Nat := 118140960795 + 918624 * 2 ^ 59
def prefixEnd_918624 : Nat := 4983230072969 + 3 ^ 40 * 918624 * 2
def baseEnd_918624 : Nat := 157231884251973037691777

theorem tailTrace_918624 : CollatzResearch.WordTrace tailWord_918624 prefixEnd_918624 157231884251973037691777 := by
  unfold tailWord_918624
  simp only [CollatzResearch.WordTrace]
  refine ⟨16752484911994805666889463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22336646549326407555852617 16752484911994805666889463)
  ·
    refine ⟨25128727367992208500334195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16752484911994805666889463 25128727367992208500334195)
    ·
      refine ⟨37693091051988312750501293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25128727367992208500334195 37693091051988312750501293)
      ·
        refine ⟨14134909144495617281437985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37693091051988312750501293 14134909144495617281437985)
        ·
          refine ⟨10601181858371712961078489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14134909144495617281437985 10601181858371712961078489)
          ·
            refine ⟨7950886393778784720808867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10601181858371712961078489 7950886393778784720808867)
            ·
              refine ⟨11926329590668177081213301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7950886393778784720808867 11926329590668177081213301)
              ·
                refine ⟨1118093399125141601363747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11926329590668177081213301 1118093399125141601363747)
                ·
                  refine ⟨1677140098687712402045621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1118093399125141601363747 1677140098687712402045621)
                  ·
                    refine ⟨157231884251973037691777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1677140098687712402045621 157231884251973037691777)
                    ·
                      rfl

theorem cell23_918624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 1, 5].length) (baseStart_918624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918624 prefixEnd_918624 := by exact prefixLift 918624
  have htrace : WordTrace (prefixWord ++ tailWord_918624) baseStart_918624 baseEnd_918624 := by
    simpa [prefixWord, tailWord_918624, baseEnd_918624] using wordTrace_append hprefix tailTrace_918624
  have hstable : (prefixWord ++ tailWord_918624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918624).length < 2 ^ (prefixWord ++ tailWord_918624).sum := by decide
  have hdescent : baseEnd_918624 < baseStart_918624 := by decide
  rcases family_descends (prefixWord ++ tailWord_918624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918631 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 4, 3, 2]
def baseStart_918631 : Nat := 118140960795 + 918631 * 2 ^ 59
def prefixEnd_918631 : Nat := 4983230072969 + 3 ^ 40 * 918631 * 2
def baseEnd_918631 : Nat := 471699247120500585687799

theorem tailTrace_918631 : CollatzResearch.WordTrace tailWord_918631 prefixEnd_918631 471699247120500585687799 := by
  unfold tailWord_918631
  simp only [CollatzResearch.WordTrace]
  refine ⟨33505225134964251529283747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22336816756642834352855831 33505225134964251529283747)
  ·
    refine ⟨50257837702446377293925621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33505225134964251529283747 50257837702446377293925621)
    ·
      refine ⟨4711672284604347871305527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50257837702446377293925621 4711672284604347871305527)
      ·
        refine ⟨7067508426906521806958291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4711672284604347871305527 7067508426906521806958291)
        ·
          refine ⟨10601262640359782710437437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7067508426906521806958291 10601262640359782710437437)
          ·
            refine ⟨3975473490134918516414039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10601262640359782710437437 3975473490134918516414039)
            ·
              refine ⟨5963210235202377774621059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3975473490134918516414039 5963210235202377774621059)
              ·
                refine ⟨8944815352803566661931589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5963210235202377774621059 8944815352803566661931589)
                ·
                  refine ⟨1677152878650668749112173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8944815352803566661931589 1677152878650668749112173)
                  ·
                    refine ⟨628932329494000780917065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1677152878650668749112173 628932329494000780917065)
                    ·
                      refine ⟨471699247120500585687799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 628932329494000780917065 471699247120500585687799)
                      ·
                        rfl

theorem cell23_918631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_918631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918631 prefixEnd_918631 := by exact prefixLift 918631
  have htrace : WordTrace (prefixWord ++ tailWord_918631) baseStart_918631 baseEnd_918631 := by
    simpa [prefixWord, tailWord_918631, baseEnd_918631] using wordTrace_append hprefix tailTrace_918631
  have hstable : (prefixWord ++ tailWord_918631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918631).length < 2 ^ (prefixWord ++ tailWord_918631).sum := by decide
  have hdescent : baseEnd_918631 < baseStart_918631 := by decide
  rcases family_descends (prefixWord ++ tailWord_918631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918632 : List Nat := [2, 1, 4, 4, 1, 1, 3, 2, 1, 4]
def baseStart_918632 : Nat := 118140960795 + 918632 * 2 ^ 59
def prefixEnd_918632 : Nat := 4983230072969 + 3 ^ 40 * 918632 * 2
def baseEnd_918632 : Nat := 157233253533718360591765

theorem tailTrace_918632 : CollatzResearch.WordTrace tailWord_918632 prefixEnd_918632 157233253533718360591765 := by
  unfold tailWord_918632
  simp only [CollatzResearch.WordTrace]
  refine ⟨16752630803980314350035075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22336841071973752466713433 16752630803980314350035075)
  ·
    refine ⟨25128946205970471525052613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16752630803980314350035075 25128946205970471525052613)
    ·
      refine ⟨4711677413619463410947365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25128946205970471525052613 4711677413619463410947365)
      ·
        refine ⟨883439515053649389552631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4711677413619463410947365 883439515053649389552631)
        ·
          refine ⟨1325159272580474084328947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 883439515053649389552631 1325159272580474084328947)
          ·
            refine ⟨1987738908870711126493421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1325159272580474084328947 1987738908870711126493421)
            ·
              refine ⟨745402090826516672435033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1987738908870711126493421 745402090826516672435033)
              ·
                refine ⟨559051568119887504326275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 745402090826516672435033 559051568119887504326275)
                ·
                  refine ⟨838577352179831256489413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 559051568119887504326275 838577352179831256489413)
                  ·
                    refine ⟨157233253533718360591765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 838577352179831256489413 157233253533718360591765)
                    ·
                      rfl

theorem cell23_918632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_918632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918632 prefixEnd_918632 := by exact prefixLift 918632
  have htrace : WordTrace (prefixWord ++ tailWord_918632) baseStart_918632 baseEnd_918632 := by
    simpa [prefixWord, tailWord_918632, baseEnd_918632] using wordTrace_append hprefix tailTrace_918632
  have hstable : (prefixWord ++ tailWord_918632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918632).length < 2 ^ (prefixWord ++ tailWord_918632).sum := by decide
  have hdescent : baseEnd_918632 < baseStart_918632 := by decide
  rcases family_descends (prefixWord ++ tailWord_918632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918638 : List Nat := [4, 1, 2, 2, 1, 2, 3, 1, 3, 1, 3]
def baseStart_918638 : Nat := 118140960795 + 918638 * 2 ^ 59
def prefixEnd_918638 : Nat := 4983230072969 + 3 ^ 40 * 918638 * 2
def baseEnd_918638 : Nat := 471702841485082058300267

theorem tailTrace_918638 : CollatzResearch.WordTrace tailWord_918638 prefixEnd_918638 471702841485082058300267 := by
  unfold tailWord_918638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4188185055742361465598571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22336986963959261149859045 4188185055742361465598571)
  ·
    refine ⟨6282277583613542198397857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4188185055742361465598571 6282277583613542198397857)
    ·
      refine ⟨4711708187710156648798393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6282277583613542198397857 4711708187710156648798393)
      ·
        refine ⟨3533781140782617486598795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4711708187710156648798393 3533781140782617486598795)
        ·
          refine ⟨5300671711173926229898193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3533781140782617486598795 5300671711173926229898193)
          ·
            refine ⟨3975503783380444672423645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5300671711173926229898193 3975503783380444672423645)
            ·
              refine ⟨1490813918767666752158867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3975503783380444672423645 1490813918767666752158867)
              ·
                refine ⟨2236220878151500128238301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1490813918767666752158867 2236220878151500128238301)
                ·
                  refine ⟨838582829306812548089363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2236220878151500128238301 838582829306812548089363)
                  ·
                    refine ⟨1257874243960218822134045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 838582829306812548089363 1257874243960218822134045)
                    ·
                      refine ⟨471702841485082058300267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1257874243960218822134045 471702841485082058300267)
                      ·
                        rfl

theorem cell23_918638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_918638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918638 prefixEnd_918638 := by exact prefixLift 918638
  have htrace : WordTrace (prefixWord ++ tailWord_918638) baseStart_918638 baseEnd_918638 := by
    simpa [prefixWord, tailWord_918638, baseEnd_918638] using wordTrace_append hprefix tailTrace_918638
  have hstable : (prefixWord ++ tailWord_918638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918638).length < 2 ^ (prefixWord ++ tailWord_918638).sum := by decide
  have hdescent : baseEnd_918638 < baseStart_918638 := by decide
  rcases family_descends (prefixWord ++ tailWord_918638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918645 : List Nat := [1, 3, 4, 3, 1, 2, 2, 1, 6]
def baseStart_918645 : Nat := 118140960795 + 918645 * 2 ^ 59
def prefixEnd_918645 : Nat := 4983230072969 + 3 ^ 40 * 918645 * 2
def baseEnd_918645 : Nat := 52411826205518170101415

theorem tailTrace_918645 : CollatzResearch.WordTrace tailWord_918645 prefixEnd_918645 52411826205518170101415 := by
  unfold tailWord_918645
  simp only [CollatzResearch.WordTrace]
  refine ⟨33505735756913531920293389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22337157171275687946862259 33505735756913531920293389)
  ·
    refine ⟨12564650908842574470110021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33505735756913531920293389 12564650908842574470110021)
    ·
      refine ⟨2355872045407982713145629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12564650908842574470110021 2355872045407982713145629)
      ·
        refine ⟨883452017027993517429611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2355872045407982713145629 883452017027993517429611)
        ·
          refine ⟨1325178025541990276144417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 883452017027993517429611 1325178025541990276144417)
          ·
            refine ⟨993883519156492707108313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1325178025541990276144417 993883519156492707108313)
            ·
              refine ⟨745412639367369530331235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 993883519156492707108313 745412639367369530331235)
              ·
                refine ⟨1118118959051054295496853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 745412639367369530331235 1118118959051054295496853)
                ·
                  refine ⟨52411826205518170101415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1118118959051054295496853 52411826205518170101415)
                  ·
                    rfl

theorem cell23_918645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 6].length) (baseStart_918645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918645 prefixEnd_918645 := by exact prefixLift 918645
  have htrace : WordTrace (prefixWord ++ tailWord_918645) baseStart_918645 baseEnd_918645 := by
    simpa [prefixWord, tailWord_918645, baseEnd_918645] using wordTrace_append hprefix tailTrace_918645
  have hstable : (prefixWord ++ tailWord_918645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918645).length < 2 ^ (prefixWord ++ tailWord_918645).sum := by decide
  have hdescent : baseEnd_918645 < baseStart_918645 := by decide
  rcases family_descends (prefixWord ++ tailWord_918645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918661 : List Nat := [1, 3, 1, 1, 6, 1, 1, 1, 3, 1, 4]
def baseStart_918661 : Nat := 118140960795 + 918661 * 2 ^ 59
def prefixEnd_918661 : Nat := 4983230072969 + 3 ^ 40 * 918661 * 2
def baseEnd_918661 : Nat := 471714651540135468312661

theorem tailTrace_918661 : CollatzResearch.WordTrace tailWord_918661 prefixEnd_918661 471714651540135468312661 := by
  unfold tailWord_918661
  simp only [CollatzResearch.WordTrace]
  refine ⟨33506319324855566652875837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22337546216570377768583891 33506319324855566652875837)
  ·
    refine ⟨12564869746820837494828439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33506319324855566652875837 12564869746820837494828439)
    ·
      refine ⟨18847304620231256242242659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12564869746820837494828439 18847304620231256242242659)
      ·
        refine ⟨28270956930346884363363989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18847304620231256242242659 28270956930346884363363989)
        ·
          refine ⟨1325201106110010204532687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28270956930346884363363989 1325201106110010204532687)
          ·
            refine ⟨1987801659165015306799031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1325201106110010204532687 1987801659165015306799031)
            ·
              refine ⟨2981702488747522960198547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1987801659165015306799031 2981702488747522960198547)
              ·
                refine ⟨4472553733121284440297821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2981702488747522960198547 4472553733121284440297821)
                ·
                  refine ⟨1677207649920481665111683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4472553733121284440297821 1677207649920481665111683)
                  ·
                    refine ⟨2515811474880722497667525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1677207649920481665111683 2515811474880722497667525)
                    ·
                      refine ⟨471714651540135468312661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2515811474880722497667525 471714651540135468312661)
                      ·
                        rfl

theorem cell23_918661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 1, 4].length) (baseStart_918661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918661 prefixEnd_918661 := by exact prefixLift 918661
  have htrace : WordTrace (prefixWord ++ tailWord_918661) baseStart_918661 baseEnd_918661 := by
    simpa [prefixWord, tailWord_918661, baseEnd_918661] using wordTrace_append hprefix tailTrace_918661
  have hstable : (prefixWord ++ tailWord_918661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918661).length < 2 ^ (prefixWord ++ tailWord_918661).sum := by decide
  have hdescent : baseEnd_918661 < baseStart_918661 := by decide
  rcases family_descends (prefixWord ++ tailWord_918661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918698 : List Nat := [3, 1, 5, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_918698 : Nat := 118140960795 + 918698 * 2 ^ 59
def prefixEnd_918698 : Nat := 4983230072969 + 3 ^ 40 * 918698 * 2
def baseEnd_918698 : Nat := 471733650324351823549991

theorem tailTrace_918698 : CollatzResearch.WordTrace tailWord_918698 prefixEnd_918698 471733650324351823549991 := by
  unfold tailWord_918698
  simp only [CollatzResearch.WordTrace]
  refine ⟨8376917206430380492993187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22338445883814347981315165 8376917206430380492993187)
  ·
    refine ⟨12565375809645570739489781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8376917206430380492993187 12565375809645570739489781)
    ·
      refine ⟨1178003982154272256827167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12565375809645570739489781 1178003982154272256827167)
      ·
        refine ⟨1767005973231408385240751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1178003982154272256827167 1767005973231408385240751)
        ·
          refine ⟨2650508959847112577861127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1767005973231408385240751 2650508959847112577861127)
          ·
            refine ⟨3975763439770668866791691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2650508959847112577861127 3975763439770668866791691)
            ·
              refine ⟨5963645159656003300187537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3975763439770668866791691 5963645159656003300187537)
              ·
                refine ⟨4472733869742002475140653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5963645159656003300187537 4472733869742002475140653)
                ·
                  refine ⟨1677275201153250928177745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4472733869742002475140653 1677275201153250928177745)
                  ·
                    refine ⟨1257956400864938196133309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1677275201153250928177745 1257956400864938196133309)
                    ·
                      refine ⟨471733650324351823549991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1257956400864938196133309 471733650324351823549991)
                      ·
                        rfl

theorem cell23_918698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_918698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918698 prefixEnd_918698 := by exact prefixLift 918698
  have htrace : WordTrace (prefixWord ++ tailWord_918698) baseStart_918698 baseEnd_918698 := by
    simpa [prefixWord, tailWord_918698, baseEnd_918698] using wordTrace_append hprefix tailTrace_918698
  have hstable : (prefixWord ++ tailWord_918698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918698).length < 2 ^ (prefixWord ++ tailWord_918698).sum := by decide
  have hdescent : baseEnd_918698 < baseStart_918698 := by decide
  rcases family_descends (prefixWord ++ tailWord_918698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918711 : List Nat := [1, 1, 3, 1, 4, 1, 4, 1, 1, 3, 3]
def baseStart_918711 : Nat := 118140960795 + 918711 * 2 ^ 59
def prefixEnd_918711 : Nat := 4983230072969 + 3 ^ 40 * 918711 * 2
def baseEnd_918711 : Nat := 471740325572860272687431

theorem tailTrace_918711 : CollatzResearch.WordTrace tailWord_918711 prefixEnd_918711 471740325572860272687431 := by
  unfold tailWord_918711
  simp only [CollatzResearch.WordTrace]
  refine ⟨33508142974674425192195987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22338761983116283461463991 33508142974674425192195987)
  ·
    refine ⟨50262214462011637788293981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33508142974674425192195987 50262214462011637788293981)
    ·
      refine ⟨18848330423254364170610243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50262214462011637788293981 18848330423254364170610243)
      ·
        refine ⟨28272495634881546255915365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18848330423254364170610243 28272495634881546255915365)
        ·
          refine ⟨5301092931540289922984131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28272495634881546255915365 5301092931540289922984131)
          ·
            refine ⟨7951639397310434884476197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5301092931540289922984131 7951639397310434884476197)
            ·
              refine ⟨1490932386995706540839287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7951639397310434884476197 1490932386995706540839287)
              ·
                refine ⟨2236398580493559811258931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1490932386995706540839287 2236398580493559811258931)
                ·
                  refine ⟨3354597870740339716888397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2236398580493559811258931 3354597870740339716888397)
                  ·
                    refine ⟨1257974201527627393833149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3354597870740339716888397 1257974201527627393833149)
                    ·
                      refine ⟨471740325572860272687431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1257974201527627393833149 471740325572860272687431)
                      ·
                        rfl

theorem cell23_918711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 3, 3].length) (baseStart_918711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918711 prefixEnd_918711 := by exact prefixLift 918711
  have htrace : WordTrace (prefixWord ++ tailWord_918711) baseStart_918711 baseEnd_918711 := by
    simpa [prefixWord, tailWord_918711, baseEnd_918711] using wordTrace_append hprefix tailTrace_918711
  have hstable : (prefixWord ++ tailWord_918711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918711).length < 2 ^ (prefixWord ++ tailWord_918711).sum := by decide
  have hdescent : baseEnd_918711 < baseStart_918711 := by decide
  rcases family_descends (prefixWord ++ tailWord_918711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918726 : List Nat := [6, 1, 2, 2, 2, 1, 2, 1, 1, 5]
def baseStart_918726 : Nat := 118140960795 + 918726 * 2 ^ 59
def prefixEnd_918726 : Nat := 4983230072969 + 3 ^ 40 * 918726 * 2
def baseEnd_918726 : Nat := 157249342594225904666621

theorem tailTrace_918726 : CollatzResearch.WordTrace tailWord_918726 prefixEnd_918726 157249342594225904666621 := by
  unfold tailWord_918726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1047146564675627586062251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22339126713080055169328021 1047146564675627586062251)
  ·
    refine ⟨1570719847013441379093377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1047146564675627586062251 1570719847013441379093377)
    ·
      refine ⟨1178039885260081034320033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1570719847013441379093377 1178039885260081034320033)
      ·
        refine ⟨883529913945060775740025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1178039885260081034320033 883529913945060775740025)
        ·
          refine ⟨662647435458795581805019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 883529913945060775740025 662647435458795581805019)
          ·
            refine ⟨993971153188193372707529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662647435458795581805019 993971153188193372707529)
            ·
              refine ⟨745478364891145029530647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 993971153188193372707529 745478364891145029530647)
              ·
                refine ⟨1118217547336717544295971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 745478364891145029530647 1118217547336717544295971)
                ·
                  refine ⟨1677326321005076316443957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1118217547336717544295971 1677326321005076316443957)
                  ·
                    refine ⟨157249342594225904666621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1677326321005076316443957 157249342594225904666621)
                    ·
                      rfl

theorem cell23_918726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_918726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918726 prefixEnd_918726 := by exact prefixLift 918726
  have htrace : WordTrace (prefixWord ++ tailWord_918726) baseStart_918726 baseEnd_918726 := by
    simpa [prefixWord, tailWord_918726, baseEnd_918726] using wordTrace_append hprefix tailTrace_918726
  have hstable : (prefixWord ++ tailWord_918726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918726).length < 2 ^ (prefixWord ++ tailWord_918726).sum := by decide
  have hdescent : baseEnd_918726 < baseStart_918726 := by decide
  rcases family_descends (prefixWord ++ tailWord_918726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918751 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 3, 4, 2]
def baseStart_918751 : Nat := 118140960795 + 918751 * 2 ^ 59
def prefixEnd_918751 : Nat := 4983230072969 + 3 ^ 40 * 918751 * 2
def baseEnd_918751 : Nat := 471760864799040116187247

theorem tailTrace_918751 : CollatzResearch.WordTrace tailWord_918751 prefixEnd_918751 471760864799040116187247 := by
  unfold tailWord_918751
  simp only [CollatzResearch.WordTrace]
  refine ⟨33509601894529512023652107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22339734596353008015768071 33509601894529512023652107)
  ·
    refine ⟨50264402841794268035478161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33509601894529512023652107 50264402841794268035478161)
    ·
      refine ⟨37698302131345701026608621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50264402841794268035478161 37698302131345701026608621)
      ·
        refine ⟨14136863299254637884978233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37698302131345701026608621 14136863299254637884978233)
        ·
          refine ⟨10602647474440978413733675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14136863299254637884978233 10602647474440978413733675)
          ·
            refine ⟨15903971211661467620600513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10602647474440978413733675 15903971211661467620600513)
            ·
              refine ⟨11927978408746100715450385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15903971211661467620600513 11927978408746100715450385)
              ·
                refine ⟨8945983806559575536587789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11927978408746100715450385 8945983806559575536587789)
                ·
                  refine ⟨3354743927459840826220421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8945983806559575536587789 3354743927459840826220421)
                  ·
                    refine ⟨629014486398720154916329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3354743927459840826220421 629014486398720154916329)
                    ·
                      refine ⟨471760864799040116187247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 629014486398720154916329 471760864799040116187247)
                      ·
                        rfl

theorem cell23_918751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 4, 2].length) (baseStart_918751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918751 prefixEnd_918751 := by exact prefixLift 918751
  have htrace : WordTrace (prefixWord ++ tailWord_918751) baseStart_918751 baseEnd_918751 := by
    simpa [prefixWord, tailWord_918751, baseEnd_918751] using wordTrace_append hprefix tailTrace_918751
  have hstable : (prefixWord ++ tailWord_918751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918751).length < 2 ^ (prefixWord ++ tailWord_918751).sum := by decide
  have hdescent : baseEnd_918751 < baseStart_918751 := by decide
  rcases family_descends (prefixWord ++ tailWord_918751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918811 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 2, 5, 2]
def baseStart_918811 : Nat := 118140960795 + 918811 * 2 ^ 59
def prefixEnd_918811 : Nat := 4983230072969 + 3 ^ 40 * 918811 * 2
def baseEnd_918811 : Nat := 471791673638309881436971

theorem tailTrace_918811 : CollatzResearch.WordTrace tailWord_918811 prefixEnd_918811 471791673638309881436971 := by
  unfold tailWord_918811
  simp only [CollatzResearch.WordTrace]
  refine ⟨33511790274312142270836287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22341193516208094847224191 33511790274312142270836287)
  ·
    refine ⟨50267685411468213406254431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33511790274312142270836287 50267685411468213406254431)
    ·
      refine ⟨75401528117202320109381647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50267685411468213406254431 75401528117202320109381647)
      ·
        refine ⟨113102292175803480164072471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75401528117202320109381647 113102292175803480164072471)
        ·
          refine ⟨169653438263705220246108707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113102292175803480164072471 169653438263705220246108707)
          ·
            refine ⟨254480157395557830369163061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169653438263705220246108707 254480157395557830369163061)
            ·
              refine ⟨23857514755833546597109037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 254480157395557830369163061 23857514755833546597109037)
              ·
                refine ⟨8946568033437579973915889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23857514755833546597109037 8946568033437579973915889)
                ·
                  refine ⟨6709926025078184980436917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8946568033437579973915889 6709926025078184980436917)
                  ·
                    refine ⟨629055564851079841915961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6709926025078184980436917 629055564851079841915961)
                    ·
                      refine ⟨471791673638309881436971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 629055564851079841915961 471791673638309881436971)
                      ·
                        rfl

theorem cell23_918811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 5, 2].length) (baseStart_918811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918811 prefixEnd_918811 := by exact prefixLift 918811
  have htrace : WordTrace (prefixWord ++ tailWord_918811) baseStart_918811 baseEnd_918811 := by
    simpa [prefixWord, tailWord_918811, baseEnd_918811] using wordTrace_append hprefix tailTrace_918811
  have hstable : (prefixWord ++ tailWord_918811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918811).length < 2 ^ (prefixWord ++ tailWord_918811).sum := by decide
  have hdescent : baseEnd_918811 < baseStart_918811 := by decide
  rcases family_descends (prefixWord ++ tailWord_918811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918868 : List Nat := [2, 4, 1, 1, 2, 1, 2, 3, 3, 4]
def baseStart_918868 : Nat := 118140960795 + 918868 * 2 ^ 59
def prefixEnd_918868 : Nat := 4983230072969 + 3 ^ 40 * 918868 * 2
def baseEnd_918868 : Nat := 157273647345205386141403

theorem tailTrace_918868 : CollatzResearch.WordTrace tailWord_918868 prefixEnd_918868 157273647345205386141403 := by
  unfold tailWord_918868
  simp only [CollatzResearch.WordTrace]
  refine ⟨16756934617552820502830629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22342579490070427337107505 16756934617552820502830629)
  ·
    refine ⟨3141925240791153844280743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16756934617552820502830629 3141925240791153844280743)
    ·
      refine ⟨4712887861186730766421115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3141925240791153844280743 4712887861186730766421115)
      ·
        refine ⟨7069331791780096149631673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4712887861186730766421115 7069331791780096149631673)
        ·
          refine ⟨5301998843835072112223755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7069331791780096149631673 5301998843835072112223755)
          ·
            refine ⟨7952998265752608168335633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5301998843835072112223755 7952998265752608168335633)
            ·
              refine ⟨5964748699314456126251725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7952998265752608168335633 5964748699314456126251725)
              ·
                refine ⟨2236780762242921047344397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5964748699314456126251725 2236780762242921047344397)
                ·
                  refine ⟨838792785841095392754149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2236780762242921047344397 838792785841095392754149)
                  ·
                    refine ⟨157273647345205386141403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 838792785841095392754149 157273647345205386141403)
                    ·
                      rfl

theorem cell23_918868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_918868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918868 prefixEnd_918868 := by exact prefixLift 918868
  have htrace : WordTrace (prefixWord ++ tailWord_918868) baseStart_918868 baseEnd_918868 := by
    simpa [prefixWord, tailWord_918868, baseEnd_918868] using wordTrace_append hprefix tailTrace_918868
  have hstable : (prefixWord ++ tailWord_918868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918868).length < 2 ^ (prefixWord ++ tailWord_918868).sum := by decide
  have hdescent : baseEnd_918868 < baseStart_918868 := by decide
  rcases family_descends (prefixWord ++ tailWord_918868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918908 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 5, 1, 3]
def baseStart_918908 : Nat := 118140960795 + 918908 * 2 ^ 59
def prefixEnd_918908 : Nat := 4983230072969 + 3 ^ 40 * 918908 * 2
def baseEnd_918908 : Nat := 471841481261796001924025

theorem tailTrace_918908 : CollatzResearch.WordTrace tailWord_918908 prefixEnd_918908 471841481261796001924025 := by
  unfold tailWord_918908
  simp only [CollatzResearch.WordTrace]
  refine ⟨16757664077480363918558689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22343552103307151891411585 16757664077480363918558689)
  ·
    refine ⟨12568248058110272938919017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16757664077480363918558689 12568248058110272938919017)
    ·
      refine ⟨9426186043582704704189263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12568248058110272938919017 9426186043582704704189263)
      ·
        refine ⟨14139279065374057056283895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9426186043582704704189263 14139279065374057056283895)
        ·
          refine ⟨21208918598061085584425843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14139279065374057056283895 21208918598061085584425843)
          ·
            refine ⟨31813377897091628376638765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21208918598061085584425843 31813377897091628376638765)
            ·
              refine ⟨11930016711409360641239537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31813377897091628376638765 11930016711409360641239537)
              ·
                refine ⟨8947512533557020480929653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11930016711409360641239537 8947512533557020480929653)
                ·
                  refine ⟨838829300020970670087155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8947512533557020480929653 838829300020970670087155)
                  ·
                    refine ⟨1258243950031456005130733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 838829300020970670087155 1258243950031456005130733)
                    ·
                      refine ⟨471841481261796001924025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1258243950031456005130733 471841481261796001924025)
                      ·
                        rfl

theorem cell23_918908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 5, 1, 3].length) (baseStart_918908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918908 prefixEnd_918908 := by exact prefixLift 918908
  have htrace : WordTrace (prefixWord ++ tailWord_918908) baseStart_918908 baseEnd_918908 := by
    simpa [prefixWord, tailWord_918908, baseEnd_918908] using wordTrace_append hprefix tailTrace_918908
  have hstable : (prefixWord ++ tailWord_918908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918908).length < 2 ^ (prefixWord ++ tailWord_918908).sum := by decide
  have hdescent : baseEnd_918908 < baseStart_918908 := by decide
  rcases family_descends (prefixWord ++ tailWord_918908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918948 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 1, 8, 2]
def baseStart_918948 : Nat := 118140960795 + 918948 * 2 ^ 59
def prefixEnd_918948 : Nat := 4983230072969 + 3 ^ 40 * 918948 * 2
def baseEnd_918948 : Nat := 471862020487975845423841

theorem tailTrace_918948 : CollatzResearch.WordTrace tailWord_918948 prefixEnd_918948 471862020487975845423841 := by
  unfold tailWord_918948
  simp only [CollatzResearch.WordTrace]
  refine ⟨16758393537407907334286749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22344524716543876445715665 16758393537407907334286749)
  ·
    refine ⟨6284397576527965250357531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16758393537407907334286749 6284397576527965250357531)
    ·
      refine ⟨9426596364791947875536297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6284397576527965250357531 9426596364791947875536297)
      ·
        refine ⟨7069947273593960906652223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9426596364791947875536297 7069947273593960906652223)
        ·
          refine ⟨10604920910390941359978335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7069947273593960906652223 10604920910390941359978335)
          ·
            refine ⟨15907381365586412039967503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10604920910390941359978335 15907381365586412039967503)
            ·
              refine ⟨23861072048379618059951255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15907381365586412039967503 23861072048379618059951255)
              ·
                refine ⟨35791608072569427089926883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23861072048379618059951255 35791608072569427089926883)
                ·
                  refine ⟨53687412108854140634890325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35791608072569427089926883 53687412108854140634890325)
                  ·
                    refine ⟨629149360650634460565121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53687412108854140634890325 629149360650634460565121)
                    ·
                      refine ⟨471862020487975845423841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 629149360650634460565121 471862020487975845423841)
                      ·
                        rfl

theorem cell23_918948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_918948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918948 prefixEnd_918948 := by exact prefixLift 918948
  have htrace : WordTrace (prefixWord ++ tailWord_918948) baseStart_918948 baseEnd_918948 := by
    simpa [prefixWord, tailWord_918948, baseEnd_918948] using wordTrace_append hprefix tailTrace_918948
  have hstable : (prefixWord ++ tailWord_918948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918948).length < 2 ^ (prefixWord ++ tailWord_918948).sum := by decide
  have hdescent : baseEnd_918948 < baseStart_918948 := by decide
  rcases family_descends (prefixWord ++ tailWord_918948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918965 : List Nat := [1, 3, 3, 2, 2, 1, 2, 3, 1, 1, 4]
def baseStart_918965 : Nat := 118140960795 + 918965 * 2 ^ 59
def prefixEnd_918965 : Nat := 4983230072969 + 3 ^ 40 * 918965 * 2
def baseEnd_918965 : Nat := 471870749659102278911263

theorem tailTrace_918965 : CollatzResearch.WordTrace tailWord_918965 prefixEnd_918965 471870749659102278911263 := by
  unfold tailWord_918965
  simp only [CollatzResearch.WordTrace]
  refine ⟨33517407115754226571942349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22344938077169484381294899 33517407115754226571942349)
  ·
    refine ⟨12569027668407834964478381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33517407115754226571942349 12569027668407834964478381)
    ·
      refine ⟨4713385375652938111679393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12569027668407834964478381 4713385375652938111679393)
      ·
        refine ⟨3535039031739703583759545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4713385375652938111679393 3535039031739703583759545)
        ·
          refine ⟨2651279273804777687819659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3535039031739703583759545 2651279273804777687819659)
          ·
            refine ⟨3976918910707166531729489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2651279273804777687819659 3976918910707166531729489)
            ·
              refine ⟨2982689183030374898797117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3976918910707166531729489 2982689183030374898797117)
              ·
                refine ⟨1118508443636390587048919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2982689183030374898797117 1118508443636390587048919)
                ·
                  refine ⟨1677762665454585880573379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1118508443636390587048919 1677762665454585880573379)
                  ·
                    refine ⟨2516643998181878820860069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1677762665454585880573379 2516643998181878820860069)
                    ·
                      refine ⟨471870749659102278911263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2516643998181878820860069 471870749659102278911263)
                      ·
                        rfl

theorem cell23_918965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_918965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918965 prefixEnd_918965 := by exact prefixLift 918965
  have htrace : WordTrace (prefixWord ++ tailWord_918965) baseStart_918965 baseEnd_918965 := by
    simpa [prefixWord, tailWord_918965, baseEnd_918965] using wordTrace_append hprefix tailTrace_918965
  have hstable : (prefixWord ++ tailWord_918965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918965).length < 2 ^ (prefixWord ++ tailWord_918965).sum := by decide
  have hdescent : baseEnd_918965 < baseStart_918965 := by decide
  rcases family_descends (prefixWord ++ tailWord_918965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918988 : List Nat := [2, 2, 1, 4, 2, 2, 2, 8]
def baseStart_918988 : Nat := 118140960795 + 918988 * 2 ^ 59
def prefixEnd_918988 : Nat := 4983230072969 + 3 ^ 40 * 918988 * 2
def baseEnd_918988 : Nat := 17477131841265025515691

theorem tailTrace_918988 : CollatzResearch.WordTrace tailWord_918988 prefixEnd_918988 17477131841265025515691 := by
  unfold tailWord_918988
  simp only [CollatzResearch.WordTrace]
  refine ⟨16759122997335450750014809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22345497329780601000019745 16759122997335450750014809)
  ·
    refine ⟨12569342248001588062511107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16759122997335450750014809 12569342248001588062511107)
    ·
      refine ⟨18854013372002382093766661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12569342248001588062511107 18854013372002382093766661)
      ·
        refine ⟨3535127507250446642581249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18854013372002382093766661 3535127507250446642581249)
        ·
          refine ⟨2651345630437834981935937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3535127507250446642581249 2651345630437834981935937)
          ·
            refine ⟨1988509222828376236451953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2651345630437834981935937 1988509222828376236451953)
            ·
              refine ⟨1491381917121282177338965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1988509222828376236451953 1491381917121282177338965)
              ·
                refine ⟨17477131841265025515691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1491381917121282177338965 17477131841265025515691)
                ·
                  rfl

theorem cell23_918988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 8].length) (baseStart_918988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_918988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_918988 prefixEnd_918988 := by exact prefixLift 918988
  have htrace : WordTrace (prefixWord ++ tailWord_918988) baseStart_918988 baseEnd_918988 := by
    simpa [prefixWord, tailWord_918988, baseEnd_918988] using wordTrace_append hprefix tailTrace_918988
  have hstable : (prefixWord ++ tailWord_918988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918988).length < 2 ^ (prefixWord ++ tailWord_918988).sum := by decide
  have hdescent : baseEnd_918988 < baseStart_918988 := by decide
  rcases family_descends (prefixWord ++ tailWord_918988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919002 : List Nat := [3, 1, 1, 2, 3, 4, 1, 2, 1, 2, 3]
def baseStart_919002 : Nat := 118140960795 + 919002 * 2 ^ 59
def prefixEnd_919002 : Nat := 4983230072969 + 3 ^ 40 * 919002 * 2
def baseEnd_919002 : Nat := 471889748443318634148593

theorem tailTrace_919002 : CollatzResearch.WordTrace tailWord_919002 prefixEnd_919002 471889748443318634148593 := by
  unfold tailWord_919002
  simp only [CollatzResearch.WordTrace]
  refine ⟨8379689154155045472759815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22345837744413454594026173 8379689154155045472759815)
  ·
    refine ⟨12569533731232568209139723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8379689154155045472759815 12569533731232568209139723)
    ·
      refine ⟨18854300596848852313709585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12569533731232568209139723 18854300596848852313709585)
      ·
        refine ⟨14140725447636639235282189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18854300596848852313709585 14140725447636639235282189)
        ·
          refine ⟨5302772042863739713230821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14140725447636639235282189 5302772042863739713230821)
          ·
            refine ⟨994269758036951196230779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5302772042863739713230821 994269758036951196230779)
            ·
              refine ⟨1491404637055426794346169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 994269758036951196230779 1491404637055426794346169)
              ·
                refine ⟨1118553477791570095759627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1491404637055426794346169 1118553477791570095759627)
                ·
                  refine ⟨1677830216687355143639441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1118553477791570095759627 1677830216687355143639441)
                  ·
                    refine ⟨1258372662515516357729581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1677830216687355143639441 1258372662515516357729581)
                    ·
                      refine ⟨471889748443318634148593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1258372662515516357729581 471889748443318634148593)
                      ·
                        rfl

theorem cell23_919002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_919002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919002 prefixEnd_919002 := by exact prefixLift 919002
  have htrace : WordTrace (prefixWord ++ tailWord_919002) baseStart_919002 baseEnd_919002 := by
    simpa [prefixWord, tailWord_919002, baseEnd_919002] using wordTrace_append hprefix tailTrace_919002
  have hstable : (prefixWord ++ tailWord_919002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919002).length < 2 ^ (prefixWord ++ tailWord_919002).sum := by decide
  have hdescent : baseEnd_919002 < baseStart_919002 := by decide
  rcases family_descends (prefixWord ++ tailWord_919002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919015 : List Nat := [1, 1, 5, 2, 1, 3, 1, 2, 1, 3, 3]
def baseStart_919015 : Nat := 118140960795 + 919015 * 2 ^ 59
def prefixEnd_919015 : Nat := 4983230072969 + 3 ^ 40 * 919015 * 2
def baseEnd_919015 : Nat := 471896423691827083286033

theorem tailTrace_919015 : CollatzResearch.WordTrace tailWord_919015 prefixEnd_919015 471896423691827083286033 := by
  unfold tailWord_919015
  simp only [CollatzResearch.WordTrace]
  refine ⟨33519230765573085111262499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22346153843715390074174999 33519230765573085111262499)
  ·
    refine ⟨50278846148359627666893749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33519230765573085111262499 50278846148359627666893749)
    ·
      refine ⟨4713641826408715093771289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50278846148359627666893749 4713641826408715093771289)
      ·
        refine ⟨3535231369806536320328467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4713641826408715093771289 3535231369806536320328467)
        ·
          refine ⟨5302847054709804480492701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3535231369806536320328467 5302847054709804480492701)
          ·
            refine ⟨1988567645516176680184763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5302847054709804480492701 1988567645516176680184763)
            ·
              refine ⟨2982851468274265020277145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1988567645516176680184763 2982851468274265020277145)
              ·
                refine ⟨2237138601205698765207859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2982851468274265020277145 2237138601205698765207859)
                ·
                  refine ⟨3355707901808548147811789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2237138601205698765207859 3355707901808548147811789)
                  ·
                    refine ⟨1258390463178205555429421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3355707901808548147811789 1258390463178205555429421)
                    ·
                      refine ⟨471896423691827083286033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1258390463178205555429421 471896423691827083286033)
                      ·
                        rfl

theorem cell23_919015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_919015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919015 prefixEnd_919015 := by exact prefixLift 919015
  have htrace : WordTrace (prefixWord ++ tailWord_919015) baseStart_919015 baseEnd_919015 := by
    simpa [prefixWord, tailWord_919015, baseEnd_919015] using wordTrace_append hprefix tailTrace_919015
  have hstable : (prefixWord ++ tailWord_919015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919015).length < 2 ^ (prefixWord ++ tailWord_919015).sum := by decide
  have hdescent : baseEnd_919015 < baseStart_919015 := by decide
  rcases family_descends (prefixWord ++ tailWord_919015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919032 : List Nat := [2, 1, 2, 1, 1, 6, 2, 2, 2, 1, 3]
def baseStart_919032 : Nat := 118140960795 + 919032 * 2 ^ 59
def prefixEnd_919032 : Nat := 4983230072969 + 3 ^ 40 * 919032 * 2
def baseEnd_919032 : Nat := 471905152862953516773455

theorem tailTrace_919032 : CollatzResearch.WordTrace tailWord_919032 prefixEnd_919032 471905152862953516773455 := by
  unfold tailWord_919032
  simp only [CollatzResearch.WordTrace]
  refine ⟨16759925403255748507315675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22346567204340998009754233 16759925403255748507315675)
  ·
    refine ⟨25139888104883622760973513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16759925403255748507315675 25139888104883622760973513)
    ·
      refine ⟨18854916078662717070730135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25139888104883622760973513 18854916078662717070730135)
      ·
        refine ⟨28282374117994075606095203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18854916078662717070730135 28282374117994075606095203)
        ·
          refine ⟨42423561176991113409142805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28282374117994075606095203 42423561176991113409142805)
          ·
            refine ⟨1988604430171458441053569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42423561176991113409142805 1988604430171458441053569)
            ·
              refine ⟨1491453322628593830790177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1988604430171458441053569 1491453322628593830790177)
              ·
                refine ⟨1118589991971445373092633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1491453322628593830790177 1118589991971445373092633)
                ·
                  refine ⟨838942493978584029819475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1118589991971445373092633 838942493978584029819475)
                  ·
                    refine ⟨1258413740967876044729213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 838942493978584029819475 1258413740967876044729213)
                    ·
                      refine ⟨471905152862953516773455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1258413740967876044729213 471905152862953516773455)
                      ·
                        rfl

theorem cell23_919032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 2, 1, 3].length) (baseStart_919032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919032 prefixEnd_919032 := by exact prefixLift 919032
  have htrace : WordTrace (prefixWord ++ tailWord_919032) baseStart_919032 baseEnd_919032 := by
    simpa [prefixWord, tailWord_919032, baseEnd_919032] using wordTrace_append hprefix tailTrace_919032
  have hstable : (prefixWord ++ tailWord_919032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919032).length < 2 ^ (prefixWord ++ tailWord_919032).sum := by decide
  have hdescent : baseEnd_919032 < baseStart_919032 := by decide
  rcases family_descends (prefixWord ++ tailWord_919032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919046 : List Nat := [6, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_919046 : Nat := 118140960795 + 919046 * 2 ^ 59
def prefixEnd_919046 : Nat := 4983230072969 + 3 ^ 40 * 919046 * 2
def baseEnd_919046 : Nat := 471912341592116461998391

theorem tailTrace_919046 : CollatzResearch.WordTrace tailWord_919046 prefixEnd_919046 471912341592116461998391 := by
  unfold tailWord_919046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1047511294639399293926281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22346907618973851603760661 1047511294639399293926281)
  ·
    refine ⟨785633470979549470444711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1047511294639399293926281 785633470979549470444711)
    ·
      refine ⟨1178450206469324205667067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 785633470979549470444711 1178450206469324205667067)
      ·
        refine ⟨1767675309703986308500601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1178450206469324205667067 1767675309703986308500601)
        ·
          refine ⟨1325756482277989731375451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1767675309703986308500601 1325756482277989731375451)
          ·
            refine ⟨1988634723416984597063177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1325756482277989731375451 1988634723416984597063177)
            ·
              refine ⟨1491476042562738447797383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1988634723416984597063177 1491476042562738447797383)
              ·
                refine ⟨2237214063844107671696075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1491476042562738447797383 2237214063844107671696075)
                ·
                  refine ⟨3355821095766161507544113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2237214063844107671696075 3355821095766161507544113)
                  ·
                    refine ⟨2516865821824621130658085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3355821095766161507544113 2516865821824621130658085)
                    ·
                      refine ⟨471912341592116461998391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2516865821824621130658085 471912341592116461998391)
                      ·
                        rfl

theorem cell23_919046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_919046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919046 prefixEnd_919046 := by exact prefixLift 919046
  have htrace : WordTrace (prefixWord ++ tailWord_919046) baseStart_919046 baseEnd_919046 := by
    simpa [prefixWord, tailWord_919046, baseEnd_919046] using wordTrace_append hprefix tailTrace_919046
  have hstable : (prefixWord ++ tailWord_919046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919046).length < 2 ^ (prefixWord ++ tailWord_919046).sum := by decide
  have hdescent : baseEnd_919046 < baseStart_919046 := by decide
  rcases family_descends (prefixWord ++ tailWord_919046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919068 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 1, 4, 4]
def baseStart_919068 : Nat := 118140960795 + 919068 * 2 ^ 59
def prefixEnd_919068 : Nat := 4983230072969 + 3 ^ 40 * 919068 * 2
def baseEnd_919068 : Nat := 471923638166515375923289

theorem tailTrace_919068 : CollatzResearch.WordTrace tailWord_919068 prefixEnd_919068 471923638166515375923289 := by
  unfold tailWord_919068
  simp only [CollatzResearch.WordTrace]
  refine ⟨16760581917190537581470929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22347442556254050108627905 16760581917190537581470929)
  ·
    refine ⟨12570436437892903186103197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16760581917190537581470929 12570436437892903186103197)
    ·
      refine ⟨4713913664209838694788699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12570436437892903186103197 4713913664209838694788699)
      ·
        refine ⟨7070870496314758042183049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4713913664209838694788699 7070870496314758042183049)
        ·
          refine ⟨5303152872236068531637287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7070870496314758042183049 5303152872236068531637287)
          ·
            refine ⟨7954729308354102797455931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5303152872236068531637287 7954729308354102797455931)
            ·
              refine ⟨11932093962531154196183897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7954729308354102797455931 11932093962531154196183897)
              ·
                refine ⟨8949070471898365647137923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11932093962531154196183897 8949070471898365647137923)
                ·
                  refine ⟨13423605707847548470706885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8949070471898365647137923 13423605707847548470706885)
                  ·
                    refine ⟨2516926070221415338257541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13423605707847548470706885 2516926070221415338257541)
                    ·
                      refine ⟨471923638166515375923289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2516926070221415338257541 471923638166515375923289)
                      ·
                        rfl

theorem cell23_919068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_919068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919068 prefixEnd_919068 := by exact prefixLift 919068
  have htrace : WordTrace (prefixWord ++ tailWord_919068) baseStart_919068 baseEnd_919068 := by
    simpa [prefixWord, tailWord_919068, baseEnd_919068] using wordTrace_append hprefix tailTrace_919068
  have hstable : (prefixWord ++ tailWord_919068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919068).length < 2 ^ (prefixWord ++ tailWord_919068).sum := by decide
  have hdescent : baseEnd_919068 < baseStart_919068 := by decide
  rcases family_descends (prefixWord ++ tailWord_919068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919070 : List Nat := [4, 3, 3, 1, 1, 2, 2, 1, 1, 2, 3]
def baseStart_919070 : Nat := 118140960795 + 919070 * 2 ^ 59
def prefixEnd_919070 : Nat := 4983230072969 + 3 ^ 40 * 919070 * 2
def baseEnd_919070 : Nat := 471924665127824368098281

theorem tailTrace_919070 : CollatzResearch.WordTrace tailWord_919070 prefixEnd_919070 471924665127824368098281 := by
  unfold tailWord_919070
  simp only [CollatzResearch.WordTrace]
  refine ⟨4190154597546728688064333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22347491186915886336343109 4190154597546728688064333)
  ·
    refine ⟨1571307974080023258024125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4190154597546728688064333 1571307974080023258024125)
    ·
      refine ⟨589240490280008721759047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1571307974080023258024125 589240490280008721759047)
      ·
        refine ⟨883860735420013082638571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589240490280008721759047 883860735420013082638571)
        ·
          refine ⟨1325791103130019623957857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 883860735420013082638571 1325791103130019623957857)
          ·
            refine ⟨994343327347514717968393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1325791103130019623957857 994343327347514717968393)
            ·
              refine ⟨745757495510636038476295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 994343327347514717968393 745757495510636038476295)
              ·
                refine ⟨1118636243265954057714443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 745757495510636038476295 1118636243265954057714443)
                ·
                  refine ⟨1677954364898931086571665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1118636243265954057714443 1677954364898931086571665)
                  ·
                    refine ⟨1258465773674198314928749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1677954364898931086571665 1258465773674198314928749)
                    ·
                      refine ⟨471924665127824368098281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1258465773674198314928749 471924665127824368098281)
                      ·
                        rfl

theorem cell23_919070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_919070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919070 prefixEnd_919070 := by exact prefixLift 919070
  have htrace : WordTrace (prefixWord ++ tailWord_919070) baseStart_919070 baseEnd_919070 := by
    simpa [prefixWord, tailWord_919070, baseEnd_919070] using wordTrace_append hprefix tailTrace_919070
  have hstable : (prefixWord ++ tailWord_919070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919070).length < 2 ^ (prefixWord ++ tailWord_919070).sum := by decide
  have hdescent : baseEnd_919070 < baseStart_919070 := by decide
  rcases family_descends (prefixWord ++ tailWord_919070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919072 : List Nat := [2, 1, 1, 6, 1, 1, 2, 2, 1, 4, 2]
def baseStart_919072 : Nat := 118140960795 + 919072 * 2 ^ 59
def prefixEnd_919072 : Nat := 4983230072969 + 3 ^ 40 * 919072 * 2
def baseEnd_919072 : Nat := 471925692089133360273271

theorem tailTrace_919072 : CollatzResearch.WordTrace tailWord_919072 prefixEnd_919072 471925692089133360273271 := by
  unfold tailWord_919072
  simp only [CollatzResearch.WordTrace]
  refine ⟨16760654863183291923043735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22347539817577722564058313 16760654863183291923043735)
  ·
    refine ⟨25140982294774937884565603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16760654863183291923043735 25140982294774937884565603)
    ·
      refine ⟨37711473442162406826848405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25140982294774937884565603 37711473442162406826848405)
      ·
        refine ⟨1767725317601362820008519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37711473442162406826848405 1767725317601362820008519)
        ·
          refine ⟨2651587976402044230012779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1767725317601362820008519 2651587976402044230012779)
          ·
            refine ⟨3977381964603066345019169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2651587976402044230012779 3977381964603066345019169)
            ·
              refine ⟨2983036473452299758764377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3977381964603066345019169 2983036473452299758764377)
              ·
                refine ⟨2237277355089224819073283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2983036473452299758764377 2237277355089224819073283)
                ·
                  refine ⟨3355916032633837228609925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2237277355089224819073283 3355916032633837228609925)
                  ·
                    refine ⟨629234256118844480364361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3355916032633837228609925 629234256118844480364361)
                    ·
                      refine ⟨471925692089133360273271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 629234256118844480364361 471925692089133360273271)
                      ·
                        rfl

theorem cell23_919072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_919072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919072 prefixEnd_919072 := by exact prefixLift 919072
  have htrace : WordTrace (prefixWord ++ tailWord_919072) baseStart_919072 baseEnd_919072 := by
    simpa [prefixWord, tailWord_919072, baseEnd_919072] using wordTrace_append hprefix tailTrace_919072
  have hstable : (prefixWord ++ tailWord_919072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919072).length < 2 ^ (prefixWord ++ tailWord_919072).sum := by decide
  have hdescent : baseEnd_919072 < baseStart_919072 := by decide
  rcases family_descends (prefixWord ++ tailWord_919072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919095 : List Nat := [1, 1, 3, 1, 2, 4, 2, 4, 5]
def baseStart_919095 : Nat := 118140960795 + 919095 * 2 ^ 59
def prefixEnd_919095 : Nat := 4983230072969 + 3 ^ 40 * 919095 * 2
def baseEnd_919095 : Nat := 52437500238242974476185

theorem tailTrace_919095 : CollatzResearch.WordTrace tailWord_919095 prefixEnd_919095 52437500238242974476185 := by
  unfold tailWord_919095
  simp only [CollatzResearch.WordTrace]
  refine ⟨33522148605283258774174739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22348099070188839182783159 33522148605283258774174739)
  ·
    refine ⟨50283222907924888161262109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33522148605283258774174739 50283222907924888161262109)
    ·
      refine ⟨18856208590471833060473291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50283222907924888161262109 18856208590471833060473291)
      ·
        refine ⟨28284312885707749590709937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18856208590471833060473291 28284312885707749590709937)
        ·
          refine ⟨21213234664280812193032453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28284312885707749590709937 21213234664280812193032453)
          ·
            refine ⟨3977481499552652286193585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21213234664280812193032453 3977481499552652286193585)
            ·
              refine ⟨2983111124664489214645189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3977481499552652286193585 2983111124664489214645189)
              ·
                refine ⟨559333335874591727745973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2983111124664489214645189 559333335874591727745973)
                ·
                  refine ⟨52437500238242974476185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 559333335874591727745973 52437500238242974476185)
                  ·
                    rfl

theorem cell23_919095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 4, 5].length) (baseStart_919095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919095 prefixEnd_919095 := by exact prefixLift 919095
  have htrace : WordTrace (prefixWord ++ tailWord_919095) baseStart_919095 baseEnd_919095 := by
    simpa [prefixWord, tailWord_919095, baseEnd_919095] using wordTrace_append hprefix tailTrace_919095
  have hstable : (prefixWord ++ tailWord_919095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919095).length < 2 ^ (prefixWord ++ tailWord_919095).sum := by decide
  have hdescent : baseEnd_919095 < baseStart_919095 := by decide
  rcases family_descends (prefixWord ++ tailWord_919095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919105 : List Nat := [1, 2, 5, 1, 1, 1, 1, 3, 2, 3, 3]
def baseStart_919105 : Nat := 118140960795 + 919105 * 2 ^ 59
def prefixEnd_919105 : Nat := 4983230072969 + 3 ^ 40 * 919105 * 2
def baseEnd_919105 : Nat := 471942636950731731160619

theorem tailTrace_919105 : CollatzResearch.WordTrace tailWord_919105 prefixEnd_919105 471942636950731731160619 := by
  unfold tailWord_919105
  simp only [CollatzResearch.WordTrace]
  refine ⟨33522513335247030482038769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22348342223498020321359179 33522513335247030482038769)
  ·
    refine ⟨25141885001435272861529077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33522513335247030482038769 25141885001435272861529077)
    ·
      refine ⟨2357051718884556830768351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25141885001435272861529077 2357051718884556830768351)
      ·
        refine ⟨3535577578326835246152527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2357051718884556830768351 3535577578326835246152527)
        ·
          refine ⟨5303366367490252869228791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3535577578326835246152527 5303366367490252869228791)
          ·
            refine ⟨7955049551235379303843187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5303366367490252869228791 7955049551235379303843187)
            ·
              refine ⟨11932574326853068955764781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7955049551235379303843187 11932574326853068955764781)
              ·
                refine ⟨4474715372569900858411793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11932574326853068955764781 4474715372569900858411793)
                ·
                  refine ⟨3356036529427425643808845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4474715372569900858411793 3356036529427425643808845)
                  ·
                    refine ⟨1258513698535284616428317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3356036529427425643808845 1258513698535284616428317)
                    ·
                      refine ⟨471942636950731731160619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1258513698535284616428317 471942636950731731160619)
                      ·
                        rfl

theorem cell23_919105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_919105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919105 prefixEnd_919105 := by exact prefixLift 919105
  have htrace : WordTrace (prefixWord ++ tailWord_919105) baseStart_919105 baseEnd_919105 := by
    simpa [prefixWord, tailWord_919105, baseEnd_919105] using wordTrace_append hprefix tailTrace_919105
  have hstable : (prefixWord ++ tailWord_919105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919105).length < 2 ^ (prefixWord ++ tailWord_919105).sum := by decide
  have hdescent : baseEnd_919105 < baseStart_919105 := by decide
  rcases family_descends (prefixWord ++ tailWord_919105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919118 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5]
def baseStart_919118 : Nat := 118140960795 + 919118 * 2 ^ 59
def prefixEnd_919118 : Nat := 4983230072969 + 3 ^ 40 * 919118 * 2
def baseEnd_919118 : Nat := 471949312199240180298059

theorem tailTrace_919118 : CollatzResearch.WordTrace tailWord_919118 prefixEnd_919118 471949312199240180298059 := by
  unfold tailWord_919118
  simp only [CollatzResearch.WordTrace]
  refine ⟨4190373435524991712782751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22348658322799955801508005 4190373435524991712782751)
  ·
    refine ⟨6285560153287487569174127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4190373435524991712782751 6285560153287487569174127)
    ·
      refine ⟨9428340229931231353761191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6285560153287487569174127 9428340229931231353761191)
      ·
        refine ⟨14142510344896847030641787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9428340229931231353761191 14142510344896847030641787)
        ·
          refine ⟨21213765517345270545962681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14142510344896847030641787 21213765517345270545962681)
          ·
            refine ⟨15910324138008952909472011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21213765517345270545962681 15910324138008952909472011)
            ·
              refine ⟨23865486207013429364208017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15910324138008952909472011 23865486207013429364208017)
              ·
                refine ⟨17899114655260072023156013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23865486207013429364208017 17899114655260072023156013)
                ·
                  refine ⟨6712167995722527008683505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17899114655260072023156013 6712167995722527008683505)
                  ·
                    refine ⟨5034125996791895256512629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6712167995722527008683505 5034125996791895256512629)
                    ·
                      refine ⟨471949312199240180298059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5034125996791895256512629 471949312199240180298059)
                      ·
                        rfl

theorem cell23_919118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_919118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919118 prefixEnd_919118 := by exact prefixLift 919118
  have htrace : WordTrace (prefixWord ++ tailWord_919118) baseStart_919118 baseEnd_919118 := by
    simpa [prefixWord, tailWord_919118, baseEnd_919118] using wordTrace_append hprefix tailTrace_919118
  have hstable : (prefixWord ++ tailWord_919118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919118).length < 2 ^ (prefixWord ++ tailWord_919118).sum := by decide
  have hdescent : baseEnd_919118 < baseStart_919118 := by decide
  rcases family_descends (prefixWord ++ tailWord_919118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919145 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 4, 4, 2]
def baseStart_919145 : Nat := 118140960795 + 919145 * 2 ^ 59
def prefixEnd_919145 : Nat := 4983230072969 + 3 ^ 40 * 919145 * 2
def baseEnd_919145 : Nat := 471963176176911574660435

theorem tailTrace_919145 : CollatzResearch.WordTrace tailWord_919145 prefixEnd_919145 471963176176911574660435 := by
  unfold tailWord_919145
  simp only [CollatzResearch.WordTrace]
  refine ⟨33523972255102117313494889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22349314836734744875663259 33523972255102117313494889)
  ·
    refine ⟨25142979191326587985121167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33523972255102117313494889 25142979191326587985121167)
    ·
      refine ⟨37714468786989881977681751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25142979191326587985121167 37714468786989881977681751)
      ·
        refine ⟨56571703180484822966522627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37714468786989881977681751 56571703180484822966522627)
        ·
          refine ⟨84857554770727234449783941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56571703180484822966522627 84857554770727234449783941)
          ·
            refine ⟨15910791519511356459334489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84857554770727234449783941 15910791519511356459334489)
            ·
              refine ⟨11933093639633517344500867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15910791519511356459334489 11933093639633517344500867)
              ·
                refine ⟨17899640459450276016751301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11933093639633517344500867 17899640459450276016751301)
                ·
                  refine ⟨3356182586146926753140869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17899640459450276016751301 3356182586146926753140869)
                  ·
                    refine ⟨629284234902548766213913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3356182586146926753140869 629284234902548766213913)
                    ·
                      refine ⟨471963176176911574660435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 629284234902548766213913 471963176176911574660435)
                      ·
                        rfl

theorem cell23_919145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 4, 2].length) (baseStart_919145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919145 prefixEnd_919145 := by exact prefixLift 919145
  have htrace : WordTrace (prefixWord ++ tailWord_919145) baseStart_919145 baseEnd_919145 := by
    simpa [prefixWord, tailWord_919145, baseEnd_919145] using wordTrace_append hprefix tailTrace_919145
  have hstable : (prefixWord ++ tailWord_919145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919145).length < 2 ^ (prefixWord ++ tailWord_919145).sum := by decide
  have hdescent : baseEnd_919145 < baseStart_919145 := by decide
  rcases family_descends (prefixWord ++ tailWord_919145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919182 : List Nat := [4, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3]
def baseStart_919182 : Nat := 118140960795 + 919182 * 2 ^ 59
def prefixEnd_919182 : Nat := 4983230072969 + 3 ^ 40 * 919182 * 2
def baseEnd_919182 : Nat := 471982174961127929897765

theorem tailTrace_919182 : CollatzResearch.WordTrace tailWord_919182 prefixEnd_919182 471982174961127929897765 := by
  unfold tailWord_919182
  simp only [CollatzResearch.WordTrace]
  refine ⟨4190665219496009079073975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22350214503978715088394533 4190665219496009079073975)
  ·
    refine ⟨6285997829244013618610963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4190665219496009079073975 6285997829244013618610963)
    ·
      refine ⟨9428996743866020427916445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6285997829244013618610963 9428996743866020427916445)
      ·
        refine ⟨3535873778949757660468667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9428996743866020427916445 3535873778949757660468667)
        ·
          refine ⟨5303810668424636490703001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3535873778949757660468667 5303810668424636490703001)
          ·
            refine ⟨3977858001318477368027251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5303810668424636490703001 3977858001318477368027251)
            ·
              refine ⟨5966787001977716052040877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3977858001318477368027251 5966787001977716052040877)
              ·
                refine ⟨2237545125741643519515329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5966787001977716052040877 2237545125741643519515329)
                ·
                  refine ⟨1678158844306232639636497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2237545125741643519515329 1678158844306232639636497)
                  ·
                    refine ⟨1258619133229674479727373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1678158844306232639636497 1258619133229674479727373)
                    ·
                      refine ⟨471982174961127929897765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1258619133229674479727373 471982174961127929897765)
                      ·
                        rfl

theorem cell23_919182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_919182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919182 prefixEnd_919182 := by exact prefixLift 919182
  have htrace : WordTrace (prefixWord ++ tailWord_919182) baseStart_919182 baseEnd_919182 := by
    simpa [prefixWord, tailWord_919182, baseEnd_919182] using wordTrace_append hprefix tailTrace_919182
  have hstable : (prefixWord ++ tailWord_919182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919182).length < 2 ^ (prefixWord ++ tailWord_919182).sum := by decide
  have hdescent : baseEnd_919182 < baseStart_919182 := by decide
  rcases family_descends (prefixWord ++ tailWord_919182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919246 : List Nat := [4, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3]
def baseStart_919246 : Nat := 118140960795 + 919246 * 2 ^ 59
def prefixEnd_919246 : Nat := 4983230072969 + 3 ^ 40 * 919246 * 2
def baseEnd_919246 : Nat := 472015037723015679497471

theorem tailTrace_919246 : CollatzResearch.WordTrace tailWord_919246 prefixEnd_919246 472015037723015679497471 := by
  unfold tailWord_919246
  simp only [CollatzResearch.WordTrace]
  refine ⟨4190957003467026445365199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22351770685157474375281061 4190957003467026445365199)
  ·
    refine ⟨6286435505200539668047799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4190957003467026445365199 6286435505200539668047799)
    ·
      refine ⟨9429653257800809502071699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6286435505200539668047799 9429653257800809502071699)
      ·
        refine ⟨14144479886701214253107549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9429653257800809502071699 14144479886701214253107549)
        ·
          refine ⟨5304179957512955344915331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14144479886701214253107549 5304179957512955344915331)
          ·
            refine ⟨7956269936269433017372997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5304179957512955344915331 7956269936269433017372997)
            ·
              refine ⟨1491800613050518690757437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7956269936269433017372997 1491800613050518690757437)
              ·
                refine ⟨559425229893944509034039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1491800613050518690757437 559425229893944509034039)
                ·
                  refine ⟨839137844840916763551059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 559425229893944509034039 839137844840916763551059)
                  ·
                    refine ⟨1258706767261375145326589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 839137844840916763551059 1258706767261375145326589)
                    ·
                      refine ⟨472015037723015679497471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1258706767261375145326589 472015037723015679497471)
                      ·
                        rfl

theorem cell23_919246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3].length) (baseStart_919246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919246 prefixEnd_919246 := by exact prefixLift 919246
  have htrace : WordTrace (prefixWord ++ tailWord_919246) baseStart_919246 baseEnd_919246 := by
    simpa [prefixWord, tailWord_919246, baseEnd_919246] using wordTrace_append hprefix tailTrace_919246
  have hstable : (prefixWord ++ tailWord_919246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919246).length < 2 ^ (prefixWord ++ tailWord_919246).sum := by decide
  have hdescent : baseEnd_919246 < baseStart_919246 := by decide
  rcases family_descends (prefixWord ++ tailWord_919246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919249 : List Nat := [1, 2, 2, 1, 2, 6, 2, 1, 1, 5]
def baseStart_919249 : Nat := 118140960795 + 919249 * 2 ^ 59
def prefixEnd_919249 : Nat := 4983230072969 + 3 ^ 40 * 919249 * 2
def baseEnd_919249 : Nat := 157338859388326389253319

theorem tailTrace_919249 : CollatzResearch.WordTrace tailWord_919249 prefixEnd_919249 157338859388326389253319 := by
  unfold tailWord_919249
  simp only [CollatzResearch.WordTrace]
  refine ⟨33527765446725343075280801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22351843631150228716853867 33527765446725343075280801)
  ·
    refine ⟨25145824085044007306460601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33527765446725343075280801 25145824085044007306460601)
    ·
      refine ⟨18859368063783005479845451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25145824085044007306460601 18859368063783005479845451)
      ·
        refine ⟨28289052095674508219768177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18859368063783005479845451 28289052095674508219768177)
        ·
          refine ⟨21216789071755881164826133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28289052095674508219768177 21216789071755881164826133)
          ·
            refine ⟨994536987738556929601225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21216789071755881164826133 994536987738556929601225)
            ·
              refine ⟨745902740803917697200919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 994536987738556929601225 745902740803917697200919)
              ·
                refine ⟨1118854111205876545801379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 745902740803917697200919 1118854111205876545801379)
                ·
                  refine ⟨1678281166808814818702069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1118854111205876545801379 1678281166808814818702069)
                  ·
                    refine ⟨157338859388326389253319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1678281166808814818702069 157338859388326389253319)
                    ·
                      rfl

theorem cell23_919249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 1, 5].length) (baseStart_919249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919249 prefixEnd_919249 := by exact prefixLift 919249
  have htrace : WordTrace (prefixWord ++ tailWord_919249) baseStart_919249 baseEnd_919249 := by
    simpa [prefixWord, tailWord_919249, baseEnd_919249] using wordTrace_append hprefix tailTrace_919249
  have hstable : (prefixWord ++ tailWord_919249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919249).length < 2 ^ (prefixWord ++ tailWord_919249).sum := by decide
  have hdescent : baseEnd_919249 < baseStart_919249 := by decide
  rcases family_descends (prefixWord ++ tailWord_919249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919255 : List Nat := [1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 5]
def baseStart_919255 : Nat := 118140960795 + 919255 * 2 ^ 59
def prefixEnd_919255 : Nat := 4983230072969 + 3 ^ 40 * 919255 * 2
def baseEnd_919255 : Nat := 472019659048906144284929

theorem tailTrace_919255 : CollatzResearch.WordTrace tailWord_919255 prefixEnd_919255 472019659048906144284929 := by
  unfold tailWord_919255
  simp only [CollatzResearch.WordTrace]
  refine ⟨33527984284703606099999219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22351989523135737399999479 33527984284703606099999219)
  ·
    refine ⟨50291976427055409149998829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33527984284703606099999219 50291976427055409149998829)
    ·
      refine ⟨18859491160145778431249561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50291976427055409149998829 18859491160145778431249561)
      ·
        refine ⟨14144618370109333823437171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18859491160145778431249561 14144618370109333823437171)
        ·
          refine ⟨21216927555164000735155757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14144618370109333823437171 21216927555164000735155757)
          ·
            refine ⟨7956347833186500275683409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21216927555164000735155757 7956347833186500275683409)
            ·
              refine ⟨5967260874889875206762557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7956347833186500275683409 5967260874889875206762557)
              ·
                refine ⟨2237722828083703202535959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5967260874889875206762557 2237722828083703202535959)
                ·
                  refine ⟨3356584242125554803803939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2237722828083703202535959 3356584242125554803803939)
                  ·
                    refine ⟨5034876363188332205705909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3356584242125554803803939 5034876363188332205705909)
                    ·
                      refine ⟨472019659048906144284929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5034876363188332205705909 472019659048906144284929)
                      ·
                        rfl

theorem cell23_919255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_919255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919255 prefixEnd_919255 := by exact prefixLift 919255
  have htrace : WordTrace (prefixWord ++ tailWord_919255) baseStart_919255 baseEnd_919255 := by
    simpa [prefixWord, tailWord_919255, baseEnd_919255] using wordTrace_append hprefix tailTrace_919255
  have hstable : (prefixWord ++ tailWord_919255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919255).length < 2 ^ (prefixWord ++ tailWord_919255).sum := by decide
  have hdescent : baseEnd_919255 < baseStart_919255 := by decide
  rcases family_descends (prefixWord ++ tailWord_919255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919272 : List Nat := [2, 1, 4, 1, 3, 2, 1, 2, 1, 1, 5]
def baseStart_919272 : Nat := 118140960795 + 919272 * 2 ^ 59
def prefixEnd_919272 : Nat := 4983230072969 + 3 ^ 40 * 919272 * 2
def baseEnd_919272 : Nat := 472028388220032577772351

theorem tailTrace_919272 : CollatzResearch.WordTrace tailWord_919272 prefixEnd_919272 472028388220032577772351 := by
  unfold tailWord_919272
  simp only [CollatzResearch.WordTrace]
  refine ⟨16764302162821009001684035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22352402883761345335578713 16764302162821009001684035)
  ·
    refine ⟨25146453244231513502526053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16764302162821009001684035 25146453244231513502526053)
    ·
      refine ⟨4714959983293408781723635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25146453244231513502526053 4714959983293408781723635)
      ·
        refine ⟨7072439974940113172585453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4714959983293408781723635 7072439974940113172585453)
        ·
          refine ⟨2652164990602542439719545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7072439974940113172585453 2652164990602542439719545)
          ·
            refine ⟨1989123742951906829789659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2652164990602542439719545 1989123742951906829789659)
            ·
              refine ⟨2983685614427860244684489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1989123742951906829789659 2983685614427860244684489)
              ·
                refine ⟨2237764210820895183513367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2983685614427860244684489 2237764210820895183513367)
                ·
                  refine ⟨3356646316231342775270051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2237764210820895183513367 3356646316231342775270051)
                  ·
                    refine ⟨5034969474347014162905077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3356646316231342775270051 5034969474347014162905077)
                    ·
                      refine ⟨472028388220032577772351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5034969474347014162905077 472028388220032577772351)
                      ·
                        rfl

theorem cell23_919272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_919272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919272 prefixEnd_919272 := by exact prefixLift 919272
  have htrace : WordTrace (prefixWord ++ tailWord_919272) baseStart_919272 baseEnd_919272 := by
    simpa [prefixWord, tailWord_919272, baseEnd_919272] using wordTrace_append hprefix tailTrace_919272
  have hstable : (prefixWord ++ tailWord_919272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919272).length < 2 ^ (prefixWord ++ tailWord_919272).sum := by decide
  have hdescent : baseEnd_919272 < baseStart_919272 := by decide
  rcases family_descends (prefixWord ++ tailWord_919272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919279 : List Nat := [1, 1, 2, 1, 5, 1, 5, 1, 2, 4]
def baseStart_919279 : Nat := 118140960795 + 919279 * 2 ^ 59
def prefixEnd_919279 : Nat := 4983230072969 + 3 ^ 40 * 919279 * 2
def baseEnd_919279 : Nat := 157343994194871350128273

theorem tailTrace_919279 : CollatzResearch.WordTrace tailWord_919279 prefixEnd_919279 157343994194871350128273 := by
  unfold tailWord_919279
  simp only [CollatzResearch.WordTrace]
  refine ⟨33528859636616658198872891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22352573091077772132581927 33528859636616658198872891)
  ·
    refine ⟨50293289454924987298309337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33528859636616658198872891 50293289454924987298309337)
    ·
      refine ⟨37719967091193740473732003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50293289454924987298309337 37719967091193740473732003)
      ·
        refine ⟨56579950636790610710598005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37719967091193740473732003 56579950636790610710598005)
        ·
          refine ⟨5304370372199119754118563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56579950636790610710598005 5304370372199119754118563)
          ·
            refine ⟨7956555558298679631177845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5304370372199119754118563 7956555558298679631177845)
            ·
              refine ⟨745927083590501215422923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7956555558298679631177845 745927083590501215422923)
              ·
                refine ⟨1118890625385751823134385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 745927083590501215422923 1118890625385751823134385)
                ·
                  refine ⟨839167969039313867350789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1118890625385751823134385 839167969039313867350789)
                  ·
                    refine ⟨157343994194871350128273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 839167969039313867350789 157343994194871350128273)
                    ·
                      rfl

theorem cell23_919279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 2, 4].length) (baseStart_919279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919279 prefixEnd_919279 := by exact prefixLift 919279
  have htrace : WordTrace (prefixWord ++ tailWord_919279) baseStart_919279 baseEnd_919279 := by
    simpa [prefixWord, tailWord_919279, baseEnd_919279] using wordTrace_append hprefix tailTrace_919279
  have hstable : (prefixWord ++ tailWord_919279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919279).length < 2 ^ (prefixWord ++ tailWord_919279).sum := by decide
  have hdescent : baseEnd_919279 < baseStart_919279 := by decide
  rcases family_descends (prefixWord ++ tailWord_919279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919286 : List Nat := [5, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2]
def baseStart_919286 : Nat := 118140960795 + 919286 * 2 ^ 59
def prefixEnd_919286 : Nat := 4983230072969 + 3 ^ 40 * 919286 * 2
def baseEnd_919286 : Nat := 472035576949195522997287

theorem tailTrace_919286 : CollatzResearch.WordTrace tailWord_919286 prefixEnd_919286 472035576949195522997287 := by
  unfold tailWord_919286
  simp only [CollatzResearch.WordTrace]
  refine ⟨2095569684224456149648607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22352743298394198929585141 2095569684224456149648607)
  ·
    refine ⟨3143354526336684224472911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2095569684224456149648607 3143354526336684224472911)
    ·
      refine ⟨4715031789505026336709367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3143354526336684224472911 4715031789505026336709367)
      ·
        refine ⟨7072547684257539505064051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4715031789505026336709367 7072547684257539505064051)
        ·
          refine ⟨10608821526386309257596077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7072547684257539505064051 10608821526386309257596077)
          ·
            refine ⟨3978308072394865971598529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10608821526386309257596077 3978308072394865971598529)
            ·
              refine ⟨2983731054296149478698897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3978308072394865971598529 2983731054296149478698897)
              ·
                refine ⟨2237798290722112109024173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2983731054296149478698897 2237798290722112109024173)
                ·
                  refine ⟨839174359020792040884065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2237798290722112109024173 839174359020792040884065)
                  ·
                    refine ⟨629380769265594030663049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 839174359020792040884065 629380769265594030663049)
                    ·
                      refine ⟨472035576949195522997287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 629380769265594030663049 472035576949195522997287)
                      ·
                        rfl

theorem cell23_919286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_919286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919286 prefixEnd_919286 := by exact prefixLift 919286
  have htrace : WordTrace (prefixWord ++ tailWord_919286) baseStart_919286 baseEnd_919286 := by
    simpa [prefixWord, tailWord_919286, baseEnd_919286] using wordTrace_append hprefix tailTrace_919286
  have hstable : (prefixWord ++ tailWord_919286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919286).length < 2 ^ (prefixWord ++ tailWord_919286).sum := by decide
  have hdescent : baseEnd_919286 < baseStart_919286 := by decide
  rcases family_descends (prefixWord ++ tailWord_919286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919319 : List Nat := [1, 1, 3, 4, 2, 1, 2, 1, 4, 1, 3]
def baseStart_919319 : Nat := 118140960795 + 919319 * 2 ^ 59
def prefixEnd_919319 : Nat := 4983230072969 + 3 ^ 40 * 919319 * 2
def baseEnd_919319 : Nat := 472052521810793893884635

theorem tailTrace_919319 : CollatzResearch.WordTrace tailWord_919319 prefixEnd_919319 472052521810793893884635 := by
  unfold tailWord_919319
  simp only [CollatzResearch.WordTrace]
  refine ⟨33530318556471745030329011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22353545704314496686886007 33530318556471745030329011)
  ·
    refine ⟨50295477834707617545493517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33530318556471745030329011 50295477834707617545493517)
    ·
      refine ⟨18860804188015356579560069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50295477834707617545493517 18860804188015356579560069)
      ·
        refine ⟨3536400785252879358667513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18860804188015356579560069 3536400785252879358667513)
        ·
          refine ⟨2652300588939659519000635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3536400785252879358667513 2652300588939659519000635)
          ·
            refine ⟨3978450883409489278500953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2652300588939659519000635 3978450883409489278500953)
            ·
              refine ⟨2983838162557116958875715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3978450883409489278500953 2983838162557116958875715)
              ·
                refine ⟨4475757243835675438313573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2983838162557116958875715 4475757243835675438313573)
                ·
                  refine ⟨839204483219189144683795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4475757243835675438313573 839204483219189144683795)
                  ·
                    refine ⟨1258806724828783717025693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 839204483219189144683795 1258806724828783717025693)
                    ·
                      refine ⟨472052521810793893884635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1258806724828783717025693 472052521810793893884635)
                      ·
                        rfl

theorem cell23_919319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_919319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919319 prefixEnd_919319 := by exact prefixLift 919319
  have htrace : WordTrace (prefixWord ++ tailWord_919319) baseStart_919319 baseEnd_919319 := by
    simpa [prefixWord, tailWord_919319, baseEnd_919319] using wordTrace_append hprefix tailTrace_919319
  have hstable : (prefixWord ++ tailWord_919319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919319).length < 2 ^ (prefixWord ++ tailWord_919319).sum := by decide
  have hdescent : baseEnd_919319 < baseStart_919319 := by decide
  rcases family_descends (prefixWord ++ tailWord_919319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919326 : List Nat := [4, 3, 2, 2, 1, 1, 2, 8]
def baseStart_919326 : Nat := 118140960795 + 919326 * 2 ^ 59
def prefixEnd_919326 : Nat := 4983230072969 + 3 ^ 40 * 919326 * 2
def baseEnd_919326 : Nat := 17483559858347235796189

theorem tailTrace_919326 : CollatzResearch.WordTrace tailWord_919326 prefixEnd_919326 17483559858347235796189 := by
  unfold tailWord_919326
  simp only [CollatzResearch.WordTrace]
  refine ⟨4191321733430798153229229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22353715911630923483889221 4191321733430798153229229)
  ·
    refine ⟨1571745650036549307460961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4191321733430798153229229 1571745650036549307460961)
    ·
      refine ⟨1178809237527411980595721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1571745650036549307460961 1178809237527411980595721)
      ·
        refine ⟨884106928145558985446791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1178809237527411980595721 884106928145558985446791)
        ·
          refine ⟨1326160392218338478170187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 884106928145558985446791 1326160392218338478170187)
          ·
            refine ⟨1989240588327507717255281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1326160392218338478170187 1989240588327507717255281)
            ·
              refine ⟨1491930441245630787941461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1989240588327507717255281 1491930441245630787941461)
              ·
                refine ⟨17483559858347235796189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1491930441245630787941461 17483559858347235796189)
                ·
                  rfl

theorem cell23_919326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 8].length) (baseStart_919326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919326 prefixEnd_919326 := by exact prefixLift 919326
  have htrace : WordTrace (prefixWord ++ tailWord_919326) baseStart_919326 baseEnd_919326 := by
    simpa [prefixWord, tailWord_919326, baseEnd_919326] using wordTrace_append hprefix tailTrace_919326
  have hstable : (prefixWord ++ tailWord_919326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919326).length < 2 ^ (prefixWord ++ tailWord_919326).sum := by decide
  have hdescent : baseEnd_919326 < baseStart_919326 := by decide
  rcases family_descends (prefixWord ++ tailWord_919326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919336 : List Nat := [2, 1, 5, 1, 1, 3, 1, 3, 2, 1, 3]
def baseStart_919336 : Nat := 118140960795 + 919336 * 2 ^ 59
def prefixEnd_919336 : Nat := 4983230072969 + 3 ^ 40 * 919336 * 2
def baseEnd_919336 : Nat := 472061250981920327372057

theorem tailTrace_919336 : CollatzResearch.WordTrace tailWord_919336 prefixEnd_919336 472061250981920327372057 := by
  unfold tailWord_919336
  simp only [CollatzResearch.WordTrace]
  refine ⟨16765469298705078466848931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22353959064940104622465241 16765469298705078466848931)
  ·
    refine ⟨25148203948057617700273397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16765469298705078466848931 25148203948057617700273397)
    ·
      refine ⟨2357644120130401659400631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25148203948057617700273397 2357644120130401659400631)
      ·
        refine ⟨3536466180195602489100947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2357644120130401659400631 3536466180195602489100947)
        ·
          refine ⟨5304699270293403733651421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3536466180195602489100947 5304699270293403733651421)
          ·
            refine ⟨1989262226360026400119283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5304699270293403733651421 1989262226360026400119283)
            ·
              refine ⟨2983893339540039600178925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1989262226360026400119283 2983893339540039600178925)
              ·
                refine ⟨1118960002327514850067097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2983893339540039600178925 1118960002327514850067097)
                ·
                  refine ⟨839220001745636137550323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1118960002327514850067097 839220001745636137550323)
                  ·
                    refine ⟨1258830002618454206325485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 839220001745636137550323 1258830002618454206325485)
                    ·
                      refine ⟨472061250981920327372057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1258830002618454206325485 472061250981920327372057)
                      ·
                        rfl

theorem cell23_919336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_919336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919336 prefixEnd_919336 := by exact prefixLift 919336
  have htrace : WordTrace (prefixWord ++ tailWord_919336) baseStart_919336 baseEnd_919336 := by
    simpa [prefixWord, tailWord_919336, baseEnd_919336] using wordTrace_append hprefix tailTrace_919336
  have hstable : (prefixWord ++ tailWord_919336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919336).length < 2 ^ (prefixWord ++ tailWord_919336).sum := by decide
  have hdescent : baseEnd_919336 < baseStart_919336 := by decide
  rcases family_descends (prefixWord ++ tailWord_919336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919346 : List Nat := [3, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2]
def baseStart_919346 : Nat := 118140960795 + 919346 * 2 ^ 59
def prefixEnd_919346 : Nat := 4983230072969 + 3 ^ 40 * 919346 * 2
def baseEnd_919346 : Nat := 472066385788465288247011

theorem tailTrace_919346 : CollatzResearch.WordTrace tailWord_919346 prefixEnd_919346 472066385788465288247011 := by
  unfold tailWord_919346
  simp only [CollatzResearch.WordTrace]
  refine ⟨8382825831843482160390473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22354202218249285761041261 8382825831843482160390473)
  ·
    refine ⟨6287119373882611620292855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8382825831843482160390473 6287119373882611620292855)
    ·
      refine ⟨9430679060823917430439283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6287119373882611620292855 9430679060823917430439283)
      ·
        refine ⟨14146018591235876145658925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9430679060823917430439283 14146018591235876145658925)
        ·
          refine ⟨5304756971713453554622097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14146018591235876145658925 5304756971713453554622097)
          ·
            refine ⟨3978567728785090165966573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5304756971713453554622097 3978567728785090165966573)
            ·
              refine ⟨1491962898294408812237465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3978567728785090165966573 1491962898294408812237465)
              ·
                refine ⟨1118972173720806609178099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1491962898294408812237465 1118972173720806609178099)
                ·
                  refine ⟨1678458260581209913767149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1118972173720806609178099 1678458260581209913767149)
                  ·
                    refine ⟨629421847717953717662681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1678458260581209913767149 629421847717953717662681)
                    ·
                      refine ⟨472066385788465288247011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 629421847717953717662681 472066385788465288247011)
                      ·
                        rfl

theorem cell23_919346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2].length) (baseStart_919346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919346 prefixEnd_919346 := by exact prefixLift 919346
  have htrace : WordTrace (prefixWord ++ tailWord_919346) baseStart_919346 baseEnd_919346 := by
    simpa [prefixWord, tailWord_919346, baseEnd_919346] using wordTrace_append hprefix tailTrace_919346
  have hstable : (prefixWord ++ tailWord_919346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919346).length < 2 ^ (prefixWord ++ tailWord_919346).sum := by decide
  have hdescent : baseEnd_919346 < baseStart_919346 := by decide
  rcases family_descends (prefixWord ++ tailWord_919346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919392 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 3]
def baseStart_919392 : Nat := 118140960795 + 919392 * 2 ^ 59
def prefixEnd_919392 : Nat := 4983230072969 + 3 ^ 40 * 919392 * 2
def baseEnd_919392 : Nat := 472090005898572108271799

theorem tailTrace_919392 : CollatzResearch.WordTrace tailWord_919392 prefixEnd_919392 472090005898572108271799 := by
  unfold tailWord_919392
  simp only [CollatzResearch.WordTrace]
  refine ⟨16766490542603639248868215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22355320723471518998490953 16766490542603639248868215)
  ·
    refine ⟨25149735813905458873302323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16766490542603639248868215 25149735813905458873302323)
    ·
      refine ⟨37724603720858188309953485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25149735813905458873302323 37724603720858188309953485)
      ·
        refine ⟨14146726395321820616232557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37724603720858188309953485 14146726395321820616232557)
        ·
          refine ⟨5305022398245682731087209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14146726395321820616232557 5305022398245682731087209)
          ·
            refine ⟨3978766798684262048315407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5305022398245682731087209 3978766798684262048315407)
            ·
              refine ⟨5968150198026393072473111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3978766798684262048315407 5968150198026393072473111)
              ·
                refine ⟨8952225297039589608709667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5968150198026393072473111 8952225297039589608709667)
                ·
                  refine ⟨13428337945559384413064501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8952225297039589608709667 13428337945559384413064501)
                  ·
                    refine ⟨1258906682396192288724797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13428337945559384413064501 1258906682396192288724797)
                    ·
                      refine ⟨472090005898572108271799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1258906682396192288724797 472090005898572108271799)
                      ·
                        rfl

theorem cell23_919392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_919392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919392 prefixEnd_919392 := by exact prefixLift 919392
  have htrace : WordTrace (prefixWord ++ tailWord_919392) baseStart_919392 baseEnd_919392 := by
    simpa [prefixWord, tailWord_919392, baseEnd_919392] using wordTrace_append hprefix tailTrace_919392
  have hstable : (prefixWord ++ tailWord_919392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919392).length < 2 ^ (prefixWord ++ tailWord_919392).sum := by decide
  have hdescent : baseEnd_919392 < baseStart_919392 := by decide
  rcases family_descends (prefixWord ++ tailWord_919392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919449 : List Nat := [1, 2, 1, 2, 1, 3, 4, 1, 2, 4, 2]
def baseStart_919449 : Nat := 118140960795 + 919449 * 2 ^ 59
def prefixEnd_919449 : Nat := 4983230072969 + 3 ^ 40 * 919449 * 2
def baseEnd_919449 : Nat := 472119274295878385259037

theorem tailTrace_919449 : CollatzResearch.WordTrace tailWord_919449 prefixEnd_919449 472119274295878385259037 := by
  unfold tailWord_919449
  simp only [CollatzResearch.WordTrace]
  refine ⟨33535060046000777232561401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22356706697333851488374267 33535060046000777232561401)
  ·
    refine ⟨25151295034500582924421051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33535060046000777232561401 25151295034500582924421051)
    ·
      refine ⟨37726942551750874386631577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25151295034500582924421051 37726942551750874386631577)
      ·
        refine ⟨28295206913813155789973683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37726942551750874386631577 28295206913813155789973683)
        ·
          refine ⟨42442810370719733684960525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28295206913813155789973683 42442810370719733684960525)
          ·
            refine ⟨15916053889019900131860197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42442810370719733684960525 15916053889019900131860197)
            ·
              refine ⟨2984260104191231274723787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15916053889019900131860197 2984260104191231274723787)
              ·
                refine ⟨4476390156286846912085681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2984260104191231274723787 4476390156286846912085681)
                ·
                  refine ⟨3357292617215135184064261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4476390156286846912085681 3357292617215135184064261)
                  ·
                    refine ⟨629492365727837847012049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3357292617215135184064261 629492365727837847012049)
                    ·
                      refine ⟨472119274295878385259037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 629492365727837847012049 472119274295878385259037)
                      ·
                        rfl

theorem cell23_919449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 4, 2].length) (baseStart_919449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919449 prefixEnd_919449 := by exact prefixLift 919449
  have htrace : WordTrace (prefixWord ++ tailWord_919449) baseStart_919449 baseEnd_919449 := by
    simpa [prefixWord, tailWord_919449, baseEnd_919449] using wordTrace_append hprefix tailTrace_919449
  have hstable : (prefixWord ++ tailWord_919449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919449).length < 2 ^ (prefixWord ++ tailWord_919449).sum := by decide
  have hdescent : baseEnd_919449 < baseStart_919449 := by decide
  rcases family_descends (prefixWord ++ tailWord_919449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919486 : List Nat := [4, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3]
def baseStart_919486 : Nat := 118140960795 + 919486 * 2 ^ 59
def prefixEnd_919486 : Nat := 4983230072969 + 3 ^ 40 * 919486 * 2
def baseEnd_919486 : Nat := 472138273080094740496367

theorem tailTrace_919486 : CollatzResearch.WordTrace tailWord_919486 prefixEnd_919486 472138273080094740496367 := by
  unfold tailWord_919486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4192051193358341568957289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22357606364577821701105541 4192051193358341568957289)
  ·
    refine ⟨3144038395018756176717967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4192051193358341568957289 3144038395018756176717967)
    ·
      refine ⟨4716057592528134265076951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3144038395018756176717967 4716057592528134265076951)
      ·
        refine ⟨7074086388792201397615427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4716057592528134265076951 7074086388792201397615427)
        ·
          refine ⟨10611129583188302096423141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7074086388792201397615427 10611129583188302096423141)
          ·
            refine ⟨1989586796847806643079339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10611129583188302096423141 1989586796847806643079339)
            ·
              refine ⟨2984380195271709964619009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1989586796847806643079339 2984380195271709964619009)
              ·
                refine ⟨2238285146453782473464257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2984380195271709964619009 2238285146453782473464257)
                ·
                  refine ⟨1678713859840336855098193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2238285146453782473464257 1678713859840336855098193)
                  ·
                    refine ⟨1259035394880252641323645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1678713859840336855098193 1259035394880252641323645)
                    ·
                      refine ⟨472138273080094740496367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1259035394880252641323645 472138273080094740496367)
                      ·
                        rfl

theorem cell23_919486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_919486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919486 prefixEnd_919486 := by exact prefixLift 919486
  have htrace : WordTrace (prefixWord ++ tailWord_919486) baseStart_919486 baseEnd_919486 := by
    simpa [prefixWord, tailWord_919486, baseEnd_919486] using wordTrace_append hprefix tailTrace_919486
  have hstable : (prefixWord ++ tailWord_919486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919486).length < 2 ^ (prefixWord ++ tailWord_919486).sum := by decide
  have hdescent : baseEnd_919486 < baseStart_919486 := by decide
  rcases family_descends (prefixWord ++ tailWord_919486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919506 : List Nat := [3, 2, 2, 3, 2, 1, 1, 3, 6]
def baseStart_919506 : Nat := 118140960795 + 919506 * 2 ^ 59
def prefixEnd_919506 : Nat := 4983230072969 + 3 ^ 40 * 919506 * 2
def baseEnd_919506 : Nat := 52460949188131629138475

theorem tailTrace_919506 : CollatzResearch.WordTrace tailWord_919506 prefixEnd_919506 52460949188131629138475 := by
  unfold tailWord_919506
  simp only [CollatzResearch.WordTrace]
  refine ⟨8384284751698568991846593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22358092671196183978257581 8384284751698568991846593)
  ·
    refine ⟨6288213563773926743884945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8384284751698568991846593 6288213563773926743884945)
    ·
      refine ⟨4716160172830445057913709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6288213563773926743884945 4716160172830445057913709)
      ·
        refine ⟨1768560064811416896717641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4716160172830445057913709 1768560064811416896717641)
        ·
          refine ⟨1326420048608562672538231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1768560064811416896717641 1326420048608562672538231)
          ·
            refine ⟨1989630072912844008807347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1326420048608562672538231 1989630072912844008807347)
            ·
              refine ⟨2984445109369266013211021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1989630072912844008807347 2984445109369266013211021)
              ·
                refine ⟨1119166916013474754954133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2984445109369266013211021 1119166916013474754954133)
                ·
                  refine ⟨52460949188131629138475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1119166916013474754954133 52460949188131629138475)
                  ·
                    rfl

theorem cell23_919506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 6].length) (baseStart_919506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919506 prefixEnd_919506 := by exact prefixLift 919506
  have htrace : WordTrace (prefixWord ++ tailWord_919506) baseStart_919506 baseEnd_919506 := by
    simpa [prefixWord, tailWord_919506, baseEnd_919506] using wordTrace_append hprefix tailTrace_919506
  have hstable : (prefixWord ++ tailWord_919506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919506).length < 2 ^ (prefixWord ++ tailWord_919506).sum := by decide
  have hdescent : baseEnd_919506 < baseStart_919506 := by decide
  rcases family_descends (prefixWord ++ tailWord_919506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919519 : List Nat := [1, 1, 2, 3, 4, 2, 1, 1, 3, 5]
def baseStart_919519 : Nat := 118140960795 + 919519 * 2 ^ 59
def prefixEnd_919519 : Nat := 4983230072969 + 3 ^ 40 * 919519 * 2
def baseEnd_919519 : Nat := 157385072647231037127905

theorem tailTrace_919519 : CollatzResearch.WordTrace tailWord_919519 prefixEnd_919519 157385072647231037127905 := by
  unfold tailWord_919519
  simp only [CollatzResearch.WordTrace]
  refine ⟨33537613155747179187609611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22358408770498119458406407 33537613155747179187609611)
  ·
    refine ⟨50306419733620768781414417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33537613155747179187609611 50306419733620768781414417)
    ·
      refine ⟨37729814800215576586060813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50306419733620768781414417 37729814800215576586060813)
      ·
        refine ⟨14148680550080841219772805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37729814800215576586060813 14148680550080841219772805)
        ·
          refine ⟨2652877603140157728707401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14148680550080841219772805 2652877603140157728707401)
          ·
            refine ⟨1989658202355118296530551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2652877603140157728707401 1989658202355118296530551)
            ·
              refine ⟨2984487303532677444795827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1989658202355118296530551 2984487303532677444795827)
              ·
                refine ⟨4476730955299016167193741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2984487303532677444795827 4476730955299016167193741)
                ·
                  refine ⟨1678774108237131062697653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4476730955299016167193741 1678774108237131062697653)
                  ·
                    refine ⟨157385072647231037127905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1678774108237131062697653 157385072647231037127905)
                    ·
                      rfl

theorem cell23_919519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 5].length) (baseStart_919519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919519 prefixEnd_919519 := by exact prefixLift 919519
  have htrace : WordTrace (prefixWord ++ tailWord_919519) baseStart_919519 baseEnd_919519 := by
    simpa [prefixWord, tailWord_919519, baseEnd_919519] using wordTrace_append hprefix tailTrace_919519
  have hstable : (prefixWord ++ tailWord_919519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919519).length < 2 ^ (prefixWord ++ tailWord_919519).sum := by decide
  have hdescent : baseEnd_919519 < baseStart_919519 := by decide
  rcases family_descends (prefixWord ++ tailWord_919519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919539 : List Nat := [1, 1, 1, 2, 2, 2, 1, 7, 1, 1, 4]
def baseStart_919539 : Nat := 118140960795 + 919539 * 2 ^ 59
def prefixEnd_919539 : Nat := 4983230072969 + 3 ^ 40 * 919539 * 2
def baseEnd_919539 : Nat := 472165487554783033133623

theorem tailTrace_919539 : CollatzResearch.WordTrace tailWord_919539 prefixEnd_919539 472165487554783033133623 := by
  unfold tailWord_919539
  simp only [CollatzResearch.WordTrace]
  refine ⟨33538342615674722603337671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22358895077116481735558447 33538342615674722603337671)
  ·
    refine ⟨50307513923512083905006507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33538342615674722603337671 50307513923512083905006507)
    ·
      refine ⟨75461270885268125857509761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50307513923512083905006507 75461270885268125857509761)
      ·
        refine ⟨56595953163951094393132321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75461270885268125857509761 56595953163951094393132321)
        ·
          refine ⟨42446964872963320794849241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56595953163951094393132321 42446964872963320794849241)
          ·
            refine ⟨31835223654722490596136931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42446964872963320794849241 31835223654722490596136931)
            ·
              refine ⟨47752835482083735894205397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31835223654722490596136931 47752835482083735894205397)
              ·
                refine ⟨1119207081611337560020439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 47752835482083735894205397 1119207081611337560020439)
                ·
                  refine ⟨1678810622417006340030659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1119207081611337560020439 1678810622417006340030659)
                  ·
                    refine ⟨2518215933625509510045989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1678810622417006340030659 2518215933625509510045989)
                    ·
                      refine ⟨472165487554783033133623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2518215933625509510045989 472165487554783033133623)
                      ·
                        rfl

theorem cell23_919539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 1, 4].length) (baseStart_919539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919539 prefixEnd_919539 := by exact prefixLift 919539
  have htrace : WordTrace (prefixWord ++ tailWord_919539) baseStart_919539 baseEnd_919539 := by
    simpa [prefixWord, tailWord_919539, baseEnd_919539] using wordTrace_append hprefix tailTrace_919539
  have hstable : (prefixWord ++ tailWord_919539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919539).length < 2 ^ (prefixWord ++ tailWord_919539).sum := by decide
  have hdescent : baseEnd_919539 < baseStart_919539 := by decide
  rcases family_descends (prefixWord ++ tailWord_919539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919549 : List Nat := [1, 4, 1, 1, 1, 2, 2, 3, 4, 4]
def baseStart_919549 : Nat := 118140960795 + 919549 * 2 ^ 59
def prefixEnd_919549 : Nat := 4983230072969 + 3 ^ 40 * 919549 * 2
def baseEnd_919549 : Nat := 157390207453775998002859

theorem tailTrace_919549 : CollatzResearch.WordTrace tailWord_919549 prefixEnd_919549 157390207453775998002859 := by
  unfold tailWord_919549
  simp only [CollatzResearch.WordTrace]
  refine ⟨33538707345638494311201701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22359138230425662874134467 33538707345638494311201701)
  ·
    refine ⟨6288507627307217683350319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33538707345638494311201701 6288507627307217683350319)
    ·
      refine ⟨9432761440960826525025479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6288507627307217683350319 9432761440960826525025479)
      ·
        refine ⟨14149142161441239787538219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9432761440960826525025479 14149142161441239787538219)
        ·
          refine ⟨21223713242161859681307329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14149142161441239787538219 21223713242161859681307329)
          ·
            refine ⟨15917784931621394760980497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21223713242161859681307329 15917784931621394760980497)
            ·
              refine ⟨11938338698716046070735373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15917784931621394760980497 11938338698716046070735373)
              ·
                refine ⟨4476877012018517276525765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11938338698716046070735373 4476877012018517276525765)
                ·
                  refine ⟨839414439753471989348581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4476877012018517276525765 839414439753471989348581)
                  ·
                    refine ⟨157390207453775998002859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 839414439753471989348581 157390207453775998002859)
                    ·
                      rfl

theorem cell23_919549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_919549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919549 prefixEnd_919549 := by exact prefixLift 919549
  have htrace : WordTrace (prefixWord ++ tailWord_919549) baseStart_919549 baseEnd_919549 := by
    simpa [prefixWord, tailWord_919549, baseEnd_919549] using wordTrace_append hprefix tailTrace_919549
  have hstable : (prefixWord ++ tailWord_919549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919549).length < 2 ^ (prefixWord ++ tailWord_919549).sum := by decide
  have hdescent : baseEnd_919549 < baseStart_919549 := by decide
  rcases family_descends (prefixWord ++ tailWord_919549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919552 : List Nat := [2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 6]
def baseStart_919552 : Nat := 118140960795 + 919552 * 2 ^ 59
def prefixEnd_919552 : Nat := 4983230072969 + 3 ^ 40 * 919552 * 2
def baseEnd_919552 : Nat := 472172162803291482271063

theorem tailTrace_919552 : CollatzResearch.WordTrace tailWord_919552 prefixEnd_919552 472172162803291482271063 := by
  unfold tailWord_919552
  simp only [CollatzResearch.WordTrace]
  refine ⟨16769408382313812911780455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22359211176418417215707273 16769408382313812911780455)
  ·
    refine ⟨25154112573470719367670683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16769408382313812911780455 25154112573470719367670683)
    ·
      refine ⟨37731168860206079051506025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25154112573470719367670683 37731168860206079051506025)
      ·
        refine ⟨28298376645154559288629519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37731168860206079051506025 28298376645154559288629519)
        ·
          refine ⟨42447564967731838932944279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28298376645154559288629519 42447564967731838932944279)
          ·
            refine ⟨63671347451597758399416419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42447564967731838932944279 63671347451597758399416419)
            ·
              refine ⟨95507021177396637599124629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63671347451597758399416419 95507021177396637599124629)
              ·
                refine ⟨4476891617690467387458967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95507021177396637599124629 4476891617690467387458967)
                ·
                  refine ⟨6715337426535701081188451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4476891617690467387458967 6715337426535701081188451)
                  ·
                    refine ⟨10073006139803551621782677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6715337426535701081188451 10073006139803551621782677)
                    ·
                      refine ⟨472172162803291482271063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10073006139803551621782677 472172162803291482271063)
                      ·
                        rfl

theorem cell23_919552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_919552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919552 prefixEnd_919552 := by exact prefixLift 919552
  have htrace : WordTrace (prefixWord ++ tailWord_919552) baseStart_919552 baseEnd_919552 := by
    simpa [prefixWord, tailWord_919552, baseEnd_919552] using wordTrace_append hprefix tailTrace_919552
  have hstable : (prefixWord ++ tailWord_919552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919552).length < 2 ^ (prefixWord ++ tailWord_919552).sum := by decide
  have hdescent : baseEnd_919552 < baseStart_919552 := by decide
  rcases family_descends (prefixWord ++ tailWord_919552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919566 : List Nat := [4, 1, 1, 2, 2, 1, 1, 5, 2, 4]
def baseStart_919566 : Nat := 118140960795 + 919566 * 2 ^ 59
def prefixEnd_919566 : Nat := 4983230072969 + 3 ^ 40 * 919566 * 2
def baseEnd_919566 : Nat := 157393117177484809165333

theorem tailTrace_919566 : CollatzResearch.WordTrace tailWord_919566 prefixEnd_919566 157393117177484809165333 := by
  unfold tailWord_919566
  simp only [CollatzResearch.WordTrace]
  refine ⟨4192415923322113276821319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22359551591051270809713701 4192415923322113276821319)
  ·
    refine ⟨6288623884983169915231979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4192415923322113276821319 6288623884983169915231979)
    ·
      refine ⟨9432935827474754872847969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6288623884983169915231979 9432935827474754872847969)
      ·
        refine ⟨7074701870606066154635977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9432935827474754872847969 7074701870606066154635977)
        ·
          refine ⟨5306026402954549615976983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7074701870606066154635977 5306026402954549615976983)
          ·
            refine ⟨7959039604431824423965475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5306026402954549615976983 7959039604431824423965475)
            ·
              refine ⟨11938559406647736635948213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7959039604431824423965475 11938559406647736635948213)
              ·
                refine ⟨1119239944373225309620145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11938559406647736635948213 1119239944373225309620145)
                ·
                  refine ⟨839429958279918982215109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1119239944373225309620145 839429958279918982215109)
                  ·
                    refine ⟨157393117177484809165333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 839429958279918982215109 157393117177484809165333)
                    ·
                      rfl

theorem cell23_919566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_919566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919566 prefixEnd_919566 := by exact prefixLift 919566
  have htrace : WordTrace (prefixWord ++ tailWord_919566) baseStart_919566 baseEnd_919566 := by
    simpa [prefixWord, tailWord_919566, baseEnd_919566] using wordTrace_append hprefix tailTrace_919566
  have hstable : (prefixWord ++ tailWord_919566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919566).length < 2 ^ (prefixWord ++ tailWord_919566).sum := by decide
  have hdescent : baseEnd_919566 < baseStart_919566 := by decide
  rcases family_descends (prefixWord ++ tailWord_919566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919576 : List Nat := [2, 1, 2, 3, 2, 1, 2, 4, 1, 2, 3]
def baseStart_919576 : Nat := 118140960795 + 919576 * 2 ^ 59
def prefixEnd_919576 : Nat := 4983230072969 + 3 ^ 40 * 919576 * 2
def baseEnd_919576 : Nat := 472184486338999388370953

theorem tailTrace_919576 : CollatzResearch.WordTrace tailWord_919576 prefixEnd_919576 472184486338999388370953 := by
  unfold tailWord_919576
  simp only [CollatzResearch.WordTrace]
  refine ⟨16769846058270338961217291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22359794744360451948289721 16769846058270338961217291)
  ·
    refine ⟨25154769087405508441825937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16769846058270338961217291 25154769087405508441825937)
    ·
      refine ⟨18866076815554131331369453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25154769087405508441825937 18866076815554131331369453)
      ·
        refine ⟨7074778805832799249263545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18866076815554131331369453 7074778805832799249263545)
        ·
          refine ⟨5306084104374599436947659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7074778805832799249263545 5306084104374599436947659)
          ·
            refine ⟨7959126156561899155421489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5306084104374599436947659 7959126156561899155421489)
            ·
              refine ⟨5969344617421424366566117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7959126156561899155421489 5969344617421424366566117)
              ·
                refine ⟨1119252115766517068731147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5969344617421424366566117 1119252115766517068731147)
                ·
                  refine ⟨1678878173649775603096721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1119252115766517068731147 1678878173649775603096721)
                  ·
                    refine ⟨1259158630237331702322541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1678878173649775603096721 1259158630237331702322541)
                    ·
                      refine ⟨472184486338999388370953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1259158630237331702322541 472184486338999388370953)
                      ·
                        rfl

theorem cell23_919576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_919576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919576 prefixEnd_919576 := by exact prefixLift 919576
  have htrace : WordTrace (prefixWord ++ tailWord_919576) baseStart_919576 baseEnd_919576 := by
    simpa [prefixWord, tailWord_919576, baseEnd_919576] using wordTrace_append hprefix tailTrace_919576
  have hstable : (prefixWord ++ tailWord_919576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919576).length < 2 ^ (prefixWord ++ tailWord_919576).sum := by decide
  have hdescent : baseEnd_919576 < baseStart_919576 := by decide
  rcases family_descends (prefixWord ++ tailWord_919576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919649 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 1, 6, 3]
def baseStart_919649 : Nat := 118140960795 + 919649 * 2 ^ 59
def prefixEnd_919649 : Nat := 4983230072969 + 3 ^ 40 * 919649 * 2
def baseEnd_919649 : Nat := 472221970426777602758117

theorem tailTrace_919649 : CollatzResearch.WordTrace tailWord_919649 prefixEnd_919649 472221970426777602758117 := by
  unfold tailWord_919649
  simp only [CollatzResearch.WordTrace]
  refine ⟨33542354645276211389842001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22361569763517474259894667 33542354645276211389842001)
  ·
    refine ⟨25156765983957158542381501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33542354645276211389842001 25156765983957158542381501)
    ·
      refine ⟨9433787243983934453393063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25156765983957158542381501 9433787243983934453393063)
      ·
        refine ⟨14150680865975901680089595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9433787243983934453393063 14150680865975901680089595)
        ·
          refine ⟨21226021298963852520134393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14150680865975901680089595 21226021298963852520134393)
          ·
            refine ⟨15919515974222889390100795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21226021298963852520134393 15919515974222889390100795)
            ·
              refine ⟨23879273961334334085151193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15919515974222889390100795 23879273961334334085151193)
              ·
                refine ⟨17909455471000750563863395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23879273961334334085151193 17909455471000750563863395)
                ·
                  refine ⟨26864183206501125845795093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17909455471000750563863395 26864183206501125845795093)
                  ·
                    refine ⟨1259258587804740274021645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26864183206501125845795093 1259258587804740274021645)
                    ·
                      refine ⟨472221970426777602758117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1259258587804740274021645 472221970426777602758117)
                      ·
                        rfl

theorem cell23_919649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_919649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919649 prefixEnd_919649 := by exact prefixLift 919649
  have htrace : WordTrace (prefixWord ++ tailWord_919649) baseStart_919649 baseEnd_919649 := by
    simpa [prefixWord, tailWord_919649, baseEnd_919649] using wordTrace_append hprefix tailTrace_919649
  have hstable : (prefixWord ++ tailWord_919649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919649).length < 2 ^ (prefixWord ++ tailWord_919649).sum := by decide
  have hdescent : baseEnd_919649 < baseStart_919649 := by decide
  rcases family_descends (prefixWord ++ tailWord_919649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919663 : List Nat := [1, 1, 2, 1, 3, 4, 2, 1, 4, 2, 2]
def baseStart_919663 : Nat := 118140960795 + 919663 * 2 ^ 59
def prefixEnd_919663 : Nat := 4983230072969 + 3 ^ 40 * 919663 * 2
def baseEnd_919663 : Nat := 472229159155940547983053

theorem tailTrace_919663 : CollatzResearch.WordTrace tailWord_919663 prefixEnd_919663 472229159155940547983053 := by
  unfold tailWord_919663
  simp only [CollatzResearch.WordTrace]
  refine ⟨33542865267225491780851643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22361910178150327853901095 33542865267225491780851643)
  ·
    refine ⟨50314297900838237671277465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33542865267225491780851643 50314297900838237671277465)
    ·
      refine ⟨37735723425628678253458099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50314297900838237671277465 37735723425628678253458099)
      ·
        refine ⟨56603585138443017380187149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37735723425628678253458099 56603585138443017380187149)
        ·
          refine ⟨21226344426916131517570181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56603585138443017380187149 21226344426916131517570181)
          ·
            refine ⟨3979939580046774659544409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21226344426916131517570181 3979939580046774659544409)
            ·
              refine ⟨2984954685035080994658307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3979939580046774659544409 2984954685035080994658307)
              ·
                refine ⟨4477432027552621491987461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2984954685035080994658307 4477432027552621491987461)
                ·
                  refine ⟨839518505166116529747649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4477432027552621491987461 839518505166116529747649)
                  ·
                    refine ⟨629638878874587397310737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 839518505166116529747649 629638878874587397310737)
                    ·
                      refine ⟨472229159155940547983053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 629638878874587397310737 472229159155940547983053)
                      ·
                        rfl

theorem cell23_919663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 4, 2, 2].length) (baseStart_919663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919663 prefixEnd_919663 := by exact prefixLift 919663
  have htrace : WordTrace (prefixWord ++ tailWord_919663) baseStart_919663 baseEnd_919663 := by
    simpa [prefixWord, tailWord_919663, baseEnd_919663] using wordTrace_append hprefix tailTrace_919663
  have hstable : (prefixWord ++ tailWord_919663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919663).length < 2 ^ (prefixWord ++ tailWord_919663).sum := by decide
  have hdescent : baseEnd_919663 < baseStart_919663 := by decide
  rcases family_descends (prefixWord ++ tailWord_919663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919759 : List Nat := [1, 1, 2, 1, 1, 3, 4, 2, 8]
def baseStart_919759 : Nat := 118140960795 + 919759 * 2 ^ 59
def prefixEnd_919759 : Nat := 4983230072969 + 3 ^ 40 * 919759 * 2
def baseEnd_919759 : Nat := 52475383699863574709179

theorem tailTrace_919759 : CollatzResearch.WordTrace tailWord_919759 prefixEnd_919759 52475383699863574709179 := by
  unfold tailWord_919759
  simp only [CollatzResearch.WordTrace]
  refine ⟨33546366674877700176346331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22364244449918466784230887 33546366674877700176346331)
  ·
    refine ⟨50319550012316550264519497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33546366674877700176346331 50319550012316550264519497)
    ·
      refine ⟨37739662509237412698389623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50319550012316550264519497 37739662509237412698389623)
      ·
        refine ⟨56609493763856119047584435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37739662509237412698389623 56609493763856119047584435)
        ·
          refine ⟨84914240645784178571376653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56609493763856119047584435 84914240645784178571376653)
          ·
            refine ⟨31842840242169066964266245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84914240645784178571376653 31842840242169066964266245)
            ·
              refine ⟨5970532545406700055799921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31842840242169066964266245 5970532545406700055799921)
              ·
                refine ⟨4477899409055025041849941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5970532545406700055799921 4477899409055025041849941)
                ·
                  refine ⟨52475383699863574709179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4477899409055025041849941 52475383699863574709179)
                  ·
                    rfl

theorem cell23_919759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 8].length) (baseStart_919759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919759 prefixEnd_919759 := by exact prefixLift 919759
  have htrace : WordTrace (prefixWord ++ tailWord_919759) baseStart_919759 baseEnd_919759 := by
    simpa [prefixWord, tailWord_919759, baseEnd_919759] using wordTrace_append hprefix tailTrace_919759
  have hstable : (prefixWord ++ tailWord_919759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919759).length < 2 ^ (prefixWord ++ tailWord_919759).sum := by decide
  have hdescent : baseEnd_919759 < baseStart_919759 := by decide
  rcases family_descends (prefixWord ++ tailWord_919759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919857 : List Nat := [1, 2, 2, 3, 5, 1, 1, 2, 1, 5]
def baseStart_919857 : Nat := 118140960795 + 919857 * 2 ^ 59
def prefixEnd_919857 : Nat := 4983230072969 + 3 ^ 40 * 919857 * 2
def baseEnd_919857 : Nat := 157442924800970929652387

theorem tailTrace_919857 : CollatzResearch.WordTrace tailWord_919857 prefixEnd_919857 157442924800970929652387 := by
  unfold tailWord_919857
  simp only [CollatzResearch.WordTrace]
  refine ⟨33549941028522662913413825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22366627352348441942275883 33549941028522662913413825)
  ·
    refine ⟨25162455771391997185060369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33549941028522662913413825 25162455771391997185060369)
    ·
      refine ⟨18871841828543997888795277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25162455771391997185060369 18871841828543997888795277)
      ·
        refine ⟨7076940685703999208298229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18871841828543997888795277 7076940685703999208298229)
        ·
          refine ⟨663463189284749925777959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7076940685703999208298229 663463189284749925777959)
          ·
            refine ⟨995194783927124888666939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 663463189284749925777959 995194783927124888666939)
            ·
              refine ⟨1492792175890687333000409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 995194783927124888666939 1492792175890687333000409)
              ·
                refine ⟨1119594131918015499750307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1492792175890687333000409 1119594131918015499750307)
                ·
                  refine ⟨1679391197877023249625461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1119594131918015499750307 1679391197877023249625461)
                  ·
                    refine ⟨157442924800970929652387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1679391197877023249625461 157442924800970929652387)
                    ·
                      rfl

theorem cell23_919857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 1, 5].length) (baseStart_919857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919857 prefixEnd_919857 := by exact prefixLift 919857
  have htrace : WordTrace (prefixWord ++ tailWord_919857) baseStart_919857 baseEnd_919857 := by
    simpa [prefixWord, tailWord_919857, baseEnd_919857] using wordTrace_append hprefix tailTrace_919857
  have hstable : (prefixWord ++ tailWord_919857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919857).length < 2 ^ (prefixWord ++ tailWord_919857).sum := by decide
  have hdescent : baseEnd_919857 < baseStart_919857 := by decide
  rcases family_descends (prefixWord ++ tailWord_919857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919860 : List Nat := [2, 5, 1, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_919860 : Nat := 118140960795 + 919860 * 2 ^ 59
def prefixEnd_919860 : Nat := 4983230072969 + 3 ^ 40 * 919860 * 2
def baseEnd_919860 : Nat := 472330314844876277219647

theorem tailTrace_919860 : CollatzResearch.WordTrace tailWord_919860 prefixEnd_919860 472330314844876277219647 := by
  unfold tailWord_919860
  simp only [CollatzResearch.WordTrace]
  refine ⟨16775025223755897212886517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22366700298341196283848689 16775025223755897212886517)
  ·
    refine ⟨1572658614727115363708111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16775025223755897212886517 1572658614727115363708111)
    ·
      refine ⟨2358987922090673045562167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1572658614727115363708111 2358987922090673045562167)
      ·
        refine ⟨3538481883136009568343251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2358987922090673045562167 3538481883136009568343251)
        ·
          refine ⟨5307722824704014352514877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3538481883136009568343251 5307722824704014352514877)
          ·
            refine ⟨1990396059264005382193079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5307722824704014352514877 1990396059264005382193079)
            ·
              refine ⟨2985594088896008073289619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1990396059264005382193079 2985594088896008073289619)
              ·
                refine ⟨4478391133344012109934429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2985594088896008073289619 4478391133344012109934429)
                ·
                  refine ⟨1679396675004004541225411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4478391133344012109934429 1679396675004004541225411)
                  ·
                    refine ⟨2519095012506006811838117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1679396675004004541225411 2519095012506006811838117)
                    ·
                      refine ⟨472330314844876277219647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2519095012506006811838117 472330314844876277219647)
                      ·
                        rfl

theorem cell23_919860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_919860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919860 prefixEnd_919860 := by exact prefixLift 919860
  have htrace : WordTrace (prefixWord ++ tailWord_919860) baseStart_919860 baseEnd_919860 := by
    simpa [prefixWord, tailWord_919860, baseEnd_919860] using wordTrace_append hprefix tailTrace_919860
  have hstable : (prefixWord ++ tailWord_919860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919860).length < 2 ^ (prefixWord ++ tailWord_919860).sum := by decide
  have hdescent : baseEnd_919860 < baseStart_919860 := by decide
  rcases family_descends (prefixWord ++ tailWord_919860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919866 : List Nat := [3, 1, 1, 1, 4, 2, 2, 9]
def baseStart_919866 : Nat := 118140960795 + 919866 * 2 ^ 59
def prefixEnd_919866 : Nat := 4983230072969 + 3 ^ 40 * 919866 * 2
def baseEnd_919866 : Nat := 17493829471437157546097

theorem tailTrace_919866 : CollatzResearch.WordTrace tailWord_919866 prefixEnd_919866 17493829471437157546097 := by
  unfold tailWord_919866
  simp only [CollatzResearch.WordTrace]
  refine ⟨8387567321372514362622863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22366846190326704966994301 8387567321372514362622863)
  ·
    refine ⟨12581350982058771543934295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8387567321372514362622863 12581350982058771543934295)
    ·
      refine ⟨18872026473088157315901443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12581350982058771543934295 18872026473088157315901443)
      ·
        refine ⟨28308039709632235973852165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18872026473088157315901443 28308039709632235973852165)
        ·
          refine ⟨5307757445556044245097281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28308039709632235973852165 5307757445556044245097281)
          ·
            refine ⟨3980818084167033183822961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5307757445556044245097281 3980818084167033183822961)
            ·
              refine ⟨2985613563125274887867221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3980818084167033183822961 2985613563125274887867221)
              ·
                refine ⟨17493829471437157546097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2985613563125274887867221 17493829471437157546097)
                ·
                  rfl

theorem cell23_919866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 9].length) (baseStart_919866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919866 prefixEnd_919866 := by exact prefixLift 919866
  have htrace : WordTrace (prefixWord ++ tailWord_919866) baseStart_919866 baseEnd_919866 := by
    simpa [prefixWord, tailWord_919866, baseEnd_919866] using wordTrace_append hprefix tailTrace_919866
  have hstable : (prefixWord ++ tailWord_919866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919866).length < 2 ^ (prefixWord ++ tailWord_919866).sum := by decide
  have hdescent : baseEnd_919866 < baseStart_919866 := by decide
  rcases family_descends (prefixWord ++ tailWord_919866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919886 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6]
def baseStart_919886 : Nat := 118140960795 + 919886 * 2 ^ 59
def prefixEnd_919886 : Nat := 4983230072969 + 3 ^ 40 * 919886 * 2
def baseEnd_919886 : Nat := 472343665341893175494527

theorem tailTrace_919886 : CollatzResearch.WordTrace tailWord_919886 prefixEnd_919886 472343665341893175494527 := by
  unfold tailWord_919886
  simp only [CollatzResearch.WordTrace]
  refine ⟨4193874843177200108277439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22367332496945067244146341 4193874843177200108277439)
  ·
    refine ⟨6290812264765800162416159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4193874843177200108277439 6290812264765800162416159)
    ·
      refine ⟨9436218397148700243624239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6290812264765800162416159 9436218397148700243624239)
      ·
        refine ⟨14154327595723050365436359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9436218397148700243624239 14154327595723050365436359)
        ·
          refine ⟨21231491393584575548154539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14154327595723050365436359 21231491393584575548154539)
          ·
            refine ⟨31847237090376863322231809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21231491393584575548154539 31847237090376863322231809)
            ·
              refine ⟨23885427817782647491673857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31847237090376863322231809 23885427817782647491673857)
              ·
                refine ⟨17914070863336985618755393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23885427817782647491673857 17914070863336985618755393)
                ·
                  refine ⟨13435553147502739214066545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17914070863336985618755393 13435553147502739214066545)
                  ·
                    refine ⟨10076664860627054410549909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13435553147502739214066545 10076664860627054410549909)
                    ·
                      refine ⟨472343665341893175494527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10076664860627054410549909 472343665341893175494527)
                      ·
                        rfl

theorem cell23_919886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_919886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919886 prefixEnd_919886 := by exact prefixLift 919886
  have htrace : WordTrace (prefixWord ++ tailWord_919886) baseStart_919886 baseEnd_919886 := by
    simpa [prefixWord, tailWord_919886, baseEnd_919886] using wordTrace_append hprefix tailTrace_919886
  have hstable : (prefixWord ++ tailWord_919886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919886).length < 2 ^ (prefixWord ++ tailWord_919886).sum := by decide
  have hdescent : baseEnd_919886 < baseStart_919886 := by decide
  rcases family_descends (prefixWord ++ tailWord_919886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919920 : List Nat := [2, 1, 1, 1, 4, 3, 2, 1, 3, 3, 2]
def baseStart_919920 : Nat := 118140960795 + 919920 * 2 ^ 59
def prefixEnd_919920 : Nat := 4983230072969 + 3 ^ 40 * 919920 * 2
def baseEnd_919920 : Nat := 472361123684146042469371

theorem tailTrace_919920 : CollatzResearch.WordTrace tailWord_919920 prefixEnd_919920 472361123684146042469371 := by
  unfold tailWord_919920
  simp only [CollatzResearch.WordTrace]
  refine ⟨16776119413647212336478607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22368159218196283115304809 16776119413647212336478607)
  ·
    refine ⟨25164179120470818504717911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16776119413647212336478607 25164179120470818504717911)
    ·
      refine ⟨37746268680706227757076867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25164179120470818504717911 37746268680706227757076867)
      ·
        refine ⟨56619403021059341635615301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37746268680706227757076867 56619403021059341635615301)
        ·
          refine ⟨10616138066448626556677869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56619403021059341635615301 10616138066448626556677869)
          ·
            refine ⟨3981051774918234958754201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10616138066448626556677869 3981051774918234958754201)
            ·
              refine ⟨2985788831188676219065651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3981051774918234958754201 2985788831188676219065651)
              ·
                refine ⟨4478683246783014328598477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2985788831188676219065651 4478683246783014328598477)
                ·
                  refine ⟨1679506217543630373224429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4478683246783014328598477 1679506217543630373224429)
                  ·
                    refine ⟨629814831578861389959161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1679506217543630373224429 629814831578861389959161)
                    ·
                      refine ⟨472361123684146042469371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 629814831578861389959161 472361123684146042469371)
                      ·
                        rfl

theorem cell23_919920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 3, 3, 2].length) (baseStart_919920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919920 prefixEnd_919920 := by exact prefixLift 919920
  have htrace : WordTrace (prefixWord ++ tailWord_919920) baseStart_919920 baseEnd_919920 := by
    simpa [prefixWord, tailWord_919920, baseEnd_919920] using wordTrace_append hprefix tailTrace_919920
  have hstable : (prefixWord ++ tailWord_919920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919920).length < 2 ^ (prefixWord ++ tailWord_919920).sum := by decide
  have hdescent : baseEnd_919920 < baseStart_919920 := by decide
  rcases family_descends (prefixWord ++ tailWord_919920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919958 : List Nat := [5, 3, 1, 2, 2, 1, 1, 1, 1, 2, 4]
def baseStart_919958 : Nat := 118140960795 + 919958 * 2 ^ 59
def prefixEnd_919958 : Nat := 4983230072969 + 3 ^ 40 * 919958 * 2
def baseEnd_919958 : Nat := 472380635949016893794197

theorem tailTrace_919958 : CollatzResearch.WordTrace tailWord_919958 prefixEnd_919958 472380635949016893794197 := by
  unfold tailWord_919958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2097101550072297322677533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22369083200771171441893685 2097101550072297322677533)
  ·
    refine ⟨786413081277111496004075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2097101550072297322677533 786413081277111496004075)
    ·
      refine ⟨1179619621915667244006113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 786413081277111496004075 1179619621915667244006113)
      ·
        refine ⟨884714716436750433004585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1179619621915667244006113 884714716436750433004585)
        ·
          refine ⟨663536037327562824753439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 884714716436750433004585 663536037327562824753439)
          ·
            refine ⟨995304055991344237130159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 663536037327562824753439 995304055991344237130159)
            ·
              refine ⟨1492956083987016355695239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 995304055991344237130159 1492956083987016355695239)
              ·
                refine ⟨2239434125980524533542859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1492956083987016355695239 2239434125980524533542859)
                ·
                  refine ⟨3359151188970786800314289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2239434125980524533542859 3359151188970786800314289)
                  ·
                    refine ⟨2519363391728090100235717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3359151188970786800314289 2519363391728090100235717)
                    ·
                      refine ⟨472380635949016893794197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2519363391728090100235717 472380635949016893794197)
                      ·
                        rfl

theorem cell23_919958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_919958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_919958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_919958 prefixEnd_919958 := by exact prefixLift 919958
  have htrace : WordTrace (prefixWord ++ tailWord_919958) baseStart_919958 baseEnd_919958 := by
    simpa [prefixWord, tailWord_919958, baseEnd_919958] using wordTrace_append hprefix tailTrace_919958
  have hstable : (prefixWord ++ tailWord_919958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919958).length < 2 ^ (prefixWord ++ tailWord_919958).sum := by decide
  have hdescent : baseEnd_919958 < baseStart_919958 := by decide
  rcases family_descends (prefixWord ++ tailWord_919958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920007 : List Nat := [1, 1, 4, 1, 1, 5, 3, 2, 5]
def baseStart_920007 : Nat := 118140960795 + 920007 * 2 ^ 59
def prefixEnd_920007 : Nat := 4983230072969 + 3 ^ 40 * 920007 * 2
def baseEnd_920007 : Nat := 52489532944565244675719

theorem tailTrace_920007 : CollatzResearch.WordTrace tailWord_920007 prefixEnd_920007 52489532944565244675719 := by
  unfold tailWord_920007
  simp only [CollatzResearch.WordTrace]
  refine ⟨33555411977979238531374275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22370274651986159020916183 33555411977979238531374275)
  ·
    refine ⟨50333117966968857797061413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33555411977979238531374275 50333117966968857797061413)
    ·
      refine ⟨9437459618806660836949015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50333117966968857797061413 9437459618806660836949015)
      ·
        refine ⟨14156189428209991255423523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9437459618806660836949015 14156189428209991255423523)
        ·
          refine ⟨21234284142314986883135285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14156189428209991255423523 21234284142314986883135285)
          ·
            refine ⟨1990714138342030020293933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21234284142314986883135285 1990714138342030020293933)
            ·
              refine ⟨746517801878261257610225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1990714138342030020293933 746517801878261257610225)
              ·
                refine ⟨559888351408695943207669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 746517801878261257610225 559888351408695943207669)
                ·
                  refine ⟨52489532944565244675719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 559888351408695943207669 52489532944565244675719)
                  ·
                    rfl

theorem cell23_920007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 2, 5].length) (baseStart_920007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920007 prefixEnd_920007 := by exact prefixLift 920007
  have htrace : WordTrace (prefixWord ++ tailWord_920007) baseStart_920007 baseEnd_920007 := by
    simpa [prefixWord, tailWord_920007, baseEnd_920007] using wordTrace_append hprefix tailTrace_920007
  have hstable : (prefixWord ++ tailWord_920007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920007).length < 2 ^ (prefixWord ++ tailWord_920007).sum := by decide
  have hdescent : baseEnd_920007 < baseStart_920007 := by decide
  rcases family_descends (prefixWord ++ tailWord_920007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920010 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 2, 5, 2]
def baseStart_920010 : Nat := 118140960795 + 920010 * 2 ^ 59
def prefixEnd_920010 : Nat := 4983230072969 + 3 ^ 40 * 920010 * 2
def baseEnd_920010 : Nat := 472407336943050690343957

theorem tailTrace_920010 : CollatzResearch.WordTrace tailWord_920010 prefixEnd_920010 472407336943050690343957 := by
  unfold tailWord_920010
  simp only [CollatzResearch.WordTrace]
  refine ⟨8388880349242092510933371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22370347597978913362488989 8388880349242092510933371)
  ·
    refine ⟨12583320523863138766400057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8388880349242092510933371 12583320523863138766400057)
    ·
      refine ⟨9437490392897354074800043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12583320523863138766400057 9437490392897354074800043)
      ·
        refine ⟨14156235589346031112200065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9437490392897354074800043 14156235589346031112200065)
        ·
          refine ⟨10617176692009523334150049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14156235589346031112200065 10617176692009523334150049)
          ·
            refine ⟨7962882519007142500612537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10617176692009523334150049 7962882519007142500612537)
            ·
              refine ⟨5972161889255356875459403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7962882519007142500612537 5972161889255356875459403)
              ·
                refine ⟨8958242833883035313189105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5972161889255356875459403 8958242833883035313189105)
                ·
                  refine ⟨6718682125412276484891829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8958242833883035313189105 6718682125412276484891829)
                  ·
                    refine ⟨629876449257400920458609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6718682125412276484891829 629876449257400920458609)
                    ·
                      refine ⟨472407336943050690343957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 629876449257400920458609 472407336943050690343957)
                      ·
                        rfl

theorem cell23_920010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 2, 5, 2].length) (baseStart_920010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920010 prefixEnd_920010 := by exact prefixLift 920010
  have htrace : WordTrace (prefixWord ++ tailWord_920010) baseStart_920010 baseEnd_920010 := by
    simpa [prefixWord, tailWord_920010, baseEnd_920010] using wordTrace_append hprefix tailTrace_920010
  have hstable : (prefixWord ++ tailWord_920010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920010).length < 2 ^ (prefixWord ++ tailWord_920010).sum := by decide
  have hdescent : baseEnd_920010 < baseStart_920010 := by decide
  rcases family_descends (prefixWord ++ tailWord_920010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920037 : List Nat := [1, 3, 1, 5, 2, 1, 2, 1, 2, 5]
def baseStart_920037 : Nat := 118140960795 + 920037 * 2 ^ 59
def prefixEnd_920037 : Nat := 4983230072969 + 3 ^ 40 * 920037 * 2
def baseEnd_920037 : Nat := 157473733640240694902111

theorem tailTrace_920037 : CollatzResearch.WordTrace tailWord_920037 prefixEnd_920037 157473733640240694902111 := by
  unfold tailWord_920037
  simp only [CollatzResearch.WordTrace]
  refine ⟨33556506167870553654966365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22371004111913702436644243 33556506167870553654966365)
  ·
    refine ⟨12583689812951457620612387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33556506167870553654966365 12583689812951457620612387)
    ·
      refine ⟨18875534719427186430918581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12583689812951457620612387 18875534719427186430918581)
      ·
        refine ⟨1769581379946298727898617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18875534719427186430918581 1769581379946298727898617)
        ·
          refine ⟨1327186034959724045923963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1769581379946298727898617 1327186034959724045923963)
          ·
            refine ⟨1990779052439586068885945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1327186034959724045923963 1990779052439586068885945)
            ·
              refine ⟨1493084289329689551664459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1990779052439586068885945 1493084289329689551664459)
              ·
                refine ⟨2239626433994534327496689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1493084289329689551664459 2239626433994534327496689)
                ·
                  refine ⟨1679719825495900745622517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2239626433994534327496689 1679719825495900745622517)
                  ·
                    refine ⟨157473733640240694902111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1679719825495900745622517 157473733640240694902111)
                    ·
                      rfl

theorem cell23_920037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 5].length) (baseStart_920037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920037 prefixEnd_920037 := by exact prefixLift 920037
  have htrace : WordTrace (prefixWord ++ tailWord_920037) baseStart_920037 baseEnd_920037 := by
    simpa [prefixWord, tailWord_920037, baseEnd_920037] using wordTrace_append hprefix tailTrace_920037
  have hstable : (prefixWord ++ tailWord_920037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920037).length < 2 ^ (prefixWord ++ tailWord_920037).sum := by decide
  have hdescent : baseEnd_920037 < baseStart_920037 := by decide
  rcases family_descends (prefixWord ++ tailWord_920037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920040 : List Nat := [2, 1, 4, 1, 1, 3, 1, 3, 2, 1, 4]
def baseStart_920040 : Nat := 118140960795 + 920040 * 2 ^ 59
def prefixEnd_920040 : Nat := 4983230072969 + 3 ^ 40 * 920040 * 2
def baseEnd_920040 : Nat := 472422741362685572968819

theorem tailTrace_920040 : CollatzResearch.WordTrace tailWord_920040 prefixEnd_920040 472422741362685572968819 := by
  unfold tailWord_920040
  simp only [CollatzResearch.WordTrace]
  refine ⟨16778307793429842583662787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22371077057906456778217049 16778307793429842583662787)
  ·
    refine ⟨25167461690144763875494181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16778307793429842583662787 25167461690144763875494181)
    ·
      refine ⟨4718899066902143226655159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25167461690144763875494181 4718899066902143226655159)
      ·
        refine ⟨7078348600353214839982739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4718899066902143226655159 7078348600353214839982739)
        ·
          refine ⟨10617522900529822259974109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7078348600353214839982739 10617522900529822259974109)
          ·
            refine ⟨3981571087698683347490291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10617522900529822259974109 3981571087698683347490291)
            ·
              refine ⟨5972356631548025021235437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3981571087698683347490291 5972356631548025021235437)
              ·
                refine ⟨2239633736830509382963289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5972356631548025021235437 2239633736830509382963289)
                ·
                  refine ⟨1679725302622882037222467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2239633736830509382963289 1679725302622882037222467)
                  ·
                    refine ⟨2519587953934323055833701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1679725302622882037222467 2519587953934323055833701)
                    ·
                      refine ⟨472422741362685572968819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2519587953934323055833701 472422741362685572968819)
                      ·
                        rfl

theorem cell23_920040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_920040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920040 prefixEnd_920040 := by exact prefixLift 920040
  have htrace : WordTrace (prefixWord ++ tailWord_920040) baseStart_920040 baseEnd_920040 := by
    simpa [prefixWord, tailWord_920040, baseEnd_920040] using wordTrace_append hprefix tailTrace_920040
  have hstable : (prefixWord ++ tailWord_920040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920040).length < 2 ^ (prefixWord ++ tailWord_920040).sum := by decide
  have hdescent : baseEnd_920040 < baseStart_920040 := by decide
  rcases family_descends (prefixWord ++ tailWord_920040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920067 : List Nat := [1, 1, 1, 3, 2, 1, 5, 4, 1, 4]
def baseStart_920067 : Nat := 118140960795 + 920067 * 2 ^ 59
def prefixEnd_920067 : Nat := 4983230072969 + 3 ^ 40 * 920067 * 2
def baseEnd_920067 : Nat := 157478868446785655777065

theorem tailTrace_920067 : CollatzResearch.WordTrace tailWord_920067 prefixEnd_920067 157478868446785655777065 := by
  unfold tailWord_920067
  simp only [CollatzResearch.WordTrace]
  refine ⟨33557600357761868778558455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22371733571841245852372303 33557600357761868778558455)
  ·
    refine ⟨50336400536642803167837683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33557600357761868778558455 50336400536642803167837683)
    ·
      refine ⟨75504600804964204751756525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50336400536642803167837683 75504600804964204751756525)
      ·
        refine ⟨28314225301861576781908697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75504600804964204751756525 28314225301861576781908697)
        ·
          refine ⟨21235668976396182586431523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28314225301861576781908697 21235668976396182586431523)
          ·
            refine ⟨31853503464594273879647285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21235668976396182586431523 31853503464594273879647285)
            ·
              refine ⟨2986265949805713176216933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31853503464594273879647285 2986265949805713176216933)
              ·
                refine ⟨559924865588571220540675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2986265949805713176216933 559924865588571220540675)
                ·
                  refine ⟨839887298382856830811013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 559924865588571220540675 839887298382856830811013)
                  ·
                    refine ⟨157478868446785655777065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 839887298382856830811013 157478868446785655777065)
                    ·
                      rfl

theorem cell23_920067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 4, 1, 4].length) (baseStart_920067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920067 prefixEnd_920067 := by exact prefixLift 920067
  have htrace : WordTrace (prefixWord ++ tailWord_920067) baseStart_920067 baseEnd_920067 := by
    simpa [prefixWord, tailWord_920067, baseEnd_920067] using wordTrace_append hprefix tailTrace_920067
  have hstable : (prefixWord ++ tailWord_920067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920067).length < 2 ^ (prefixWord ++ tailWord_920067).sum := by decide
  have hdescent : baseEnd_920067 < baseStart_920067 := by decide
  rcases family_descends (prefixWord ++ tailWord_920067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920084 : List Nat := [2, 4, 3, 1, 1, 2, 1, 2, 3, 4]
def baseStart_920084 : Nat := 118140960795 + 920084 * 2 ^ 59
def prefixEnd_920084 : Nat := 4983230072969 + 3 ^ 40 * 920084 * 2
def baseEnd_920084 : Nat := 157481778170494466939539

theorem tailTrace_920084 : CollatzResearch.WordTrace tailWord_920084 prefixEnd_920084 157481778170494466939539 := by
  unfold tailWord_920084
  simp only [CollatzResearch.WordTrace]
  refine ⟨16779110199350140340963653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22372146932466853787951537 16779110199350140340963653)
  ·
    refine ⟨3146083162378151313930685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16779110199350140340963653 3146083162378151313930685)
    ·
      refine ⟨1179781185891806742724007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3146083162378151313930685 1179781185891806742724007)
      ·
        refine ⟨1769671778837710114086011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1179781185891806742724007 1769671778837710114086011)
        ·
          refine ⟨2654507668256565171129017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1769671778837710114086011 2654507668256565171129017)
          ·
            refine ⟨1990880751192423878346763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2654507668256565171129017 1990880751192423878346763)
            ·
              refine ⟨2986321126788635817520145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1990880751192423878346763 2986321126788635817520145)
              ·
                refine ⟨2239740845091476863140109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2986321126788635817520145 2239740845091476863140109)
                ·
                  refine ⟨839902816909303823677541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2239740845091476863140109 839902816909303823677541)
                  ·
                    refine ⟨157481778170494466939539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 839902816909303823677541 157481778170494466939539)
                    ·
                      rfl

theorem cell23_920084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_920084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920084 prefixEnd_920084 := by exact prefixLift 920084
  have htrace : WordTrace (prefixWord ++ tailWord_920084) baseStart_920084 baseEnd_920084 := by
    simpa [prefixWord, tailWord_920084, baseEnd_920084] using wordTrace_append hprefix tailTrace_920084
  have hstable : (prefixWord ++ tailWord_920084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920084).length < 2 ^ (prefixWord ++ tailWord_920084).sum := by decide
  have hdescent : baseEnd_920084 < baseStart_920084 := by decide
  rcases family_descends (prefixWord ++ tailWord_920084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920117 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 4, 3, 2]
def baseStart_920117 : Nat := 118140960795 + 920117 * 2 ^ 59
def prefixEnd_920117 : Nat := 4983230072969 + 3 ^ 40 * 920117 * 2
def baseEnd_920117 : Nat := 472462279373081771705965

theorem tailTrace_920117 : CollatzResearch.WordTrace tailWord_920117 prefixEnd_920117 472462279373081771705965 := by
  unfold tailWord_920117
  simp only [CollatzResearch.WordTrace]
  refine ⟨33559424007580727317878605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22372949338387151545252403 33559424007580727317878605)
  ·
    refine ⟨12584784002842772744204477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33559424007580727317878605 12584784002842772744204477)
    ·
      refine ⟨4719294001066039779076679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12584784002842772744204477 4719294001066039779076679)
      ·
        refine ⟨7078941001599059668615019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4719294001066039779076679 7078941001599059668615019)
        ·
          refine ⟨10618411502398589502922529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7078941001599059668615019 10618411502398589502922529)
          ·
            refine ⟨7963808626798942127191897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10618411502398589502922529 7963808626798942127191897)
            ·
              refine ⟨5972856470099206595393923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7963808626798942127191897 5972856470099206595393923)
              ·
                refine ⟨8959284705148809893090885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5972856470099206595393923 8959284705148809893090885)
                ·
                  refine ⟨1679865882215401854954541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8959284705148809893090885 1679865882215401854954541)
                  ·
                    refine ⟨629949705830775695607953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1679865882215401854954541 629949705830775695607953)
                    ·
                      refine ⟨472462279373081771705965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 629949705830775695607953 472462279373081771705965)
                      ·
                        rfl

theorem cell23_920117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_920117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920117 prefixEnd_920117 := by exact prefixLift 920117
  have htrace : WordTrace (prefixWord ++ tailWord_920117) baseStart_920117 baseEnd_920117 := by
    simpa [prefixWord, tailWord_920117, baseEnd_920117] using wordTrace_append hprefix tailTrace_920117
  have hstable : (prefixWord ++ tailWord_920117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920117).length < 2 ^ (prefixWord ++ tailWord_920117).sum := by decide
  have hdescent : baseEnd_920117 < baseStart_920117 := by decide
  rcases family_descends (prefixWord ++ tailWord_920117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920124 : List Nat := [2, 2, 2, 2, 3, 2, 2, 1, 3, 1, 3]
def baseStart_920124 : Nat := 118140960795 + 920124 * 2 ^ 59
def prefixEnd_920124 : Nat := 4983230072969 + 3 ^ 40 * 920124 * 2
def baseEnd_920124 : Nat := 472465873737663244318433

theorem tailTrace_920124 : CollatzResearch.WordTrace tailWord_920124 prefixEnd_920124 472465873737663244318433 := by
  unfold tailWord_920124
  simp only [CollatzResearch.WordTrace]
  refine ⟨16779839659277683756691713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22373119545703578342255617 16779839659277683756691713)
  ·
    refine ⟨12584879744458262817518785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16779839659277683756691713 12584879744458262817518785)
    ·
      refine ⟨9438659808343697113139089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12584879744458262817518785 9438659808343697113139089)
      ·
        refine ⟨7078994856257772834854317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9438659808343697113139089 7078994856257772834854317)
        ·
          refine ⟨2654623071096664813070369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7078994856257772834854317 2654623071096664813070369)
          ·
            refine ⟨1990967303322498609802777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2654623071096664813070369 1990967303322498609802777)
            ·
              refine ⟨1493225477491873957352083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1990967303322498609802777 1493225477491873957352083)
              ·
                refine ⟨2239838216237810936028125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1493225477491873957352083 2239838216237810936028125)
                ·
                  refine ⟨839939331089179101010547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2239838216237810936028125 839939331089179101010547)
                  ·
                    refine ⟨1259908996633768651515821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 839939331089179101010547 1259908996633768651515821)
                    ·
                      refine ⟨472465873737663244318433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1259908996633768651515821 472465873737663244318433)
                      ·
                        rfl

theorem cell23_920124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_920124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920124 prefixEnd_920124 := by exact prefixLift 920124
  have htrace : WordTrace (prefixWord ++ tailWord_920124) baseStart_920124 baseEnd_920124 := by
    simpa [prefixWord, tailWord_920124, baseEnd_920124] using wordTrace_append hprefix tailTrace_920124
  have hstable : (prefixWord ++ tailWord_920124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920124).length < 2 ^ (prefixWord ++ tailWord_920124).sum := by decide
  have hdescent : baseEnd_920124 < baseStart_920124 := by decide
  rcases family_descends (prefixWord ++ tailWord_920124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920160 : List Nat := [2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 4]
def baseStart_920160 : Nat := 118140960795 + 920160 * 2 ^ 59
def prefixEnd_920160 : Nat := 4983230072969 + 3 ^ 40 * 920160 * 2
def baseEnd_920160 : Nat := 472484359041225103468267

theorem tailTrace_920160 : CollatzResearch.WordTrace tailWord_920160 prefixEnd_920160 472484359041225103468267 := by
  unfold tailWord_920160
  simp only [CollatzResearch.WordTrace]
  refine ⟨16780496173212472830846967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22373994897616630441129289 16780496173212472830846967)
  ·
    refine ⟨25170744259818709246270451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16780496173212472830846967 25170744259818709246270451)
    ·
      refine ⟨37756116389728063869405677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25170744259818709246270451 37756116389728063869405677)
      ·
        refine ⟨14158543646148023951027129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37756116389728063869405677 14158543646148023951027129)
        ·
          refine ⟨10618907734611017963270347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14158543646148023951027129 10618907734611017963270347)
          ·
            refine ⟨15928361601916526944905521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10618907734611017963270347 15928361601916526944905521)
            ·
              refine ⟨11946271201437395208679141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15928361601916526944905521 11946271201437395208679141)
              ·
                refine ⟨2239925850269511601627339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11946271201437395208679141 2239925850269511601627339)
                ·
                  refine ⟨3359888775404267402441009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2239925850269511601627339 3359888775404267402441009)
                  ·
                    refine ⟨2519916581553200551830757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3359888775404267402441009 2519916581553200551830757)
                    ·
                      refine ⟨472484359041225103468267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2519916581553200551830757 472484359041225103468267)
                      ·
                        rfl

theorem cell23_920160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_920160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920160 prefixEnd_920160 := by exact prefixLift 920160
  have htrace : WordTrace (prefixWord ++ tailWord_920160) baseStart_920160 baseEnd_920160 := by
    simpa [prefixWord, tailWord_920160, baseEnd_920160] using wordTrace_append hprefix tailTrace_920160
  have hstable : (prefixWord ++ tailWord_920160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920160).length < 2 ^ (prefixWord ++ tailWord_920160).sum := by decide
  have hdescent : baseEnd_920160 < baseStart_920160 := by decide
  rcases family_descends (prefixWord ++ tailWord_920160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920207 : List Nat := [1, 1, 2, 1, 1, 1, 1, 7, 3, 3, 2]
def baseStart_920207 : Nat := 118140960795 + 920207 * 2 ^ 59
def prefixEnd_920207 : Nat := 4983230072969 + 3 ^ 40 * 920207 * 2
def baseEnd_920207 : Nat := 472508492631986419580551

theorem tailTrace_920207 : CollatzResearch.WordTrace tailWord_920207 prefixEnd_920207 472508492631986419580551 := by
  unfold tailWord_920207
  simp only [CollatzResearch.WordTrace]
  refine ⟨33562706577254672688654875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22375137718169781792436583 33562706577254672688654875)
  ·
    refine ⟨50344059865882009032982313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33562706577254672688654875 50344059865882009032982313)
    ·
      refine ⟨37758044899411506774736735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50344059865882009032982313 37758044899411506774736735)
      ·
        refine ⟨56637067349117260162105103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37758044899411506774736735 56637067349117260162105103)
        ·
          refine ⟨84955601023675890243157655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56637067349117260162105103 84955601023675890243157655)
          ·
            refine ⟨127433401535513835364736483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84955601023675890243157655 127433401535513835364736483)
            ·
              refine ⟨191150102303270753047104725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127433401535513835364736483 191150102303270753047104725)
              ·
                refine ⟨4480080522732908274541517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 191150102303270753047104725 4480080522732908274541517)
                ·
                  refine ⟨1680030196024840602953069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4480080522732908274541517 1680030196024840602953069)
                  ·
                    refine ⟨630011323509315226107401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1680030196024840602953069 630011323509315226107401)
                    ·
                      refine ⟨472508492631986419580551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 630011323509315226107401 472508492631986419580551)
                      ·
                        rfl

theorem cell23_920207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 3, 2].length) (baseStart_920207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920207 prefixEnd_920207 := by exact prefixLift 920207
  have htrace : WordTrace (prefixWord ++ tailWord_920207) baseStart_920207 baseEnd_920207 := by
    simpa [prefixWord, tailWord_920207, baseEnd_920207] using wordTrace_append hprefix tailTrace_920207
  have hstable : (prefixWord ++ tailWord_920207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920207).length < 2 ^ (prefixWord ++ tailWord_920207).sum := by decide
  have hdescent : baseEnd_920207 < baseStart_920207 := by decide
  rcases family_descends (prefixWord ++ tailWord_920207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920218 : List Nat := [3, 1, 1, 6, 1, 1, 3, 1, 1, 2, 3]
def baseStart_920218 : Nat := 118140960795 + 920218 * 2 ^ 59
def prefixEnd_920218 : Nat := 4983230072969 + 3 ^ 40 * 920218 * 2
def baseEnd_920218 : Nat := 472514140919185876543001

theorem tailTrace_920218 : CollatzResearch.WordTrace tailWord_920218 prefixEnd_920218 472514140919185876543001 := by
  unfold tailWord_920218
  simp only [CollatzResearch.WordTrace]
  refine ⟨8390776945053705391826327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22375405186809881044870205 8390776945053705391826327)
  ·
    refine ⟨12586165417580558087739491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8390776945053705391826327 12586165417580558087739491)
    ·
      refine ⟨18879248126370837131609237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12586165417580558087739491 18879248126370837131609237)
      ·
        refine ⟨884964755923632990544183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18879248126370837131609237 884964755923632990544183)
        ·
          refine ⟨1327447133885449485816275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 884964755923632990544183 1327447133885449485816275)
          ·
            refine ⟨1991170700828174228724413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1327447133885449485816275 1991170700828174228724413)
            ·
              refine ⟨746689012810565335771655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1991170700828174228724413 746689012810565335771655)
              ·
                refine ⟨1120033519215848003657483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 746689012810565335771655 1120033519215848003657483)
                ·
                  refine ⟨1680050278823772005486225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1120033519215848003657483 1680050278823772005486225)
                  ·
                    refine ⟨1260037709117829004114669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1680050278823772005486225 1260037709117829004114669)
                    ·
                      refine ⟨472514140919185876543001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1260037709117829004114669 472514140919185876543001)
                      ·
                        rfl

theorem cell23_920218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_920218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920218 prefixEnd_920218 := by exact prefixLift 920218
  have htrace : WordTrace (prefixWord ++ tailWord_920218) baseStart_920218 baseEnd_920218 := by
    simpa [prefixWord, tailWord_920218, baseEnd_920218] using wordTrace_append hprefix tailTrace_920218
  have hstable : (prefixWord ++ tailWord_920218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920218).length < 2 ^ (prefixWord ++ tailWord_920218).sum := by decide
  have hdescent : baseEnd_920218 < baseStart_920218 := by decide
  rcases family_descends (prefixWord ++ tailWord_920218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920237 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_920237 : Nat := 118140960795 + 920237 * 2 ^ 59
def prefixEnd_920237 : Nat := 4983230072969 + 3 ^ 40 * 920237 * 2
def baseEnd_920237 : Nat := 472523897051621302205413

theorem tailTrace_920237 : CollatzResearch.WordTrace tailWord_920237 prefixEnd_920237 472523897051621302205413 := by
  unfold tailWord_920237
  simp only [CollatzResearch.WordTrace]
  refine ⟨33563800767145987812246965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22375867178097325208164643 33563800767145987812246965)
  ·
    refine ⟨3146606321919936357398153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33563800767145987812246965 3146606321919936357398153)
    ·
      refine ⟨2359954741439952268048615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3146606321919936357398153 2359954741439952268048615)
      ·
        refine ⟨3539932112159928402072923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2359954741439952268048615 3539932112159928402072923)
        ·
          refine ⟨5309898168239892603109385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3539932112159928402072923 5309898168239892603109385)
          ·
            refine ⟨3982423626179919452332039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5309898168239892603109385 3982423626179919452332039)
            ·
              refine ⟨5973635439269879178498059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3982423626179919452332039 5973635439269879178498059)
              ·
                refine ⟨8960453158904818767747089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5973635439269879178498059 8960453158904818767747089)
                ·
                  refine ⟨6720339869178614075810317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8960453158904818767747089 6720339869178614075810317)
                  ·
                    refine ⟨2520127450941980278428869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6720339869178614075810317 2520127450941980278428869)
                    ·
                      refine ⟨472523897051621302205413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2520127450941980278428869 472523897051621302205413)
                      ·
                        rfl

theorem cell23_920237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_920237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920237 prefixEnd_920237 := by exact prefixLift 920237
  have htrace : WordTrace (prefixWord ++ tailWord_920237) baseStart_920237 baseEnd_920237 := by
    simpa [prefixWord, tailWord_920237, baseEnd_920237] using wordTrace_append hprefix tailTrace_920237
  have hstable : (prefixWord ++ tailWord_920237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920237).length < 2 ^ (prefixWord ++ tailWord_920237).sum := by decide
  have hdescent : baseEnd_920237 < baseStart_920237 := by decide
  rcases family_descends (prefixWord ++ tailWord_920237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920247 : List Nat := [1, 1, 3, 1, 6, 1, 1, 1, 2, 6]
def baseStart_920247 : Nat := 118140960795 + 920247 * 2 ^ 59
def prefixEnd_920247 : Nat := 4983230072969 + 3 ^ 40 * 920247 * 2
def baseEnd_920247 : Nat := 157509677286055421026789

theorem tailTrace_920247 : CollatzResearch.WordTrace tailWord_920247 prefixEnd_920247 157509677286055421026789 := by
  unfold tailWord_920247
  simp only [CollatzResearch.WordTrace]
  refine ⟨33564165497109759520110995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22376110331406506346740663 33564165497109759520110995)
  ·
    refine ⟨50346248245664639280166493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33564165497109759520110995 50346248245664639280166493)
    ·
      refine ⟨18879843092124239730062435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50346248245664639280166493 18879843092124239730062435)
      ·
        refine ⟨28319764638186359595093653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18879843092124239730062435 28319764638186359595093653)
        ·
          refine ⟨1327488967414985606020015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28319764638186359595093653 1327488967414985606020015)
          ·
            refine ⟨1991233451122478409030023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1327488967414985606020015 1991233451122478409030023)
            ·
              refine ⟨2986850176683717613545035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1991233451122478409030023 2986850176683717613545035)
              ·
                refine ⟨4480275265025576420317553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2986850176683717613545035 4480275265025576420317553)
                ·
                  refine ⟨3360206448769182315238165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4480275265025576420317553 3360206448769182315238165)
                  ·
                    refine ⟨157509677286055421026789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3360206448769182315238165 157509677286055421026789)
                    ·
                      rfl

theorem cell23_920247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 6].length) (baseStart_920247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920247 prefixEnd_920247 := by exact prefixLift 920247
  have htrace : WordTrace (prefixWord ++ tailWord_920247) baseStart_920247 baseEnd_920247 := by
    simpa [prefixWord, tailWord_920247, baseEnd_920247] using wordTrace_append hprefix tailTrace_920247
  have hstable : (prefixWord ++ tailWord_920247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920247).length < 2 ^ (prefixWord ++ tailWord_920247).sum := by decide
  have hdescent : baseEnd_920247 < baseStart_920247 := by decide
  rcases family_descends (prefixWord ++ tailWord_920247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920284 : List Nat := [2, 2, 5, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_920284 : Nat := 118140960795 + 920284 * 2 ^ 59
def prefixEnd_920284 : Nat := 4983230072969 + 3 ^ 40 * 920284 * 2
def baseEnd_920284 : Nat := 472548030642382618317697

theorem tailTrace_920284 : CollatzResearch.WordTrace tailWord_920284 prefixEnd_920284 472548030642382618317697 := by
  unfold tailWord_920284
  simp only [CollatzResearch.WordTrace]
  refine ⟨16782757498987857419603953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22377009998650476559471937 16782757498987857419603953)
  ·
    refine ⟨12587068124240893064702965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16782757498987857419603953 12587068124240893064702965)
    ·
      refine ⟨1180037636647583724815903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12587068124240893064702965 1180037636647583724815903)
      ·
        refine ⟨1770056454971375587223855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1180037636647583724815903 1770056454971375587223855)
        ·
          refine ⟨2655084682457063380835783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1770056454971375587223855 2655084682457063380835783)
          ·
            refine ⟨3982627023685595071253675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2655084682457063380835783 3982627023685595071253675)
            ·
              refine ⟨5973940535528392606880513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3982627023685595071253675 5973940535528392606880513)
              ·
                refine ⟨4480455401646294455160385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5973940535528392606880513 4480455401646294455160385)
                ·
                  refine ⟨3360341551234720841370289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4480455401646294455160385 3360341551234720841370289)
                  ·
                    refine ⟨2520256163426040631027717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3360341551234720841370289 2520256163426040631027717)
                    ·
                      refine ⟨472548030642382618317697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2520256163426040631027717 472548030642382618317697)
                      ·
                        rfl

theorem cell23_920284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_920284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920284 prefixEnd_920284 := by exact prefixLift 920284
  have htrace : WordTrace (prefixWord ++ tailWord_920284) baseStart_920284 baseEnd_920284 := by
    simpa [prefixWord, tailWord_920284, baseEnd_920284] using wordTrace_append hprefix tailTrace_920284
  have hstable : (prefixWord ++ tailWord_920284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920284).length < 2 ^ (prefixWord ++ tailWord_920284).sum := by decide
  have hdescent : baseEnd_920284 < baseStart_920284 := by decide
  rcases family_descends (prefixWord ++ tailWord_920284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920287 : List Nat := [1, 1, 2, 3, 2, 3, 1, 2, 2, 3, 3]
def baseStart_920287 : Nat := 118140960795 + 920287 * 2 ^ 59
def prefixEnd_920287 : Nat := 4983230072969 + 3 ^ 40 * 920287 * 2
def baseEnd_920287 : Nat := 472549571084346106580183

theorem tailTrace_920287 : CollatzResearch.WordTrace tailWord_920287 prefixEnd_920287 472549571084346106580183 := by
  unfold tailWord_920287
  simp only [CollatzResearch.WordTrace]
  refine ⟨33565624416964846351567115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22377082944643230901044743 33565624416964846351567115)
  ·
    refine ⟨50348436625447269527350673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33565624416964846351567115 50348436625447269527350673)
    ·
      refine ⟨37761327469085452145513005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50348436625447269527350673 37761327469085452145513005)
      ·
        refine ⟨14160497800907044554567377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37761327469085452145513005 14160497800907044554567377)
        ·
          refine ⟨10620373350680283415925533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14160497800907044554567377 10620373350680283415925533)
          ·
            refine ⟨3982640006505106280972075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10620373350680283415925533 3982640006505106280972075)
            ·
              refine ⟨5973960009757659421458113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3982640006505106280972075 5973960009757659421458113)
              ·
                refine ⟨4480470007318244566093585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5973960009757659421458113 4480470007318244566093585)
                ·
                  refine ⟨3360352505488683424570189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4480470007318244566093585 3360352505488683424570189)
                  ·
                    refine ⟨1260132189558256284213821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3360352505488683424570189 1260132189558256284213821)
                    ·
                      refine ⟨472549571084346106580183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1260132189558256284213821 472549571084346106580183)
                      ·
                        rfl

theorem cell23_920287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_920287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920287 prefixEnd_920287 := by exact prefixLift 920287
  have htrace : WordTrace (prefixWord ++ tailWord_920287) baseStart_920287 baseEnd_920287 := by
    simpa [prefixWord, tailWord_920287, baseEnd_920287] using wordTrace_append hprefix tailTrace_920287
  have hstable : (prefixWord ++ tailWord_920287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920287).length < 2 ^ (prefixWord ++ tailWord_920287).sum := by decide
  have hdescent : baseEnd_920287 < baseStart_920287 := by decide
  rcases family_descends (prefixWord ++ tailWord_920287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920297 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 1, 7, 2]
def baseStart_920297 : Nat := 118140960795 + 920297 * 2 ^ 59
def prefixEnd_920297 : Nat := 4983230072969 + 3 ^ 40 * 920297 * 2
def baseEnd_920297 : Nat := 472554705890891067455137

theorem tailTrace_920297 : CollatzResearch.WordTrace tailWord_920297 prefixEnd_920297 472554705890891067455137 := by
  unfold tailWord_920297
  simp only [CollatzResearch.WordTrace]
  refine ⟨33565989146928618059431145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22377326097952412039620763 33565989146928618059431145)
  ·
    refine ⟨25174491860196463544573359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33565989146928618059431145 25174491860196463544573359)
    ·
      refine ⟨37761737790294695316860039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25174491860196463544573359 37761737790294695316860039)
      ·
        refine ⟨56642606685442042975290059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37761737790294695316860039 56642606685442042975290059)
        ·
          refine ⟨84963910028163064462935089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56642606685442042975290059 84963910028163064462935089)
          ·
            refine ⟨63722932521122298347201317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84963910028163064462935089 63722932521122298347201317)
            ·
              refine ⟨11948049847710430940100247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63722932521122298347201317 11948049847710430940100247)
              ·
                refine ⟨17922074771565646410150371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11948049847710430940100247 17922074771565646410150371)
                ·
                  refine ⟨26883112157348469615225557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17922074771565646410150371 26883112157348469615225557)
                  ·
                    refine ⟨630072941187854756606849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26883112157348469615225557 630072941187854756606849)
                    ·
                      refine ⟨472554705890891067455137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 630072941187854756606849 472554705890891067455137)
                      ·
                        rfl

theorem cell23_920297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 7, 2].length) (baseStart_920297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920297 prefixEnd_920297 := by exact prefixLift 920297
  have htrace : WordTrace (prefixWord ++ tailWord_920297) baseStart_920297 baseEnd_920297 := by
    simpa [prefixWord, tailWord_920297, baseEnd_920297] using wordTrace_append hprefix tailTrace_920297
  have hstable : (prefixWord ++ tailWord_920297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920297).length < 2 ^ (prefixWord ++ tailWord_920297).sum := by decide
  have hdescent : baseEnd_920297 < baseStart_920297 := by decide
  rcases family_descends (prefixWord ++ tailWord_920297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920300 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 7]
def baseStart_920300 : Nat := 118140960795 + 920300 * 2 ^ 59
def prefixEnd_920300 : Nat := 4983230072969 + 3 ^ 40 * 920300 * 2
def baseEnd_920300 : Nat := 472556246332854555717623

theorem tailTrace_920300 : CollatzResearch.WordTrace tailWord_920300 prefixEnd_920300 472556246332854555717623 := by
  unfold tailWord_920300
  simp only [CollatzResearch.WordTrace]
  refine ⟨16783049282958874785895177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22377399043945166381193569 16783049282958874785895177)
  ·
    refine ⟨12587286962219156089421383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16783049282958874785895177 12587286962219156089421383)
    ·
      refine ⟨18880930443328734134132075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12587286962219156089421383 18880930443328734134132075)
      ·
        refine ⟨28321395664993101201198113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18880930443328734134132075 28321395664993101201198113)
        ·
          refine ⟨21241046748744825900898585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28321395664993101201198113 21241046748744825900898585)
          ·
            refine ⟨15930785061558619425673939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21241046748744825900898585 15930785061558619425673939)
            ·
              refine ⟨23896177592337929138510909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15930785061558619425673939 23896177592337929138510909)
              ·
                refine ⟨8961066597126723426941591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23896177592337929138510909 8961066597126723426941591)
                ·
                  refine ⟨13441599895690085140412387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8961066597126723426941591 13441599895690085140412387)
                  ·
                    refine ⟨20162399843535127710618581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13441599895690085140412387 20162399843535127710618581)
                    ·
                      refine ⟨472556246332854555717623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 20162399843535127710618581 472556246332854555717623)
                      ·
                        rfl

theorem cell23_920300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_920300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920300 prefixEnd_920300 := by exact prefixLift 920300
  have htrace : WordTrace (prefixWord ++ tailWord_920300) baseStart_920300 baseEnd_920300 := by
    simpa [prefixWord, tailWord_920300, baseEnd_920300] using wordTrace_append hprefix tailTrace_920300
  have hstable : (prefixWord ++ tailWord_920300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920300).length < 2 ^ (prefixWord ++ tailWord_920300).sum := by decide
  have hdescent : baseEnd_920300 < baseStart_920300 := by decide
  rcases family_descends (prefixWord ++ tailWord_920300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920337 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 5, 4]
def baseStart_920337 : Nat := 118140960795 + 920337 * 2 ^ 59
def prefixEnd_920337 : Nat := 4983230072969 + 3 ^ 40 * 920337 * 2
def baseEnd_920337 : Nat := 157525081705690303651651

theorem tailTrace_920337 : CollatzResearch.WordTrace tailWord_920337 prefixEnd_920337 157525081705690303651651 := by
  unfold tailWord_920337
  simp only [CollatzResearch.WordTrace]
  refine ⟨33567448066783704890887265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22378298711189136593924843 33567448066783704890887265)
  ·
    refine ⟨25175586050087778668165449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33567448066783704890887265 25175586050087778668165449)
    ·
      refine ⟨18881689537565834001124087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25175586050087778668165449 18881689537565834001124087)
      ·
        refine ⟨28322534306348751001686131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18881689537565834001124087 28322534306348751001686131)
        ·
          refine ⟨42483801459523126502529197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28322534306348751001686131 42483801459523126502529197)
          ·
            refine ⟨15931425547321172438448449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42483801459523126502529197 15931425547321172438448449)
            ·
              refine ⟨11948569160490879328836337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15931425547321172438448449 11948569160490879328836337)
              ·
                refine ⟨8961426870368159496627253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11948569160490879328836337 8961426870368159496627253)
                ·
                  refine ⟨840133769097014952808805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8961426870368159496627253 840133769097014952808805)
                  ·
                    refine ⟨157525081705690303651651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 840133769097014952808805 157525081705690303651651)
                    ·
                      rfl

theorem cell23_920337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 5, 4].length) (baseStart_920337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920337 prefixEnd_920337 := by exact prefixLift 920337
  have htrace : WordTrace (prefixWord ++ tailWord_920337) baseStart_920337 baseEnd_920337 := by
    simpa [prefixWord, tailWord_920337, baseEnd_920337] using wordTrace_append hprefix tailTrace_920337
  have hstable : (prefixWord ++ tailWord_920337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920337).length < 2 ^ (prefixWord ++ tailWord_920337).sum := by decide
  have hdescent : baseEnd_920337 < baseStart_920337 := by decide
  rcases family_descends (prefixWord ++ tailWord_920337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920394 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 7, 1, 3]
def baseStart_920394 : Nat := 118140960795 + 920394 * 2 ^ 59
def prefixEnd_920394 : Nat := 4983230072969 + 3 ^ 40 * 920394 * 2
def baseEnd_920394 : Nat := 472604513514377187942191

theorem tailTrace_920394 : CollatzResearch.WordTrace tailWord_920394 prefixEnd_920394 472604513514377187942191 := by
  unfold tailWord_920394
  simp only [CollatzResearch.WordTrace]
  refine ⟨8392381756894300906428059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22379684685051469083808157 8392381756894300906428059)
  ·
    refine ⟨12588572635341451359642089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8392381756894300906428059 12588572635341451359642089)
    ·
      refine ⟨9441429476506088519731567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12588572635341451359642089 9441429476506088519731567)
      ·
        refine ⟨14162144214759132779597351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9441429476506088519731567 14162144214759132779597351)
        ·
          refine ⟨21243216322138699169396027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14162144214759132779597351 21243216322138699169396027)
          ·
            refine ⟨31864824483208048754094041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21243216322138699169396027 31864824483208048754094041)
            ·
              refine ⟨23898618362406036565570531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31864824483208048754094041 23898618362406036565570531)
              ·
                refine ⟨35847927543609054848355797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23898618362406036565570531 35847927543609054848355797)
                ·
                  refine ⟨840185801803337223008339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 35847927543609054848355797 840185801803337223008339)
                  ·
                    refine ⟨1260278702705005834512509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 840185801803337223008339 1260278702705005834512509)
                    ·
                      refine ⟨472604513514377187942191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1260278702705005834512509 472604513514377187942191)
                      ·
                        rfl

theorem cell23_920394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 7, 1, 3].length) (baseStart_920394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920394 prefixEnd_920394 := by exact prefixLift 920394
  have htrace : WordTrace (prefixWord ++ tailWord_920394) baseStart_920394 baseEnd_920394 := by
    simpa [prefixWord, tailWord_920394, baseEnd_920394] using wordTrace_append hprefix tailTrace_920394
  have hstable : (prefixWord ++ tailWord_920394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920394).length < 2 ^ (prefixWord ++ tailWord_920394).sum := by decide
  have hdescent : baseEnd_920394 < baseStart_920394 := by decide
  rcases family_descends (prefixWord ++ tailWord_920394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920427 : List Nat := [1, 1, 1, 1, 2, 2, 5, 3, 1, 6]
def baseStart_920427 : Nat := 118140960795 + 920427 * 2 ^ 59
def prefixEnd_920427 : Nat := 4983230072969 + 3 ^ 40 * 920427 * 2
def baseEnd_920427 : Nat := 157540486125325186276513

theorem tailTrace_920427 : CollatzResearch.WordTrace tailWord_920427 prefixEnd_920427 157540486125325186276513 := by
  unfold tailWord_920427
  simp only [CollatzResearch.WordTrace]
  refine ⟨33570730636457650261663535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22380487090971766841109023 33570730636457650261663535)
  ·
    refine ⟨50356095954686475392495303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33570730636457650261663535 50356095954686475392495303)
    ·
      refine ⟨75534143932029713088742955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50356095954686475392495303 75534143932029713088742955)
      ·
        refine ⟨113301215898044569633114433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75534143932029713088742955 113301215898044569633114433)
        ·
          refine ⟨84975911923533427224835825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113301215898044569633114433 84975911923533427224835825)
          ·
            refine ⟨63731933942650070418626869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84975911923533427224835825 63731933942650070418626869)
            ·
              refine ⟨5974868807123444101746269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63731933942650070418626869 5974868807123444101746269)
              ·
                refine ⟨2240575802671291538154851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5974868807123444101746269 2240575802671291538154851)
                ·
                  refine ⟨3360863704006937307232277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2240575802671291538154851 3360863704006937307232277)
                  ·
                    refine ⟨157540486125325186276513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3360863704006937307232277 157540486125325186276513)
                    ·
                      rfl

theorem cell23_920427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 6].length) (baseStart_920427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920427 prefixEnd_920427 := by exact prefixLift 920427
  have htrace : WordTrace (prefixWord ++ tailWord_920427) baseStart_920427 baseEnd_920427 := by
    simpa [prefixWord, tailWord_920427, baseEnd_920427] using wordTrace_append hprefix tailTrace_920427
  have hstable : (prefixWord ++ tailWord_920427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920427).length < 2 ^ (prefixWord ++ tailWord_920427).sum := by decide
  have hdescent : baseEnd_920427 < baseStart_920427 := by decide
  rcases family_descends (prefixWord ++ tailWord_920427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920434 : List Nat := [3, 2, 1, 2, 1, 1, 4, 1, 3, 1, 4]
def baseStart_920434 : Nat := 118140960795 + 920434 * 2 ^ 59
def prefixEnd_920434 : Nat := 4983230072969 + 3 ^ 40 * 920434 * 2
def baseEnd_920434 : Nat := 472625052740557031442007

theorem tailTrace_920434 : CollatzResearch.WordTrace tailWord_920434 prefixEnd_920434 472625052740557031442007 := by
  unfold tailWord_920434
  simp only [CollatzResearch.WordTrace]
  refine ⟨8392746486858072614292089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22380657298288193638112237 8392746486858072614292089)
  ·
    refine ⟨6294559865143554460719067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8392746486858072614292089 6294559865143554460719067)
    ·
      refine ⟨9441839797715331691078601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6294559865143554460719067 9441839797715331691078601)
      ·
        refine ⟨7081379848286498768308951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9441839797715331691078601 7081379848286498768308951)
        ·
          refine ⟨10622069772429748152463427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7081379848286498768308951 10622069772429748152463427)
          ·
            refine ⟨15933104658644622228695141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10622069772429748152463427 15933104658644622228695141)
            ·
              refine ⟨2987457123495866667880339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15933104658644622228695141 2987457123495866667880339)
              ·
                refine ⟨4481185685243800001820509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2987457123495866667880339 4481185685243800001820509)
                ·
                  refine ⟨1680444631966425000682691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4481185685243800001820509 1680444631966425000682691)
                  ·
                    refine ⟨2520666947949637501024037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1680444631966425000682691 2520666947949637501024037)
                    ·
                      refine ⟨472625052740557031442007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2520666947949637501024037 472625052740557031442007)
                      ·
                        rfl

theorem cell23_920434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_920434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920434 prefixEnd_920434 := by exact prefixLift 920434
  have htrace : WordTrace (prefixWord ++ tailWord_920434) baseStart_920434 baseEnd_920434 := by
    simpa [prefixWord, tailWord_920434, baseEnd_920434] using wordTrace_append hprefix tailTrace_920434
  have hstable : (prefixWord ++ tailWord_920434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920434).length < 2 ^ (prefixWord ++ tailWord_920434).sum := by decide
  have hdescent : baseEnd_920434 < baseStart_920434 := by decide
  rcases family_descends (prefixWord ++ tailWord_920434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920438 : List Nat := [5, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2]
def baseStart_920438 : Nat := 118140960795 + 920438 * 2 ^ 59
def prefixEnd_920438 : Nat := 4983230072969 + 3 ^ 40 * 920438 * 2
def baseEnd_920438 : Nat := 472627106663175015791989

theorem tailTrace_920438 : CollatzResearch.WordTrace tailWord_920438 prefixEnd_920438 472627106663175015791989 := by
  unfold tailWord_920438
  simp only [CollatzResearch.WordTrace]
  refine ⟨2098195739963612446269623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22380754559611866093542645 2098195739963612446269623)
  ·
    refine ⟨3147293609945418669404435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2098195739963612446269623 3147293609945418669404435)
    ·
      refine ⟨4720940414918128004106653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3147293609945418669404435 4720940414918128004106653)
      ·
        refine ⟨1770352655594298001539995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4720940414918128004106653 1770352655594298001539995)
        ·
          refine ⟨2655528983391447002309993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1770352655594298001539995 2655528983391447002309993)
          ·
            refine ⟨1991646737543585251732495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2655528983391447002309993 1991646737543585251732495)
            ·
              refine ⟨2987470106315377877598743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1991646737543585251732495 2987470106315377877598743)
              ·
                refine ⟨4481205159473066816398115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2987470106315377877598743 4481205159473066816398115)
                ·
                  refine ⟨6721807739209600224597173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4481205159473066816398115 6721807739209600224597173)
                  ·
                    refine ⟨630169475550900021055985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6721807739209600224597173 630169475550900021055985)
                    ·
                      refine ⟨472627106663175015791989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 630169475550900021055985 472627106663175015791989)
                      ·
                        rfl

theorem cell23_920438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_920438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920438 prefixEnd_920438 := by exact prefixLift 920438
  have htrace : WordTrace (prefixWord ++ tailWord_920438) baseStart_920438 baseEnd_920438 := by
    simpa [prefixWord, tailWord_920438, baseEnd_920438] using wordTrace_append hprefix tailTrace_920438
  have hstable : (prefixWord ++ tailWord_920438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920438).length < 2 ^ (prefixWord ++ tailWord_920438).sum := by decide
  have hdescent : baseEnd_920438 < baseStart_920438 := by decide
  rcases family_descends (prefixWord ++ tailWord_920438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920451 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 5, 2, 2]
def baseStart_920451 : Nat := 118140960795 + 920451 * 2 ^ 59
def prefixEnd_920451 : Nat := 4983230072969 + 3 ^ 40 * 920451 * 2
def baseEnd_920451 : Nat := 472633781911683464929429

theorem tailTrace_920451 : CollatzResearch.WordTrace tailWord_920451 prefixEnd_920451 472633781911683464929429 := by
  unfold tailWord_920451
  simp only [CollatzResearch.WordTrace]
  refine ⟨33571605988370702360537207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22381070658913801573691471 33571605988370702360537207)
  ·
    refine ⟨50357408982556053540805811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33571605988370702360537207 50357408982556053540805811)
    ·
      refine ⟨75536113473834080311208717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50357408982556053540805811 75536113473834080311208717)
      ·
        refine ⟨28326042552687780116703269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75536113473834080311208717 28326042552687780116703269)
        ·
          refine ⟨5311132978628958771881863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28326042552687780116703269 5311132978628958771881863)
          ·
            refine ⟨7966699467943438157822795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5311132978628958771881863 7966699467943438157822795)
            ·
              refine ⟨11950049201915157236734193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7966699467943438157822795 11950049201915157236734193)
              ·
                refine ⟨8962536901436367927550645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11950049201915157236734193 8962536901436367927550645)
                ·
                  refine ⟨840237834509659493207873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8962536901436367927550645 840237834509659493207873)
                  ·
                    refine ⟨630178375882244619905905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 840237834509659493207873 630178375882244619905905)
                    ·
                      refine ⟨472633781911683464929429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 630178375882244619905905 472633781911683464929429)
                      ·
                        rfl

theorem cell23_920451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 5, 2, 2].length) (baseStart_920451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920451 prefixEnd_920451 := by exact prefixLift 920451
  have htrace : WordTrace (prefixWord ++ tailWord_920451) baseStart_920451 baseEnd_920451 := by
    simpa [prefixWord, tailWord_920451, baseEnd_920451] using wordTrace_append hprefix tailTrace_920451
  have hstable : (prefixWord ++ tailWord_920451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920451).length < 2 ^ (prefixWord ++ tailWord_920451).sum := by decide
  have hdescent : baseEnd_920451 < baseStart_920451 := by decide
  rcases family_descends (prefixWord ++ tailWord_920451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920457 : List Nat := [1, 2, 1, 1, 5, 3, 10]
def baseStart_920457 : Nat := 118140960795 + 920457 * 2 ^ 59
def prefixEnd_920457 : Nat := 4983230072969 + 3 ^ 40 * 920457 * 2
def baseEnd_920457 : Nat := 5835022997476672116721

theorem tailTrace_920457 : CollatzResearch.WordTrace tailWord_920457 prefixEnd_920457 5835022997476672116721 := by
  unfold tailWord_920457
  simp only [CollatzResearch.WordTrace]
  refine ⟨33571824826348965385255625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22381216550899310256837083 33571824826348965385255625)
  ·
    refine ⟨25178868619761724038941719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33571824826348965385255625 25178868619761724038941719)
    ·
      refine ⟨37768302929642586058412579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25178868619761724038941719 37768302929642586058412579)
      ·
        refine ⟨56652454394463879087618869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37768302929642586058412579 56652454394463879087618869)
        ·
          refine ⟨5311167599480988664464269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56652454394463879087618869 5311167599480988664464269)
          ·
            refine ⟨1991687849805370749174101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5311167599480988664464269 1991687849805370749174101)
            ·
              refine ⟨5835022997476672116721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1991687849805370749174101 5835022997476672116721)
              ·
                rfl

theorem cell23_920457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 10].length) (baseStart_920457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920457 prefixEnd_920457 := by exact prefixLift 920457
  have htrace : WordTrace (prefixWord ++ tailWord_920457) baseStart_920457 baseEnd_920457 := by
    simpa [prefixWord, tailWord_920457, baseEnd_920457] using wordTrace_append hprefix tailTrace_920457
  have hstable : (prefixWord ++ tailWord_920457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920457).length < 2 ^ (prefixWord ++ tailWord_920457).sum := by decide
  have hdescent : baseEnd_920457 < baseStart_920457 := by decide
  rcases family_descends (prefixWord ++ tailWord_920457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920481 : List Nat := [1, 2, 3, 4, 1, 1, 3, 1, 1, 2, 4]
def baseStart_920481 : Nat := 118140960795 + 920481 * 2 ^ 59
def prefixEnd_920481 : Nat := 4983230072969 + 3 ^ 40 * 920481 * 2
def baseEnd_920481 : Nat := 472649186331318347554291

theorem tailTrace_920481 : CollatzResearch.WordTrace tailWord_920481 prefixEnd_920481 472649186331318347554291 := by
  unfold tailWord_920481
  simp only [CollatzResearch.WordTrace]
  refine ⟨33572700178262017484129297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22381800118841344989419531 33572700178262017484129297)
  ·
    refine ⟨25179525133696513113096973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33572700178262017484129297 25179525133696513113096973)
    ·
      refine ⟨9442321925136192417411365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25179525133696513113096973 9442321925136192417411365)
      ·
        refine ⟨1770435360963036078264631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9442321925136192417411365 1770435360963036078264631)
        ·
          refine ⟨2655653041444554117396947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1770435360963036078264631 2655653041444554117396947)
          ·
            refine ⟨3983479562166831176095421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2655653041444554117396947 3983479562166831176095421)
            ·
              refine ⟨1493804835812561691035783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3983479562166831176095421 1493804835812561691035783)
              ·
                refine ⟨2240707253718842536553675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1493804835812561691035783 2240707253718842536553675)
                ·
                  refine ⟨3361060880578263804830513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2240707253718842536553675 3361060880578263804830513)
                  ·
                    refine ⟨2520795660433697853622885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3361060880578263804830513 2520795660433697853622885)
                    ·
                      refine ⟨472649186331318347554291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2520795660433697853622885 472649186331318347554291)
                      ·
                        rfl

theorem cell23_920481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_920481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920481 prefixEnd_920481 := by exact prefixLift 920481
  have htrace : WordTrace (prefixWord ++ tailWord_920481) baseStart_920481 baseEnd_920481 := by
    simpa [prefixWord, tailWord_920481, baseEnd_920481] using wordTrace_append hprefix tailTrace_920481
  have hstable : (prefixWord ++ tailWord_920481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920481).length < 2 ^ (prefixWord ++ tailWord_920481).sum := by decide
  have hdescent : baseEnd_920481 < baseStart_920481 := by decide
  rcases family_descends (prefixWord ++ tailWord_920481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920501 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 6, 1, 3]
def baseStart_920501 : Nat := 118140960795 + 920501 * 2 ^ 59
def prefixEnd_920501 : Nat := 4983230072969 + 3 ^ 40 * 920501 * 2
def baseEnd_920501 : Nat := 472659455944408269304199

theorem tailTrace_920501 : CollatzResearch.WordTrace tailWord_920501 prefixEnd_920501 472659455944408269304199 := by
  unfold tailWord_920501
  simp only [CollatzResearch.WordTrace]
  refine ⟨33573429638189560899857357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22382286425459707266571571 33573429638189560899857357)
  ·
    refine ⟨12590036114321085337446509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33573429638189560899857357 12590036114321085337446509)
    ·
      refine ⟨4721263542870407001542441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12590036114321085337446509 4721263542870407001542441)
      ·
        refine ⟨3540947657152805251156831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4721263542870407001542441 3540947657152805251156831)
        ·
          refine ⟨5311421485729207876735247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3540947657152805251156831 5311421485729207876735247)
          ·
            refine ⟨7967132228593811815102871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5311421485729207876735247 7967132228593811815102871)
            ·
              refine ⟨11950698342890717722654307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7967132228593811815102871 11950698342890717722654307)
              ·
                refine ⟨17926047514336076583981461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11950698342890717722654307 17926047514336076583981461)
                ·
                  refine ⟨840283477234503589874131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17926047514336076583981461 840283477234503589874131)
                  ·
                    refine ⟨1260425215851755384811197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 840283477234503589874131 1260425215851755384811197)
                    ·
                      refine ⟨472659455944408269304199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1260425215851755384811197 472659455944408269304199)
                      ·
                        rfl

theorem cell23_920501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_920501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920501 prefixEnd_920501 := by exact prefixLift 920501
  have htrace : WordTrace (prefixWord ++ tailWord_920501) baseStart_920501 baseEnd_920501 := by
    simpa [prefixWord, tailWord_920501, baseEnd_920501] using wordTrace_append hprefix tailTrace_920501
  have hstable : (prefixWord ++ tailWord_920501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920501).length < 2 ^ (prefixWord ++ tailWord_920501).sum := by decide
  have hdescent : baseEnd_920501 < baseStart_920501 := by decide
  rcases family_descends (prefixWord ++ tailWord_920501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920524 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 2, 3, 4]
def baseStart_920524 : Nat := 118140960795 + 920524 * 2 ^ 59
def prefixEnd_920524 : Nat := 4983230072969 + 3 ^ 40 * 920524 * 2
def baseEnd_920524 : Nat := 472671265999461679316593

theorem tailTrace_920524 : CollatzResearch.WordTrace tailWord_920524 prefixEnd_920524 472671265999461679316593 := by
  unfold tailWord_920524
  simp only [CollatzResearch.WordTrace]
  refine ⟨16787134258553117913972313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22382845678070823885296417 16787134258553117913972313)
  ·
    refine ⟨12590350693914838435479235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16787134258553117913972313 12590350693914838435479235)
    ·
      refine ⟨18885526040872257653218853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12590350693914838435479235 18885526040872257653218853)
      ·
        refine ⟨3541036132663548309978535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18885526040872257653218853 3541036132663548309978535)
        ·
          refine ⟨5311554198995322464967803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3541036132663548309978535 5311554198995322464967803)
          ·
            refine ⟨7967331298492983697451705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5311554198995322464967803 7967331298492983697451705)
            ·
              refine ⟨5975498473869737773088779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7967331298492983697451705 5975498473869737773088779)
              ·
                refine ⟨8963247710804606659633169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5975498473869737773088779 8963247710804606659633169)
                ·
                  refine ⟨6722435783103454994724877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8963247710804606659633169 6722435783103454994724877)
                  ·
                    refine ⟨2520913418663795623021829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6722435783103454994724877 2520913418663795623021829)
                    ·
                      refine ⟨472671265999461679316593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2520913418663795623021829 472671265999461679316593)
                      ·
                        rfl

theorem cell23_920524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_920524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920524 prefixEnd_920524 := by exact prefixLift 920524
  have htrace : WordTrace (prefixWord ++ tailWord_920524) baseStart_920524 baseEnd_920524 := by
    simpa [prefixWord, tailWord_920524, baseEnd_920524] using wordTrace_append hprefix tailTrace_920524
  have hstable : (prefixWord ++ tailWord_920524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920524).length < 2 ^ (prefixWord ++ tailWord_920524).sum := by decide
  have hdescent : baseEnd_920524 < baseStart_920524 := by decide
  rcases family_descends (prefixWord ++ tailWord_920524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920525 : List Nat := [1, 6, 3, 1, 1, 1, 2, 8]
def baseStart_920525 : Nat := 118140960795 + 920525 * 2 ^ 59
def prefixEnd_920525 : Nat := 4983230072969 + 3 ^ 40 * 920525 * 2
def baseEnd_920525 : Nat := 17506362202967265755707

theorem tailTrace_920525 : CollatzResearch.WordTrace tailWord_920525 prefixEnd_920525 17506362202967265755707 := by
  unfold tailWord_920525
  simp only [CollatzResearch.WordTrace]
  refine ⟨33574304990102612998731029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22382869993401741999154019 33574304990102612998731029)
  ·
    refine ⟨1573795546411059984315517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33574304990102612998731029 1573795546411059984315517)
    ·
      refine ⟨590173329904147494118319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1573795546411059984315517 590173329904147494118319)
      ·
        refine ⟨885259994856221241177479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590173329904147494118319 885259994856221241177479)
        ·
          refine ⟨1327889992284331861766219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 885259994856221241177479 1327889992284331861766219)
          ·
            refine ⟨1991834988426497792649329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1327889992284331861766219 1991834988426497792649329)
            ·
              refine ⟨1493876241319873344486997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1991834988426497792649329 1493876241319873344486997)
              ·
                refine ⟨17506362202967265755707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1493876241319873344486997 17506362202967265755707)
                ·
                  rfl

theorem cell23_920525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 8].length) (baseStart_920525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920525 prefixEnd_920525 := by exact prefixLift 920525
  have htrace : WordTrace (prefixWord ++ tailWord_920525) baseStart_920525 baseEnd_920525 := by
    simpa [prefixWord, tailWord_920525, baseEnd_920525] using wordTrace_append hprefix tailTrace_920525
  have hstable : (prefixWord ++ tailWord_920525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920525).length < 2 ^ (prefixWord ++ tailWord_920525).sum := by decide
  have hdescent : baseEnd_920525 < baseStart_920525 := by decide
  rcases family_descends (prefixWord ++ tailWord_920525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920581 : List Nat := [1, 3, 1, 1, 2, 3, 3, 4, 5]
def baseStart_920581 : Nat := 118140960795 + 920581 * 2 ^ 59
def prefixEnd_920581 : Nat := 4983230072969 + 3 ^ 40 * 920581 * 2
def baseEnd_920581 : Nat := 52522281599640884033759

theorem tailTrace_920581 : CollatzResearch.WordTrace tailWord_920581 prefixEnd_920581 52522281599640884033759 := by
  unfold tailWord_920581
  simp only [CollatzResearch.WordTrace]
  refine ⟨33576347477899734562769597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22384231651933156375179731 33576347477899734562769597)
  ·
    refine ⟨12591130304212400461038599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33576347477899734562769597 12591130304212400461038599)
    ·
      refine ⟨18886695456318600691557899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12591130304212400461038599 18886695456318600691557899)
      ·
        refine ⟨28330043184477901037336849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18886695456318600691557899 28330043184477901037336849)
        ·
          refine ⟨21247532388358425778002637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28330043184477901037336849 21247532388358425778002637)
          ·
            refine ⟨7967824645634409666750989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21247532388358425778002637 7967824645634409666750989)
            ·
              refine ⟨2987934242112903625031621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7967824645634409666750989 2987934242112903625031621)
              ·
                refine ⟨560237670396169429693429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2987934242112903625031621 560237670396169429693429)
                ·
                  refine ⟨52522281599640884033759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 560237670396169429693429 52522281599640884033759)
                  ·
                    rfl

theorem cell23_920581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 4, 5].length) (baseStart_920581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920581 prefixEnd_920581 := by exact prefixLift 920581
  have htrace : WordTrace (prefixWord ++ tailWord_920581) baseStart_920581 baseEnd_920581 := by
    simpa [prefixWord, tailWord_920581, baseEnd_920581] using wordTrace_append hprefix tailTrace_920581
  have hstable : (prefixWord ++ tailWord_920581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920581).length < 2 ^ (prefixWord ++ tailWord_920581).sum := by decide
  have hdescent : baseEnd_920581 < baseStart_920581 := by decide
  rcases family_descends (prefixWord ++ tailWord_920581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920611 : List Nat := [1, 1, 1, 4, 3, 2, 3, 1, 2, 5]
def baseStart_920611 : Nat := 118140960795 + 920611 * 2 ^ 59
def prefixEnd_920611 : Nat := 4983230072969 + 3 ^ 40 * 920611 * 2
def baseEnd_920611 : Nat := 157571979605467612976231

theorem tailTrace_920611 : CollatzResearch.WordTrace tailWord_920611 prefixEnd_920611 157571979605467612976231 := by
  unfold tailWord_920611
  simp only [CollatzResearch.WordTrace]
  refine ⟨33577441667791049686361687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22384961111860699790907791 33577441667791049686361687)
  ·
    refine ⟨50366162501686574529542531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33577441667791049686361687 50366162501686574529542531)
    ·
      refine ⟨75549243752529861794313797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50366162501686574529542531 75549243752529861794313797)
      ·
        refine ⟨14165483203599349086433837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75549243752529861794313797 14165483203599349086433837)
        ·
          refine ⟨5312056201349755907412689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14165483203599349086433837 5312056201349755907412689)
          ·
            refine ⟨3984042151012316930559517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5312056201349755907412689 3984042151012316930559517)
            ·
              refine ⟨1494015806629618848959819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3984042151012316930559517 1494015806629618848959819)
              ·
                refine ⟨2241023709944428273439729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1494015806629618848959819 2241023709944428273439729)
                ·
                  refine ⟨1680767782458321205079797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2241023709944428273439729 1680767782458321205079797)
                  ·
                    refine ⟨157571979605467612976231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1680767782458321205079797 157571979605467612976231)
                    ·
                      rfl

theorem cell23_920611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 5].length) (baseStart_920611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920611 prefixEnd_920611 := by exact prefixLift 920611
  have htrace : WordTrace (prefixWord ++ tailWord_920611) baseStart_920611 baseEnd_920611 := by
    simpa [prefixWord, tailWord_920611, baseEnd_920611] using wordTrace_append hprefix tailTrace_920611
  have hstable : (prefixWord ++ tailWord_920611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920611).length < 2 ^ (prefixWord ++ tailWord_920611).sum := by decide
  have hdescent : baseEnd_920611 < baseStart_920611 := by decide
  rcases family_descends (prefixWord ++ tailWord_920611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920615 : List Nat := [1, 1, 7, 1, 1, 2, 2, 3, 5]
def baseStart_920615 : Nat := 118140960795 + 920615 * 2 ^ 59
def prefixEnd_920615 : Nat := 4983230072969 + 3 ^ 40 * 920615 * 2
def baseEnd_920615 : Nat := 52524221415446758142075

theorem tailTrace_920615 : CollatzResearch.WordTrace tailWord_920615 prefixEnd_920615 52524221415446758142075 := by
  unfold tailWord_920615
  simp only [CollatzResearch.WordTrace]
  refine ⟨33577587559776558369507299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22385058373184372246338199 33577587559776558369507299)
  ·
    refine ⟨50366381339664837554260949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33577587559776558369507299 50366381339664837554260949)
    ·
      refine ⟨1180462062648394630177991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 50366381339664837554260949 1180462062648394630177991)
      ·
        refine ⟨1770693093972591945266987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1180462062648394630177991 1770693093972591945266987)
        ·
          refine ⟨2656039640958887917900481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1770693093972591945266987 2656039640958887917900481)
          ·
            refine ⟨1992029730719165938425361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2656039640958887917900481 1992029730719165938425361)
            ·
              refine ⟨1494022298039374453819021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1992029730719165938425361 1494022298039374453819021)
              ·
                refine ⟨560258361764765420182133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1494022298039374453819021 560258361764765420182133)
                ·
                  refine ⟨52524221415446758142075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 560258361764765420182133 52524221415446758142075)
                  ·
                    rfl

theorem cell23_920615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 3, 5].length) (baseStart_920615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920615 prefixEnd_920615 := by exact prefixLift 920615
  have htrace : WordTrace (prefixWord ++ tailWord_920615) baseStart_920615 baseEnd_920615 := by
    simpa [prefixWord, tailWord_920615, baseEnd_920615] using wordTrace_append hprefix tailTrace_920615
  have hstable : (prefixWord ++ tailWord_920615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920615).length < 2 ^ (prefixWord ++ tailWord_920615).sum := by decide
  have hdescent : baseEnd_920615 < baseStart_920615 := by decide
  rcases family_descends (prefixWord ++ tailWord_920615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920634 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 2, 3, 5]
def baseStart_920634 : Nat := 118140960795 + 920634 * 2 ^ 59
def prefixEnd_920634 : Nat := 4983230072969 + 3 ^ 40 * 920634 * 2
def baseEnd_920634 : Nat := 472727748871456248941087

theorem tailTrace_920634 : CollatzResearch.WordTrace tailWord_920634 prefixEnd_920634 472727748871456248941087 := by
  unfold tailWord_920634
  simp only [CollatzResearch.WordTrace]
  refine ⟨8394570136676931153612239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22385520364471816409632637 8394570136676931153612239)
  ·
    refine ⟨12591855205015396730418359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8394570136676931153612239 12591855205015396730418359)
    ·
      refine ⟨18887782807523095095627539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12591855205015396730418359 18887782807523095095627539)
      ·
        refine ⟨28331674211284642643441309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18887782807523095095627539 28331674211284642643441309)
        ·
          refine ⟨10624377829231740991290491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28331674211284642643441309 10624377829231740991290491)
          ·
            refine ⟨15936566743847611486935737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10624377829231740991290491 15936566743847611486935737)
            ·
              refine ⟨11952425057885708615201803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15936566743847611486935737 11952425057885708615201803)
              ·
                refine ⟨17928637586828562922802705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11952425057885708615201803 17928637586828562922802705)
                ·
                  refine ⟨13446478190121422192102029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17928637586828562922802705 13446478190121422192102029)
                  ·
                    refine ⟨5042429321295533322038261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13446478190121422192102029 5042429321295533322038261)
                    ·
                      refine ⟨472727748871456248941087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5042429321295533322038261 472727748871456248941087)
                      ·
                        rfl

theorem cell23_920634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_920634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920634 prefixEnd_920634 := by exact prefixLift 920634
  have htrace : WordTrace (prefixWord ++ tailWord_920634) baseStart_920634 baseEnd_920634 := by
    simpa [prefixWord, tailWord_920634, baseEnd_920634] using wordTrace_append hprefix tailTrace_920634
  have hstable : (prefixWord ++ tailWord_920634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920634).length < 2 ^ (prefixWord ++ tailWord_920634).sum := by decide
  have hdescent : baseEnd_920634 < baseStart_920634 := by decide
  rcases family_descends (prefixWord ++ tailWord_920634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920658 : List Nat := [3, 2, 2, 1, 3, 1, 2, 2, 3, 4]
def baseStart_920658 : Nat := 118140960795 + 920658 * 2 ^ 59
def prefixEnd_920658 : Nat := 4983230072969 + 3 ^ 40 * 920658 * 2
def baseEnd_920658 : Nat := 157580024135721385013659

theorem tailTrace_920658 : CollatzResearch.WordTrace tailWord_920658 prefixEnd_920658 157580024135721385013659 := by
  unfold tailWord_920658
  simp only [CollatzResearch.WordTrace]
  refine ⟨8394788974655194178330657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22386103932413851142215085 8394788974655194178330657)
  ·
    refine ⟨6296091730991395633747993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8394788974655194178330657 6296091730991395633747993)
    ·
      refine ⟨4722068798243546725310995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6296091730991395633747993 4722068798243546725310995)
      ·
        refine ⟨7083103197365320087966493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4722068798243546725310995 7083103197365320087966493)
        ·
          refine ⟨2656163699011995032987435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7083103197365320087966493 2656163699011995032987435)
          ·
            refine ⟨3984245548517992549481153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2656163699011995032987435 3984245548517992549481153)
            ·
              refine ⟨2988184161388494412110865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3984245548517992549481153 2988184161388494412110865)
              ·
                refine ⟨2241138121041370809083149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2988184161388494412110865 2241138121041370809083149)
                ·
                  refine ⟨840426795390514053406181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2241138121041370809083149 840426795390514053406181)
                  ·
                    refine ⟨157580024135721385013659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 840426795390514053406181 157580024135721385013659)
                    ·
                      rfl

theorem cell23_920658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_920658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920658 prefixEnd_920658 := by exact prefixLift 920658
  have htrace : WordTrace (prefixWord ++ tailWord_920658) baseStart_920658 baseEnd_920658 := by
    simpa [prefixWord, tailWord_920658, baseEnd_920658] using wordTrace_append hprefix tailTrace_920658
  have hstable : (prefixWord ++ tailWord_920658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920658).length < 2 ^ (prefixWord ++ tailWord_920658).sum := by decide
  have hdescent : baseEnd_920658 < baseStart_920658 := by decide
  rcases family_descends (prefixWord ++ tailWord_920658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920668 : List Nat := [2, 2, 4, 1, 1, 1, 2, 3, 2, 2, 3]
def baseStart_920668 : Nat := 118140960795 + 920668 * 2 ^ 59
def prefixEnd_920668 : Nat := 4983230072969 + 3 ^ 40 * 920668 * 2
def baseEnd_920668 : Nat := 472745207213709115915931

theorem tailTrace_920668 : CollatzResearch.WordTrace tailWord_920668 prefixEnd_920668 472745207213709115915931 := by
  unfold tailWord_920668
  simp only [CollatzResearch.WordTrace]
  refine ⟨16789760314292274210593329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22386347085723032280791105 16789760314292274210593329)
  ·
    refine ⟨12592320235719205657944997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16789760314292274210593329 12592320235719205657944997)
    ·
      refine ⟨2361060044197351060864687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12592320235719205657944997 2361060044197351060864687)
      ·
        refine ⟨3541590066296026591297031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2361060044197351060864687 3541590066296026591297031)
        ·
          refine ⟨5312385099444039886945547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3541590066296026591297031 5312385099444039886945547)
          ·
            refine ⟨7968577649166059830418321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5312385099444039886945547 7968577649166059830418321)
            ·
              refine ⟨5976433236874544872813741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7968577649166059830418321 5976433236874544872813741)
              ·
                refine ⟨2241162463827954327305153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5976433236874544872813741 2241162463827954327305153)
                ·
                  refine ⟨1680871847870965745478865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2241162463827954327305153 1680871847870965745478865)
                  ·
                    refine ⟨1260653885903224309109149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1680871847870965745478865 1260653885903224309109149)
                    ·
                      refine ⟨472745207213709115915931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1260653885903224309109149 472745207213709115915931)
                      ·
                        rfl

theorem cell23_920668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_920668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920668 prefixEnd_920668 := by exact prefixLift 920668
  have htrace : WordTrace (prefixWord ++ tailWord_920668) baseStart_920668 baseEnd_920668 := by
    simpa [prefixWord, tailWord_920668, baseEnd_920668] using wordTrace_append hprefix tailTrace_920668
  have hstable : (prefixWord ++ tailWord_920668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920668).length < 2 ^ (prefixWord ++ tailWord_920668).sum := by decide
  have hdescent : baseEnd_920668 < baseStart_920668 := by decide
  rcases family_descends (prefixWord ++ tailWord_920668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920691 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 2, 9, 2]
def baseStart_920691 : Nat := 118140960795 + 920691 * 2 ^ 59
def prefixEnd_920691 : Nat := 4983230072969 + 3 ^ 40 * 920691 * 2
def baseEnd_920691 : Nat := 472757017268762525928325

theorem tailTrace_920691 : CollatzResearch.WordTrace tailWord_920691 prefixEnd_920691 472757017268762525928325 := by
  unfold tailWord_920691
  simp only [CollatzResearch.WordTrace]
  refine ⟨33580359507501223349273927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22386906338334148899515951 33580359507501223349273927)
  ·
    refine ⟨50370539261251835023910891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33580359507501223349273927 50370539261251835023910891)
    ·
      refine ⟨75555808891877752535866337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50370539261251835023910891 75555808891877752535866337)
      ·
        refine ⟨56666856668908314401899753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75555808891877752535866337 56666856668908314401899753)
        ·
          refine ⟨42500142501681235801424815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56666856668908314401899753 42500142501681235801424815)
          ·
            refine ⟨63750213752521853702137223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42500142501681235801424815 63750213752521853702137223)
            ·
              refine ⟨95625320628782780553205835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63750213752521853702137223 95625320628782780553205835)
              ·
                refine ⟨143437980943174170829808753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95625320628782780553205835 143437980943174170829808753)
                ·
                  refine ⟨107578485707380628122356565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143437980943174170829808753 107578485707380628122356565)
                  ·
                    refine ⟨630342689691683367904433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 107578485707380628122356565 630342689691683367904433)
                    ·
                      refine ⟨472757017268762525928325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 630342689691683367904433 472757017268762525928325)
                      ·
                        rfl

theorem cell23_920691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 9, 2].length) (baseStart_920691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920691 prefixEnd_920691 := by exact prefixLift 920691
  have htrace : WordTrace (prefixWord ++ tailWord_920691) baseStart_920691 baseEnd_920691 := by
    simpa [prefixWord, tailWord_920691, baseEnd_920691] using wordTrace_append hprefix tailTrace_920691
  have hstable : (prefixWord ++ tailWord_920691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920691).length < 2 ^ (prefixWord ++ tailWord_920691).sum := by decide
  have hdescent : baseEnd_920691 < baseStart_920691 := by decide
  rcases family_descends (prefixWord ++ tailWord_920691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920701 : List Nat := [1, 4, 1, 1, 3, 1, 2, 2, 3, 5]
def baseStart_920701 : Nat := 118140960795 + 920701 * 2 ^ 59
def prefixEnd_920701 : Nat := 4983230072969 + 3 ^ 40 * 920701 * 2
def baseEnd_920701 : Nat := 157587384025102495601093

theorem tailTrace_920701 : CollatzResearch.WordTrace tailWord_920701 prefixEnd_920701 157587384025102495601093 := by
  unfold tailWord_920701
  simp only [CollatzResearch.WordTrace]
  refine ⟨33580724237464995057137957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22387149491643330038091971 33580724237464995057137957)
  ·
    refine ⟨6296385794524686573213367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33580724237464995057137957 6296385794524686573213367)
    ·
      refine ⟨9444578691787029859820051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6296385794524686573213367 9444578691787029859820051)
      ·
        refine ⟨14166868037680544789730077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9444578691787029859820051 14166868037680544789730077)
        ·
          refine ⟨5312575514130204296148779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14166868037680544789730077 5312575514130204296148779)
          ·
            refine ⟨7968863271195306444223169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5312575514130204296148779 7968863271195306444223169)
            ·
              refine ⟨5976647453396479833167377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7968863271195306444223169 5976647453396479833167377)
              ·
                refine ⟨4482485590047359874875533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5976647453396479833167377 4482485590047359874875533)
                ·
                  refine ⟨1680932096267759953078325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4482485590047359874875533 1680932096267759953078325)
                  ·
                    refine ⟨157587384025102495601093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1680932096267759953078325 157587384025102495601093)
                    ·
                      rfl

theorem cell23_920701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_920701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920701 prefixEnd_920701 := by exact prefixLift 920701
  have htrace : WordTrace (prefixWord ++ tailWord_920701) baseStart_920701 baseEnd_920701 := by
    simpa [prefixWord, tailWord_920701, baseEnd_920701] using wordTrace_append hprefix tailTrace_920701
  have hstable : (prefixWord ++ tailWord_920701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920701).length < 2 ^ (prefixWord ++ tailWord_920701).sum := by decide
  have hdescent : baseEnd_920701 < baseStart_920701 := by decide
  rcases family_descends (prefixWord ++ tailWord_920701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920705 : List Nat := [1, 2, 4, 2, 2, 3, 2, 1, 6]
def baseStart_920705 : Nat := 118140960795 + 920705 * 2 ^ 59
def prefixEnd_920705 : Nat := 4983230072969 + 3 ^ 40 * 920705 * 2
def baseEnd_920705 : Nat := 52529356221991719017029

theorem tailTrace_920705 : CollatzResearch.WordTrace tailWord_920705 prefixEnd_920705 52529356221991719017029 := by
  unfold tailWord_920705
  simp only [CollatzResearch.WordTrace]
  refine ⟨33580870129450503740283569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22387246752967002493522379 33580870129450503740283569)
  ·
    refine ⟨25185652597087877805212677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33580870129450503740283569 25185652597087877805212677)
    ·
      refine ⟨4722309861953977088477377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25185652597087877805212677 4722309861953977088477377)
      ·
        refine ⟨3541732396465482816358033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4722309861953977088477377 3541732396465482816358033)
        ·
          refine ⟨2656299297349112112268525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3541732396465482816358033 2656299297349112112268525)
          ·
            refine ⟨996112236505917042100697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2656299297349112112268525 996112236505917042100697)
            ·
              refine ⟨747084177379437781575523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 996112236505917042100697 747084177379437781575523)
              ·
                refine ⟨1120626266069156672363285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 747084177379437781575523 1120626266069156672363285)
                ·
                  refine ⟨52529356221991719017029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1120626266069156672363285 52529356221991719017029)
                  ·
                    rfl

theorem cell23_920705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 6].length) (baseStart_920705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920705 prefixEnd_920705 := by exact prefixLift 920705
  have htrace : WordTrace (prefixWord ++ tailWord_920705) baseStart_920705 baseEnd_920705 := by
    simpa [prefixWord, tailWord_920705, baseEnd_920705] using wordTrace_append hprefix tailTrace_920705
  have hstable : (prefixWord ++ tailWord_920705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920705).length < 2 ^ (prefixWord ++ tailWord_920705).sum := by decide
  have hdescent : baseEnd_920705 < baseStart_920705 := by decide
  rcases family_descends (prefixWord ++ tailWord_920705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920718 : List Nat := [4, 1, 1, 3, 2, 2, 1, 1, 3, 5]
def baseStart_920718 : Nat := 118140960795 + 920718 * 2 ^ 59
def prefixEnd_920718 : Nat := 4983230072969 + 3 ^ 40 * 920718 * 2
def baseEnd_920718 : Nat := 157590293748811306763567

theorem tailTrace_920718 : CollatzResearch.WordTrace tailWord_920718 prefixEnd_920718 157590293748811306763567 := by
  unfold tailWord_920718
  simp only [CollatzResearch.WordTrace]
  refine ⟨4197668034800425870063351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22387562852268937973671205 4197668034800425870063351)
  ·
    refine ⟨6296502052200638805095027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4197668034800425870063351 6296502052200638805095027)
    ·
      refine ⟨9444753078300958207642541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6296502052200638805095027 9444753078300958207642541)
      ·
        refine ⟨3541782404362859327865953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9444753078300958207642541 3541782404362859327865953)
        ·
          refine ⟨2656336803272144495899465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3541782404362859327865953 2656336803272144495899465)
          ·
            refine ⟨1992252602454108371924599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2656336803272144495899465 1992252602454108371924599)
            ·
              refine ⟨2988378903681162557886899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1992252602454108371924599 2988378903681162557886899)
              ·
                refine ⟨4482568355521743836830349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2988378903681162557886899 4482568355521743836830349)
                ·
                  refine ⟨1680963133320653938811381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4482568355521743836830349 1680963133320653938811381)
                  ·
                    refine ⟨157590293748811306763567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1680963133320653938811381 157590293748811306763567)
                    ·
                      rfl

theorem cell23_920718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_920718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920718 prefixEnd_920718 := by exact prefixLift 920718
  have htrace : WordTrace (prefixWord ++ tailWord_920718) baseStart_920718 baseEnd_920718 := by
    simpa [prefixWord, tailWord_920718, baseEnd_920718] using wordTrace_append hprefix tailTrace_920718
  have hstable : (prefixWord ++ tailWord_920718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920718).length < 2 ^ (prefixWord ++ tailWord_920718).sum := by decide
  have hdescent : baseEnd_920718 < baseStart_920718 := by decide
  rcases family_descends (prefixWord ++ tailWord_920718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920744 : List Nat := [2, 1, 20]
def baseStart_920744 : Nat := 118140960795 + 920744 * 2 ^ 59
def prefixEnd_920744 : Nat := 4983230072969 + 3 ^ 40 * 920744 * 2
def baseEnd_920744 : Nat := 72059782311149339821

theorem tailTrace_920744 : CollatzResearch.WordTrace tailWord_920744 prefixEnd_920744 72059782311149339821 := by
  unfold tailWord_920744
  simp only [CollatzResearch.WordTrace]
  refine ⟨16791146288154606700476643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22388195050872808933968857 16791146288154606700476643)
  ·
    refine ⟨25186719432231910050714965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16791146288154606700476643 25186719432231910050714965)
    ·
      refine ⟨72059782311149339821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 20 25186719432231910050714965 72059782311149339821)
      ·
        rfl

theorem cell23_920744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 20].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 20].length) (baseStart_920744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920744 prefixEnd_920744 := by exact prefixLift 920744
  have htrace : WordTrace (prefixWord ++ tailWord_920744) baseStart_920744 baseEnd_920744 := by
    simpa [prefixWord, tailWord_920744, baseEnd_920744] using wordTrace_append hprefix tailTrace_920744
  have hstable : (prefixWord ++ tailWord_920744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920744).length < 2 ^ (prefixWord ++ tailWord_920744).sum := by decide
  have hdescent : baseEnd_920744 < baseStart_920744 := by decide
  rcases family_descends (prefixWord ++ tailWord_920744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920749 : List Nat := [1, 5, 2, 1, 3, 1, 1, 4, 1, 1, 3]
def baseStart_920749 : Nat := 118140960795 + 920749 * 2 ^ 59
def prefixEnd_920749 : Nat := 4983230072969 + 3 ^ 40 * 920749 * 2
def baseEnd_920749 : Nat := 472786799146723299003059

theorem tailTrace_920749 : CollatzResearch.WordTrace tailWord_920749 prefixEnd_920749 472786799146723299003059 := by
  unfold tailWord_920749
  simp only [CollatzResearch.WordTrace]
  refine ⟨33582474941291099254885301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22388316627527399503256867 33582474941291099254885301)
  ·
    refine ⟨3148357025746040555145497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33582474941291099254885301 3148357025746040555145497)
    ·
      refine ⟨2361267769309530416359123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3148357025746040555145497 2361267769309530416359123)
      ·
        refine ⟨3541901653964295624538685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2361267769309530416359123 3541901653964295624538685)
        ·
          refine ⟨1328213120236610859202007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3541901653964295624538685 1328213120236610859202007)
          ·
            refine ⟨1992319680354916288803011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1328213120236610859202007 1992319680354916288803011)
            ·
              refine ⟨2988479520532374433204517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1992319680354916288803011 2988479520532374433204517)
              ·
                refine ⟨560339910099820206225847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2988479520532374433204517 560339910099820206225847)
                ·
                  refine ⟨840509865149730309338771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 560339910099820206225847 840509865149730309338771)
                  ·
                    refine ⟨1260764797724595464008157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 840509865149730309338771 1260764797724595464008157)
                    ·
                      refine ⟨472786799146723299003059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1260764797724595464008157 472786799146723299003059)
                      ·
                        rfl

theorem cell23_920749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_920749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920749 prefixEnd_920749 := by exact prefixLift 920749
  have htrace : WordTrace (prefixWord ++ tailWord_920749) baseStart_920749 baseEnd_920749 := by
    simpa [prefixWord, tailWord_920749, baseEnd_920749] using wordTrace_append hprefix tailTrace_920749
  have hstable : (prefixWord ++ tailWord_920749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920749).length < 2 ^ (prefixWord ++ tailWord_920749).sum := by decide
  have hdescent : baseEnd_920749 < baseStart_920749 := by decide
  rcases family_descends (prefixWord ++ tailWord_920749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920761 : List Nat := [1, 2, 1, 4, 1, 3, 3, 8]
def baseStart_920761 : Nat := 118140960795 + 920761 * 2 ^ 59
def prefixEnd_920761 : Nat := 4983230072969 + 3 ^ 40 * 920761 * 2
def baseEnd_920761 : Nat := 17510850404243601927889

theorem tailTrace_920761 : CollatzResearch.WordTrace tailWord_920761 prefixEnd_920761 17510850404243601927889 := by
  unfold tailWord_920761
  simp only [CollatzResearch.WordTrace]
  refine ⟨33582912617247625304322137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22388608411498416869548091 33582912617247625304322137)
  ·
    refine ⟨25187184462935718978241603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33582912617247625304322137 25187184462935718978241603)
    ·
      refine ⟨37780776694403578467362405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25187184462935718978241603 37780776694403578467362405)
      ·
        refine ⟨7083895630200670962630451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37780776694403578467362405 7083895630200670962630451)
        ·
          refine ⟨10625843445301006443945677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7083895630200670962630451 10625843445301006443945677)
          ·
            refine ⟨3984691291987877416479629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10625843445301006443945677 3984691291987877416479629)
            ·
              refine ⟨1494259234495454031179861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3984691291987877416479629 1494259234495454031179861)
              ·
                refine ⟨17510850404243601927889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1494259234495454031179861 17510850404243601927889)
                ·
                  rfl

theorem cell23_920761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 8].length) (baseStart_920761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920761 prefixEnd_920761 := by exact prefixLift 920761
  have htrace : WordTrace (prefixWord ++ tailWord_920761) baseStart_920761 baseEnd_920761 := by
    simpa [prefixWord, tailWord_920761, baseEnd_920761] using wordTrace_append hprefix tailTrace_920761
  have hstable : (prefixWord ++ tailWord_920761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920761).length < 2 ^ (prefixWord ++ tailWord_920761).sum := by decide
  have hdescent : baseEnd_920761 < baseStart_920761 := by decide
  rcases family_descends (prefixWord ++ tailWord_920761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920778 : List Nat := [3, 1, 2, 1, 3, 3, 3, 7]
def baseStart_920778 : Nat := 118140960795 + 920778 * 2 ^ 59
def prefixEnd_920778 : Nat := 4983230072969 + 3 ^ 40 * 920778 * 2
def baseEnd_920778 : Nat := 17511173706877914279275

theorem tailTrace_920778 : CollatzResearch.WordTrace tailWord_920778 prefixEnd_920778 17511173706877914279275 := by
  unfold tailWord_920778
  simp only [CollatzResearch.WordTrace]
  refine ⟨8395883164546509301922747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22389021772124024805127325 8395883164546509301922747)
  ·
    refine ⟨12593824746819763952884121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8395883164546509301922747 12593824746819763952884121)
    ·
      refine ⟨9445368560114822964663091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12593824746819763952884121 9445368560114822964663091)
      ·
        refine ⟨14168052840172234446994637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9445368560114822964663091 14168052840172234446994637)
        ·
          refine ⟨5313019815064587917622989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14168052840172234446994637 5313019815064587917622989)
          ·
            refine ⟨1992382430649220469108621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5313019815064587917622989 1992382430649220469108621)
            ·
              refine ⟨747143411493457675915733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1992382430649220469108621 747143411493457675915733)
              ·
                refine ⟨17511173706877914279275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 747143411493457675915733 17511173706877914279275)
                ·
                  rfl

theorem cell23_920778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 7].length) (baseStart_920778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920778 prefixEnd_920778 := by exact prefixLift 920778
  have htrace : WordTrace (prefixWord ++ tailWord_920778) baseStart_920778 baseEnd_920778 := by
    simpa [prefixWord, tailWord_920778, baseEnd_920778] using wordTrace_append hprefix tailTrace_920778
  have hstable : (prefixWord ++ tailWord_920778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920778).length < 2 ^ (prefixWord ++ tailWord_920778).sum := by decide
  have hdescent : baseEnd_920778 < baseStart_920778 := by decide
  rcases family_descends (prefixWord ++ tailWord_920778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920789 : List Nat := [1, 3, 2, 4, 1, 1, 1, 5, 1, 2, 2]
def baseStart_920789 : Nat := 118140960795 + 920789 * 2 ^ 59
def prefixEnd_920789 : Nat := 4983230072969 + 3 ^ 40 * 920789 * 2
def baseEnd_920789 : Nat := 472807338372903142502875

theorem tailTrace_920789 : CollatzResearch.WordTrace tailWord_920789 prefixEnd_920789 472807338372903142502875 := by
  unfold tailWord_920789
  simp only [CollatzResearch.WordTrace]
  refine ⟨33583933861146186086341421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22389289240764124057560947 33583933861146186086341421)
  ·
    refine ⟨12593975197929819782378033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33583933861146186086341421 12593975197929819782378033)
    ·
      refine ⟨9445481398447364836783525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12593975197929819782378033 9445481398447364836783525)
      ·
        refine ⟨1771027762208880906896911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9445481398447364836783525 1771027762208880906896911)
        ·
          refine ⟨2656541643313321360345367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1771027762208880906896911 2656541643313321360345367)
          ·
            refine ⟨3984812464969982040518051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2656541643313321360345367 3984812464969982040518051)
            ·
              refine ⟨5977218697454973060777077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3984812464969982040518051 5977218697454973060777077)
              ·
                refine ⟨560364252886403724447851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5977218697454973060777077 560364252886403724447851)
                ·
                  refine ⟨840546379329605586671777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 560364252886403724447851 840546379329605586671777)
                  ·
                    refine ⟨630409784497204190003833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 840546379329605586671777 630409784497204190003833)
                    ·
                      refine ⟨472807338372903142502875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 630409784497204190003833 472807338372903142502875)
                      ·
                        rfl

theorem cell23_920789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_920789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920789 prefixEnd_920789 := by exact prefixLift 920789
  have htrace : WordTrace (prefixWord ++ tailWord_920789) baseStart_920789 baseEnd_920789 := by
    simpa [prefixWord, tailWord_920789, baseEnd_920789] using wordTrace_append hprefix tailTrace_920789
  have hstable : (prefixWord ++ tailWord_920789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920789).length < 2 ^ (prefixWord ++ tailWord_920789).sum := by decide
  have hdescent : baseEnd_920789 < baseStart_920789 := by decide
  rcases family_descends (prefixWord ++ tailWord_920789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920908 : List Nat := [2, 2, 1, 3, 2, 2, 1, 2, 1, 2, 5]
def baseStart_920908 : Nat := 118140960795 + 920908 * 2 ^ 59
def prefixEnd_920908 : Nat := 4983230072969 + 3 ^ 40 * 920908 * 2
def baseEnd_920908 : Nat := 472868442570788176914827

theorem tailTrace_920908 : CollatzResearch.WordTrace tailWord_920908 prefixEnd_920908 472868442570788176914827 := by
  unfold tailWord_920908
  simp only [CollatzResearch.WordTrace]
  refine ⟨16794137073857534704961689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22392182765143379606615585 16794137073857534704961689)
  ·
    refine ⟨12595602805393151028721267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16794137073857534704961689 12595602805393151028721267)
    ·
      refine ⟨18893404208089726543081901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12595602805393151028721267 18893404208089726543081901)
      ·
        refine ⟨7085026578033647453655713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18893404208089726543081901 7085026578033647453655713)
        ·
          refine ⟨5313769933525235590241785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7085026578033647453655713 5313769933525235590241785)
          ·
            refine ⟨3985327450143926692681339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5313769933525235590241785 3985327450143926692681339)
            ·
              refine ⟨5977991175215890039022009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3985327450143926692681339 5977991175215890039022009)
              ·
                refine ⟨4483493381411917529266507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5977991175215890039022009 4483493381411917529266507)
                ·
                  refine ⟨6725240072117876293899761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4483493381411917529266507 6725240072117876293899761)
                  ·
                    refine ⟨5043930054088407220424821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6725240072117876293899761 5043930054088407220424821)
                    ·
                      refine ⟨472868442570788176914827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5043930054088407220424821 472868442570788176914827)
                      ·
                        rfl

theorem cell23_920908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_920908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920908 prefixEnd_920908 := by exact prefixLift 920908
  have htrace : WordTrace (prefixWord ++ tailWord_920908) baseStart_920908 baseEnd_920908 := by
    simpa [prefixWord, tailWord_920908, baseEnd_920908] using wordTrace_append hprefix tailTrace_920908
  have hstable : (prefixWord ++ tailWord_920908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920908).length < 2 ^ (prefixWord ++ tailWord_920908).sum := by decide
  have hdescent : baseEnd_920908 < baseStart_920908 := by decide
  rcases family_descends (prefixWord ++ tailWord_920908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920911 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 4, 8]
def baseStart_920911 : Nat := 118140960795 + 920911 * 2 ^ 59
def prefixEnd_920911 : Nat := 4983230072969 + 3 ^ 40 * 920911 * 2
def baseEnd_920911 : Nat := 157623327670917221725771

theorem tailTrace_920911 : CollatzResearch.WordTrace tailWord_920911 prefixEnd_920911 157623327670917221725771 := by
  unfold tailWord_920911
  simp only [CollatzResearch.WordTrace]
  refine ⟨33588383566704200922282587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22392255711136133948188391 33588383566704200922282587)
  ·
    refine ⟨50382575350056301383423881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33588383566704200922282587 50382575350056301383423881)
    ·
      refine ⟨37786931512542226037567911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50382575350056301383423881 37786931512542226037567911)
      ·
        refine ⟨56680397268813339056351867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37786931512542226037567911 56680397268813339056351867)
        ·
          refine ⟨85020595903220008584527801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56680397268813339056351867 85020595903220008584527801)
          ·
            refine ⟨63765446927415006438395851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85020595903220008584527801 63765446927415006438395851)
            ·
              refine ⟨95648170391122509657593777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63765446927415006438395851 95648170391122509657593777)
              ·
                refine ⟨71736127793341882243195333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95648170391122509657593777 71736127793341882243195333)
                ·
                  refine ⟨13450523961251602920599125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71736127793341882243195333 13450523961251602920599125)
                  ·
                    refine ⟨157623327670917221725771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 13450523961251602920599125 157623327670917221725771)
                    ·
                      rfl

theorem cell23_920911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 8].length) (baseStart_920911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920911 prefixEnd_920911 := by exact prefixLift 920911
  have htrace : WordTrace (prefixWord ++ tailWord_920911) baseStart_920911 baseEnd_920911 := by
    simpa [prefixWord, tailWord_920911, baseEnd_920911] using wordTrace_append hprefix tailTrace_920911
  have hstable : (prefixWord ++ tailWord_920911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920911).length < 2 ^ (prefixWord ++ tailWord_920911).sum := by decide
  have hdescent : baseEnd_920911 < baseStart_920911 := by decide
  rcases family_descends (prefixWord ++ tailWord_920911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920949 : List Nat := [1, 3, 4, 1, 4, 1, 1, 1, 2, 5]
def baseStart_920949 : Nat := 118140960795 + 920949 * 2 ^ 59
def prefixEnd_920949 : Nat := 4983230072969 + 3 ^ 40 * 920949 * 2
def baseEnd_920949 : Nat := 157629831759207505500713

theorem tailTrace_920949 : CollatzResearch.WordTrace tailWord_920949 prefixEnd_920949 157629831759207505500713 := by
  unfold tailWord_920949
  simp only [CollatzResearch.WordTrace]
  refine ⟨33589769540566533412165901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22393179693711022274777267 33589769540566533412165901)
  ·
    refine ⟨12596163577712450029562213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33589769540566533412165901 12596163577712450029562213)
    ·
      refine ⟨2361780670821084380542915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12596163577712450029562213 2361780670821084380542915)
      ·
        refine ⟨3542671006231626570814373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2361780670821084380542915 3542671006231626570814373)
        ·
          refine ⟨664250813668429982027695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3542671006231626570814373 664250813668429982027695)
          ·
            refine ⟨996376220502644973041543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664250813668429982027695 996376220502644973041543)
            ·
              refine ⟨1494564330753967459562315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 996376220502644973041543 1494564330753967459562315)
              ·
                refine ⟨2241846496130951189343473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1494564330753967459562315 2241846496130951189343473)
                ·
                  refine ⟨1681384872098213392007605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2241846496130951189343473 1681384872098213392007605)
                  ·
                    refine ⟨157629831759207505500713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1681384872098213392007605 157629831759207505500713)
                    ·
                      rfl

theorem cell23_920949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_920949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920949 prefixEnd_920949 := by exact prefixLift 920949
  have htrace : WordTrace (prefixWord ++ tailWord_920949) baseStart_920949 baseEnd_920949 := by
    simpa [prefixWord, tailWord_920949, baseEnd_920949] using wordTrace_append hprefix tailTrace_920949
  have hstable : (prefixWord ++ tailWord_920949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920949).length < 2 ^ (prefixWord ++ tailWord_920949).sum := by decide
  have hdescent : baseEnd_920949 < baseStart_920949 := by decide
  rcases family_descends (prefixWord ++ tailWord_920949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920995 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 3, 5, 2]
def baseStart_920995 : Nat := 118140960795 + 920995 * 2 ^ 59
def prefixEnd_920995 : Nat := 4983230072969 + 3 ^ 40 * 920995 * 2
def baseEnd_920995 : Nat := 472913115387729336526927

theorem tailTrace_920995 : CollatzResearch.WordTrace tailWord_920995 prefixEnd_920995 472913115387729336526927 := by
  unfold tailWord_920995
  simp only [CollatzResearch.WordTrace]
  refine ⟨33591447298399883268340439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22394298198933255512226959 33591447298399883268340439)
  ·
    refine ⟨50387170947599824902510659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33591447298399883268340439 50387170947599824902510659)
    ·
      refine ⟨75580756421399737353765989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50387170947599824902510659 75580756421399737353765989)
      ·
        refine ⟨14171391829012450753831123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75580756421399737353765989 14171391829012450753831123)
        ·
          refine ⟨21257087743518676130746685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14171391829012450753831123 21257087743518676130746685)
          ·
            refine ⟨7971407903819503549030007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21257087743518676130746685 7971407903819503549030007)
            ·
              refine ⟨11957111855729255323545011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7971407903819503549030007 11957111855729255323545011)
              ·
                refine ⟨17935667783593882985317517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11957111855729255323545011 17935667783593882985317517)
                ·
                  refine ⟨6725875418847706119494069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17935667783593882985317517 6725875418847706119494069)
                  ·
                    refine ⟨630550820516972448702569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6725875418847706119494069 630550820516972448702569)
                    ·
                      refine ⟨472913115387729336526927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 630550820516972448702569 472913115387729336526927)
                      ·
                        rfl

theorem cell23_920995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 5, 2].length) (baseStart_920995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_920995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_920995 prefixEnd_920995 := by exact prefixLift 920995
  have htrace : WordTrace (prefixWord ++ tailWord_920995) baseStart_920995 baseEnd_920995 := by
    simpa [prefixWord, tailWord_920995, baseEnd_920995] using wordTrace_append hprefix tailTrace_920995
  have hstable : (prefixWord ++ tailWord_920995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920995).length < 2 ^ (prefixWord ++ tailWord_920995).sum := by decide
  have hdescent : baseEnd_920995 < baseStart_920995 := by decide
  rcases family_descends (prefixWord ++ tailWord_920995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921035 : List Nat := [1, 1, 1, 1, 3, 3, 4, 1, 4, 4]
def baseStart_921035 : Nat := 118140960795 + 921035 * 2 ^ 59
def prefixEnd_921035 : Nat := 4983230072969 + 3 ^ 40 * 921035 * 2
def baseEnd_921035 : Nat := 157644551537969726675581

theorem tailTrace_921035 : CollatzResearch.WordTrace tailWord_921035 prefixEnd_921035 157644551537969726675581 := by
  unfold tailWord_921035
  simp only [CollatzResearch.WordTrace]
  refine ⟨33592906218254970099796559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22395270812169980066531039 33592906218254970099796559)
  ·
    refine ⟨50389359327382455149694839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33592906218254970099796559 50389359327382455149694839)
    ·
      refine ⟨75584038991073682724542259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50389359327382455149694839 75584038991073682724542259)
      ·
        refine ⟨113376058486610524086813389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75584038991073682724542259 113376058486610524086813389)
        ·
          refine ⟨42516021932478946532555021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113376058486610524086813389 42516021932478946532555021)
          ·
            refine ⟨15943508224679604949708133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42516021932478946532555021 15943508224679604949708133)
            ·
              refine ⟨2989407792127425928070275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15943508224679604949708133 2989407792127425928070275)
              ·
                refine ⟨4484111688191138892105413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2989407792127425928070275 4484111688191138892105413)
                ·
                  refine ⟨840770941535838542269765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4484111688191138892105413 840770941535838542269765)
                  ·
                    refine ⟨157644551537969726675581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 840770941535838542269765 157644551537969726675581)
                    ·
                      rfl

theorem cell23_921035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 4, 4].length) (baseStart_921035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921035 prefixEnd_921035 := by exact prefixLift 921035
  have htrace : WordTrace (prefixWord ++ tailWord_921035) baseStart_921035 baseEnd_921035 := by
    simpa [prefixWord, tailWord_921035, baseEnd_921035] using wordTrace_append hprefix tailTrace_921035
  have hstable : (prefixWord ++ tailWord_921035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921035).length < 2 ^ (prefixWord ++ tailWord_921035).sum := by decide
  have hdescent : baseEnd_921035 < baseStart_921035 := by decide
  rcases family_descends (prefixWord ++ tailWord_921035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921045 : List Nat := [1, 3, 2, 3, 1, 1, 1, 4, 1, 1, 5]
def baseStart_921045 : Nat := 118140960795 + 921045 * 2 ^ 59
def prefixEnd_921045 : Nat := 4983230072969 + 3 ^ 40 * 921045 * 2
def baseEnd_921045 : Nat := 472938789420454140901697

theorem tailTrace_921045 : CollatzResearch.WordTrace tailWord_921045 prefixEnd_921045 472938789420454140901697 := by
  unfold tailWord_921045
  simp only [CollatzResearch.WordTrace]
  refine ⟨33593270948218741807660589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22395513965479161205107059 33593270948218741807660589)
  ·
    refine ⟨12597476605582028177872721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33593270948218741807660589 12597476605582028177872721)
    ·
      refine ⟨9448107454186521133404541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12597476605582028177872721 9448107454186521133404541)
      ·
        refine ⟨3543040295319945425026703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9448107454186521133404541 3543040295319945425026703)
        ·
          refine ⟨5314560442979918137540055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3543040295319945425026703 5314560442979918137540055)
          ·
            refine ⟨7971840664469877206310083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5314560442979918137540055 7971840664469877206310083)
            ·
              refine ⟨11957760996704815809465125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7971840664469877206310083 11957760996704815809465125)
              ·
                refine ⟨2242080186882152964274711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11957760996704815809465125 2242080186882152964274711)
                ·
                  refine ⟨3363120280323229446412067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2242080186882152964274711 3363120280323229446412067)
                  ·
                    refine ⟨5044680420484844169618101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3363120280323229446412067 5044680420484844169618101)
                    ·
                      refine ⟨472938789420454140901697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5044680420484844169618101 472938789420454140901697)
                      ·
                        rfl

theorem cell23_921045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_921045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921045 prefixEnd_921045 := by exact prefixLift 921045
  have htrace : WordTrace (prefixWord ++ tailWord_921045) baseStart_921045 baseEnd_921045 := by
    simpa [prefixWord, tailWord_921045, baseEnd_921045] using wordTrace_append hprefix tailTrace_921045
  have hstable : (prefixWord ++ tailWord_921045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921045).length < 2 ^ (prefixWord ++ tailWord_921045).sum := by decide
  have hdescent : baseEnd_921045 < baseStart_921045 := by decide
  rcases family_descends (prefixWord ++ tailWord_921045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921048 : List Nat := [2, 1, 2, 2, 2, 1, 3, 10]
def baseStart_921048 : Nat := 118140960795 + 921048 * 2 ^ 59
def prefixEnd_921048 : Nat := 4983230072969 + 3 ^ 40 * 921048 * 2
def baseEnd_921048 : Nat := 17516308513422875154229

theorem tailTrace_921048 : CollatzResearch.WordTrace tailWord_921048 prefixEnd_921048 17516308513422875154229 := by
  unfold tailWord_921048
  simp only [CollatzResearch.WordTrace]
  refine ⟨16796690183603936660009899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22395586911471915546679865 16796690183603936660009899)
  ·
    refine ⟨25195035275405904990014849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16796690183603936660009899 25195035275405904990014849)
    ·
      refine ⟨18896276456554428742511137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25195035275405904990014849 18896276456554428742511137)
      ·
        refine ⟨14172207342415821556883353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18896276456554428742511137 14172207342415821556883353)
        ·
          refine ⟨10629155506811866167662515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14172207342415821556883353 10629155506811866167662515)
          ·
            refine ⟨15943733260217799251493773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10629155506811866167662515 15943733260217799251493773)
            ·
              refine ⟨5978899972581674719310165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15943733260217799251493773 5978899972581674719310165)
              ·
                refine ⟨17516308513422875154229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5978899972581674719310165 17516308513422875154229)
                ·
                  rfl

theorem cell23_921048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 10].length) (baseStart_921048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921048 prefixEnd_921048 := by exact prefixLift 921048
  have htrace : WordTrace (prefixWord ++ tailWord_921048) baseStart_921048 baseEnd_921048 := by
    simpa [prefixWord, tailWord_921048, baseEnd_921048] using wordTrace_append hprefix tailTrace_921048
  have hstable : (prefixWord ++ tailWord_921048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921048).length < 2 ^ (prefixWord ++ tailWord_921048).sum := by decide
  have hdescent : baseEnd_921048 < baseStart_921048 := by decide
  rcases family_descends (prefixWord ++ tailWord_921048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921055 : List Nat := [1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 4]
def baseStart_921055 : Nat := 118140960795 + 921055 * 2 ^ 59
def prefixEnd_921055 : Nat := 4983230072969 + 3 ^ 40 * 921055 * 2
def baseEnd_921055 : Nat := 472943924226999101776651

theorem tailTrace_921055 : CollatzResearch.WordTrace tailWord_921055 prefixEnd_921055 472943924226999101776651 := by
  unfold tailWord_921055
  simp only [CollatzResearch.WordTrace]
  refine ⟨33593635678182513515524619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22395757118788342343683079 33593635678182513515524619)
  ·
    refine ⟨50390453517273770273286929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33593635678182513515524619 50390453517273770273286929)
    ·
      refine ⟨37792840137955327704965197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50390453517273770273286929 37792840137955327704965197)
      ·
        refine ⟨14172315051733247889361949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37792840137955327704965197 14172315051733247889361949)
        ·
          refine ⟨5314618144399967958510731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14172315051733247889361949 5314618144399967958510731)
          ·
            refine ⟨7971927216599951937766097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5314618144399967958510731 7971927216599951937766097)
            ·
              refine ⟨5978945412449963953324573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7971927216599951937766097 5978945412449963953324573)
              ·
                refine ⟨2242104529668736482496715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5978945412449963953324573 2242104529668736482496715)
                ·
                  refine ⟨3363156794503104723745073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2242104529668736482496715 3363156794503104723745073)
                  ·
                    refine ⟨2522367595877328542808805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3363156794503104723745073 2522367595877328542808805)
                    ·
                      refine ⟨472943924226999101776651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2522367595877328542808805 472943924226999101776651)
                      ·
                        rfl

theorem cell23_921055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_921055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921055 prefixEnd_921055 := by exact prefixLift 921055
  have htrace : WordTrace (prefixWord ++ tailWord_921055) baseStart_921055 baseEnd_921055 := by
    simpa [prefixWord, tailWord_921055, baseEnd_921055] using wordTrace_append hprefix tailTrace_921055
  have hstable : (prefixWord ++ tailWord_921055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921055).length < 2 ^ (prefixWord ++ tailWord_921055).sum := by decide
  have hdescent : baseEnd_921055 < baseStart_921055 := by decide
  rcases family_descends (prefixWord ++ tailWord_921055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921059 : List Nat := [1, 1, 1, 6, 2, 3, 1, 2, 1, 1, 4]
def baseStart_921059 : Nat := 118140960795 + 921059 * 2 ^ 59
def prefixEnd_921059 : Nat := 4983230072969 + 3 ^ 40 * 921059 * 2
def baseEnd_921059 : Nat := 472945978149617086126633

theorem tailTrace_921059 : CollatzResearch.WordTrace tailWord_921059 prefixEnd_921059 472945978149617086126633 := by
  unfold tailWord_921059
  simp only [CollatzResearch.WordTrace]
  refine ⟨33593781570168022198670231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22395854380112014799113487 33593781570168022198670231)
  ·
    refine ⟨50390672355252033298005347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33593781570168022198670231 50390672355252033298005347)
    ·
      refine ⟨75586008532878049947008021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50390672355252033298005347 75586008532878049947008021)
      ·
        refine ⟨3543094149978658591266001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 75586008532878049947008021 3543094149978658591266001)
        ·
          refine ⟨2657320612483993943449501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3543094149978658591266001 2657320612483993943449501)
          ·
            refine ⟨996495229681497728793563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2657320612483993943449501 996495229681497728793563)
            ·
              refine ⟨1494742844522246593190345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 996495229681497728793563 1494742844522246593190345)
              ·
                refine ⟨1121057133391684944892759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1494742844522246593190345 1121057133391684944892759)
                ·
                  refine ⟨1681585700087527417339139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1121057133391684944892759 1681585700087527417339139)
                  ·
                    refine ⟨2522378550131291126008709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1681585700087527417339139 2522378550131291126008709)
                    ·
                      refine ⟨472945978149617086126633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2522378550131291126008709 472945978149617086126633)
                      ·
                        rfl

theorem cell23_921059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_921059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921059 prefixEnd_921059 := by exact prefixLift 921059
  have htrace : WordTrace (prefixWord ++ tailWord_921059) baseStart_921059 baseEnd_921059 := by
    simpa [prefixWord, tailWord_921059, baseEnd_921059] using wordTrace_append hprefix tailTrace_921059
  have hstable : (prefixWord ++ tailWord_921059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921059).length < 2 ^ (prefixWord ++ tailWord_921059).sum := by decide
  have hdescent : baseEnd_921059 < baseStart_921059 := by decide
  rcases family_descends (prefixWord ++ tailWord_921059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921088 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 7]
def baseStart_921088 : Nat := 118140960795 + 921088 * 2 ^ 59
def prefixEnd_921088 : Nat := 4983230072969 + 3 ^ 40 * 921088 * 2
def baseEnd_921088 : Nat := 472960869088597472663999

theorem tailTrace_921088 : CollatzResearch.WordTrace tailWord_921088 prefixEnd_921088 472960869088597472663999 := by
  unfold tailWord_921088
  simp only [CollatzResearch.WordTrace]
  refine ⟨16797419643531480075737959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22396559524708640100983945 16797419643531480075737959)
  ·
    refine ⟨25196129465297220113606939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16797419643531480075737959 25196129465297220113606939)
    ·
      refine ⟨37794194197945830170410409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25196129465297220113606939 37794194197945830170410409)
      ·
        refine ⟨28345645648459372627807807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37794194197945830170410409 28345645648459372627807807)
        ·
          refine ⟨42518468472689058941711711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28345645648459372627807807 42518468472689058941711711)
          ·
            refine ⟨63777702709033588412567567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42518468472689058941711711 63777702709033588412567567)
            ·
              refine ⟨95666554063550382618851351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63777702709033588412567567 95666554063550382618851351)
              ·
                refine ⟨143499831095325573928277027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95666554063550382618851351 143499831095325573928277027)
                ·
                  refine ⟨215249746642988360892415541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143499831095325573928277027 215249746642988360892415541)
                  ·
                    refine ⟨20179663747780158833663957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 215249746642988360892415541 20179663747780158833663957)
                    ·
                      refine ⟨472960869088597472663999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 20179663747780158833663957 472960869088597472663999)
                      ·
                        rfl

theorem cell23_921088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_921088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921088 prefixEnd_921088 := by exact prefixLift 921088
  have htrace : WordTrace (prefixWord ++ tailWord_921088) baseStart_921088 baseEnd_921088 := by
    simpa [prefixWord, tailWord_921088, baseEnd_921088] using wordTrace_append hprefix tailTrace_921088
  have hstable : (prefixWord ++ tailWord_921088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921088).length < 2 ^ (prefixWord ++ tailWord_921088).sum := by decide
  have hdescent : baseEnd_921088 < baseStart_921088 := by decide
  rcases family_descends (prefixWord ++ tailWord_921088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921095 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 2, 7]
def baseStart_921095 : Nat := 118140960795 + 921095 * 2 ^ 59
def prefixEnd_921095 : Nat := 4983230072969 + 3 ^ 40 * 921095 * 2
def baseEnd_921095 : Nat := 157654821151059648425489

theorem tailTrace_921095 : CollatzResearch.WordTrace tailWord_921095 prefixEnd_921095 157654821151059648425489 := by
  unfold tailWord_921095
  simp only [CollatzResearch.WordTrace]
  refine ⟨33595094598037600346980739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22396729732025066897987159 33595094598037600346980739)
  ·
    refine ⟨50392641897056400520471109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33595094598037600346980739 50392641897056400520471109)
    ·
      refine ⟨9448620355698075097588333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50392641897056400520471109 9448620355698075097588333)
      ·
        refine ⟨3543232633386778161595625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9448620355698075097588333 3543232633386778161595625)
        ·
          refine ⟨2657424475040083621196719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3543232633386778161595625 2657424475040083621196719)
          ·
            refine ⟨3986136712560125431795079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2657424475040083621196719 3986136712560125431795079)
            ·
              refine ⟨5979205068840188147692619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3986136712560125431795079 5979205068840188147692619)
              ·
                refine ⟨8968807603260282221538929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5979205068840188147692619 8968807603260282221538929)
                ·
                  refine ⟨6726605702445211666154197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8968807603260282221538929 6726605702445211666154197)
                  ·
                    refine ⟨157654821151059648425489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6726605702445211666154197 157654821151059648425489)
                    ·
                      rfl

theorem cell23_921095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_921095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921095 prefixEnd_921095 := by exact prefixLift 921095
  have htrace : WordTrace (prefixWord ++ tailWord_921095) baseStart_921095 baseEnd_921095 := by
    simpa [prefixWord, tailWord_921095, baseEnd_921095] using wordTrace_append hprefix tailTrace_921095
  have hstable : (prefixWord ++ tailWord_921095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921095).length < 2 ^ (prefixWord ++ tailWord_921095).sum := by decide
  have hdescent : baseEnd_921095 < baseStart_921095 := by decide
  rcases family_descends (prefixWord ++ tailWord_921095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921109 : List Nat := [1, 3, 2, 1, 3, 2, 2, 3, 2, 1, 3]
def baseStart_921109 : Nat := 118140960795 + 921109 * 2 ^ 59
def prefixEnd_921109 : Nat := 4983230072969 + 3 ^ 40 * 921109 * 2
def baseEnd_921109 : Nat := 472971652182341890501403

theorem tailTrace_921109 : CollatzResearch.WordTrace tailWord_921109 prefixEnd_921109 472971652182341890501403 := by
  unfold tailWord_921109
  simp only [CollatzResearch.WordTrace]
  refine ⟨33595605219986880737990381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22397070146657920491993587 33595605219986880737990381)
  ·
    refine ⟨12598351957495080276746393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33595605219986880737990381 12598351957495080276746393)
    ·
      refine ⟨9448763968121310207559795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12598351957495080276746393 9448763968121310207559795)
      ·
        refine ⟨14173145952181965311339693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9448763968121310207559795 14173145952181965311339693)
        ·
          refine ⟨5314929732068236991752385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14173145952181965311339693 5314929732068236991752385)
          ·
            refine ⟨3986197299051177743814289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5314929732068236991752385 3986197299051177743814289)
            ·
              refine ⟨2989647974288383307860717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3986197299051177743814289 2989647974288383307860717)
              ·
                refine ⟨1121117990358143740447769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2989647974288383307860717 1121117990358143740447769)
                ·
                  refine ⟨840838492768607805335827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1121117990358143740447769 840838492768607805335827)
                  ·
                    refine ⟨1261257739152911708003741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 840838492768607805335827 1261257739152911708003741)
                    ·
                      refine ⟨472971652182341890501403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1261257739152911708003741 472971652182341890501403)
                      ·
                        rfl

theorem cell23_921109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 2, 1, 3].length) (baseStart_921109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921109 prefixEnd_921109 := by exact prefixLift 921109
  have htrace : WordTrace (prefixWord ++ tailWord_921109) baseStart_921109 baseEnd_921109 := by
    simpa [prefixWord, tailWord_921109, baseEnd_921109] using wordTrace_append hprefix tailTrace_921109
  have hstable : (prefixWord ++ tailWord_921109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921109).length < 2 ^ (prefixWord ++ tailWord_921109).sum := by decide
  have hdescent : baseEnd_921109 < baseStart_921109 := by decide
  rcases family_descends (prefixWord ++ tailWord_921109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921185 : List Nat := [1, 2, 3, 1, 1, 3, 1, 3, 1, 7]
def baseStart_921185 : Nat := 118140960795 + 921185 * 2 ^ 59
def prefixEnd_921185 : Nat := 4983230072969 + 3 ^ 40 * 921185 * 2
def baseEnd_921185 : Nat := 157670225570694531050351

theorem tailTrace_921185 : CollatzResearch.WordTrace tailWord_921185 prefixEnd_921185 157670225570694531050351 := by
  unfold tailWord_921185
  simp only [CollatzResearch.WordTrace]
  refine ⟨33598377167711545717757009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22398918111807697145171339 33598377167711545717757009)
  ·
    refine ⟨25198782875783659288317757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33598377167711545717757009 25198782875783659288317757)
    ·
      refine ⟨9449543578418872233119159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25198782875783659288317757 9449543578418872233119159)
      ·
        refine ⟨14174315367628308349678739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9449543578418872233119159 14174315367628308349678739)
        ·
          refine ⟨21261473051442462524518109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14174315367628308349678739 21261473051442462524518109)
          ·
            refine ⟨7973052394290923446694291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21261473051442462524518109 7973052394290923446694291)
            ·
              refine ⟨11959578591436385170041437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7973052394290923446694291 11959578591436385170041437)
              ·
                refine ⟨4484841971788644438765539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11959578591436385170041437 4484841971788644438765539)
                ·
                  refine ⟨6727262957682966658148309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4484841971788644438765539 6727262957682966658148309)
                  ·
                    refine ⟨157670225570694531050351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6727262957682966658148309 157670225570694531050351)
                    ·
                      rfl

theorem cell23_921185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_921185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921185 prefixEnd_921185 := by exact prefixLift 921185
  have htrace : WordTrace (prefixWord ++ tailWord_921185) baseStart_921185 baseEnd_921185 := by
    simpa [prefixWord, tailWord_921185, baseEnd_921185] using wordTrace_append hprefix tailTrace_921185
  have hstable : (prefixWord ++ tailWord_921185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921185).length < 2 ^ (prefixWord ++ tailWord_921185).sum := by decide
  have hdescent : baseEnd_921185 < baseStart_921185 := by decide
  rcases family_descends (prefixWord ++ tailWord_921185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921189 : List Nat := [1, 3, 1, 3, 3, 1, 3, 3, 5]
def baseStart_921189 : Nat := 118140960795 + 921189 * 2 ^ 59
def prefixEnd_921189 : Nat := 4983230072969 + 3 ^ 40 * 921189 * 2
def baseEnd_921189 : Nat := 52556970070522397500115

theorem tailTrace_921189 : CollatzResearch.WordTrace tailWord_921189 prefixEnd_921189 52556970070522397500115 := by
  unfold tailWord_921189
  simp only [CollatzResearch.WordTrace]
  refine ⟨33598523059697054400902621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22399015373131369600601747 33598523059697054400902621)
  ·
    refine ⟨12599446147386395400338483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33598523059697054400902621 12599446147386395400338483)
    ·
      refine ⟨18899169221079593100507725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12599446147386395400338483 18899169221079593100507725)
      ·
        refine ⟨7087188457904847412690397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18899169221079593100507725 7087188457904847412690397)
        ·
          refine ⟨2657695671714317779758899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7087188457904847412690397 2657695671714317779758899)
          ·
            refine ⟨3986543507571476669638349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2657695671714317779758899 3986543507571476669638349)
            ·
              refine ⟨1494953815339303751114381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3986543507571476669638349 1494953815339303751114381)
              ·
                refine ⟨560607680752238906667893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1494953815339303751114381 560607680752238906667893)
                ·
                  refine ⟨52556970070522397500115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 560607680752238906667893 52556970070522397500115)
                  ·
                    rfl

theorem cell23_921189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 3, 5].length) (baseStart_921189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921189 prefixEnd_921189 := by exact prefixLift 921189
  have htrace : WordTrace (prefixWord ++ tailWord_921189) baseStart_921189 baseEnd_921189 := by
    simpa [prefixWord, tailWord_921189, baseEnd_921189] using wordTrace_append hprefix tailTrace_921189
  have hstable : (prefixWord ++ tailWord_921189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921189).length < 2 ^ (prefixWord ++ tailWord_921189).sum := by decide
  have hdescent : baseEnd_921189 < baseStart_921189 := by decide
  rcases family_descends (prefixWord ++ tailWord_921189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921202 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 4, 5]
def baseStart_921202 : Nat := 118140960795 + 921202 * 2 ^ 59
def prefixEnd_921202 : Nat := 4983230072969 + 3 ^ 40 * 921202 * 2
def baseEnd_921202 : Nat := 157673135294403342212825

theorem tailTrace_921202 : CollatzResearch.WordTrace tailWord_921202 prefixEnd_921202 157673135294403342212825 := by
  unfold tailWord_921202
  simp only [CollatzResearch.WordTrace]
  refine ⟨8399749302162489405281465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22399331472433305080750573 8399749302162489405281465)
  ·
    refine ⟨6299811976621867053961099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8399749302162489405281465 6299811976621867053961099)
    ·
      refine ⟨9449717964932800580941649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6299811976621867053961099 9449717964932800580941649)
      ·
        refine ⟨7087288473699600435706237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9449717964932800580941649 7087288473699600435706237)
        ·
          refine ⟨2657733177637350163389839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7087288473699600435706237 2657733177637350163389839)
          ·
            refine ⟨3986599766456025245084759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2657733177637350163389839 3986599766456025245084759)
            ·
              refine ⟨5979899649684037867627139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3986599766456025245084759 5979899649684037867627139)
              ·
                refine ⟨8969849474526056801440709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5979899649684037867627139 8969849474526056801440709)
                ·
                  refine ⟨1681846776473635650270133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8969849474526056801440709 1681846776473635650270133)
                  ·
                    refine ⟨157673135294403342212825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1681846776473635650270133 157673135294403342212825)
                    ·
                      rfl

theorem cell23_921202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_921202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921202 prefixEnd_921202 := by exact prefixLift 921202
  have htrace : WordTrace (prefixWord ++ tailWord_921202) baseStart_921202 baseEnd_921202 := by
    simpa [prefixWord, tailWord_921202, baseEnd_921202] using wordTrace_append hprefix tailTrace_921202
  have hstable : (prefixWord ++ tailWord_921202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921202).length < 2 ^ (prefixWord ++ tailWord_921202).sum := by decide
  have hdescent : baseEnd_921202 < baseStart_921202 := by decide
  rcases family_descends (prefixWord ++ tailWord_921202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921232 : List Nat := [2, 1, 1, 1, 1, 1, 3, 6, 3, 4]
def baseStart_921232 : Nat := 118140960795 + 921232 * 2 ^ 59
def prefixEnd_921232 : Nat := 4983230072969 + 3 ^ 40 * 921232 * 2
def baseEnd_921232 : Nat := 157678270100948303087779

theorem tailTrace_921232 : CollatzResearch.WordTrace tailWord_921232 prefixEnd_921232 157678270100948303087779 := by
  unfold tailWord_921232
  simp only [CollatzResearch.WordTrace]
  refine ⟨16800045699270636372358975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22400060932360848496478633 16800045699270636372358975)
  ·
    refine ⟨25200068548905954558538463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16800045699270636372358975 25200068548905954558538463)
    ·
      refine ⟨37800102823358931837807695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25200068548905954558538463 37800102823358931837807695)
      ·
        refine ⟨56700154235038397756711543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37800102823358931837807695 56700154235038397756711543)
        ·
          refine ⟨85050231352557596635067315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56700154235038397756711543 85050231352557596635067315)
          ·
            refine ⟨127575347028836394952600973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85050231352557596635067315 127575347028836394952600973)
            ·
              refine ⟨47840755135813648107225365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127575347028836394952600973 47840755135813648107225365)
              ·
                refine ⟨2242535396991264755026189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47840755135813648107225365 2242535396991264755026189)
                ·
                  refine ⟨840950773871724283134821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2242535396991264755026189 840950773871724283134821)
                  ·
                    refine ⟨157678270100948303087779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 840950773871724283134821 157678270100948303087779)
                    ·
                      rfl

theorem cell23_921232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 3, 4].length) (baseStart_921232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921232 prefixEnd_921232 := by exact prefixLift 921232
  have htrace : WordTrace (prefixWord ++ tailWord_921232) baseStart_921232 baseEnd_921232 := by
    simpa [prefixWord, tailWord_921232, baseEnd_921232] using wordTrace_append hprefix tailTrace_921232
  have hstable : (prefixWord ++ tailWord_921232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921232).length < 2 ^ (prefixWord ++ tailWord_921232).sum := by decide
  have hdescent : baseEnd_921232 < baseStart_921232 := by decide
  rcases family_descends (prefixWord ++ tailWord_921232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921236 : List Nat := [2, 4, 2, 2, 2, 1, 2, 1, 2, 5]
def baseStart_921236 : Nat := 118140960795 + 921236 * 2 ^ 59
def prefixEnd_921236 : Nat := 4983230072969 + 3 ^ 40 * 921236 * 2
def baseEnd_921236 : Nat := 157678954741820964537773

theorem tailTrace_921236 : CollatzResearch.WordTrace tailWord_921236 prefixEnd_921236 157678954741820964537773 := by
  unfold tailWord_921236
  simp only [CollatzResearch.WordTrace]
  refine ⟨16800118645263390713931781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22400158193684520951909041 16800118645263390713931781)
  ·
    refine ⟨3150022245986885758862209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16800118645263390713931781 3150022245986885758862209)
    ·
      refine ⟨2362516684490164319146657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3150022245986885758862209 2362516684490164319146657)
      ·
        refine ⟨1771887513367623239359993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2362516684490164319146657 1771887513367623239359993)
        ·
          refine ⟨1328915635025717429519995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1771887513367623239359993 1328915635025717429519995)
          ·
            refine ⟨1993373452538576144279993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1328915635025717429519995 1993373452538576144279993)
            ·
              refine ⟨1495030089403932108209995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1993373452538576144279993 1495030089403932108209995)
              ·
                refine ⟨2242545134105898162314993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1495030089403932108209995 2242545134105898162314993)
                ·
                  refine ⟨1681908850579423621736245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2242545134105898162314993 1681908850579423621736245)
                  ·
                    refine ⟨157678954741820964537773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1681908850579423621736245 157678954741820964537773)
                    ·
                      rfl

theorem cell23_921236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_921236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921236 prefixEnd_921236 := by exact prefixLift 921236
  have htrace : WordTrace (prefixWord ++ tailWord_921236) baseStart_921236 baseEnd_921236 := by
    simpa [prefixWord, tailWord_921236, baseEnd_921236] using wordTrace_append hprefix tailTrace_921236
  have hstable : (prefixWord ++ tailWord_921236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921236).length < 2 ^ (prefixWord ++ tailWord_921236).sum := by decide
  have hdescent : baseEnd_921236 < baseStart_921236 := by decide
  rcases family_descends (prefixWord ++ tailWord_921236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921239 : List Nat := [1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 4]
def baseStart_921239 : Nat := 118140960795 + 921239 * 2 ^ 59
def prefixEnd_921239 : Nat := 4983230072969 + 3 ^ 40 * 921239 * 2
def baseEnd_921239 : Nat := 473038404667426381875805

theorem tailTrace_921239 : CollatzResearch.WordTrace tailWord_921239 prefixEnd_921239 473038404667426381875805 := by
  unfold tailWord_921239
  simp only [CollatzResearch.WordTrace]
  refine ⟨33600346709515912940222771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22400231139677275293481847 33600346709515912940222771)
  ·
    refine ⟨50400520064273869410334157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33600346709515912940222771 50400520064273869410334157)
    ·
      refine ⟨18900195024102701028875309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50400520064273869410334157 18900195024102701028875309)
      ·
        refine ⟨7087573134038512885828241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18900195024102701028875309 7087573134038512885828241)
        ·
          refine ⟨5315679850528884664371181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7087573134038512885828241 5315679850528884664371181)
          ·
            refine ⟨1993379943948331749139193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5315679850528884664371181 1993379943948331749139193)
            ·
              refine ⟨1495034957961248811854395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1993379943948331749139193 1495034957961248811854395)
              ·
                refine ⟨2242552436941873217781593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1495034957961248811854395 2242552436941873217781593)
                ·
                  refine ⟨1681914327706404913336195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2242552436941873217781593 1681914327706404913336195)
                  ·
                    refine ⟨2522871491559607370004293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1681914327706404913336195 2522871491559607370004293)
                    ·
                      refine ⟨473038404667426381875805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2522871491559607370004293 473038404667426381875805)
                      ·
                        rfl

theorem cell23_921239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_921239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921239 prefixEnd_921239 := by exact prefixLift 921239
  have htrace : WordTrace (prefixWord ++ tailWord_921239) baseStart_921239 baseEnd_921239 := by
    simpa [prefixWord, tailWord_921239, baseEnd_921239] using wordTrace_append hprefix tailTrace_921239
  have hstable : (prefixWord ++ tailWord_921239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921239).length < 2 ^ (prefixWord ++ tailWord_921239).sum := by decide
  have hdescent : baseEnd_921239 < baseStart_921239 := by decide
  rcases family_descends (prefixWord ++ tailWord_921239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921293 : List Nat := [1, 6, 2, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_921293 : Nat := 118140960795 + 921293 * 2 ^ 59
def prefixEnd_921293 : Nat := 4983230072969 + 3 ^ 40 * 921293 * 2
def baseEnd_921293 : Nat := 473066132622769170600557

theorem tailTrace_921293 : CollatzResearch.WordTrace tailWord_921293 prefixEnd_921293 473066132622769170600557 := by
  unfold tailWord_921293
  simp only [CollatzResearch.WordTrace]
  refine ⟨33602316251320280162688533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22401544167546853441792355 33602316251320280162688533)
  ·
    refine ⟨1575108574280638132626025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33602316251320280162688533 1575108574280638132626025)
    ·
      refine ⟨1181331430710478599469519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1575108574280638132626025 1181331430710478599469519)
      ·
        refine ⟨1771997146065717899204279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1181331430710478599469519 1771997146065717899204279)
        ·
          refine ⟨2657995719098576848806419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1771997146065717899204279 2657995719098576848806419)
          ·
            refine ⟨3986993578647865273209629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2657995719098576848806419 3986993578647865273209629)
            ·
              refine ⟨1495122591992949477453611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3986993578647865273209629 1495122591992949477453611)
              ·
                refine ⟨2242683887989424216180417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1495122591992949477453611 2242683887989424216180417)
                ·
                  refine ⟨1682012915992068162135313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2242683887989424216180417 1682012915992068162135313)
                  ·
                    refine ⟨1261509686994051121601485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1682012915992068162135313 1261509686994051121601485)
                    ·
                      refine ⟨473066132622769170600557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1261509686994051121601485 473066132622769170600557)
                      ·
                        rfl

theorem cell23_921293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_921293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921293 prefixEnd_921293 := by exact prefixLift 921293
  have htrace : WordTrace (prefixWord ++ tailWord_921293) baseStart_921293 baseEnd_921293 := by
    simpa [prefixWord, tailWord_921293, baseEnd_921293] using wordTrace_append hprefix tailTrace_921293
  have hstable : (prefixWord ++ tailWord_921293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921293).length < 2 ^ (prefixWord ++ tailWord_921293).sum := by decide
  have hdescent : baseEnd_921293 < baseStart_921293 := by decide
  rcases family_descends (prefixWord ++ tailWord_921293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921322 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 3, 6]
def baseStart_921322 : Nat := 118140960795 + 921322 * 2 ^ 59
def prefixEnd_921322 : Nat := 4983230072969 + 3 ^ 40 * 921322 * 2
def baseEnd_921322 : Nat := 157693674520583185712641

theorem tailTrace_921322 : CollatzResearch.WordTrace tailWord_921322 prefixEnd_921322 157693674520583185712641 := by
  unfold tailWord_921322
  simp only [CollatzResearch.WordTrace]
  refine ⟨8400843492053804528873555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22402249312143478743662813 8400843492053804528873555)
  ·
    refine ⟨12601265238080706793310333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8400843492053804528873555 12601265238080706793310333)
    ·
      refine ⟨4725474464280265047491375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12601265238080706793310333 4725474464280265047491375)
      ·
        refine ⟨7088211696420397571237063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4725474464280265047491375 7088211696420397571237063)
        ·
          refine ⟨10632317544630596356855595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7088211696420397571237063 10632317544630596356855595)
          ·
            refine ⟨15948476316945894535283393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10632317544630596356855595 15948476316945894535283393)
            ·
              refine ⟨11961357237709420901462545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15948476316945894535283393 11961357237709420901462545)
              ·
                refine ⟨8971017928282065676096909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11961357237709420901462545 8971017928282065676096909)
                ·
                  refine ⟨3364131723105774628536341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8971017928282065676096909 3364131723105774628536341)
                  ·
                    refine ⟨157693674520583185712641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3364131723105774628536341 157693674520583185712641)
                    ·
                      rfl

theorem cell23_921322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_921322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921322 prefixEnd_921322 := by exact prefixLift 921322
  have htrace : WordTrace (prefixWord ++ tailWord_921322) baseStart_921322 baseEnd_921322 := by
    simpa [prefixWord, tailWord_921322, baseEnd_921322] using wordTrace_append hprefix tailTrace_921322
  have hstable : (prefixWord ++ tailWord_921322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921322).length < 2 ^ (prefixWord ++ tailWord_921322).sum := by decide
  have hdescent : baseEnd_921322 < baseStart_921322 := by decide
  rcases family_descends (prefixWord ++ tailWord_921322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921346 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 2, 6, 2]
def baseStart_921346 : Nat := 118140960795 + 921346 * 2 ^ 59
def prefixEnd_921346 : Nat := 4983230072969 + 3 ^ 40 * 921346 * 2
def baseEnd_921346 : Nat := 473093347097457463237813

theorem tailTrace_921346 : CollatzResearch.WordTrace tailWord_921346 prefixEnd_921346 473093347097457463237813 := by
  unfold tailWord_921346
  simp only [CollatzResearch.WordTrace]
  refine ⟨8401062330032067553591973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22402832880085513476245261 8401062330032067553591973)
  ·
    refine ⟨1575199186881012666298495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8401062330032067553591973 1575199186881012666298495)
    ·
      refine ⟨2362798780321518999447743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1575199186881012666298495 2362798780321518999447743)
      ·
        refine ⟨3544198170482278499171615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2362798780321518999447743 3544198170482278499171615)
        ·
          refine ⟨5316297255723417748757423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3544198170482278499171615 5316297255723417748757423)
          ·
            refine ⟨7974445883585126623136135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5316297255723417748757423 7974445883585126623136135)
            ·
              refine ⟨11961668825377689934704203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7974445883585126623136135 11961668825377689934704203)
              ·
                refine ⟨17942503238066534902056305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11961668825377689934704203 17942503238066534902056305)
                ·
                  refine ⟨13456877428549901176542229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17942503238066534902056305 13456877428549901176542229)
                  ·
                    refine ⟨630791129463276617650417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13456877428549901176542229 630791129463276617650417)
                    ·
                      refine ⟨473093347097457463237813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 630791129463276617650417 473093347097457463237813)
                      ·
                        rfl

theorem cell23_921346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_921346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921346 prefixEnd_921346 := by exact prefixLift 921346
  have htrace : WordTrace (prefixWord ++ tailWord_921346) baseStart_921346 baseEnd_921346 := by
    simpa [prefixWord, tailWord_921346, baseEnd_921346] using wordTrace_append hprefix tailTrace_921346
  have hstable : (prefixWord ++ tailWord_921346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921346).length < 2 ^ (prefixWord ++ tailWord_921346).sum := by decide
  have hdescent : baseEnd_921346 < baseStart_921346 := by decide
  rcases family_descends (prefixWord ++ tailWord_921346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921352 : List Nat := [2, 1, 3, 2, 2, 1, 3, 9]
def baseStart_921352 : Nat := 118140960795 + 921352 * 2 ^ 59
def prefixEnd_921352 : Nat := 4983230072969 + 3 ^ 40 * 921352 * 2
def baseEnd_921352 : Nat := 17522089925236460731955

theorem tailTrace_921352 : CollatzResearch.WordTrace tailWord_921352 prefixEnd_921352 17522089925236460731955 := by
  unfold tailWord_921352
  simp only [CollatzResearch.WordTrace]
  refine ⟨16802234079053266619543155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22402978772071022159390873 16802234079053266619543155)
  ·
    refine ⟨25203351118579899929314733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16802234079053266619543155 25203351118579899929314733)
    ·
      refine ⟨9451256669467462473493025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25203351118579899929314733 9451256669467462473493025)
      ·
        refine ⟨7088442502100596855119769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9451256669467462473493025 7088442502100596855119769)
        ·
          refine ⟨5316331876575447641339827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7088442502100596855119769 5316331876575447641339827)
          ·
            refine ⟨7974497814863171462009741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5316331876575447641339827 7974497814863171462009741)
            ·
              refine ⟨2990436680573689298253653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7974497814863171462009741 2990436680573689298253653)
              ·
                refine ⟨17522089925236460731955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2990436680573689298253653 17522089925236460731955)
                ·
                  rfl

theorem cell23_921352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 9].length) (baseStart_921352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921352 prefixEnd_921352 := by exact prefixLift 921352
  have htrace : WordTrace (prefixWord ++ tailWord_921352) baseStart_921352 baseEnd_921352 := by
    simpa [prefixWord, tailWord_921352, baseEnd_921352] using wordTrace_append hprefix tailTrace_921352
  have hstable : (prefixWord ++ tailWord_921352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921352).length < 2 ^ (prefixWord ++ tailWord_921352).sum := by decide
  have hdescent : baseEnd_921352 < baseStart_921352 := by decide
  rcases family_descends (prefixWord ++ tailWord_921352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921363 : List Nat := [1, 1, 1, 2, 1, 3, 2, 7, 1, 2, 2]
def baseStart_921363 : Nat := 118140960795 + 921363 * 2 ^ 59
def prefixEnd_921363 : Nat := 4983230072969 + 3 ^ 40 * 921363 * 2
def baseEnd_921363 : Nat := 473102076268583896725235

theorem tailTrace_921363 : CollatzResearch.WordTrace tailWord_921363 prefixEnd_921363 473102076268583896725235 := by
  unfold tailWord_921363
  simp only [CollatzResearch.WordTrace]
  refine ⟨33604869361066682117736743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22403246240711121411824495 33604869361066682117736743)
  ·
    refine ⟨50407304041600023176605115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33604869361066682117736743 50407304041600023176605115)
    ·
      refine ⟨75610956062400034764907673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50407304041600023176605115 75610956062400034764907673)
      ·
        refine ⟨56708217046800026073680755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75610956062400034764907673 56708217046800026073680755)
        ·
          refine ⟨85062325570200039110521133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56708217046800026073680755 85062325570200039110521133)
          ·
            refine ⟨31898372088825014666445425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85062325570200039110521133 31898372088825014666445425)
            ·
              refine ⟨23923779066618760999834069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31898372088825014666445425 23923779066618760999834069)
              ·
                refine ⟨560713571873877210933611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 23923779066618760999834069 560713571873877210933611)
                ·
                  refine ⟨841070357810815816400417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 560713571873877210933611 841070357810815816400417)
                  ·
                    refine ⟨630802768358111862300313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 841070357810815816400417 630802768358111862300313)
                    ·
                      refine ⟨473102076268583896725235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 630802768358111862300313 473102076268583896725235)
                      ·
                        rfl

theorem cell23_921363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 7, 1, 2, 2].length) (baseStart_921363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921363 prefixEnd_921363 := by exact prefixLift 921363
  have htrace : WordTrace (prefixWord ++ tailWord_921363) baseStart_921363 baseEnd_921363 := by
    simpa [prefixWord, tailWord_921363, baseEnd_921363] using wordTrace_append hprefix tailTrace_921363
  have hstable : (prefixWord ++ tailWord_921363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921363).length < 2 ^ (prefixWord ++ tailWord_921363).sum := by decide
  have hdescent : baseEnd_921363 < baseStart_921363 := by decide
  rcases family_descends (prefixWord ++ tailWord_921363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921374 : List Nat := [4, 3, 2, 2, 2, 1, 1, 1, 3, 1, 3]
def baseStart_921374 : Nat := 118140960795 + 921374 * 2 ^ 59
def prefixEnd_921374 : Nat := 4983230072969 + 3 ^ 40 * 921374 * 2
def baseEnd_921374 : Nat := 473107724555783353687685

theorem tailTrace_921374 : CollatzResearch.WordTrace tailWord_921374 prefixEnd_921374 473107724555783353687685 := by
  unfold tailWord_921374
  simp only [CollatzResearch.WordTrace]
  refine ⟨4200658820503353874548397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22403513709351220664258117 4200658820503353874548397)
  ·
    refine ⟨1575247057688757702955649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4200658820503353874548397 1575247057688757702955649)
    ·
      refine ⟨1181435293266568277216737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1575247057688757702955649 1181435293266568277216737)
      ·
        refine ⟨886076469949926207912553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1181435293266568277216737 886076469949926207912553)
        ·
          refine ⟨664557352462444655934415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 886076469949926207912553 664557352462444655934415)
          ·
            refine ⟨996836028693666983901623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664557352462444655934415 996836028693666983901623)
            ·
              refine ⟨1495254043040500475852435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 996836028693666983901623 1495254043040500475852435)
              ·
                refine ⟨2242881064560750713778653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1495254043040500475852435 2242881064560750713778653)
                ·
                  refine ⟨841080399210281517666995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2242881064560750713778653 841080399210281517666995)
                  ·
                    refine ⟨1261620598815422276500493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 841080399210281517666995 1261620598815422276500493)
                    ·
                      refine ⟨473107724555783353687685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1261620598815422276500493 473107724555783353687685)
                      ·
                        rfl

theorem cell23_921374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_921374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921374 prefixEnd_921374 := by exact prefixLift 921374
  have htrace : WordTrace (prefixWord ++ tailWord_921374) baseStart_921374 baseEnd_921374 := by
    simpa [prefixWord, tailWord_921374, baseEnd_921374] using wordTrace_append hprefix tailTrace_921374
  have hstable : (prefixWord ++ tailWord_921374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921374).length < 2 ^ (prefixWord ++ tailWord_921374).sum := by decide
  have hdescent : baseEnd_921374 < baseStart_921374 := by decide
  rcases family_descends (prefixWord ++ tailWord_921374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921380 : List Nat := [2, 3, 1, 3, 2, 3, 1, 1, 3, 2, 2]
def baseStart_921380 : Nat := 118140960795 + 921380 * 2 ^ 59
def prefixEnd_921380 : Nat := 4983230072969 + 3 ^ 40 * 921380 * 2
def baseEnd_921380 : Nat := 473110805439710330212657

theorem tailTrace_921380 : CollatzResearch.WordTrace tailWord_921380 prefixEnd_921380 473110805439710330212657 := by
  unfold tailWord_921380
  simp only [CollatzResearch.WordTrace]
  refine ⟨16802744701002547010552797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22403659601336729347403729 16802744701002547010552797)
  ·
    refine ⟨6301029262875955128957299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16802744701002547010552797 6301029262875955128957299)
    ·
      refine ⟨9451543894313932693435949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6301029262875955128957299 9451543894313932693435949)
      ·
        refine ⟨3544328960367724760038481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9451543894313932693435949 3544328960367724760038481)
        ·
          refine ⟨2658246720275793570028861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3544328960367724760038481 2658246720275793570028861)
          ·
            refine ⟨996842520103422588760823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2658246720275793570028861 996842520103422588760823)
            ·
              refine ⟨1495263780155133883141235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 996842520103422588760823 1495263780155133883141235)
              ·
                refine ⟨2242895670232700824711853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1495263780155133883141235 2242895670232700824711853)
                ·
                  refine ⟨841085876337262809266945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2242895670232700824711853 841085876337262809266945)
                  ·
                    refine ⟨630814407252947106950209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 841085876337262809266945 630814407252947106950209)
                    ·
                      refine ⟨473110805439710330212657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 630814407252947106950209 473110805439710330212657)
                      ·
                        rfl

theorem cell23_921380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_921380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921380 prefixEnd_921380 := by exact prefixLift 921380
  have htrace : WordTrace (prefixWord ++ tailWord_921380) baseStart_921380 baseEnd_921380 := by
    simpa [prefixWord, tailWord_921380, baseEnd_921380] using wordTrace_append hprefix tailTrace_921380
  have hstable : (prefixWord ++ tailWord_921380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921380).length < 2 ^ (prefixWord ++ tailWord_921380).sum := by decide
  have hdescent : baseEnd_921380 < baseStart_921380 := by decide
  rcases family_descends (prefixWord ++ tailWord_921380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921432 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 1, 5, 6]
def baseStart_921432 : Nat := 118140960795 + 921432 * 2 ^ 59
def prefixEnd_921432 : Nat := 4983230072969 + 3 ^ 40 * 921432 * 2
def baseEnd_921432 : Nat := 473137506433744126762417

theorem tailTrace_921432 : CollatzResearch.WordTrace tailWord_921432 prefixEnd_921432 473137506433744126762417 := by
  unfold tailWord_921432
  simp only [CollatzResearch.WordTrace]
  refine ⟨16803692998908353450999275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22404923998544471267999033 16803692998908353450999275)
  ·
    refine ⟨25205539498362530176498913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16803692998908353450999275 25205539498362530176498913)
    ·
      refine ⟨18904154623771897632374185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25205539498362530176498913 18904154623771897632374185)
      ·
        refine ⟨14178115967828923224280639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18904154623771897632374185 14178115967828923224280639)
        ·
          refine ⟨21267173951743384836420959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14178115967828923224280639 21267173951743384836420959)
          ·
            refine ⟨31900760927615077254631439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21267173951743384836420959 31900760927615077254631439)
            ·
              refine ⟨47851141391422615881947159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31900760927615077254631439 47851141391422615881947159)
              ·
                refine ⟨71776712087133923822920739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47851141391422615881947159 71776712087133923822920739)
                ·
                  refine ⟨107665068130700885734381109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71776712087133923822920739 107665068130700885734381109)
                  ·
                    refine ⟨10093600137253208037598229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 107665068130700885734381109 10093600137253208037598229)
                    ·
                      refine ⟨473137506433744126762417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10093600137253208037598229 473137506433744126762417)
                      ·
                        rfl

theorem cell23_921432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_921432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921432 prefixEnd_921432 := by exact prefixLift 921432
  have htrace : WordTrace (prefixWord ++ tailWord_921432) baseStart_921432 baseEnd_921432 := by
    simpa [prefixWord, tailWord_921432, baseEnd_921432] using wordTrace_append hprefix tailTrace_921432
  have hstable : (prefixWord ++ tailWord_921432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921432).length < 2 ^ (prefixWord ++ tailWord_921432).sum := by decide
  have hdescent : baseEnd_921432 < baseStart_921432 := by decide
  rcases family_descends (prefixWord ++ tailWord_921432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921439 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 2, 4, 3]
def baseStart_921439 : Nat := 118140960795 + 921439 * 2 ^ 59
def prefixEnd_921439 : Nat := 4983230072969 + 3 ^ 40 * 921439 * 2
def baseEnd_921439 : Nat := 473141100798325599374885

theorem tailTrace_921439 : CollatzResearch.WordTrace tailWord_921439 prefixEnd_921439 473141100798325599374885 := by
  unfold tailWord_921439
  simp only [CollatzResearch.WordTrace]
  refine ⟨33607641308791347097503371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22405094205860898065002247 33607641308791347097503371)
  ·
    refine ⟨50411461963187020646255057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33607641308791347097503371 50411461963187020646255057)
    ·
      refine ⟨37808596472390265484691293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50411461963187020646255057 37808596472390265484691293)
      ·
        refine ⟨14178223677146349556759235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37808596472390265484691293 14178223677146349556759235)
        ·
          refine ⟨21267335515719524335138853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14178223677146349556759235 21267335515719524335138853)
          ·
            refine ⟨3987625409197410812838535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21267335515719524335138853 3987625409197410812838535)
            ·
              refine ⟨5981438113796116219257803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3987625409197410812838535 5981438113796116219257803)
              ·
                refine ⟨8972157170694174328886705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5981438113796116219257803 8972157170694174328886705)
                ·
                  refine ⟨6729117878020630746665029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8972157170694174328886705 6729117878020630746665029)
                  ·
                    refine ⟨1261709602128868264999693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6729117878020630746665029 1261709602128868264999693)
                    ·
                      refine ⟨473141100798325599374885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1261709602128868264999693 473141100798325599374885)
                      ·
                        rfl

theorem cell23_921439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_921439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921439 prefixEnd_921439 := by exact prefixLift 921439
  have htrace : WordTrace (prefixWord ++ tailWord_921439) baseStart_921439 baseEnd_921439 := by
    simpa [prefixWord, tailWord_921439, baseEnd_921439] using wordTrace_append hprefix tailTrace_921439
  have hstable : (prefixWord ++ tailWord_921439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921439).length < 2 ^ (prefixWord ++ tailWord_921439).sum := by decide
  have hdescent : baseEnd_921439 < baseStart_921439 := by decide
  rcases family_descends (prefixWord ++ tailWord_921439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921469 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 3, 5, 3]
def baseStart_921469 : Nat := 118140960795 + 921469 * 2 ^ 59
def prefixEnd_921469 : Nat := 4983230072969 + 3 ^ 40 * 921469 * 2
def baseEnd_921469 : Nat := 473156505217960481999747

theorem tailTrace_921469 : CollatzResearch.WordTrace tailWord_921469 prefixEnd_921469 473156505217960481999747 := by
  unfold tailWord_921469
  simp only [CollatzResearch.WordTrace]
  refine ⟨33608735498682662221095461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22405823665788441480730307 33608735498682662221095461)
  ·
    refine ⟨6301637906002999166455399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33608735498682662221095461 6301637906002999166455399)
    ·
      refine ⟨9452456859004498749683099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6301637906002999166455399 9452456859004498749683099)
      ·
        refine ⟨14178685288506748124524649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9452456859004498749683099 14178685288506748124524649)
        ·
          refine ⟨10634013966380061093393487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14178685288506748124524649 10634013966380061093393487)
          ·
            refine ⟨15951020949570091640090231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10634013966380061093393487 15951020949570091640090231)
            ·
              refine ⟨23926531424355137460135347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15951020949570091640090231 23926531424355137460135347)
              ·
                refine ⟨35889797136532706190203021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23926531424355137460135347 35889797136532706190203021)
                ·
                  refine ⟨13458673926199764821326133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35889797136532706190203021 13458673926199764821326133)
                  ·
                    refine ⟨1261750680581227951999325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13458673926199764821326133 1261750680581227951999325)
                    ·
                      refine ⟨473156505217960481999747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1261750680581227951999325 473156505217960481999747)
                      ·
                        rfl

theorem cell23_921469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_921469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921469 prefixEnd_921469 := by exact prefixLift 921469
  have htrace : WordTrace (prefixWord ++ tailWord_921469) baseStart_921469 baseEnd_921469 := by
    simpa [prefixWord, tailWord_921469, baseEnd_921469] using wordTrace_append hprefix tailTrace_921469
  have hstable : (prefixWord ++ tailWord_921469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921469).length < 2 ^ (prefixWord ++ tailWord_921469).sum := by decide
  have hdescent : baseEnd_921469 < baseStart_921469 := by decide
  rcases family_descends (prefixWord ++ tailWord_921469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921470 : List Nat := [4, 2, 3, 1, 1, 1, 2, 2, 1, 4, 2]
def baseStart_921470 : Nat := 118140960795 + 921470 * 2 ^ 59
def prefixEnd_921470 : Nat := 4983230072969 + 3 ^ 40 * 921470 * 2
def baseEnd_921470 : Nat := 473157018698614978087243

theorem tailTrace_921470 : CollatzResearch.WordTrace tailWord_921470 prefixEnd_921470 473157018698614978087243 := by
  unfold tailWord_921470
  simp only [CollatzResearch.WordTrace]
  refine ⟨4201096496459879923985233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22405847981119359594587909 4201096496459879923985233)
  ·
    refine ⟨3150822372344909942988925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4201096496459879923985233 3150822372344909942988925)
    ·
      refine ⟨1181558389629341228620847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3150822372344909942988925 1181558389629341228620847)
      ·
        refine ⟨1772337584444011842931271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1181558389629341228620847 1772337584444011842931271)
        ·
          refine ⟨2658506376666017764396907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1772337584444011842931271 2658506376666017764396907)
          ·
            refine ⟨3987759564999026646595361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2658506376666017764396907 3987759564999026646595361)
            ·
              refine ⟨2990819673749269984946521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3987759564999026646595361 2990819673749269984946521)
              ·
                refine ⟨2243114755311952488709891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2990819673749269984946521 2243114755311952488709891)
                ·
                  refine ⟨3364672132967928733064837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2243114755311952488709891 3364672132967928733064837)
                  ·
                    refine ⟨630876024931486637449657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3364672132967928733064837 630876024931486637449657)
                    ·
                      refine ⟨473157018698614978087243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 630876024931486637449657 473157018698614978087243)
                      ·
                        rfl

theorem cell23_921470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_921470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921470 prefixEnd_921470 := by exact prefixLift 921470
  have htrace : WordTrace (prefixWord ++ tailWord_921470) baseStart_921470 baseEnd_921470 := by
    simpa [prefixWord, tailWord_921470, baseEnd_921470] using wordTrace_append hprefix tailTrace_921470
  have hstable : (prefixWord ++ tailWord_921470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921470).length < 2 ^ (prefixWord ++ tailWord_921470).sum := by decide
  have hdescent : baseEnd_921470 < baseStart_921470 := by decide
  rcases family_descends (prefixWord ++ tailWord_921470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921476 : List Nat := [2, 3, 2, 1, 1, 1, 3, 5, 5]
def baseStart_921476 : Nat := 118140960795 + 921476 * 2 ^ 59
def prefixEnd_921476 : Nat := 4983230072969 + 3 ^ 40 * 921476 * 2
def baseEnd_921476 : Nat := 52573344398060217179135

theorem tailTrace_921476 : CollatzResearch.WordTrace tailWord_921476 prefixEnd_921476 52573344398060217179135 := by
  unfold tailWord_921476
  simp only [CollatzResearch.WordTrace]
  refine ⟨16804495404828651208300141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22405993873104868277733521 16804495404828651208300141)
  ·
    refine ⟨6301685776810744203112553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16804495404828651208300141 6301685776810744203112553)
    ·
      refine ⟨4726264332608058152334415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6301685776810744203112553 4726264332608058152334415)
      ·
        refine ⟨7089396498912087228501623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4726264332608058152334415 7089396498912087228501623)
        ·
          refine ⟨10634094748368130842752435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7089396498912087228501623 10634094748368130842752435)
          ·
            refine ⟨15951142122552196264128653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10634094748368130842752435 15951142122552196264128653)
            ·
              refine ⟨5981678295957073599048245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15951142122552196264128653 5981678295957073599048245)
              ·
                refine ⟨560782340245975649910773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5981678295957073599048245 560782340245975649910773)
                ·
                  refine ⟨52573344398060217179135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 560782340245975649910773 52573344398060217179135)
                  ·
                    rfl

theorem cell23_921476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 5, 5].length) (baseStart_921476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921476 prefixEnd_921476 := by exact prefixLift 921476
  have htrace : WordTrace (prefixWord ++ tailWord_921476) baseStart_921476 baseEnd_921476 := by
    simpa [prefixWord, tailWord_921476, baseEnd_921476] using wordTrace_append hprefix tailTrace_921476
  have hstable : (prefixWord ++ tailWord_921476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921476).length < 2 ^ (prefixWord ++ tailWord_921476).sum := by decide
  have hdescent : baseEnd_921476 < baseStart_921476 := by decide
  rcases family_descends (prefixWord ++ tailWord_921476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921489 : List Nat := [1, 2, 2, 1, 1, 1, 4, 4, 2, 5]
def baseStart_921489 : Nat := 118140960795 + 921489 * 2 ^ 59
def prefixEnd_921489 : Nat := 4983230072969 + 3 ^ 40 * 921489 * 2
def baseEnd_921489 : Nat := 157722258277016801249885

theorem tailTrace_921489 : CollatzResearch.WordTrace tailWord_921489 prefixEnd_921489 157722258277016801249885 := by
  unfold tailWord_921489
  simp only [CollatzResearch.WordTrace]
  refine ⟨33609464958610205636823521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22406309972406803757882347 33609464958610205636823521)
  ·
    refine ⟨25207098718957654227617641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33609464958610205636823521 25207098718957654227617641)
    ·
      refine ⟨18905324039218240670713231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25207098718957654227617641 18905324039218240670713231)
      ·
        refine ⟨28357986058827361006069847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18905324039218240670713231 28357986058827361006069847)
        ·
          refine ⟨42536979088241041509104771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28357986058827361006069847 42536979088241041509104771)
          ·
            refine ⟨63805468632361562263657157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42536979088241041509104771 63805468632361562263657157)
            ·
              refine ⟨11963525368567792924435717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63805468632361562263657157 11963525368567792924435717)
              ·
                refine ⟨2243161006606461173331697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11963525368567792924435717 2243161006606461173331697)
                ·
                  refine ⟨1682370754954845879998773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2243161006606461173331697 1682370754954845879998773)
                  ·
                    refine ⟨157722258277016801249885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1682370754954845879998773 157722258277016801249885)
                    ·
                      rfl

theorem cell23_921489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 5].length) (baseStart_921489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921489 prefixEnd_921489 := by exact prefixLift 921489
  have htrace : WordTrace (prefixWord ++ tailWord_921489) baseStart_921489 baseEnd_921489 := by
    simpa [prefixWord, tailWord_921489, baseEnd_921489] using wordTrace_append hprefix tailTrace_921489
  have hstable : (prefixWord ++ tailWord_921489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921489).length < 2 ^ (prefixWord ++ tailWord_921489).sum := by decide
  have hdescent : baseEnd_921489 < baseStart_921489 := by decide
  rcases family_descends (prefixWord ++ tailWord_921489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921546 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 4, 2, 3]
def baseStart_921546 : Nat := 118140960795 + 921546 * 2 ^ 59
def prefixEnd_921546 : Nat := 4983230072969 + 3 ^ 40 * 921546 * 2
def baseEnd_921546 : Nat := 473196043228356680736893

theorem tailTrace_921546 : CollatzResearch.WordTrace tailWord_921546 prefixEnd_921546 473196043228356680736893 := by
  unfold tailWord_921546
  simp only [CollatzResearch.WordTrace]
  refine ⟨8402885979850926092912123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22407695946269136247765661 8402885979850926092912123)
  ·
    refine ⟨12604328969776389139368185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8402885979850926092912123 12604328969776389139368185)
    ·
      refine ⟨9453246727332291854526139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12604328969776389139368185 9453246727332291854526139)
      ·
        refine ⟨14179870090998437781789209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9453246727332291854526139 14179870090998437781789209)
        ·
          refine ⟨10634902568248828336341907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14179870090998437781789209 10634902568248828336341907)
          ·
            refine ⟨15952353852373242504512861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10634902568248828336341907 15952353852373242504512861)
            ·
              refine ⟨5982132694639965939192323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15952353852373242504512861 5982132694639965939192323)
              ·
                refine ⟨8973199041959948908788485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5982132694639965939192323 8973199041959948908788485)
                ·
                  refine ⟨1682474820367490420397841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8973199041959948908788485 1682474820367490420397841)
                  ·
                    refine ⟨1261856115275617815298381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1682474820367490420397841 1261856115275617815298381)
                    ·
                      refine ⟨473196043228356680736893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1261856115275617815298381 473196043228356680736893)
                      ·
                        rfl

theorem cell23_921546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_921546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921546 prefixEnd_921546 := by exact prefixLift 921546
  have htrace : WordTrace (prefixWord ++ tailWord_921546) baseStart_921546 baseEnd_921546 := by
    simpa [prefixWord, tailWord_921546, baseEnd_921546] using wordTrace_append hprefix tailTrace_921546
  have hstable : (prefixWord ++ tailWord_921546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921546).length < 2 ^ (prefixWord ++ tailWord_921546).sum := by decide
  have hdescent : baseEnd_921546 < baseStart_921546 := by decide
  rcases family_descends (prefixWord ++ tailWord_921546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921569 : List Nat := [1, 2, 3, 1, 2, 1, 2, 2, 1, 2, 6]
def baseStart_921569 : Nat := 118140960795 + 921569 * 2 ^ 59
def prefixEnd_921569 : Nat := 4983230072969 + 3 ^ 40 * 921569 * 2
def baseEnd_921569 : Nat := 473207853283410090749287

theorem tailTrace_921569 : CollatzResearch.WordTrace tailWord_921569 prefixEnd_921569 473207853283410090749287 := by
  unfold tailWord_921569
  simp only [CollatzResearch.WordTrace]
  refine ⟨33612382798320379299735761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22408255198880252866490507 33612382798320379299735761)
  ·
    refine ⟨25209287098740284474801821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33612382798320379299735761 25209287098740284474801821)
    ·
      refine ⟨9453482662027606678050683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25209287098740284474801821 9453482662027606678050683)
      ·
        refine ⟨14180223993041410017076025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9453482662027606678050683 14180223993041410017076025)
        ·
          refine ⟨10635167994781057512807019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14180223993041410017076025 10635167994781057512807019)
          ·
            refine ⟨15952751992171586269210529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10635167994781057512807019 15952751992171586269210529)
            ·
              refine ⟨11964563994128689701907897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15952751992171586269210529 11964563994128689701907897)
              ·
                refine ⟨8973422995596517276430923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11964563994128689701907897 8973422995596517276430923)
                ·
                  refine ⟨13460134493394775914646385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8973422995596517276430923 13460134493394775914646385)
                  ·
                    refine ⟨10095100870046081935984789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13460134493394775914646385 10095100870046081935984789)
                    ·
                      refine ⟨473207853283410090749287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10095100870046081935984789 473207853283410090749287)
                      ·
                        rfl

theorem cell23_921569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_921569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921569 prefixEnd_921569 := by exact prefixLift 921569
  have htrace : WordTrace (prefixWord ++ tailWord_921569) baseStart_921569 baseEnd_921569 := by
    simpa [prefixWord, tailWord_921569, baseEnd_921569] using wordTrace_append hprefix tailTrace_921569
  have hstable : (prefixWord ++ tailWord_921569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921569).length < 2 ^ (prefixWord ++ tailWord_921569).sum := by decide
  have hdescent : baseEnd_921569 < baseStart_921569 := by decide
  rcases family_descends (prefixWord ++ tailWord_921569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921626 : List Nat := [3, 1, 1, 3, 1, 3, 1, 3, 1, 6]
def baseStart_921626 : Nat := 118140960795 + 921626 * 2 ^ 59
def prefixEnd_921626 : Nat := 4983230072969 + 3 ^ 40 * 921626 * 2
def baseEnd_921626 : Nat := 157745707226905455912175

theorem tailTrace_921626 : CollatzResearch.WordTrace tailWord_921626 prefixEnd_921626 157745707226905455912175 := by
  unfold tailWord_921626
  simp only [CollatzResearch.WordTrace]
  refine ⟨8403615439778469508640183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22409641172742585356373821 8403615439778469508640183)
  ·
    refine ⟨12605423159667704262960275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8403615439778469508640183 12605423159667704262960275)
    ·
      refine ⟨18908134739501556394440413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12605423159667704262960275 18908134739501556394440413)
      ·
        refine ⟨7090550527313083647915155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18908134739501556394440413 7090550527313083647915155)
        ·
          refine ⟨10635825790969625471872733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7090550527313083647915155 10635825790969625471872733)
          ·
            refine ⟨3988434671613609551952275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10635825790969625471872733 3988434671613609551952275)
            ·
              refine ⟨5982652007420414327928413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3988434671613609551952275 5982652007420414327928413)
              ·
                refine ⟨2243494502782655372973155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5982652007420414327928413 2243494502782655372973155)
                ·
                  refine ⟨3365241754173983059459733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2243494502782655372973155 3365241754173983059459733)
                  ·
                    refine ⟨157745707226905455912175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3365241754173983059459733 157745707226905455912175)
                    ·
                      rfl

theorem cell23_921626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 1, 6].length) (baseStart_921626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921626 prefixEnd_921626 := by exact prefixLift 921626
  have htrace : WordTrace (prefixWord ++ tailWord_921626) baseStart_921626 baseEnd_921626 := by
    simpa [prefixWord, tailWord_921626, baseEnd_921626] using wordTrace_append hprefix tailTrace_921626
  have hstable : (prefixWord ++ tailWord_921626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921626).length < 2 ^ (prefixWord ++ tailWord_921626).sum := by decide
  have hdescent : baseEnd_921626 < baseStart_921626 := by decide
  rcases family_descends (prefixWord ++ tailWord_921626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921650 : List Nat := [3, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4]
def baseStart_921650 : Nat := 118140960795 + 921650 * 2 ^ 59
def prefixEnd_921650 : Nat := 4983230072969 + 3 ^ 40 * 921650 * 2
def baseEnd_921650 : Nat := 473249445216424273836415

theorem tailTrace_921650 : CollatzResearch.WordTrace tailWord_921650 prefixEnd_921650 473249445216424273836415 := by
  unfold tailWord_921650
  simp only [CollatzResearch.WordTrace]
  refine ⟨8403834277756732533358601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22410224740684620088956269 8403834277756732533358601)
  ·
    refine ⟨6302875708317549400018951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8403834277756732533358601 6302875708317549400018951)
    ·
      refine ⟨9454313562476324100028427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6302875708317549400018951 9454313562476324100028427)
      ·
        refine ⟨14181470343714486150042641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9454313562476324100028427 14181470343714486150042641)
        ·
          refine ⟨10636102757785864612531981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14181470343714486150042641 10636102757785864612531981)
          ·
            refine ⟨3988538534169699229699493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10636102757785864612531981 3988538534169699229699493)
            ·
              refine ⟨747850975156818605568655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3988538534169699229699493 747850975156818605568655)
              ·
                refine ⟨1121776462735227908352983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 747850975156818605568655 1121776462735227908352983)
                ·
                  refine ⟨1682664694102841862529475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1121776462735227908352983 1682664694102841862529475)
                  ·
                    refine ⟨2523997041154262793794213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1682664694102841862529475 2523997041154262793794213)
                    ·
                      refine ⟨473249445216424273836415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2523997041154262793794213 473249445216424273836415)
                      ·
                        rfl

theorem cell23_921650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4].length) (baseStart_921650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921650 prefixEnd_921650 := by exact prefixLift 921650
  have htrace : WordTrace (prefixWord ++ tailWord_921650) baseStart_921650 baseEnd_921650 := by
    simpa [prefixWord, tailWord_921650, baseEnd_921650] using wordTrace_append hprefix tailTrace_921650
  have hstable : (prefixWord ++ tailWord_921650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921650).length < 2 ^ (prefixWord ++ tailWord_921650).sum := by decide
  have hdescent : baseEnd_921650 < baseStart_921650 := by decide
  rcases family_descends (prefixWord ++ tailWord_921650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921656 : List Nat := [2, 1, 2, 1, 6, 1, 10]
def baseStart_921656 : Nat := 118140960795 + 921656 * 2 ^ 59
def prefixEnd_921656 : Nat := 4983230072969 + 3 ^ 40 * 921656 * 2
def baseEnd_921656 : Nat := 5842623779016682103227

theorem tailTrace_921656 : CollatzResearch.WordTrace tailWord_921656 prefixEnd_921656 5842623779016682103227 := by
  unfold tailWord_921656
  simp only [CollatzResearch.WordTrace]
  refine ⟨16807777974502596579076411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22410370632670128772101881 16807777974502596579076411)
  ·
    refine ⟨25211666961753894868614617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16807777974502596579076411 25211666961753894868614617)
    ·
      refine ⟨18908750221315421151460963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25211666961753894868614617 18908750221315421151460963)
      ·
        refine ⟨28363125331973131727191445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18908750221315421151460963 28363125331973131727191445)
        ·
          refine ⟨1329521499936240549712099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28363125331973131727191445 1329521499936240549712099)
          ·
            refine ⟨1994282249904360824568149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1329521499936240549712099 1994282249904360824568149)
            ·
              refine ⟨5842623779016682103227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1994282249904360824568149 5842623779016682103227)
              ·
                rfl

theorem cell23_921656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 10].length) (baseStart_921656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921656 prefixEnd_921656 := by exact prefixLift 921656
  have htrace : WordTrace (prefixWord ++ tailWord_921656) baseStart_921656 baseEnd_921656 := by
    simpa [prefixWord, tailWord_921656, baseEnd_921656] using wordTrace_append hprefix tailTrace_921656
  have hstable : (prefixWord ++ tailWord_921656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921656).length < 2 ^ (prefixWord ++ tailWord_921656).sum := by decide
  have hdescent : baseEnd_921656 < baseStart_921656 := by decide
  rcases family_descends (prefixWord ++ tailWord_921656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921670 : List Nat := [6, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_921670 : Nat := 118140960795 + 921670 * 2 ^ 59
def prefixEnd_921670 : Nat := 4983230072969 + 3 ^ 40 * 921670 * 2
def baseEnd_921670 : Nat := 473259714829514195586323

theorem tailTrace_921670 : CollatzResearch.WordTrace tailWord_921670 prefixEnd_921670 473259714829514195586323 := by
  unfold tailWord_921670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1050502080342327298411327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22410711047302982366108309 1050502080342327298411327)
  ·
    refine ⟨1575753120513490947616991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1050502080342327298411327 1575753120513490947616991)
    ·
      refine ⟨2363629680770236421425487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1575753120513490947616991 2363629680770236421425487)
      ·
        refine ⟨3545444521155354632138231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2363629680770236421425487 3545444521155354632138231)
        ·
          refine ⟨5318166781733031948207347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3545444521155354632138231 5318166781733031948207347)
          ·
            refine ⟨7977250172599547922311021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5318166781733031948207347 7977250172599547922311021)
            ·
              refine ⟨2991468814724830470866633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7977250172599547922311021 2991468814724830470866633)
              ·
                refine ⟨2243601611043622853149975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2991468814724830470866633 2243601611043622853149975)
                ·
                  refine ⟨3365402416565434279724963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2243601611043622853149975 3365402416565434279724963)
                  ·
                    refine ⟨5048103624848151419587445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3365402416565434279724963 5048103624848151419587445)
                    ·
                      refine ⟨473259714829514195586323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5048103624848151419587445 473259714829514195586323)
                      ·
                        rfl

theorem cell23_921670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_921670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921670 prefixEnd_921670 := by exact prefixLift 921670
  have htrace : WordTrace (prefixWord ++ tailWord_921670) baseStart_921670 baseEnd_921670 := by
    simpa [prefixWord, tailWord_921670, baseEnd_921670] using wordTrace_append hprefix tailTrace_921670
  have hstable : (prefixWord ++ tailWord_921670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921670).length < 2 ^ (prefixWord ++ tailWord_921670).sum := by decide
  have hdescent : baseEnd_921670 < baseStart_921670 := by decide
  rcases family_descends (prefixWord ++ tailWord_921670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921677 : List Nat := [1, 6, 1, 1, 1, 1, 5, 1, 2, 4]
def baseStart_921677 : Nat := 118140960795 + 921677 * 2 ^ 59
def prefixEnd_921677 : Nat := 4983230072969 + 3 ^ 40 * 921677 * 2
def baseEnd_921677 : Nat := 157754436398031889399597

theorem tailTrace_921677 : CollatzResearch.WordTrace tailWord_921677 prefixEnd_921677 157754436398031889399597 := by
  unfold tailWord_921677
  simp only [CollatzResearch.WordTrace]
  refine ⟨33616321881929113744667285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22410881254619409163111523 33616321881929113744667285)
  ·
    refine ⟨1575765088215427206781279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33616321881929113744667285 1575765088215427206781279)
    ·
      refine ⟨2363647632323140810171919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1575765088215427206781279 2363647632323140810171919)
      ·
        refine ⟨3545471448484711215257879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2363647632323140810171919 3545471448484711215257879)
        ·
          refine ⟨5318207172727066822886819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3545471448484711215257879 5318207172727066822886819)
          ·
            refine ⟨7977310759090600234330229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5318207172727066822886819 7977310759090600234330229)
            ·
              refine ⟨747872883664743771968459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7977310759090600234330229 747872883664743771968459)
              ·
                refine ⟨1121809325497115657952689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 747872883664743771968459 1121809325497115657952689)
                ·
                  refine ⟨841356994122836743464517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1121809325497115657952689 841356994122836743464517)
                  ·
                    refine ⟨157754436398031889399597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 841356994122836743464517 157754436398031889399597)
                    ·
                      rfl

theorem cell23_921677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_921677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921677 prefixEnd_921677 := by exact prefixLift 921677
  have htrace : WordTrace (prefixWord ++ tailWord_921677) baseStart_921677 baseEnd_921677 := by
    simpa [prefixWord, tailWord_921677, baseEnd_921677] using wordTrace_append hprefix tailTrace_921677
  have hstable : (prefixWord ++ tailWord_921677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921677).length < 2 ^ (prefixWord ++ tailWord_921677).sum := by decide
  have hdescent : baseEnd_921677 < baseStart_921677 := by decide
  rcases family_descends (prefixWord ++ tailWord_921677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921696 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 5]
def baseStart_921696 : Nat := 118140960795 + 921696 * 2 ^ 59
def prefixEnd_921696 : Nat := 4983230072969 + 3 ^ 40 * 921696 * 2
def baseEnd_921696 : Nat := 473273065326531093861203

theorem tailTrace_921696 : CollatzResearch.WordTrace tailWord_921696 prefixEnd_921696 473273065326531093861203 := by
  unfold tailWord_921696
  simp only [CollatzResearch.WordTrace]
  refine ⟨16808507434430139994804471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22411343245906853326405961 16808507434430139994804471)
  ·
    refine ⟨25212761151645209992206707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16808507434430139994804471 25212761151645209992206707)
    ·
      refine ⟨37819141727467814988310061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25212761151645209992206707 37819141727467814988310061)
      ·
        refine ⟨14182178147800430620616273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37819141727467814988310061 14182178147800430620616273)
        ·
          refine ⟨10636633610850322965462205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14182178147800430620616273 10636633610850322965462205)
          ·
            refine ⟨3988737604068871112048327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10636633610850322965462205 3988737604068871112048327)
            ·
              refine ⟨5983106406103306668072491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3988737604068871112048327 5983106406103306668072491)
              ·
                refine ⟨8974659609154960002108737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5983106406103306668072491 8974659609154960002108737)
                ·
                  refine ⟨6730994706866220001581553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8974659609154960002108737 6730994706866220001581553)
                  ·
                    refine ⟨5048246030149665001186165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6730994706866220001581553 5048246030149665001186165)
                    ·
                      refine ⟨473273065326531093861203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5048246030149665001186165 473273065326531093861203)
                      ·
                        rfl

theorem cell23_921696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_921696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921696 prefixEnd_921696 := by exact prefixLift 921696
  have htrace : WordTrace (prefixWord ++ tailWord_921696) baseStart_921696 baseEnd_921696 := by
    simpa [prefixWord, tailWord_921696, baseEnd_921696] using wordTrace_append hprefix tailTrace_921696
  have hstable : (prefixWord ++ tailWord_921696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921696).length < 2 ^ (prefixWord ++ tailWord_921696).sum := by decide
  have hdescent : baseEnd_921696 < baseStart_921696 := by decide
  rcases family_descends (prefixWord ++ tailWord_921696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921810 : List Nat := [3, 2, 2, 2, 1, 2, 3, 1, 2, 5]
def baseStart_921810 : Nat := 118140960795 + 921810 * 2 ^ 59
def prefixEnd_921810 : Nat := 4983230072969 + 3 ^ 40 * 921810 * 2
def baseEnd_921810 : Nat := 157777200707047882611893

theorem tailTrace_921810 : CollatzResearch.WordTrace tailWord_921810 prefixEnd_921810 157777200707047882611893 := by
  unfold tailWord_921810
  simp only [CollatzResearch.WordTrace]
  refine ⟨8405293197611819364814721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22414115193631518306172589 8405293197611819364814721)
  ·
    refine ⟨6303969898208864523611041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8405293197611819364814721 6303969898208864523611041)
    ·
      refine ⟨4727977423656648392708281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6303969898208864523611041 4727977423656648392708281)
      ·
        refine ⟨3545983067742486294531211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4727977423656648392708281 3545983067742486294531211)
        ·
          refine ⟨5318974601613729441796817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3545983067742486294531211 5318974601613729441796817)
          ·
            refine ⟨3989230951210297081347613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5318974601613729441796817 3989230951210297081347613)
            ·
              refine ⟨1495961606703861405505355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3989230951210297081347613 1495961606703861405505355)
              ·
                refine ⟨2243942410055792108258033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1495961606703861405505355 2243942410055792108258033)
                ·
                  refine ⟨1682956807541844081193525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2243942410055792108258033 1682956807541844081193525)
                  ·
                    refine ⟨157777200707047882611893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1682956807541844081193525 157777200707047882611893)
                    ·
                      rfl

theorem cell23_921810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_921810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921810 prefixEnd_921810 := by exact prefixLift 921810
  have htrace : WordTrace (prefixWord ++ tailWord_921810) baseStart_921810 baseEnd_921810 := by
    simpa [prefixWord, tailWord_921810, baseEnd_921810] using wordTrace_append hprefix tailTrace_921810
  have hstable : (prefixWord ++ tailWord_921810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921810).length < 2 ^ (prefixWord ++ tailWord_921810).sum := by decide
  have hdescent : baseEnd_921810 < baseStart_921810 := by decide
  rcases family_descends (prefixWord ++ tailWord_921810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921814 : List Nat := [5, 2, 1, 2, 1, 2, 2, 3, 5]
def baseStart_921814 : Nat := 118140960795 + 921814 * 2 ^ 59
def prefixEnd_921814 : Nat := 4983230072969 + 3 ^ 40 * 921814 * 2
def baseEnd_921814 : Nat := 52592628449306848020629

theorem tailTrace_921814 : CollatzResearch.WordTrace tailWord_921814 prefixEnd_921814 52592628449306848020629 := by
  unfold tailWord_921814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2101332417652049133900281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22414212454955190761602997 2101332417652049133900281)
  ·
    refine ⟨1575999313239036850425211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2101332417652049133900281 1575999313239036850425211)
    ·
      refine ⟨2363998969858555275637817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1575999313239036850425211 2363998969858555275637817)
      ·
        refine ⟨1772999227393916456728363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2363998969858555275637817 1772999227393916456728363)
        ·
          refine ⟨2659498841090874685092545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1772999227393916456728363 2659498841090874685092545)
          ·
            refine ⟨1994624130818156013819409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2659498841090874685092545 1994624130818156013819409)
            ·
              refine ⟨1495968098113617010364557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1994624130818156013819409 1495968098113617010364557)
              ·
                refine ⟨560988036792606378886709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1495968098113617010364557 560988036792606378886709)
                ·
                  refine ⟨52592628449306848020629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 560988036792606378886709 52592628449306848020629)
                  ·
                    rfl

theorem cell23_921814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_921814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921814 prefixEnd_921814 := by exact prefixLift 921814
  have htrace : WordTrace (prefixWord ++ tailWord_921814) baseStart_921814 baseEnd_921814 := by
    simpa [prefixWord, tailWord_921814, baseEnd_921814] using wordTrace_append hprefix tailTrace_921814
  have hstable : (prefixWord ++ tailWord_921814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921814).length < 2 ^ (prefixWord ++ tailWord_921814).sum := by decide
  have hdescent : baseEnd_921814 < baseStart_921814 := by decide
  rcases family_descends (prefixWord ++ tailWord_921814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921823 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 7, 4]
def baseStart_921823 : Nat := 118140960795 + 921823 * 2 ^ 59
def prefixEnd_921823 : Nat := 4983230072969 + 3 ^ 40 * 921823 * 2
def baseEnd_921823 : Nat := 157779425789884032324373

theorem tailTrace_921823 : CollatzResearch.WordTrace tailWord_921823 prefixEnd_921823 157779425789884032324373 := by
  unfold tailWord_921823
  simp only [CollatzResearch.WordTrace]
  refine ⟨33621646939400180679482123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22414431292933453786321415 33621646939400180679482123)
  ·
    refine ⟨50432470409100271019223185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33621646939400180679482123 50432470409100271019223185)
    ·
      refine ⟨37824352806825203264417389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50432470409100271019223185 37824352806825203264417389)
      ·
        refine ⟨14184132302559451224156521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37824352806825203264417389 14184132302559451224156521)
        ·
          refine ⟨10638099226919588418117391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14184132302559451224156521 10638099226919588418117391)
          ·
            refine ⟨15957148840379382627176087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10638099226919588418117391 15957148840379382627176087)
            ·
              refine ⟨23935723260569073940764131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15957148840379382627176087 23935723260569073940764131)
              ·
                refine ⟨35903584890853610911146197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23935723260569073940764131 35903584890853610911146197)
                ·
                  refine ⟨841490270879381505729989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 35903584890853610911146197 841490270879381505729989)
                  ·
                    refine ⟨157779425789884032324373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 841490270879381505729989 157779425789884032324373)
                    ·
                      rfl

theorem cell23_921823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 7, 4].length) (baseStart_921823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921823 prefixEnd_921823 := by exact prefixLift 921823
  have htrace : WordTrace (prefixWord ++ tailWord_921823) baseStart_921823 baseEnd_921823 := by
    simpa [prefixWord, tailWord_921823, baseEnd_921823] using wordTrace_append hprefix tailTrace_921823
  have hstable : (prefixWord ++ tailWord_921823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921823).length < 2 ^ (prefixWord ++ tailWord_921823).sum := by decide
  have hdescent : baseEnd_921823 < baseStart_921823 := by decide
  rcases family_descends (prefixWord ++ tailWord_921823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921853 : List Nat := [1, 4, 1, 1, 1, 1, 1, 7, 6]
def baseStart_921853 : Nat := 118140960795 + 921853 * 2 ^ 59
def prefixEnd_921853 : Nat := 4983230072969 + 3 ^ 40 * 921853 * 2
def baseEnd_921853 : Nat := 52594853532142997733109

theorem tailTrace_921853 : CollatzResearch.WordTrace tailWord_921853 prefixEnd_921853 52594853532142997733109 := by
  unfold tailWord_921853
  simp only [CollatzResearch.WordTrace]
  refine ⟨33622741129291495803074213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22415160752860997202049475 33622741129291495803074213)
  ·
    refine ⟨6304263961742155463076415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33622741129291495803074213 6304263961742155463076415)
    ·
      refine ⟨9456395942613233194614623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6304263961742155463076415 9456395942613233194614623)
      ·
        refine ⟨14184593913919849791921935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9456395942613233194614623 14184593913919849791921935)
        ·
          refine ⟨21276890870879774687882903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14184593913919849791921935 21276890870879774687882903)
          ·
            refine ⟨31915336306319662031824355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21276890870879774687882903 31915336306319662031824355)
            ·
              refine ⟨47873004459479493047736533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31915336306319662031824355 47873004459479493047736533)
              ·
                refine ⟨1122023542019050618306325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 47873004459479493047736533 1122023542019050618306325)
                ·
                  refine ⟨52594853532142997733109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1122023542019050618306325 52594853532142997733109)
                  ·
                    rfl

theorem cell23_921853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 6].length) (baseStart_921853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921853 prefixEnd_921853 := by exact prefixLift 921853
  have htrace : WordTrace (prefixWord ++ tailWord_921853) baseStart_921853 baseEnd_921853 := by
    simpa [prefixWord, tailWord_921853, baseEnd_921853] using wordTrace_append hprefix tailTrace_921853
  have hstable : (prefixWord ++ tailWord_921853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921853).length < 2 ^ (prefixWord ++ tailWord_921853).sum := by decide
  have hdescent : baseEnd_921853 < baseStart_921853 := by decide
  rcases family_descends (prefixWord ++ tailWord_921853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921920 : List Nat := [2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 4]
def baseStart_921920 : Nat := 118140960795 + 921920 * 2 ^ 59
def prefixEnd_921920 : Nat := 4983230072969 + 3 ^ 40 * 921920 * 2
def baseEnd_921920 : Nat := 473388084993138217460173

theorem tailTrace_921920 : CollatzResearch.WordTrace tailWord_921920 prefixEnd_921920 473388084993138217460173 := by
  unfold tailWord_921920
  simp only [CollatzResearch.WordTrace]
  refine ⟨16812592410024383122881607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22416789880032510830508809 16812592410024383122881607)
  ·
    refine ⟨25218888615036574684322411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16812592410024383122881607 25218888615036574684322411)
    ·
      refine ⟨37828332922554862026483617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25218888615036574684322411 37828332922554862026483617)
      ·
        refine ⟨28371249691916146519862713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37828332922554862026483617 28371249691916146519862713)
        ·
          refine ⟨21278437268937109889897035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28371249691916146519862713 21278437268937109889897035)
          ·
            refine ⟨31917655903405664834845553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21278437268937109889897035 31917655903405664834845553)
            ·
              refine ⟨23938241927554248626134165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31917655903405664834845553 23938241927554248626134165)
              ·
                refine ⟨1122105090354105404350039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23938241927554248626134165 1122105090354105404350039)
                ·
                  refine ⟨1683157635531158106525059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1122105090354105404350039 1683157635531158106525059)
                  ·
                    refine ⟨2524736453296737159787589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1683157635531158106525059 2524736453296737159787589)
                    ·
                      refine ⟨473388084993138217460173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2524736453296737159787589 473388084993138217460173)
                      ·
                        rfl

theorem cell23_921920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 4].length) (baseStart_921920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921920 prefixEnd_921920 := by exact prefixLift 921920
  have htrace : WordTrace (prefixWord ++ tailWord_921920) baseStart_921920 baseEnd_921920 := by
    simpa [prefixWord, tailWord_921920, baseEnd_921920] using wordTrace_append hprefix tailTrace_921920
  have hstable : (prefixWord ++ tailWord_921920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921920).length < 2 ^ (prefixWord ++ tailWord_921920).sum := by decide
  have hdescent : baseEnd_921920 < baseStart_921920 := by decide
  rcases family_descends (prefixWord ++ tailWord_921920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921923 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 5]
def baseStart_921923 : Nat := 118140960795 + 921923 * 2 ^ 59
def prefixEnd_921923 : Nat := 4983230072969 + 3 ^ 40 * 921923 * 2
def baseEnd_921923 : Nat := 473389625435101705722659

theorem tailTrace_921923 : CollatzResearch.WordTrace tailWord_921923 prefixEnd_921923 473389625435101705722659 := by
  unfold tailWord_921923
  simp only [CollatzResearch.WordTrace]
  refine ⟨33625294239037897758122423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22416862826025265172081615 33625294239037897758122423)
  ·
    refine ⟨50437941358556846637183635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33625294239037897758122423 50437941358556846637183635)
    ·
      refine ⟨75656912037835269955775453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50437941358556846637183635 75656912037835269955775453)
      ·
        refine ⟨28371342014188226233415795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75656912037835269955775453 28371342014188226233415795)
        ·
          refine ⟨42557013021282339350123693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28371342014188226233415795 42557013021282339350123693)
          ·
            refine ⟨15958879882980877256296385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42557013021282339350123693 15958879882980877256296385)
            ·
              refine ⟨11969159912235657942222289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15958879882980877256296385 11969159912235657942222289)
              ·
                refine ⟨8976869934176743456666717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11969159912235657942222289 8976869934176743456666717)
                ·
                  refine ⟨3366326225316278796250019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8976869934176743456666717 3366326225316278796250019)
                  ·
                    refine ⟨5049489337974418194375029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3366326225316278796250019 5049489337974418194375029)
                    ·
                      refine ⟨473389625435101705722659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5049489337974418194375029 473389625435101705722659)
                      ·
                        rfl

theorem cell23_921923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_921923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921923 prefixEnd_921923 := by exact prefixLift 921923
  have htrace : WordTrace (prefixWord ++ tailWord_921923) baseStart_921923 baseEnd_921923 := by
    simpa [prefixWord, tailWord_921923, baseEnd_921923] using wordTrace_append hprefix tailTrace_921923
  have hstable : (prefixWord ++ tailWord_921923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921923).length < 2 ^ (prefixWord ++ tailWord_921923).sum := by decide
  have hdescent : baseEnd_921923 < baseStart_921923 := by decide
  rcases family_descends (prefixWord ++ tailWord_921923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921948 : List Nat := [2, 2, 4, 3, 1, 1, 1, 4, 1, 1, 3]
def baseStart_921948 : Nat := 118140960795 + 921948 * 2 ^ 59
def prefixEnd_921948 : Nat := 4983230072969 + 3 ^ 40 * 921948 * 2
def baseEnd_921948 : Nat := 473402462451464107910045

theorem tailTrace_921948 : CollatzResearch.WordTrace tailWord_921948 prefixEnd_921948 473402462451464107910045 := by
  unfold tailWord_921948
  simp only [CollatzResearch.WordTrace]
  refine ⟨16813103031973663513891249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22417470709298218018521665 16813103031973663513891249)
  ·
    refine ⟨12609827273980247635418437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16813103031973663513891249 12609827273980247635418437)
    ·
      refine ⟨2364342613871296431640957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12609827273980247635418437 2364342613871296431640957)
      ·
        refine ⟨886628480201736161865359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2364342613871296431640957 886628480201736161865359)
        ·
          refine ⟨1329942720302604242798039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 886628480201736161865359 1329942720302604242798039)
          ·
            refine ⟨1994914080453906364197059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1329942720302604242798039 1994914080453906364197059)
            ·
              refine ⟨2992371120680859546295589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1994914080453906364197059 2992371120680859546295589)
              ·
                refine ⟨561069585127661164930423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2992371120680859546295589 561069585127661164930423)
                ·
                  refine ⟨841604377691491747395635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 561069585127661164930423 841604377691491747395635)
                  ·
                    refine ⟨1262406566537237621093453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 841604377691491747395635 1262406566537237621093453)
                    ·
                      refine ⟨473402462451464107910045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1262406566537237621093453 473402462451464107910045)
                      ·
                        rfl

theorem cell23_921948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_921948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921948 prefixEnd_921948 := by exact prefixLift 921948
  have htrace : WordTrace (prefixWord ++ tailWord_921948) baseStart_921948 baseEnd_921948 := by
    simpa [prefixWord, tailWord_921948, baseEnd_921948] using wordTrace_append hprefix tailTrace_921948
  have hstable : (prefixWord ++ tailWord_921948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921948).length < 2 ^ (prefixWord ++ tailWord_921948).sum := by decide
  have hdescent : baseEnd_921948 < baseStart_921948 := by decide
  rcases family_descends (prefixWord ++ tailWord_921948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921960 : List Nat := [2, 1, 4, 2, 2, 1, 3, 8]
def baseStart_921960 : Nat := 118140960795 + 921960 * 2 ^ 59
def prefixEnd_921960 : Nat := 4983230072969 + 3 ^ 40 * 921960 * 2
def baseEnd_921960 : Nat := 17533652748863631887407

theorem tailTrace_921960 : CollatzResearch.WordTrace tailWord_921960 prefixEnd_921960 17533652748863631887407 := by
  unfold tailWord_921960
  simp only [CollatzResearch.WordTrace]
  refine ⟨16813321869951926538609667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22417762493269235384812889 16813321869951926538609667)
  ·
    refine ⟨25219982804927889807914501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16813321869951926538609667 25219982804927889807914501)
    ·
      refine ⟨4728746775923979338983969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25219982804927889807914501 4728746775923979338983969)
      ·
        refine ⟨3546560081942984504237977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4728746775923979338983969 3546560081942984504237977)
        ·
          refine ⟨2659920061457238378178483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3546560081942984504237977 2659920061457238378178483)
          ·
            refine ⟨3989880092185857567267725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2659920061457238378178483 3989880092185857567267725)
            ·
              refine ⟨1496205034569696587725397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3989880092185857567267725 1496205034569696587725397)
              ·
                refine ⟨17533652748863631887407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1496205034569696587725397 17533652748863631887407)
                ·
                  rfl

theorem cell23_921960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 8].length) (baseStart_921960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921960 prefixEnd_921960 := by exact prefixLift 921960
  have htrace : WordTrace (prefixWord ++ tailWord_921960) baseStart_921960 baseEnd_921960 := by
    simpa [prefixWord, tailWord_921960, baseEnd_921960] using wordTrace_append hprefix tailTrace_921960
  have hstable : (prefixWord ++ tailWord_921960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921960).length < 2 ^ (prefixWord ++ tailWord_921960).sum := by decide
  have hdescent : baseEnd_921960 < baseStart_921960 := by decide
  rcases family_descends (prefixWord ++ tailWord_921960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921983 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 5]
def baseStart_921983 : Nat := 118140960795 + 921983 * 2 ^ 59
def prefixEnd_921983 : Nat := 4983230072969 + 3 ^ 40 * 921983 * 2
def baseEnd_921983 : Nat := 473420434274371470972383

theorem tailTrace_921983 : CollatzResearch.WordTrace tailWord_921983 prefixEnd_921983 473420434274371470972383 := by
  unfold tailWord_921983
  simp only [CollatzResearch.WordTrace]
  refine ⟨33627482618820528005306603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22418321745880352003537735 33627482618820528005306603)
  ·
    refine ⟨50441223928230792007959905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33627482618820528005306603 50441223928230792007959905)
    ·
      refine ⟨37830917946173094005969929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50441223928230792007959905 37830917946173094005969929)
      ·
        refine ⟨28373188459629820504477447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37830917946173094005969929 28373188459629820504477447)
        ·
          refine ⟨42559782689444730756716171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28373188459629820504477447 42559782689444730756716171)
          ·
            refine ⟨63839674034167096135074257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42559782689444730756716171 63839674034167096135074257)
            ·
              refine ⟨47879755525625322101305693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63839674034167096135074257 47879755525625322101305693)
              ·
                refine ⟨17954908322109495787989635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47879755525625322101305693 17954908322109495787989635)
                ·
                  refine ⟨26932362483164243681984453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17954908322109495787989635 26932362483164243681984453)
                  ·
                    refine ⟨5049817965593295690372085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26932362483164243681984453 5049817965593295690372085)
                    ·
                      refine ⟨473420434274371470972383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5049817965593295690372085 473420434274371470972383)
                      ·
                        rfl

theorem cell23_921983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_921983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_921983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_921983 prefixEnd_921983 := by exact prefixLift 921983
  have htrace : WordTrace (prefixWord ++ tailWord_921983) baseStart_921983 baseEnd_921983 := by
    simpa [prefixWord, tailWord_921983, baseEnd_921983] using wordTrace_append hprefix tailTrace_921983
  have hstable : (prefixWord ++ tailWord_921983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921983).length < 2 ^ (prefixWord ++ tailWord_921983).sum := by decide
  have hdescent : baseEnd_921983 < baseStart_921983 := by decide
  rcases family_descends (prefixWord ++ tailWord_921983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922020 : List Nat := [2, 3, 1, 2, 1, 1, 4, 1, 2, 6]
def baseStart_922020 : Nat := 118140960795 + 922020 * 2 ^ 59
def prefixEnd_922020 : Nat := 4983230072969 + 3 ^ 40 * 922020 * 2
def baseEnd_922020 : Nat := 157813144352862608736571

theorem tailTrace_922020 : CollatzResearch.WordTrace tailWord_922020 prefixEnd_922020 157813144352862608736571 := by
  unfold tailWord_922020
  simp only [CollatzResearch.WordTrace]
  refine ⟨16814416059843241662201757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22419221413124322216269009 16814416059843241662201757)
  ·
    refine ⟨6305406022441215623325659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16814416059843241662201757 6305406022441215623325659)
    ·
      refine ⟨9458109033661823434988489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6305406022441215623325659 9458109033661823434988489)
      ·
        refine ⟨7093581775246367576241367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9458109033661823434988489 7093581775246367576241367)
        ·
          refine ⟨10640372662869551364362051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7093581775246367576241367 10640372662869551364362051)
          ·
            refine ⟨15960558994304327046543077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10640372662869551364362051 15960558994304327046543077)
            ·
              refine ⟨2992604811432061321226827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15960558994304327046543077 2992604811432061321226827)
              ·
                refine ⟨4488907217148091981840241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2992604811432061321226827 4488907217148091981840241)
                ·
                  refine ⟨3366680412861068986380181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4488907217148091981840241 3366680412861068986380181)
                  ·
                    refine ⟨157813144352862608736571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3366680412861068986380181 157813144352862608736571)
                    ·
                      rfl

theorem cell23_922020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_922020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922020 prefixEnd_922020 := by exact prefixLift 922020
  have htrace : WordTrace (prefixWord ++ tailWord_922020) baseStart_922020 baseEnd_922020 := by
    simpa [prefixWord, tailWord_922020, baseEnd_922020] using wordTrace_append hprefix tailTrace_922020
  have hstable : (prefixWord ++ tailWord_922020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922020).length < 2 ^ (prefixWord ++ tailWord_922020).sum := by decide
  have hdescent : baseEnd_922020 < baseStart_922020 := by decide
  rcases family_descends (prefixWord ++ tailWord_922020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922077 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 1, 5, 3]
def baseStart_922077 : Nat := 118140960795 + 922077 * 2 ^ 59
def prefixEnd_922077 : Nat := 4983230072969 + 3 ^ 40 * 922077 * 2
def baseEnd_922077 : Nat := 473468701455894103196951

theorem tailTrace_922077 : CollatzResearch.WordTrace tailWord_922077 prefixEnd_922077 473468701455894103196951 := by
  unfold tailWord_922077
  simp only [CollatzResearch.WordTrace]
  refine ⟨33630911080479982059228485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22420607386986654706152323 33630911080479982059228485)
  ·
    refine ⟨6305795827589996636105341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33630911080479982059228485 6305795827589996636105341)
    ·
      refine ⟨2364673435346248738539503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6305795827589996636105341 2364673435346248738539503)
      ·
        refine ⟨3547010153019373107809255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2364673435346248738539503 3547010153019373107809255)
        ·
          refine ⟨5320515229529059661713883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3547010153019373107809255 5320515229529059661713883)
          ·
            refine ⟨7980772844293589492570825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5320515229529059661713883 7980772844293589492570825)
            ·
              refine ⟨5985579633220192119428119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7980772844293589492570825 5985579633220192119428119)
              ·
                refine ⟨8978369449830288179142179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5985579633220192119428119 8978369449830288179142179)
                ·
                  refine ⟨13467554174745432268713269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8978369449830288179142179 13467554174745432268713269)
                  ·
                    refine ⟨1262583203882384275191869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13467554174745432268713269 1262583203882384275191869)
                    ·
                      refine ⟨473468701455894103196951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1262583203882384275191869 473468701455894103196951)
                      ·
                        rfl

theorem cell23_922077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_922077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922077 prefixEnd_922077 := by exact prefixLift 922077
  have htrace : WordTrace (prefixWord ++ tailWord_922077) baseStart_922077 baseEnd_922077 := by
    simpa [prefixWord, tailWord_922077, baseEnd_922077] using wordTrace_append hprefix tailTrace_922077
  have hstable : (prefixWord ++ tailWord_922077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922077).length < 2 ^ (prefixWord ++ tailWord_922077).sum := by decide
  have hdescent : baseEnd_922077 < baseStart_922077 := by decide
  rcases family_descends (prefixWord ++ tailWord_922077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922080 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 4, 5]
def baseStart_922080 : Nat := 118140960795 + 922080 * 2 ^ 59
def prefixEnd_922080 : Nat := 4983230072969 + 3 ^ 40 * 922080 * 2
def baseEnd_922080 : Nat := 157823413965952530486479

theorem tailTrace_922080 : CollatzResearch.WordTrace tailWord_922080 prefixEnd_922080 157823413965952530486479 := by
  unfold tailWord_922080
  simp only [CollatzResearch.WordTrace]
  refine ⟨16815510249734556785793847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22420680332979409047725129 16815510249734556785793847)
  ·
    refine ⟨25223265374601835178690771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16815510249734556785793847 25223265374601835178690771)
    ·
      refine ⟨37834898061902752768036157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25223265374601835178690771 37834898061902752768036157)
      ·
        refine ⟨14188086773213532288013559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37834898061902752768036157 14188086773213532288013559)
        ·
          refine ⟨21282130159820298432020339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14188086773213532288013559 21282130159820298432020339)
          ·
            refine ⟨31923195239730447648030509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21282130159820298432020339 31923195239730447648030509)
            ·
              refine ⟨11971198214898917868011441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31923195239730447648030509 11971198214898917868011441)
              ·
                refine ⟨8978398661174188401008581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11971198214898917868011441 8978398661174188401008581)
                ·
                  refine ⟨1683449748970160325189109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8978398661174188401008581 1683449748970160325189109)
                  ·
                    refine ⟨157823413965952530486479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1683449748970160325189109 157823413965952530486479)
                    ·
                      rfl

theorem cell23_922080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 4, 5].length) (baseStart_922080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922080 prefixEnd_922080 := by exact prefixLift 922080
  have htrace : WordTrace (prefixWord ++ tailWord_922080) baseStart_922080 baseEnd_922080 := by
    simpa [prefixWord, tailWord_922080, baseEnd_922080] using wordTrace_append hprefix tailTrace_922080
  have hstable : (prefixWord ++ tailWord_922080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922080).length < 2 ^ (prefixWord ++ tailWord_922080).sum := by decide
  have hdescent : baseEnd_922080 < baseStart_922080 := by decide
  rcases family_descends (prefixWord ++ tailWord_922080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922082 : List Nat := [3, 3, 3, 2, 2, 1, 1, 2, 1, 3, 2]
def baseStart_922082 : Nat := 118140960795 + 922082 * 2 ^ 59
def prefixEnd_922082 : Nat := 4983230072969 + 3 ^ 40 * 922082 * 2
def baseEnd_922082 : Nat := 473471268859166583634429

theorem tailTrace_922082 : CollatzResearch.WordTrace tailWord_922082 prefixEnd_922082 473471268859166583634429 := by
  unfold tailWord_922082
  simp only [CollatzResearch.WordTrace]
  refine ⟨8407773361365466978290125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22420728963641245275440333 8407773361365466978290125)
  ·
    refine ⟨3152915010512050116858797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8407773361365466978290125 3152915010512050116858797)
    ·
      refine ⟨1182343128942018793822049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3152915010512050116858797 1182343128942018793822049)
      ·
        refine ⟨886757346706514095366537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1182343128942018793822049 886757346706514095366537)
        ·
          refine ⟨665068010029885571524903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 886757346706514095366537 665068010029885571524903)
          ·
            refine ⟨997602015044828357287355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665068010029885571524903 997602015044828357287355)
            ·
              refine ⟨1496403022567242535931033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 997602015044828357287355 1496403022567242535931033)
              ·
                refine ⟨1122302266925431901948275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1496403022567242535931033 1122302266925431901948275)
                ·
                  refine ⟨1683453400388147852922413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1122302266925431901948275 1683453400388147852922413)
                  ·
                    refine ⟨631295025145555444845905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1683453400388147852922413 631295025145555444845905)
                    ·
                      refine ⟨473471268859166583634429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 631295025145555444845905 473471268859166583634429)
                      ·
                        rfl

theorem cell23_922082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_922082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922082 prefixEnd_922082 := by exact prefixLift 922082
  have htrace : WordTrace (prefixWord ++ tailWord_922082) baseStart_922082 baseEnd_922082 := by
    simpa [prefixWord, tailWord_922082, baseEnd_922082] using wordTrace_append hprefix tailTrace_922082
  have hstable : (prefixWord ++ tailWord_922082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922082).length < 2 ^ (prefixWord ++ tailWord_922082).sum := by decide
  have hdescent : baseEnd_922082 < baseStart_922082 := by decide
  rcases family_descends (prefixWord ++ tailWord_922082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922097 : List Nat := [1, 2, 2, 2, 3, 1, 4, 1, 2, 5]
def baseStart_922097 : Nat := 118140960795 + 922097 * 2 ^ 59
def prefixEnd_922097 : Nat := 4983230072969 + 3 ^ 40 * 922097 * 2
def baseEnd_922097 : Nat := 157826323689661341648953

theorem tailTrace_922097 : CollatzResearch.WordTrace tailWord_922097 prefixEnd_922097 157826323689661341648953 := by
  unfold tailWord_922097
  simp only [CollatzResearch.WordTrace]
  refine ⟨33631640540407525474956545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22421093693605016983304363 33631640540407525474956545)
  ·
    refine ⟨25223730405305644106217409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33631640540407525474956545 25223730405305644106217409)
    ·
      refine ⟨18917797803979233079663057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25223730405305644106217409 18917797803979233079663057)
      ·
        refine ⟨14188348352984424809747293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18917797803979233079663057 14188348352984424809747293)
        ·
          refine ⟨5320630632369159303655235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14188348352984424809747293 5320630632369159303655235)
          ·
            refine ⟨7980945948553738955482853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5320630632369159303655235 7980945948553738955482853)
            ·
              refine ⟨1496427365353826054153035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7980945948553738955482853 1496427365353826054153035)
              ·
                refine ⟨2244641048030739081229553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1496427365353826054153035 2244641048030739081229553)
                ·
                  refine ⟨1683480786023054310922165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2244641048030739081229553 1683480786023054310922165)
                  ·
                    refine ⟨157826323689661341648953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1683480786023054310922165 157826323689661341648953)
                    ·
                      rfl

theorem cell23_922097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 5].length) (baseStart_922097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922097 prefixEnd_922097 := by exact prefixLift 922097
  have htrace : WordTrace (prefixWord ++ tailWord_922097) baseStart_922097 baseEnd_922097 := by
    simpa [prefixWord, tailWord_922097, baseEnd_922097] using wordTrace_append hprefix tailTrace_922097
  have hstable : (prefixWord ++ tailWord_922097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922097).length < 2 ^ (prefixWord ++ tailWord_922097).sum := by decide
  have hdescent : baseEnd_922097 < baseStart_922097 := by decide
  rcases family_descends (prefixWord ++ tailWord_922097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922117 : List Nat := [1, 3, 1, 1, 2, 2, 4, 2, 2, 1, 4]
def baseStart_922117 : Nat := 118140960795 + 922117 * 2 ^ 59
def prefixEnd_922117 : Nat := 4983230072969 + 3 ^ 40 * 922117 * 2
def baseEnd_922117 : Nat := 473489240682073946696767

theorem tailTrace_922117 : CollatzResearch.WordTrace tailWord_922117 prefixEnd_922117 473489240682073946696767 := by
  unfold tailWord_922117
  simp only [CollatzResearch.WordTrace]
  refine ⟨33632370000335068890684605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22421580000223379260456403 33632370000335068890684605)
  ·
    refine ⟨12612138750125650834006727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33632370000335068890684605 12612138750125650834006727)
    ·
      refine ⟨18918208125188476251010091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12612138750125650834006727 18918208125188476251010091)
      ·
        refine ⟨28377312187782714376515137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18918208125188476251010091 28377312187782714376515137)
        ·
          refine ⟨21282984140837035782386353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28377312187782714376515137 21282984140837035782386353)
          ·
            refine ⟨15962238105627776836789765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21282984140837035782386353 15962238105627776836789765)
            ·
              refine ⟨2992919644805208156898081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15962238105627776836789765 2992919644805208156898081)
              ·
                refine ⟨2244689733603906117673561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2992919644805208156898081 2244689733603906117673561)
                ·
                  refine ⟨1683517300202929588255171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2244689733603906117673561 1683517300202929588255171)
                  ·
                    refine ⟨2525275950304394382382757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1683517300202929588255171 2525275950304394382382757)
                    ·
                      refine ⟨473489240682073946696767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2525275950304394382382757 473489240682073946696767)
                      ·
                        rfl

theorem cell23_922117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 1, 4].length) (baseStart_922117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922117 prefixEnd_922117 := by exact prefixLift 922117
  have htrace : WordTrace (prefixWord ++ tailWord_922117) baseStart_922117 baseEnd_922117 := by
    simpa [prefixWord, tailWord_922117, baseEnd_922117] using wordTrace_append hprefix tailTrace_922117
  have hstable : (prefixWord ++ tailWord_922117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922117).length < 2 ^ (prefixWord ++ tailWord_922117).sum := by decide
  have hdescent : baseEnd_922117 < baseStart_922117 := by decide
  rcases family_descends (prefixWord ++ tailWord_922117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922120 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 1, 5, 5]
def baseStart_922120 : Nat := 118140960795 + 922120 * 2 ^ 59
def prefixEnd_922120 : Nat := 4983230072969 + 3 ^ 40 * 922120 * 2
def baseEnd_922120 : Nat := 473490781124037434959253

theorem tailTrace_922120 : CollatzResearch.WordTrace tailWord_922120 prefixEnd_922120 473490781124037434959253 := by
  unfold tailWord_922120
  simp only [CollatzResearch.WordTrace]
  refine ⟨16816239709662100201521907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22421652946216133602029209 16816239709662100201521907)
  ·
    refine ⟨25224359564493150302282861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16816239709662100201521907 25224359564493150302282861)
    ·
      refine ⟨9459134836684931363356073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25224359564493150302282861 9459134836684931363356073)
      ·
        refine ⟨7094351127513698522517055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9459134836684931363356073 7094351127513698522517055)
        ·
          refine ⟨10641526691270547783775583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7094351127513698522517055 10641526691270547783775583)
          ·
            refine ⟨15962290036905821675663375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10641526691270547783775583 15962290036905821675663375)
            ·
              refine ⟨23943435055358732513495063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15962290036905821675663375 23943435055358732513495063)
              ·
                refine ⟨35915152583038098770242595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23943435055358732513495063 35915152583038098770242595)
                ·
                  refine ⟨53872728874557148155363893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35915152583038098770242595 53872728874557148155363893)
                  ·
                    refine ⟨5050568331989732639565365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53872728874557148155363893 5050568331989732639565365)
                    ·
                      refine ⟨473490781124037434959253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5050568331989732639565365 473490781124037434959253)
                      ·
                        rfl

theorem cell23_922120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_922120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922120 prefixEnd_922120 := by exact prefixLift 922120
  have htrace : WordTrace (prefixWord ++ tailWord_922120) baseStart_922120 baseEnd_922120 := by
    simpa [prefixWord, tailWord_922120, baseEnd_922120] using wordTrace_append hprefix tailTrace_922120
  have hstable : (prefixWord ++ tailWord_922120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922120).length < 2 ^ (prefixWord ++ tailWord_922120).sum := by decide
  have hdescent : baseEnd_922120 < baseStart_922120 := by decide
  rcases family_descends (prefixWord ++ tailWord_922120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922148 : List Nat := [2, 3, 1, 5, 2, 1, 1, 1, 2, 5]
def baseStart_922148 : Nat := 118140960795 + 922148 * 2 ^ 59
def prefixEnd_922148 : Nat := 4983230072969 + 3 ^ 40 * 922148 * 2
def baseEnd_922148 : Nat := 157835052860787775136375

theorem tailTrace_922148 : CollatzResearch.WordTrace tailWord_922148 prefixEnd_922148 157835052860787775136375 := by
  unfold tailWord_922148
  simp only [CollatzResearch.WordTrace]
  refine ⟨16816750331611380592531549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22422333775481840790042065 16816750331611380592531549)
  ·
    refine ⟨6306281374354267722199331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16816750331611380592531549 6306281374354267722199331)
    ·
      refine ⟨9459422061531401583298997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6306281374354267722199331 9459422061531401583298997)
      ·
        refine ⟨886820818268568898434281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9459422061531401583298997 886820818268568898434281)
        ·
          refine ⟨665115613701426673825711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 886820818268568898434281 665115613701426673825711)
          ·
            refine ⟨997673420552140010738567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665115613701426673825711 997673420552140010738567)
            ·
              refine ⟨1496510130828210016107851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 997673420552140010738567 1496510130828210016107851)
              ·
                refine ⟨2244765196242315024161777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1496510130828210016107851 2244765196242315024161777)
                ·
                  refine ⟨1683573897181736268121333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2244765196242315024161777 1683573897181736268121333)
                  ·
                    refine ⟨157835052860787775136375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1683573897181736268121333 157835052860787775136375)
                    ·
                      rfl

theorem cell23_922148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 2, 5].length) (baseStart_922148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922148 prefixEnd_922148 := by exact prefixLift 922148
  have htrace : WordTrace (prefixWord ++ tailWord_922148) baseStart_922148 baseEnd_922148 := by
    simpa [prefixWord, tailWord_922148, baseEnd_922148] using wordTrace_append hprefix tailTrace_922148
  have hstable : (prefixWord ++ tailWord_922148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922148).length < 2 ^ (prefixWord ++ tailWord_922148).sum := by decide
  have hdescent : baseEnd_922148 < baseStart_922148 := by decide
  rcases family_descends (prefixWord ++ tailWord_922148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922151 : List Nat := [1, 1, 7, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_922151 : Nat := 118140960795 + 922151 * 2 ^ 59
def prefixEnd_922151 : Nat := 4983230072969 + 3 ^ 40 * 922151 * 2
def baseEnd_922151 : Nat := 473506699024326813671611

theorem tailTrace_922151 : CollatzResearch.WordTrace tailWord_922151 prefixEnd_922151 473506699024326813671611 := by
  unfold tailWord_922151
  simp only [CollatzResearch.WordTrace]
  refine ⟨33633610082211892697422307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22422406721474595131614871 33633610082211892697422307)
  ·
    refine ⟨50450415123317839046133461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33633610082211892697422307 50450415123317839046133461)
    ·
      refine ⟨1182431604452761852643753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 50450415123317839046133461 1182431604452761852643753)
      ·
        refine ⟨886823703339571389482815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1182431604452761852643753 886823703339571389482815)
        ·
          refine ⟨1330235555009357084224223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 886823703339571389482815 1330235555009357084224223)
          ·
            refine ⟨1995353332514035626336335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1330235555009357084224223 1995353332514035626336335)
            ·
              refine ⟨2993029998771053439504503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1995353332514035626336335 2993029998771053439504503)
              ·
                refine ⟨4489544998156580159256755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2993029998771053439504503 4489544998156580159256755)
                ·
                  refine ⟨6734317497234870238885133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4489544998156580159256755 6734317497234870238885133)
                  ·
                    refine ⟨2525369061463076339581925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6734317497234870238885133 2525369061463076339581925)
                    ·
                      refine ⟨473506699024326813671611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2525369061463076339581925 473506699024326813671611)
                      ·
                        rfl

theorem cell23_922151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_922151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922151 prefixEnd_922151 := by exact prefixLift 922151
  have htrace : WordTrace (prefixWord ++ tailWord_922151) baseStart_922151 baseEnd_922151 := by
    simpa [prefixWord, tailWord_922151, baseEnd_922151] using wordTrace_append hprefix tailTrace_922151
  have hstable : (prefixWord ++ tailWord_922151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922151).length < 2 ^ (prefixWord ++ tailWord_922151).sum := by decide
  have hdescent : baseEnd_922151 < baseStart_922151 := by decide
  rcases family_descends (prefixWord ++ tailWord_922151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922154 : List Nat := [3, 1, 4, 1, 1, 3, 1, 1, 1, 4, 3]
def baseStart_922154 : Nat := 118140960795 + 922154 * 2 ^ 59
def prefixEnd_922154 : Nat := 4983230072969 + 3 ^ 40 * 922154 * 2
def baseEnd_922154 : Nat := 473508239466290301934097

theorem tailTrace_922154 : CollatzResearch.WordTrace tailWord_922154 prefixEnd_922154 473508239466290301934097 := by
  unfold tailWord_922154
  simp only [CollatzResearch.WordTrace]
  refine ⟨8408429875300256052445379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22422479667467349473187677 8408429875300256052445379)
  ·
    refine ⟨12612644812950384078668069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8408429875300256052445379 12612644812950384078668069)
    ·
      refine ⟨2364870902428197014750263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12612644812950384078668069 2364870902428197014750263)
      ·
        refine ⟨3547306353642295522125395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2364870902428197014750263 3547306353642295522125395)
        ·
          refine ⟨5320959530463443283188093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3547306353642295522125395 5320959530463443283188093)
          ·
            refine ⟨1995359823923791231195535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5320959530463443283188093 1995359823923791231195535)
            ·
              refine ⟨2993039735885686846793303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1995359823923791231195535 2993039735885686846793303)
              ·
                refine ⟨4489559603828530270189955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2993039735885686846793303 4489559603828530270189955)
                ·
                  refine ⟨6734339405742795405284933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4489559603828530270189955 6734339405742795405284933)
                  ·
                    refine ⟨1262688638576774138490925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6734339405742795405284933 1262688638576774138490925)
                    ·
                      refine ⟨473508239466290301934097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1262688638576774138490925 473508239466290301934097)
                      ·
                        rfl

theorem cell23_922154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_922154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922154 prefixEnd_922154 := by exact prefixLift 922154
  have htrace : WordTrace (prefixWord ++ tailWord_922154) baseStart_922154 baseEnd_922154 := by
    simpa [prefixWord, tailWord_922154, baseEnd_922154] using wordTrace_append hprefix tailTrace_922154
  have hstable : (prefixWord ++ tailWord_922154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922154).length < 2 ^ (prefixWord ++ tailWord_922154).sum := by decide
  have hdescent : baseEnd_922154 < baseStart_922154 := by decide
  rcases family_descends (prefixWord ++ tailWord_922154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922177 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_922177 : Nat := 118140960795 + 922177 * 2 ^ 59
def prefixEnd_922177 : Nat := 4983230072969 + 3 ^ 40 * 922177 * 2
def baseEnd_922177 : Nat := 473520049521343711946491

theorem tailTrace_922177 : CollatzResearch.WordTrace tailWord_922177 prefixEnd_922177 473520049521343711946491 := by
  unfold tailWord_922177
  simp only [CollatzResearch.WordTrace]
  refine ⟨33634558380117699137868785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22423038920078466091912523 33634558380117699137868785)
  ·
    refine ⟨25225918785088274353401589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33634558380117699137868785 25225918785088274353401589)
    ·
      refine ⟨2364929886102025720631399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25225918785088274353401589 2364929886102025720631399)
      ·
        refine ⟨3547394829153038580947099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2364929886102025720631399 3547394829153038580947099)
        ·
          refine ⟨5321092243729557871420649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3547394829153038580947099 5321092243729557871420649)
          ·
            refine ⟨3990819182797168403565487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5321092243729557871420649 3990819182797168403565487)
            ·
              refine ⟨5986228774195752605348231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3990819182797168403565487 5986228774195752605348231)
              ·
                refine ⟨8979343161293628908022347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5986228774195752605348231 8979343161293628908022347)
                ·
                  refine ⟨13469014741940443362033521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8979343161293628908022347 13469014741940443362033521)
                  ·
                    refine ⟨10101761056455332521525141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13469014741940443362033521 10101761056455332521525141)
                    ·
                      refine ⟨473520049521343711946491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10101761056455332521525141 473520049521343711946491)
                      ·
                        rfl

theorem cell23_922177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_922177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922177 prefixEnd_922177 := by exact prefixLift 922177
  have htrace : WordTrace (prefixWord ++ tailWord_922177) baseStart_922177 baseEnd_922177 := by
    simpa [prefixWord, tailWord_922177, baseEnd_922177] using wordTrace_append hprefix tailTrace_922177
  have hstable : (prefixWord ++ tailWord_922177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922177).length < 2 ^ (prefixWord ++ tailWord_922177).sum := by decide
  have hdescent : baseEnd_922177 < baseStart_922177 := by decide
  rcases family_descends (prefixWord ++ tailWord_922177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922194 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 3, 5, 2]
def baseStart_922194 : Nat := 118140960795 + 922194 * 2 ^ 59
def prefixEnd_922194 : Nat := 4983230072969 + 3 ^ 40 * 922194 * 2
def baseEnd_922194 : Nat := 473528778692470145433913

theorem tailTrace_922194 : CollatzResearch.WordTrace tailWord_922194 prefixEnd_922194 473528778692470145433913 := by
  unfold tailWord_922194
  simp only [CollatzResearch.WordTrace]
  refine ⟨8408794605264027760309409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22423452280704074027491757 8408794605264027760309409)
  ·
    refine ⟨6306595953948020820232057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8408794605264027760309409 6306595953948020820232057)
    ·
      refine ⟨4729946965461015615174043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6306595953948020820232057 4729946965461015615174043)
      ·
        refine ⟨7094920448191523422761065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4729946965461015615174043 7094920448191523422761065)
        ·
          refine ⟨5321190336143642567070799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7094920448191523422761065 5321190336143642567070799)
          ·
            refine ⟨7981785504215463850606199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5321190336143642567070799 7981785504215463850606199)
            ·
              refine ⟨11972678256323195775909299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7981785504215463850606199 11972678256323195775909299)
              ·
                refine ⟨17959017384484793663863949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11972678256323195775909299 17959017384484793663863949)
                ·
                  refine ⟨6734631519181797623948981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17959017384484793663863949 6734631519181797623948981)
                  ·
                    refine ⟨631371704923293527245217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6734631519181797623948981 631371704923293527245217)
                    ·
                      refine ⟨473528778692470145433913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 631371704923293527245217 473528778692470145433913)
                      ·
                        rfl

theorem cell23_922194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_922194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922194 prefixEnd_922194 := by exact prefixLift 922194
  have htrace : WordTrace (prefixWord ++ tailWord_922194) baseStart_922194 baseEnd_922194 := by
    simpa [prefixWord, tailWord_922194, baseEnd_922194] using wordTrace_append hprefix tailTrace_922194
  have hstable : (prefixWord ++ tailWord_922194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922194).length < 2 ^ (prefixWord ++ tailWord_922194).sum := by decide
  have hdescent : baseEnd_922194 < baseStart_922194 := by decide
  rcases family_descends (prefixWord ++ tailWord_922194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922207 : List Nat := [1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 4]
def baseStart_922207 : Nat := 118140960795 + 922207 * 2 ^ 59
def prefixEnd_922207 : Nat := 4983230072969 + 3 ^ 40 * 922207 * 2
def baseEnd_922207 : Nat := 473535453940978594571353

theorem tailTrace_922207 : CollatzResearch.WordTrace tailWord_922207 prefixEnd_922207 473535453940978594571353 := by
  unfold tailWord_922207
  simp only [CollatzResearch.WordTrace]
  refine ⟨33635652570009014261460875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22423768380006009507640583 33635652570009014261460875)
  ·
    refine ⟨50453478855013521392191313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33635652570009014261460875 50453478855013521392191313)
    ·
      refine ⟨37840109141260141044143485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50453478855013521392191313 37840109141260141044143485)
      ·
        refine ⟨14190040927972552891553807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37840109141260141044143485 14190040927972552891553807)
        ·
          refine ⟨21285061391958829337330711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14190040927972552891553807 21285061391958829337330711)
          ·
            refine ⟨31927592087938244005996067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21285061391958829337330711 31927592087938244005996067)
            ·
              refine ⟨47891388131907366008994101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31927592087938244005996067 47891388131907366008994101)
              ·
                refine ⟨4489817637366315563343197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47891388131907366008994101 4489817637366315563343197)
                ·
                  refine ⟨1683681614012368336253699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4489817637366315563343197 1683681614012368336253699)
                  ·
                    refine ⟨2525522421018552504380549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1683681614012368336253699 2525522421018552504380549)
                    ·
                      refine ⟨473535453940978594571353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2525522421018552504380549 473535453940978594571353)
                      ·
                        rfl

theorem cell23_922207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_922207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_922207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_922207 prefixEnd_922207 := by exact prefixLift 922207
  have htrace : WordTrace (prefixWord ++ tailWord_922207) baseStart_922207 baseEnd_922207 := by
    simpa [prefixWord, tailWord_922207, baseEnd_922207] using wordTrace_append hprefix tailTrace_922207
  have hstable : (prefixWord ++ tailWord_922207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922207).length < 2 ^ (prefixWord ++ tailWord_922207).sum := by decide
  have hdescent : baseEnd_922207 < baseStart_922207 := by decide
  rcases family_descends (prefixWord ++ tailWord_922207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
