import V185TrunkScan23Chunk0635

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3760311 : List Nat := [1, 1, 3, 1, 4, 3, 2, 3, 1, 2, 2]
def baseStart_3760311 : Nat := 118140960795 + 3760311 * 2 ^ 59
def prefixEnd_3760311 : Nat := 4983230072969 + 3 ^ 40 * 3760311 * 2
def baseEnd_3760311 : Nat := 1930846953388942499619151

theorem tailTrace_3760311 : CollatzResearch.WordTrace tailWord_3760311 prefixEnd_3760311 1930846953388942499619151 := by
  unfold tailWord_3760311
  simp only [CollatzResearch.WordTrace]
  refine ⟨137149809480042931834960787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91433206320028621223307191 137149809480042931834960787)
  ·
    refine ⟨205724714220064397752441181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137149809480042931834960787 205724714220064397752441181)
    ·
      refine ⟨77146767832524149157165443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205724714220064397752441181 77146767832524149157165443)
      ·
        refine ⟨115720151748786223735748165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77146767832524149157165443 115720151748786223735748165)
        ·
          refine ⟨21697528452897416950452781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115720151748786223735748165 21697528452897416950452781)
          ·
            refine ⟨8136573169836531356419793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21697528452897416950452781 8136573169836531356419793)
            ·
              refine ⟨6102429877377398517314845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8136573169836531356419793 6102429877377398517314845)
              ·
                refine ⟨2288411204016524443993067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6102429877377398517314845 2288411204016524443993067)
                ·
                  refine ⟨3432616806024786665989601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2288411204016524443993067 3432616806024786665989601)
                  ·
                    refine ⟨2574462604518589999492201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3432616806024786665989601 2574462604518589999492201)
                    ·
                      refine ⟨1930846953388942499619151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2574462604518589999492201 1930846953388942499619151)
                      ·
                        rfl

theorem cell23_3760311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 3, 1, 2, 2].length) (baseStart_3760311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760311 prefixEnd_3760311 := by exact prefixLift 3760311
  have htrace : WordTrace (prefixWord ++ tailWord_3760311) baseStart_3760311 baseEnd_3760311 := by
    simpa [prefixWord, tailWord_3760311, baseEnd_3760311] using wordTrace_append hprefix tailTrace_3760311
  have hstable : (prefixWord ++ tailWord_3760311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760311).length < 2 ^ (prefixWord ++ tailWord_3760311).sum := by decide
  have hdescent : baseEnd_3760311 < baseStart_3760311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760321 : List Nat := [1, 2, 6, 1, 2, 2, 1, 2, 2, 4]
def baseStart_3760321 : Nat := 118140960795 + 3760321 * 2 ^ 59
def prefixEnd_3760321 : Nat := 4983230072969 + 3 ^ 40 * 3760321 * 2
def baseEnd_3760321 : Nat := 643617362731829153498035

theorem tailTrace_3760321 : CollatzResearch.WordTrace tailWord_3760321 prefixEnd_3760321 643617362731829153498035 := by
  unfold tailWord_3760321
  simp only [CollatzResearch.WordTrace]
  refine ⟨137150174210006703542824817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91433449473337802361883211 137150174210006703542824817)
  ·
    refine ⟨102862630657505027657118613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137150174210006703542824817 102862630657505027657118613)
    ·
      refine ⟨4821685812070548171427435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 102862630657505027657118613 4821685812070548171427435)
      ·
        refine ⟨7232528718105822257141153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4821685812070548171427435 7232528718105822257141153)
        ·
          refine ⟨5424396538579366692855865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7232528718105822257141153 5424396538579366692855865)
          ·
            refine ⟨4068297403934525019641899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5424396538579366692855865 4068297403934525019641899)
            ·
              refine ⟨6102446105901787529462849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4068297403934525019641899 6102446105901787529462849)
              ·
                refine ⟨4576834579426340647097137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6102446105901787529462849 4576834579426340647097137)
                ·
                  refine ⟨3432625934569755485322853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4576834579426340647097137 3432625934569755485322853)
                  ·
                    refine ⟨643617362731829153498035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3432625934569755485322853 643617362731829153498035)
                    ·
                      rfl

theorem cell23_3760321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_3760321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760321 prefixEnd_3760321 := by exact prefixLift 3760321
  have htrace : WordTrace (prefixWord ++ tailWord_3760321) baseStart_3760321 baseEnd_3760321 := by
    simpa [prefixWord, tailWord_3760321, baseEnd_3760321] using wordTrace_append hprefix tailTrace_3760321
  have hstable : (prefixWord ++ tailWord_3760321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760321).length < 2 ^ (prefixWord ++ tailWord_3760321).sum := by decide
  have hdescent : baseEnd_3760321 < baseStart_3760321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760370 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 1, 3, 5]
def baseStart_3760370 : Nat := 118140960795 + 3760370 * 2 ^ 59
def prefixEnd_3760370 : Nat := 4983230072969 + 3 ^ 40 * 3760370 * 2
def baseEnd_3760370 : Nat := 1930877248747557768781379

theorem tailTrace_3760370 : CollatzResearch.WordTrace tailWord_3760370 prefixEnd_3760370 1930877248747557768781379 := by
  unfold tailWord_3760370
  simp only [CollatzResearch.WordTrace]
  refine ⟨34287990346707296227839641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91434640924552789940905709 34287990346707296227839641)
  ·
    refine ⟨25715992760030472170879731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34287990346707296227839641 25715992760030472170879731)
    ·
      refine ⟨38573989140045708256319597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25715992760030472170879731 38573989140045708256319597)
      ·
        refine ⟨14465245927517140596119849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38573989140045708256319597 14465245927517140596119849)
        ·
          refine ⟨10848934445637855447089887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14465245927517140596119849 10848934445637855447089887)
          ·
            refine ⟨16273401668456783170634831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10848934445637855447089887 16273401668456783170634831)
            ·
              refine ⟨24410102502685174755952247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16273401668456783170634831 24410102502685174755952247)
              ·
                refine ⟨36615153754027762133928371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24410102502685174755952247 36615153754027762133928371)
                ·
                  refine ⟨54922730631041643200892557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36615153754027762133928371 54922730631041643200892557)
                  ·
                    refine ⟨20596023986640616200334709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54922730631041643200892557 20596023986640616200334709)
                    ·
                      refine ⟨1930877248747557768781379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20596023986640616200334709 1930877248747557768781379)
                      ·
                        rfl

theorem cell23_3760370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_3760370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760370 prefixEnd_3760370 := by exact prefixLift 3760370
  have htrace : WordTrace (prefixWord ++ tailWord_3760370) baseStart_3760370 baseEnd_3760370 := by
    simpa [prefixWord, tailWord_3760370, baseEnd_3760370] using wordTrace_append hprefix tailTrace_3760370
  have hstable : (prefixWord ++ tailWord_3760370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760370).length < 2 ^ (prefixWord ++ tailWord_3760370).sum := by decide
  have hdescent : baseEnd_3760370 < baseStart_3760370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760383 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 7]
def baseStart_3760383 : Nat := 118140960795 + 3760383 * 2 ^ 59
def prefixEnd_3760383 : Nat := 4983230072969 + 3 ^ 40 * 3760383 * 2
def baseEnd_3760383 : Nat := 1930883923996066217918819

theorem tailTrace_3760383 : CollatzResearch.WordTrace tailWord_3760383 prefixEnd_3760383 1930883923996066217918819 := by
  unfold tailWord_3760383
  simp only [CollatzResearch.WordTrace]
  refine ⟨137152435535782088131581803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91434957023854725421054535 137152435535782088131581803)
  ·
    refine ⟨205728653303673132197372705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137152435535782088131581803 205728653303673132197372705)
    ·
      refine ⟨154296489977754849148029529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205728653303673132197372705 154296489977754849148029529)
      ·
        refine ⟨115722367483316136861022147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154296489977754849148029529 115722367483316136861022147)
        ·
          refine ⟨173583551224974205291533221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115722367483316136861022147 173583551224974205291533221)
          ·
            refine ⟨32546915854682663492162479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173583551224974205291533221 32546915854682663492162479)
            ·
              refine ⟨48820373782023995238243719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32546915854682663492162479 48820373782023995238243719)
              ·
                refine ⟨73230560673035992857365579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48820373782023995238243719 73230560673035992857365579)
                ·
                  refine ⟨109845841009553989286048369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73230560673035992857365579 109845841009553989286048369)
                  ·
                    refine ⟨82384380757165491964536277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 109845841009553989286048369 82384380757165491964536277)
                    ·
                      refine ⟨1930883923996066217918819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 82384380757165491964536277 1930883923996066217918819)
                      ·
                        rfl

theorem cell23_3760383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_3760383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760383 prefixEnd_3760383 := by exact prefixLift 3760383
  have htrace : WordTrace (prefixWord ++ tailWord_3760383) baseStart_3760383 baseEnd_3760383 := by
    simpa [prefixWord, tailWord_3760383, baseEnd_3760383] using wordTrace_append hprefix tailTrace_3760383
  have hstable : (prefixWord ++ tailWord_3760383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760383).length < 2 ^ (prefixWord ++ tailWord_3760383).sum := by decide
  have hdescent : baseEnd_3760383 < baseStart_3760383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760401 : List Nat := [1, 2, 2, 1, 1, 5, 4, 1, 2, 2, 2]
def baseStart_3760401 : Nat := 118140960795 + 3760401 * 2 ^ 59
def prefixEnd_3760401 : Nat := 4983230072969 + 3 ^ 40 * 3760401 * 2
def baseEnd_3760401 : Nat := 1930893166647847147493737

theorem tailTrace_3760401 : CollatzResearch.WordTrace tailWord_3760401 prefixEnd_3760401 1930893166647847147493737 := by
  unfold tailWord_3760401
  simp only [CollatzResearch.WordTrace]
  refine ⟨137153092049716877205737057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91435394699811251470491371 137153092049716877205737057)
  ·
    refine ⟨102864819037287657904302793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137153092049716877205737057 102864819037287657904302793)
    ·
      refine ⟨77148614277965743428227095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102864819037287657904302793 77148614277965743428227095)
      ·
        refine ⟨115722921416948615142340643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77148614277965743428227095 115722921416948615142340643)
        ·
          refine ⟨173584382125422922713510965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115722921416948615142340643 173584382125422922713510965)
          ·
            refine ⟨16273535824258399004391653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173584382125422922713510965 16273535824258399004391653)
            ·
              refine ⟨3051287967048449813323435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16273535824258399004391653 3051287967048449813323435)
              ·
                refine ⟨4576931950572674719985153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3051287967048449813323435 4576931950572674719985153)
                ·
                  refine ⟨3432698962929506039988865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4576931950572674719985153 3432698962929506039988865)
                  ·
                    refine ⟨2574524222197129529991649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3432698962929506039988865 2574524222197129529991649)
                    ·
                      refine ⟨1930893166647847147493737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2574524222197129529991649 1930893166647847147493737)
                      ·
                        rfl

theorem cell23_3760401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 2, 2, 2].length) (baseStart_3760401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760401 prefixEnd_3760401 := by exact prefixLift 3760401
  have htrace : WordTrace (prefixWord ++ tailWord_3760401) baseStart_3760401 baseEnd_3760401 := by
    simpa [prefixWord, tailWord_3760401, baseEnd_3760401] using wordTrace_append hprefix tailTrace_3760401
  have hstable : (prefixWord ++ tailWord_3760401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760401).length < 2 ^ (prefixWord ++ tailWord_3760401).sum := by decide
  have hdescent : baseEnd_3760401 < baseStart_3760401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760403 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 3, 7]
def baseStart_3760403 : Nat := 118140960795 + 3760403 * 2 ^ 59
def prefixEnd_3760403 : Nat := 4983230072969 + 3 ^ 40 * 3760403 * 2
def baseEnd_3760403 : Nat := 643631397869718713222909

theorem tailTrace_3760403 : CollatzResearch.WordTrace tailWord_3760403 prefixEnd_3760403 643631397869718713222909 := by
  unfold tailWord_3760403
  simp only [CollatzResearch.WordTrace]
  refine ⟨137153164995709631547309863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91435443330473087698206575 137153164995709631547309863)
  ·
    refine ⟨205729747493564447320964795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137153164995709631547309863 205729747493564447320964795)
    ·
      refine ⟨308594621240346670981447193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205729747493564447320964795 308594621240346670981447193)
      ·
        refine ⟨231445965930260003236085395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308594621240346670981447193 231445965930260003236085395)
        ·
          refine ⟨347168948895390004854128093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231445965930260003236085395 347168948895390004854128093)
          ·
            refine ⟨130188355835771251820298035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 347168948895390004854128093 130188355835771251820298035)
            ·
              refine ⟨195282533753656877730447053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130188355835771251820298035 195282533753656877730447053)
              ·
                refine ⟨73230950157621329148917645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195282533753656877730447053 73230950157621329148917645)
                ·
                  refine ⟨27461606309107998430844117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73230950157621329148917645 27461606309107998430844117)
                  ·
                    refine ⟨643631397869718713222909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27461606309107998430844117 643631397869718713222909)
                    ·
                      rfl

theorem cell23_3760403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 7].length) (baseStart_3760403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760403 prefixEnd_3760403 := by exact prefixLift 3760403
  have htrace : WordTrace (prefixWord ++ tailWord_3760403) baseStart_3760403 baseEnd_3760403 := by
    simpa [prefixWord, tailWord_3760403, baseEnd_3760403] using wordTrace_append hprefix tailTrace_3760403
  have hstable : (prefixWord ++ tailWord_3760403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760403).length < 2 ^ (prefixWord ++ tailWord_3760403).sum := by decide
  have hdescent : baseEnd_3760403 < baseStart_3760403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760441 : List Nat := [1, 2, 1, 6, 1, 3, 2, 2, 5]
def baseStart_3760441 : Nat := 118140960795 + 3760441 * 2 ^ 59
def prefixEnd_3760441 : Nat := 4983230072969 + 3 ^ 40 * 3760441 * 2
def baseEnd_3760441 : Nat := 214545967319336332332617

theorem tailTrace_3760441 : CollatzResearch.WordTrace tailWord_3760441 prefixEnd_3760441 214545967319336332332617 := by
  unfold tailWord_3760441
  simp only [CollatzResearch.WordTrace]
  refine ⟨137154550969571964037193177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91436367313047976024795451 137154550969571964037193177)
  ·
    refine ⟨102865913227178973027894883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137154550969571964037193177 102865913227178973027894883)
    ·
      refine ⟨154298869840768459541842325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102865913227178973027894883 154298869840768459541842325)
      ·
        refine ⟨7232759523786021541023859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 154298869840768459541842325 7232759523786021541023859)
        ·
          refine ⟨10849139285679032311535789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7232759523786021541023859 10849139285679032311535789)
          ·
            refine ⟨4068427232129637116825921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10849139285679032311535789 4068427232129637116825921)
            ·
              refine ⟨3051320424097227837619441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4068427232129637116825921 3051320424097227837619441)
              ·
                refine ⟨2288490318072920878214581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3051320424097227837619441 2288490318072920878214581)
                ·
                  refine ⟨214545967319336332332617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2288490318072920878214581 214545967319336332332617)
                  ·
                    rfl

theorem cell23_3760441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 2, 5].length) (baseStart_3760441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760441 prefixEnd_3760441 := by exact prefixLift 3760441
  have htrace : WordTrace (prefixWord ++ tailWord_3760441) baseStart_3760441 baseEnd_3760441 := by
    simpa [prefixWord, tailWord_3760441, baseEnd_3760441] using wordTrace_append hprefix tailTrace_3760441
  have hstable : (prefixWord ++ tailWord_3760441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760441).length < 2 ^ (prefixWord ++ tailWord_3760441).sum := by decide
  have hdescent : baseEnd_3760441 < baseStart_3760441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760501 : List Nat := [1, 3, 4, 1, 2, 1, 2, 4, 1, 4]
def baseStart_3760501 : Nat := 118140960795 + 3760501 * 2 ^ 59
def prefixEnd_3760501 : Nat := 4983230072969 + 3 ^ 40 * 3760501 * 2
def baseEnd_3760501 : Nat := 643648171571098918747759

theorem tailTrace_3760501 : CollatzResearch.WordTrace tailWord_3760501 prefixEnd_3760501 643648171571098918747759 := by
  unfold tailWord_3760501
  simp only [CollatzResearch.WordTrace]
  refine ⟨137156739349354594284377357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91437826232903062856251571 137156739349354594284377357)
  ·
    refine ⟨51433777256007972856641509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137156739349354594284377357 51433777256007972856641509)
    ·
      refine ⟨9643833235501494910620283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51433777256007972856641509 9643833235501494910620283)
      ·
        refine ⟨14465749853252242365930425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9643833235501494910620283 14465749853252242365930425)
        ·
          refine ⟨10849312389939181774447819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14465749853252242365930425 10849312389939181774447819)
          ·
            refine ⟨16273968584908772661671729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10849312389939181774447819 16273968584908772661671729)
            ·
              refine ⟨12205476438681579496253797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16273968584908772661671729 12205476438681579496253797)
              ·
                refine ⟨2288526832252796155547587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12205476438681579496253797 2288526832252796155547587)
                ·
                  refine ⟨3432790248379194233321381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2288526832252796155547587 3432790248379194233321381)
                  ·
                    refine ⟨643648171571098918747759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3432790248379194233321381 643648171571098918747759)
                    ·
                      rfl

theorem cell23_3760501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_3760501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760501 prefixEnd_3760501 := by exact prefixLift 3760501
  have htrace : WordTrace (prefixWord ++ tailWord_3760501) baseStart_3760501 baseEnd_3760501 := by
    simpa [prefixWord, tailWord_3760501, baseEnd_3760501] using wordTrace_append hprefix tailTrace_3760501
  have hstable : (prefixWord ++ tailWord_3760501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760501).length < 2 ^ (prefixWord ++ tailWord_3760501).sum := by decide
  have hdescent : baseEnd_3760501 < baseStart_3760501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760524 : List Nat := [2, 2, 1, 2, 1, 4, 2, 2, 3, 1, 3]
def baseStart_3760524 : Nat := 118140960795 + 3760524 * 2 ^ 59
def prefixEnd_3760524 : Nat := 4983230072969 + 3 ^ 40 * 3760524 * 2
def baseEnd_3760524 : Nat := 1930956324768350166255671

theorem tailTrace_3760524 : CollatzResearch.WordTrace tailWord_3760524 prefixEnd_3760524 1930956324768350166255671 := by
  unfold tailWord_3760524
  simp only [CollatzResearch.WordTrace]
  refine ⟨68578789114135634606232313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91438385485514179474976417 68578789114135634606232313)
  ·
    refine ⟨51434091835601725954674235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68578789114135634606232313 51434091835601725954674235)
    ·
      refine ⟨77151137753402588932011353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51434091835601725954674235 77151137753402588932011353)
      ·
        refine ⟨57863353315051941699008515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77151137753402588932011353 57863353315051941699008515)
        ·
          refine ⟨86795029972577912548512773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57863353315051941699008515 86795029972577912548512773)
          ·
            refine ⟨16274068119858358602846145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86795029972577912548512773 16274068119858358602846145)
            ·
              refine ⟨12205551089893768952134609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16274068119858358602846145 12205551089893768952134609)
              ·
                refine ⟨9154163317420326714100957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12205551089893768952134609 9154163317420326714100957)
                ·
                  refine ⟨3432811244032622517787859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9154163317420326714100957 3432811244032622517787859)
                  ·
                    refine ⟨5149216866048933776681789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3432811244032622517787859 5149216866048933776681789)
                    ·
                      refine ⟨1930956324768350166255671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5149216866048933776681789 1930956324768350166255671)
                      ·
                        rfl

theorem cell23_3760524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 3, 1, 3].length) (baseStart_3760524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760524 prefixEnd_3760524 := by exact prefixLift 3760524
  have htrace : WordTrace (prefixWord ++ tailWord_3760524) baseStart_3760524 baseEnd_3760524 := by
    simpa [prefixWord, tailWord_3760524, baseEnd_3760524] using wordTrace_append hprefix tailTrace_3760524
  have hstable : (prefixWord ++ tailWord_3760524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760524).length < 2 ^ (prefixWord ++ tailWord_3760524).sum := by decide
  have hdescent : baseEnd_3760524 < baseStart_3760524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760551 : List Nat := [1, 1, 6, 1, 1, 3, 1, 2, 2, 3, 2]
def baseStart_3760551 : Nat := 118140960795 + 3760551 * 2 ^ 59
def prefixEnd_3760551 : Nat := 4983230072969 + 3 ^ 40 * 3760551 * 2
def baseEnd_3760551 : Nat := 1930970188746021560618047

theorem tailTrace_3760551 : CollatzResearch.WordTrace tailWord_3760551 prefixEnd_3760551 1930970188746021560618047 := by
  unfold tailWord_3760551
  simp only [CollatzResearch.WordTrace]
  refine ⟨137158562999173452823697507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91439041999448968549131671 137158562999173452823697507)
  ·
    refine ⟨205737844498760179235546261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137158562999173452823697507 205737844498760179235546261)
    ·
      refine ⟨9643961460879383401666231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 205737844498760179235546261 9643961460879383401666231)
      ·
        refine ⟨14465942191319075102499347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9643961460879383401666231 14465942191319075102499347)
        ·
          refine ⟨21698913286978612653749021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14465942191319075102499347 21698913286978612653749021)
          ·
            refine ⟨8137092482616979745155883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21698913286978612653749021 8137092482616979745155883)
            ·
              refine ⟨12205638723925469617733825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8137092482616979745155883 12205638723925469617733825)
              ·
                refine ⟨9154229042944102213300369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12205638723925469617733825 9154229042944102213300369)
                ·
                  refine ⟨6865671782208076659975277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9154229042944102213300369 6865671782208076659975277)
                  ·
                    refine ⟨2574626918328028747490729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6865671782208076659975277 2574626918328028747490729)
                    ·
                      refine ⟨1930970188746021560618047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2574626918328028747490729 1930970188746021560618047)
                      ·
                        rfl

theorem cell23_3760551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_3760551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760551 prefixEnd_3760551 := by exact prefixLift 3760551
  have htrace : WordTrace (prefixWord ++ tailWord_3760551) baseStart_3760551 baseEnd_3760551 := by
    simpa [prefixWord, tailWord_3760551, baseEnd_3760551] using wordTrace_append hprefix tailTrace_3760551
  have hstable : (prefixWord ++ tailWord_3760551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760551).length < 2 ^ (prefixWord ++ tailWord_3760551).sum := by decide
  have hdescent : baseEnd_3760551 < baseStart_3760551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760567 : List Nat := [1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 5]
def baseStart_3760567 : Nat := 118140960795 + 3760567 * 2 ^ 59
def prefixEnd_3760567 : Nat := 4983230072969 + 3 ^ 40 * 3760567 * 2
def baseEnd_3760567 : Nat := 1930978404436493498017973

theorem tailTrace_3760567 : CollatzResearch.WordTrace tailWord_3760567 prefixEnd_3760567 1930978404436493498017973 := by
  unfold tailWord_3760567
  simp only [CollatzResearch.WordTrace]
  refine ⟨137159146567115487556279955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91439431044743658370853303 137159146567115487556279955)
  ·
    refine ⟨205738719850673231334419933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137159146567115487556279955 205738719850673231334419933)
    ·
      refine ⟨77152019944002461750407475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205738719850673231334419933 77152019944002461750407475)
      ·
        refine ⟨115728029916003692625611213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77152019944002461750407475 115728029916003692625611213)
        ·
          refine ⟨43398011218501384734604205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115728029916003692625611213 43398011218501384734604205)
          ·
            refine ⟨16274254206938019275476577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43398011218501384734604205 16274254206938019275476577)
            ·
              refine ⟨12205690655203514456607433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16274254206938019275476577 12205690655203514456607433)
              ·
                refine ⟨9154267991402635842455575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12205690655203514456607433 9154267991402635842455575)
                ·
                  refine ⟨13731401987103953763683363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9154267991402635842455575 13731401987103953763683363)
                  ·
                    refine ⟨20597102980655930645525045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13731401987103953763683363 20597102980655930645525045)
                    ·
                      refine ⟨1930978404436493498017973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20597102980655930645525045 1930978404436493498017973)
                      ·
                        rfl

theorem cell23_3760567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 5].length) (baseStart_3760567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760567 prefixEnd_3760567 := by exact prefixLift 3760567
  have htrace : WordTrace (prefixWord ++ tailWord_3760567) baseStart_3760567 baseEnd_3760567 := by
    simpa [prefixWord, tailWord_3760567, baseEnd_3760567] using wordTrace_append hprefix tailTrace_3760567
  have hstable : (prefixWord ++ tailWord_3760567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760567).length < 2 ^ (prefixWord ++ tailWord_3760567).sum := by decide
  have hdescent : baseEnd_3760567 < baseStart_3760567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760584 : List Nat := [2, 1, 3, 1, 3, 3, 1, 1, 3, 2, 3]
def baseStart_3760584 : Nat := 118140960795 + 3760584 * 2 ^ 59
def prefixEnd_3760584 : Nat := 4983230072969 + 3 ^ 40 * 3760584 * 2
def baseEnd_3760584 : Nat := 1930987133607619931505395

theorem tailTrace_3760584 : CollatzResearch.WordTrace tailWord_3760584 prefixEnd_3760584 1930987133607619931505395 := by
  unfold tailWord_3760584
  simp only [CollatzResearch.WordTrace]
  refine ⟨68579883304026949729824403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91439844405369266306432537 68579883304026949729824403)
  ·
    refine ⟨102869824956040424594736605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68579883304026949729824403 102869824956040424594736605)
    ·
      refine ⟨38576184358515159223026227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102869824956040424594736605 38576184358515159223026227)
      ·
        refine ⟨57864276537772738834539341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38576184358515159223026227 57864276537772738834539341)
        ·
          refine ⟨21699103701664777062952253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57864276537772738834539341 21699103701664777062952253)
          ·
            refine ⟨8137163888124291398607095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21699103701664777062952253 8137163888124291398607095)
            ·
              refine ⟨12205745832186437097910643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8137163888124291398607095 12205745832186437097910643)
              ·
                refine ⟨18308618748279655646865965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12205745832186437097910643 18308618748279655646865965)
                ·
                  refine ⟨6865732030604870867574737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18308618748279655646865965 6865732030604870867574737)
                  ·
                    refine ⟨5149299022953653150681053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6865732030604870867574737 5149299022953653150681053)
                    ·
                      refine ⟨1930987133607619931505395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5149299022953653150681053 1930987133607619931505395)
                      ·
                        rfl

theorem cell23_3760584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_3760584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760584 prefixEnd_3760584 := by exact prefixLift 3760584
  have htrace : WordTrace (prefixWord ++ tailWord_3760584) baseStart_3760584 baseEnd_3760584 := by
    simpa [prefixWord, tailWord_3760584, baseEnd_3760584] using wordTrace_append hprefix tailTrace_3760584
  have hstable : (prefixWord ++ tailWord_3760584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760584).length < 2 ^ (prefixWord ++ tailWord_3760584).sum := by decide
  have hdescent : baseEnd_3760584 < baseStart_3760584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760598 : List Nat := [5, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4]
def baseStart_3760598 : Nat := 118140960795 + 3760598 * 2 ^ 59
def prefixEnd_3760598 : Nat := 4983230072969 + 3 ^ 40 * 3760598 * 2
def baseEnd_3760598 : Nat := 1930994322336782876730331

theorem tailTrace_3760598 : CollatzResearch.WordTrace tailWord_3760598 prefixEnd_3760598 1930994322336782876730331 := by
  unfold tailWord_3760598
  simp only [CollatzResearch.WordTrace]
  refine ⟨8572517326875198740666153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91440184820002119900438965 8572517326875198740666153)
  ·
    refine ⟨6429387995156399055499615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8572517326875198740666153 6429387995156399055499615)
    ·
      refine ⟨9644081992734598583249423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6429387995156399055499615 9644081992734598583249423)
      ·
        refine ⟨14466122989101897874874135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9644081992734598583249423 14466122989101897874874135)
        ·
          refine ⟨21699184483652846812311203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14466122989101897874874135 21699184483652846812311203)
          ·
            refine ⟨32548776725479270218466805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21699184483652846812311203 32548776725479270218466805)
            ·
              refine ⟨3051447818013681582981263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32548776725479270218466805 3051447818013681582981263)
              ·
                refine ⟨4577171727020522374471895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3051447818013681582981263 4577171727020522374471895)
                ·
                  refine ⟨6865757590530783561707843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4577171727020522374471895 6865757590530783561707843)
                  ·
                    refine ⟨10298636385796175342561765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6865757590530783561707843 10298636385796175342561765)
                    ·
                      refine ⟨1930994322336782876730331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10298636385796175342561765 1930994322336782876730331)
                      ·
                        rfl

theorem cell23_3760598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_3760598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760598 prefixEnd_3760598 := by exact prefixLift 3760598
  have htrace : WordTrace (prefixWord ++ tailWord_3760598) baseStart_3760598 baseEnd_3760598 := by
    simpa [prefixWord, tailWord_3760598, baseEnd_3760598] using wordTrace_append hprefix tailTrace_3760598
  have hstable : (prefixWord ++ tailWord_3760598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760598).length < 2 ^ (prefixWord ++ tailWord_3760598).sum := by decide
  have hdescent : baseEnd_3760598 < baseStart_3760598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760601 : List Nat := [1, 2, 1, 2, 4, 1, 5, 1, 1, 2, 3]
def baseStart_3760601 : Nat := 118140960795 + 3760601 * 2 ^ 59
def prefixEnd_3760601 : Nat := 4983230072969 + 3 ^ 40 * 3760601 * 2
def baseEnd_3760601 : Nat := 1930995862778746364992817

theorem tailTrace_3760601 : CollatzResearch.WordTrace tailWord_3760601 prefixEnd_3760601 1930995862778746364992817 := by
  unfold tailWord_3760601
  simp only [CollatzResearch.WordTrace]
  refine ⟨137160386648992311363017657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91440257765994874242011771 137160386648992311363017657)
  ·
    refine ⟨102870289986744233522263243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137160386648992311363017657 102870289986744233522263243)
    ·
      refine ⟨154305434980116350283394865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102870289986744233522263243 154305434980116350283394865)
      ·
        refine ⟨115729076235087262712546149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154305434980116350283394865 115729076235087262712546149)
        ·
          refine ⟨21699201794078861758602403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115729076235087262712546149 21699201794078861758602403)
          ·
            refine ⟨32548802691118292637903605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21699201794078861758602403 32548802691118292637903605)
            ·
              refine ⟨3051450252292339934803463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32548802691118292637903605 3051450252292339934803463)
              ·
                refine ⟨4577175378438509902205195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3051450252292339934803463 4577175378438509902205195)
                ·
                  refine ⟨6865763067657764853307793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4577175378438509902205195 6865763067657764853307793)
                  ·
                    refine ⟨5149322300743323639980845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6865763067657764853307793 5149322300743323639980845)
                    ·
                      refine ⟨1930995862778746364992817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5149322300743323639980845 1930995862778746364992817)
                      ·
                        rfl

theorem cell23_3760601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 1, 2, 3].length) (baseStart_3760601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760601 prefixEnd_3760601 := by exact prefixLift 3760601
  have htrace : WordTrace (prefixWord ++ tailWord_3760601) baseStart_3760601 baseEnd_3760601 := by
    simpa [prefixWord, tailWord_3760601, baseEnd_3760601] using wordTrace_append hprefix tailTrace_3760601
  have hstable : (prefixWord ++ tailWord_3760601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760601).length < 2 ^ (prefixWord ++ tailWord_3760601).sum := by decide
  have hdescent : baseEnd_3760601 < baseStart_3760601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760624 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 5, 3, 2]
def baseStart_3760624 : Nat := 118140960795 + 3760624 * 2 ^ 59
def prefixEnd_3760624 : Nat := 4983230072969 + 3 ^ 40 * 3760624 * 2
def baseEnd_3760624 : Nat := 1931007672833799775005211

theorem tailTrace_3760624 : CollatzResearch.WordTrace tailWord_3760624 prefixEnd_3760624 1931007672833799775005211 := by
  unfold tailWord_3760624
  simp only [CollatzResearch.WordTrace]
  refine ⟨68580612763954493145552463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91440817018605990860736617 68580612763954493145552463)
  ·
    refine ⟨102870919145931739718328695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68580612763954493145552463 102870919145931739718328695)
    ·
      refine ⟨154306378718897609577493043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102870919145931739718328695 154306378718897609577493043)
      ·
        refine ⟨231459568078346414366239565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154306378718897609577493043 231459568078346414366239565)
        ·
          refine ⟨86797338029379905387339837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231459568078346414366239565 86797338029379905387339837)
          ·
            refine ⟨32549001761017464520252439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86797338029379905387339837 32549001761017464520252439)
            ·
              refine ⟨48823502641526196780378659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32549001761017464520252439 48823502641526196780378659)
              ·
                refine ⟨73235253962289295170567989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48823502641526196780378659 73235253962289295170567989)
                ·
                  refine ⟨6865805058964621422240749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73235253962289295170567989 6865805058964621422240749)
                  ·
                    refine ⟨2574676897111733033340281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6865805058964621422240749 2574676897111733033340281)
                    ·
                      refine ⟨1931007672833799775005211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2574676897111733033340281 1931007672833799775005211)
                      ·
                        rfl

theorem cell23_3760624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 5, 3, 2].length) (baseStart_3760624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760624 prefixEnd_3760624 := by exact prefixLift 3760624
  have htrace : WordTrace (prefixWord ++ tailWord_3760624) baseStart_3760624 baseEnd_3760624 := by
    simpa [prefixWord, tailWord_3760624, baseEnd_3760624] using wordTrace_append hprefix tailTrace_3760624
  have hstable : (prefixWord ++ tailWord_3760624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760624).length < 2 ^ (prefixWord ++ tailWord_3760624).sum := by decide
  have hdescent : baseEnd_3760624 < baseStart_3760624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760637 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 2, 3, 4]
def baseStart_3760637 : Nat := 118140960795 + 3760637 * 2 ^ 59
def prefixEnd_3760637 : Nat := 4983230072969 + 3 ^ 40 * 3760637 * 2
def baseEnd_3760637 : Nat := 1931014348082308224142651

theorem tailTrace_3760637 : CollatzResearch.WordTrace tailWord_3760637 prefixEnd_3760637 1931014348082308224142651 := by
  unfold tailWord_3760637
  simp only [CollatzResearch.WordTrace]
  refine ⟨137161699676861889511328165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91441133117907926340885443 137161699676861889511328165)
  ·
    refine ⟨25717818689411604283374031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137161699676861889511328165 25717818689411604283374031)
    ·
      refine ⟨38576728034117406425061047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25717818689411604283374031 38576728034117406425061047)
      ·
        refine ⟨57865092051176109637591571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38576728034117406425061047 57865092051176109637591571)
        ·
          refine ⟨86797638076764164456387357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57865092051176109637591571 86797638076764164456387357)
          ·
            refine ⟨32549114278786561671145259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86797638076764164456387357 32549114278786561671145259)
            ·
              refine ⟨48823671418179842506717889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32549114278786561671145259 48823671418179842506717889)
              ·
                refine ⟨36617753563634881880038417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48823671418179842506717889 36617753563634881880038417)
                ·
                  refine ⟨27463315172726161410028813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36617753563634881880038417 27463315172726161410028813)
                  ·
                    refine ⟨10298743189772310528760805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27463315172726161410028813 10298743189772310528760805)
                    ·
                      refine ⟨1931014348082308224142651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10298743189772310528760805 1931014348082308224142651)
                      ·
                        rfl

theorem cell23_3760637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_3760637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760637 prefixEnd_3760637 := by exact prefixLift 3760637
  have htrace : WordTrace (prefixWord ++ tailWord_3760637) baseStart_3760637 baseEnd_3760637 := by
    simpa [prefixWord, tailWord_3760637, baseEnd_3760637] using wordTrace_append hprefix tailTrace_3760637
  have hstable : (prefixWord ++ tailWord_3760637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760637).length < 2 ^ (prefixWord ++ tailWord_3760637).sum := by decide
  have hdescent : baseEnd_3760637 < baseStart_3760637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760641 : List Nat := [1, 2, 4, 1, 3, 1, 2, 1, 3, 3, 2]
def baseStart_3760641 : Nat := 118140960795 + 3760641 * 2 ^ 59
def prefixEnd_3760641 : Nat := 4983230072969 + 3 ^ 40 * 3760641 * 2
def baseEnd_3760641 : Nat := 1931016402004926208492633

theorem tailTrace_3760641 : CollatzResearch.WordTrace tailWord_3760641 prefixEnd_3760641 1931016402004926208492633 := by
  unfold tailWord_3760641
  simp only [CollatzResearch.WordTrace]
  refine ⟨137161845568847398194473777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91441230379231598796315851 137161845568847398194473777)
  ·
    refine ⟨102871384176635548645855333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137161845568847398194473777 102871384176635548645855333)
    ·
      refine ⟨19288384533119165371097875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102871384176635548645855333 19288384533119165371097875)
      ·
        refine ⟨28932576799678748056646813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19288384533119165371097875 28932576799678748056646813)
        ·
          refine ⟨10849716299879530521242555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28932576799678748056646813 10849716299879530521242555)
          ·
            refine ⟨16274574449819295781863833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10849716299879530521242555 16274574449819295781863833)
            ·
              refine ⟨12205930837364471836397875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16274574449819295781863833 12205930837364471836397875)
              ·
                refine ⟨18308896256046707754596813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12205930837364471836397875 18308896256046707754596813)
                ·
                  refine ⟨6865836096017515407973805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18308896256046707754596813 6865836096017515407973805)
                  ·
                    refine ⟨2574688536006568277990177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6865836096017515407973805 2574688536006568277990177)
                    ·
                      refine ⟨1931016402004926208492633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2574688536006568277990177 1931016402004926208492633)
                      ·
                        rfl

theorem cell23_3760641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_3760641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760641 prefixEnd_3760641 := by exact prefixLift 3760641
  have htrace : WordTrace (prefixWord ++ tailWord_3760641) baseStart_3760641 baseEnd_3760641 := by
    simpa [prefixWord, tailWord_3760641, baseEnd_3760641] using wordTrace_append hprefix tailTrace_3760641
  have hstable : (prefixWord ++ tailWord_3760641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760641).length < 2 ^ (prefixWord ++ tailWord_3760641).sum := by decide
  have hdescent : baseEnd_3760641 < baseStart_3760641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760657 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 3]
def baseStart_3760657 : Nat := 118140960795 + 3760657 * 2 ^ 59
def prefixEnd_3760657 : Nat := 4983230072969 + 3 ^ 40 * 3760657 * 2
def baseEnd_3760657 : Nat := 1931024617695398145892559

theorem tailTrace_3760657 : CollatzResearch.WordTrace tailWord_3760657 prefixEnd_3760657 1931024617695398145892559 := by
  unfold tailWord_3760657
  simp only [CollatzResearch.WordTrace]
  refine ⟨137162429136789432927056225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91441619424526288618037483 137162429136789432927056225)
  ·
    refine ⟨102871821852592074695292169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137162429136789432927056225 102871821852592074695292169)
    ·
      refine ⟨77153866389444056021469127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102871821852592074695292169 77153866389444056021469127)
      ·
        refine ⟨115730799584166084032203691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77153866389444056021469127 115730799584166084032203691)
        ·
          refine ⟨173596199376249126048305537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115730799584166084032203691 173596199376249126048305537)
          ·
            refine ⟨130197149532186844536229153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173596199376249126048305537 130197149532186844536229153)
            ·
              refine ⟨97647862149140133402171865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130197149532186844536229153 97647862149140133402171865)
              ·
                refine ⟨73235896611855100051628899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97647862149140133402171865 73235896611855100051628899)
                ·
                  refine ⟨109853844917782650077443349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73235896611855100051628899 109853844917782650077443349)
                  ·
                    refine ⟨5149398980521061722380157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 109853844917782650077443349 5149398980521061722380157)
                    ·
                      refine ⟨1931024617695398145892559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5149398980521061722380157 1931024617695398145892559)
                      ·
                        rfl

theorem cell23_3760657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 3].length) (baseStart_3760657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760657 prefixEnd_3760657 := by exact prefixLift 3760657
  have htrace : WordTrace (prefixWord ++ tailWord_3760657) baseStart_3760657 baseEnd_3760657 := by
    simpa [prefixWord, tailWord_3760657, baseEnd_3760657] using wordTrace_append hprefix tailTrace_3760657
  have hstable : (prefixWord ++ tailWord_3760657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760657).length < 2 ^ (prefixWord ++ tailWord_3760657).sum := by decide
  have hdescent : baseEnd_3760657 < baseStart_3760657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760677 : List Nat := [1, 3, 1, 2, 2, 1, 3, 3, 7]
def baseStart_3760677 : Nat := 118140960795 + 3760677 * 2 ^ 59
def prefixEnd_3760677 : Nat := 4983230072969 + 3 ^ 40 * 3760677 * 2
def baseEnd_3760677 : Nat := 214559431923165340849163

theorem tailTrace_3760677 : CollatzResearch.WordTrace tailWord_3760677 prefixEnd_3760677 214559431923165340849163 := by
  unfold tailWord_3760677
  simp only [CollatzResearch.WordTrace]
  refine ⟨137163158596716976342784285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91442105731144650895189523 137163158596716976342784285)
  ·
    refine ⟨51436184473768866128544107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137163158596716976342784285 51436184473768866128544107)
    ·
      refine ⟨77154276710653299192816161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51436184473768866128544107 77154276710653299192816161)
      ·
        refine ⟨57865707532989974394612121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77154276710653299192816161 57865707532989974394612121)
        ·
          refine ⟨43399280649742480795959091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57865707532989974394612121 43399280649742480795959091)
          ·
            refine ⟨65098920974613721193938637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43399280649742480795959091 65098920974613721193938637)
            ·
              refine ⟨24412095365480145447726989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65098920974613721193938637 24412095365480145447726989)
              ·
                refine ⟨9154535762055054542897621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24412095365480145447726989 9154535762055054542897621)
                ·
                  refine ⟨214559431923165340849163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9154535762055054542897621 214559431923165340849163)
                  ·
                    rfl

theorem cell23_3760677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 7].length) (baseStart_3760677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760677 prefixEnd_3760677 := by exact prefixLift 3760677
  have htrace : WordTrace (prefixWord ++ tailWord_3760677) baseStart_3760677 baseEnd_3760677 := by
    simpa [prefixWord, tailWord_3760677, baseEnd_3760677] using wordTrace_append hprefix tailTrace_3760677
  have hstable : (prefixWord ++ tailWord_3760677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760677).length < 2 ^ (prefixWord ++ tailWord_3760677).sum := by decide
  have hdescent : baseEnd_3760677 < baseStart_3760677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760692 : List Nat := [2, 5, 1, 3, 1, 1, 2, 2, 1, 3, 2]
def baseStart_3760692 : Nat := 118140960795 + 3760692 * 2 ^ 59
def prefixEnd_3760692 : Nat := 4983230072969 + 3 ^ 40 * 3760692 * 2
def baseEnd_3760692 : Nat := 1931042589518305508954899

theorem tailTrace_3760692 : CollatzResearch.WordTrace tailWord_3760692 prefixEnd_3760692 1931042589518305508954899 := by
  unfold tailWord_3760692
  simp only [CollatzResearch.WordTrace]
  refine ⟨68581852845831316952290165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91442470461108422603053553 68581852845831316952290165)
  ·
    refine ⟨6429548704296685964277203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68581852845831316952290165 6429548704296685964277203)
    ·
      refine ⟨9644323056445028946415805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6429548704296685964277203 9644323056445028946415805)
      ·
        refine ⟨3616621146166885854905927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9644323056445028946415805 3616621146166885854905927)
        ·
          refine ⟨5424931719250328782358891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3616621146166885854905927 5424931719250328782358891)
          ·
            refine ⟨8137397578875493173538337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5424931719250328782358891 8137397578875493173538337)
            ·
              refine ⟨6103048184156619880153753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8137397578875493173538337 6103048184156619880153753)
              ·
                refine ⟨4577286138117464910115315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6103048184156619880153753 4577286138117464910115315)
                ·
                  refine ⟨6865929207176197365172973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4577286138117464910115315 6865929207176197365172973)
                  ·
                    refine ⟨2574723452691074011939865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6865929207176197365172973 2574723452691074011939865)
                    ·
                      refine ⟨1931042589518305508954899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2574723452691074011939865 1931042589518305508954899)
                      ·
                        rfl

theorem cell23_3760692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_3760692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760692 prefixEnd_3760692 := by exact prefixLift 3760692
  have htrace : WordTrace (prefixWord ++ tailWord_3760692) baseStart_3760692 baseEnd_3760692 := by
    simpa [prefixWord, tailWord_3760692, baseEnd_3760692] using wordTrace_append hprefix tailTrace_3760692
  have hstable : (prefixWord ++ tailWord_3760692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760692).length < 2 ^ (prefixWord ++ tailWord_3760692).sum := by decide
  have hdescent : baseEnd_3760692 < baseStart_3760692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760707 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 6, 5]
def baseStart_3760707 : Nat := 118140960795 + 3760707 * 2 ^ 59
def prefixEnd_3760707 : Nat := 4983230072969 + 3 ^ 40 * 3760707 * 2
def baseEnd_3760707 : Nat := 643683430576040983422443

theorem tailTrace_3760707 : CollatzResearch.WordTrace tailWord_3760707 prefixEnd_3760707 643683430576040983422443 := by
  unfold tailWord_3760707
  simp only [CollatzResearch.WordTrace]
  refine ⟨137164252786608291466376375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91442835191072194310917583 137164252786608291466376375)
  ·
    refine ⟨205746379179912437199564563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137164252786608291466376375 205746379179912437199564563)
    ·
      refine ⟨308619568769868655799346845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205746379179912437199564563 308619568769868655799346845)
      ·
        refine ⟨115732338288700745924755067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308619568769868655799346845 115732338288700745924755067)
        ·
          refine ⟨173598507433051118887132601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115732338288700745924755067 173598507433051118887132601)
          ·
            refine ⟨130198880574788339165349451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173598507433051118887132601 130198880574788339165349451)
            ·
              refine ⟨195298320862182508748024177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130198880574788339165349451 195298320862182508748024177)
              ·
                refine ⟨146473740646636881561018133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195298320862182508748024177 146473740646636881561018133)
                ·
                  refine ⟨6865956592811103823172725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 146473740646636881561018133 6865956592811103823172725)
                  ·
                    refine ⟨643683430576040983422443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6865956592811103823172725 643683430576040983422443)
                    ·
                      rfl

theorem cell23_3760707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 5].length) (baseStart_3760707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760707 prefixEnd_3760707 := by exact prefixLift 3760707
  have htrace : WordTrace (prefixWord ++ tailWord_3760707) baseStart_3760707 baseEnd_3760707 := by
    simpa [prefixWord, tailWord_3760707, baseEnd_3760707] using wordTrace_append hprefix tailTrace_3760707
  have hstable : (prefixWord ++ tailWord_3760707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760707).length < 2 ^ (prefixWord ++ tailWord_3760707).sum := by decide
  have hdescent : baseEnd_3760707 < baseStart_3760707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760711 : List Nat := [1, 1, 4, 1, 4, 1, 3, 3, 5]
def baseStart_3760711 : Nat := 118140960795 + 3760711 * 2 ^ 59
def prefixEnd_3760711 : Nat := 4983230072969 + 3 ^ 40 * 3760711 * 2
def baseEnd_3760711 : Nat := 214561371738971214957479

theorem tailTrace_3760711 : CollatzResearch.WordTrace tailWord_3760711 prefixEnd_3760711 214561371738971214957479 := by
  unfold tailWord_3760711
  simp only [CollatzResearch.WordTrace]
  refine ⟨137164398678593800149521987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91442932452395866766347991 137164398678593800149521987)
  ·
    refine ⟨205746598017890700224282981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137164398678593800149521987 205746598017890700224282981)
    ·
      refine ⟨38577487128354506292053059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205746598017890700224282981 38577487128354506292053059)
      ·
        refine ⟨57866230692531759438079589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38577487128354506292053059 57866230692531759438079589)
        ·
          refine ⟨10849918254849704894639923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57866230692531759438079589 10849918254849704894639923)
          ·
            refine ⟨16274877382274557341959885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10849918254849704894639923 16274877382274557341959885)
            ·
              refine ⟨6103079018352959003234957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16274877382274557341959885 6103079018352959003234957)
              ·
                refine ⟨2288654631882359626213109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6103079018352959003234957 2288654631882359626213109)
                ·
                  refine ⟨214561371738971214957479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2288654631882359626213109 214561371738971214957479)
                  ·
                    rfl

theorem cell23_3760711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 3, 5].length) (baseStart_3760711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760711 prefixEnd_3760711 := by exact prefixLift 3760711
  have htrace : WordTrace (prefixWord ++ tailWord_3760711) baseStart_3760711 baseEnd_3760711 := by
    simpa [prefixWord, tailWord_3760711, baseEnd_3760711] using wordTrace_append hprefix tailTrace_3760711
  have hstable : (prefixWord ++ tailWord_3760711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760711).length < 2 ^ (prefixWord ++ tailWord_3760711).sum := by decide
  have hdescent : baseEnd_3760711 < baseStart_3760711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760724 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 4, 5]
def baseStart_3760724 : Nat := 118140960795 + 3760724 * 2 ^ 59
def prefixEnd_3760724 : Nat := 4983230072969 + 3 ^ 40 * 3760724 * 2
def baseEnd_3760724 : Nat := 643686340299749794584917

theorem tailTrace_3760724 : CollatzResearch.WordTrace tailWord_3760724 prefixEnd_3760724 643686340299749794584917 := by
  unfold tailWord_3760724
  simp only [CollatzResearch.WordTrace]
  refine ⟨68582436413773351684872613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91443248551697802246496817 68582436413773351684872613)
  ·
    refine ⟨12859206827582503440913615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68582436413773351684872613 12859206827582503440913615)
    ·
      refine ⟨19288810241373755161370423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12859206827582503440913615 19288810241373755161370423)
      ·
        refine ⟨28933215362060632742055635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19288810241373755161370423 28933215362060632742055635)
        ·
          refine ⟨43399823043090949113083453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28933215362060632742055635 43399823043090949113083453)
          ·
            refine ⟨16274933641159105917406295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43399823043090949113083453 16274933641159105917406295)
            ·
              refine ⟨24412400461738658876109443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16274933641159105917406295 24412400461738658876109443)
              ·
                refine ⟨36618600692607988314164165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24412400461738658876109443 36618600692607988314164165)
                ·
                  refine ⟨6865987629863997808905781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36618600692607988314164165 6865987629863997808905781)
                  ·
                    refine ⟨643686340299749794584917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6865987629863997808905781 643686340299749794584917)
                    ·
                      rfl

theorem cell23_3760724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_3760724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760724 prefixEnd_3760724 := by exact prefixLift 3760724
  have htrace : WordTrace (prefixWord ++ tailWord_3760724) baseStart_3760724 baseEnd_3760724 := by
    simpa [prefixWord, tailWord_3760724, baseEnd_3760724] using wordTrace_append hprefix tailTrace_3760724
  have hstable : (prefixWord ++ tailWord_3760724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760724).length < 2 ^ (prefixWord ++ tailWord_3760724).sum := by decide
  have hdescent : baseEnd_3760724 < baseStart_3760724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760758 : List Nat := [5, 1, 1, 2, 3, 1, 2, 1, 2, 5]
def baseStart_3760758 : Nat := 118140960795 + 3760758 * 2 ^ 59
def prefixEnd_3760758 : Nat := 4983230072969 + 3 ^ 40 * 3760758 * 2
def baseEnd_3760758 : Nat := 643692159747167416909865

theorem tailTrace_3760758 : CollatzResearch.WordTrace tailWord_3760758 prefixEnd_3760758 643692159747167416909865 := by
  unfold tailWord_3760758
  simp only [CollatzResearch.WordTrace]
  refine ⟨8572882056838970448530183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91444075272949018117655285 8572882056838970448530183)
  ·
    refine ⟨12859323085258455672795275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8572882056838970448530183 12859323085258455672795275)
    ·
      refine ⟨19288984627887683509192913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12859323085258455672795275 19288984627887683509192913)
      ·
        refine ⟨14466738470915762631894685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19288984627887683509192913 14466738470915762631894685)
        ·
          refine ⟨5425026926593410986960507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14466738470915762631894685 5425026926593410986960507)
          ·
            refine ⟨8137540389890116480440761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5425026926593410986960507 8137540389890116480440761)
            ·
              refine ⟨6103155292417587360330571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8137540389890116480440761 6103155292417587360330571)
              ·
                refine ⟨9154732938626381040495857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6103155292417587360330571 9154732938626381040495857)
                ·
                  refine ⟨6866049703969785780371893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9154732938626381040495857 6866049703969785780371893)
                  ·
                    refine ⟨643692159747167416909865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6866049703969785780371893 643692159747167416909865)
                    ·
                      rfl

theorem cell23_3760758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_3760758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760758 prefixEnd_3760758 := by exact prefixLift 3760758
  have htrace : WordTrace (prefixWord ++ tailWord_3760758) baseStart_3760758 baseEnd_3760758 := by
    simpa [prefixWord, tailWord_3760758, baseEnd_3760758] using wordTrace_append hprefix tailTrace_3760758
  have hstable : (prefixWord ++ tailWord_3760758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760758).length < 2 ^ (prefixWord ++ tailWord_3760758).sum := by decide
  have hdescent : baseEnd_3760758 < baseStart_3760758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760761 : List Nat := [1, 2, 1, 3, 3, 3, 2, 1, 2, 1, 4]
def baseStart_3760761 : Nat := 118140960795 + 3760761 * 2 ^ 59
def prefixEnd_3760761 : Nat := 4983230072969 + 3 ^ 40 * 3760761 * 2
def baseEnd_3760761 : Nat := 1931078019683465738992081

theorem tailTrace_3760761 : CollatzResearch.WordTrace tailWord_3760761 prefixEnd_3760761 1931078019683465738992081 := by
  unfold tailWord_3760761
  simp only [CollatzResearch.WordTrace]
  refine ⟨137166222328412658688842137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91444148218941772459228091 137166222328412658688842137)
  ·
    refine ⟨102874666746309494016631603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137166222328412658688842137 102874666746309494016631603)
    ·
      refine ⟨154312000119464241024947405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102874666746309494016631603 154312000119464241024947405)
      ·
        refine ⟨57867000044799090384355277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154312000119464241024947405 57867000044799090384355277)
        ·
          refine ⟨21700125016799658894133229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57867000044799090384355277 21700125016799658894133229)
          ·
            refine ⟨8137546881299872085299961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21700125016799658894133229 8137546881299872085299961)
            ·
              refine ⟨6103160160974904063974971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8137546881299872085299961 6103160160974904063974971)
              ·
                refine ⟨9154740241462356095962457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6103160160974904063974971 9154740241462356095962457)
                ·
                  refine ⟨6866055181096767071971843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9154740241462356095962457 6866055181096767071971843)
                  ·
                    refine ⟨10299082771645150607957765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6866055181096767071971843 10299082771645150607957765)
                    ·
                      refine ⟨1931078019683465738992081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10299082771645150607957765 1931078019683465738992081)
                      ·
                        rfl

theorem cell23_3760761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_3760761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760761 prefixEnd_3760761 := by exact prefixLift 3760761
  have htrace : WordTrace (prefixWord ++ tailWord_3760761) baseStart_3760761 baseEnd_3760761 := by
    simpa [prefixWord, tailWord_3760761, baseEnd_3760761] using wordTrace_append hprefix tailTrace_3760761
  have hstable : (prefixWord ++ tailWord_3760761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760761).length < 2 ^ (prefixWord ++ tailWord_3760761).sum := by decide
  have hdescent : baseEnd_3760761 < baseStart_3760761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760764 : List Nat := [2, 2, 2, 1, 1, 2, 2, 3, 1, 4, 3]
def baseStart_3760764 : Nat := 118140960795 + 3760764 * 2 ^ 59
def prefixEnd_3760764 : Nat := 4983230072969 + 3 ^ 40 * 3760764 * 2
def baseEnd_3760764 : Nat := 1931079560125429227254567

theorem tailTrace_3760764 : CollatzResearch.WordTrace tailWord_3760764 prefixEnd_3760764 1931079560125429227254567 := by
  unfold tailWord_3760764
  simp only [CollatzResearch.WordTrace]
  refine ⟨68583165873700895100600673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91444221164934526800800897 68583165873700895100600673)
  ·
    refine ⟨51437374405275671325450505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68583165873700895100600673 51437374405275671325450505)
    ·
      refine ⟨38578030803956753494087879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51437374405275671325450505 38578030803956753494087879)
      ·
        refine ⟨57867046205935130241131819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38578030803956753494087879 57867046205935130241131819)
        ·
          refine ⟨86800569308902695361697729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57867046205935130241131819 86800569308902695361697729)
          ·
            refine ⟨65100426981677021521273297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86800569308902695361697729 65100426981677021521273297)
            ·
              refine ⟨48825320236257766140954973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65100426981677021521273297 48825320236257766140954973)
              ·
                refine ⟨18309495088596662302858115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48825320236257766140954973 18309495088596662302858115)
                ·
                  refine ⟨27464242632894993454287173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18309495088596662302858115 27464242632894993454287173)
                  ·
                    refine ⟨5149545493667811272678845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27464242632894993454287173 5149545493667811272678845)
                    ·
                      refine ⟨1931079560125429227254567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5149545493667811272678845 1931079560125429227254567)
                      ·
                        rfl

theorem cell23_3760764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_3760764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760764 prefixEnd_3760764 := by exact prefixLift 3760764
  have htrace : WordTrace (prefixWord ++ tailWord_3760764) baseStart_3760764 baseEnd_3760764 := by
    simpa [prefixWord, tailWord_3760764, baseEnd_3760764] using wordTrace_append hprefix tailTrace_3760764
  have hstable : (prefixWord ++ tailWord_3760764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760764).length < 2 ^ (prefixWord ++ tailWord_3760764).sum := by decide
  have hdescent : baseEnd_3760764 < baseStart_3760764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760767 : List Nat := [1, 1, 2, 2, 1, 1, 1, 6, 8]
def baseStart_3760767 : Nat := 118140960795 + 3760767 * 2 ^ 59
def prefixEnd_3760767 : Nat := 4983230072969 + 3 ^ 40 * 3760767 * 2
def baseEnd_3760767 : Nat := 214564566729710301724117

theorem tailTrace_3760767 : CollatzResearch.WordTrace tailWord_3760767 prefixEnd_3760767 214564566729710301724117 := by
  unfold tailWord_3760767
  simp only [CollatzResearch.WordTrace]
  refine ⟨137166441166390921713560555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91444294110927281142373703 137166441166390921713560555)
  ·
    refine ⟨205749661749586382570340833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137166441166390921713560555 205749661749586382570340833)
    ·
      refine ⟨154312246312189786927755625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205749661749586382570340833 154312246312189786927755625)
      ·
        refine ⟨115734184734142340195816719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154312246312189786927755625 115734184734142340195816719)
        ·
          refine ⟨173601277101213510293725079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115734184734142340195816719 173601277101213510293725079)
          ·
            refine ⟨260401915651820265440587619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173601277101213510293725079 260401915651820265440587619)
            ·
              refine ⟨390602873477730398160881429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260401915651820265440587619 390602873477730398160881429)
              ·
                refine ⟨18309509694268612413791317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 390602873477730398160881429 18309509694268612413791317)
                ·
                  refine ⟨214564566729710301724117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18309509694268612413791317 214564566729710301724117)
                  ·
                    rfl

theorem cell23_3760767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 8].length) (baseStart_3760767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760767 prefixEnd_3760767 := by exact prefixLift 3760767
  have htrace : WordTrace (prefixWord ++ tailWord_3760767) baseStart_3760767 baseEnd_3760767 := by
    simpa [prefixWord, tailWord_3760767, baseEnd_3760767] using wordTrace_append hprefix tailTrace_3760767
  have hstable : (prefixWord ++ tailWord_3760767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760767).length < 2 ^ (prefixWord ++ tailWord_3760767).sum := by decide
  have hdescent : baseEnd_3760767 < baseStart_3760767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760787 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 8]
def baseStart_3760787 : Nat := 118140960795 + 3760787 * 2 ^ 59
def prefixEnd_3760787 : Nat := 4983230072969 + 3 ^ 40 * 3760787 * 2
def baseEnd_3760787 : Nat := 1931091370180482637266961

theorem tailTrace_3760787 : CollatzResearch.WordTrace tailWord_3760787 prefixEnd_3760787 1931091370180482637266961 := by
  unfold tailWord_3760787
  simp only [CollatzResearch.WordTrace]
  refine ⟨137167170626318465129288615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91444780417545643419525743 137167170626318465129288615)
  ·
    refine ⟨205750755939477697693932923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137167170626318465129288615 205750755939477697693932923)
    ·
      refine ⟨308626133909216546540899385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205750755939477697693932923 308626133909216546540899385)
      ·
        refine ⟨231469600431912409905674539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308626133909216546540899385 231469600431912409905674539)
        ·
          refine ⟨347204400647868614858511809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231469600431912409905674539 347204400647868614858511809)
          ·
            refine ⟨260403300485901461143883857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347204400647868614858511809 260403300485901461143883857)
            ·
              refine ⟨195302475364426095857912893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260403300485901461143883857 195302475364426095857912893)
              ·
                refine ⟨73238428261659785946717335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195302475364426095857912893 73238428261659785946717335)
                ·
                  refine ⟨109857642392489678920076003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73238428261659785946717335 109857642392489678920076003)
                  ·
                    refine ⟨164786463588734518380114005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109857642392489678920076003 164786463588734518380114005)
                    ·
                      refine ⟨1931091370180482637266961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 164786463588734518380114005 1931091370180482637266961)
                      ·
                        rfl

theorem cell23_3760787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 8].length) (baseStart_3760787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760787 prefixEnd_3760787 := by exact prefixLift 3760787
  have htrace : WordTrace (prefixWord ++ tailWord_3760787) baseStart_3760787 baseEnd_3760787 := by
    simpa [prefixWord, tailWord_3760787, baseEnd_3760787] using wordTrace_append hprefix tailTrace_3760787
  have hstable : (prefixWord ++ tailWord_3760787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760787).length < 2 ^ (prefixWord ++ tailWord_3760787).sum := by decide
  have hdescent : baseEnd_3760787 < baseStart_3760787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760831 : List Nat := [1, 1, 2, 2, 2, 5, 1, 3, 1, 5]
def baseStart_3760831 : Nat := 118140960795 + 3760831 * 2 ^ 59
def prefixEnd_3760831 : Nat := 4983230072969 + 3 ^ 40 * 3760831 * 2
def baseEnd_3760831 : Nat := 643704654443093488372253

theorem tailTrace_3760831 : CollatzResearch.WordTrace tailWord_3760831 prefixEnd_3760831 643704654443093488372253 := by
  unfold tailWord_3760831
  simp only [CollatzResearch.WordTrace]
  refine ⟨137168775438159060643890347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91445850292106040429260231 137168775438159060643890347)
  ·
    refine ⟨205753163157238590965835521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137168775438159060643890347 205753163157238590965835521)
    ·
      refine ⟨154314872367928943224376641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205753163157238590965835521 154314872367928943224376641)
      ·
        refine ⟨115736154275946707418282481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154314872367928943224376641 115736154275946707418282481)
        ·
          refine ⟨86802115706960030563711861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115736154275946707418282481 86802115706960030563711861)
          ·
            refine ⟨8137698347527502865347987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86802115706960030563711861 8137698347527502865347987)
            ·
              refine ⟨12206547521291254298021981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8137698347527502865347987 12206547521291254298021981)
              ·
                refine ⟨4577455320484220361758243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12206547521291254298021981 4577455320484220361758243)
                ·
                  refine ⟨6866182980726330542637365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4577455320484220361758243 6866182980726330542637365)
                  ·
                    refine ⟨643704654443093488372253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6866182980726330542637365 643704654443093488372253)
                    ·
                      rfl

theorem cell23_3760831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 5].length) (baseStart_3760831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760831 prefixEnd_3760831 := by exact prefixLift 3760831
  have htrace : WordTrace (prefixWord ++ tailWord_3760831) baseStart_3760831 baseEnd_3760831 := by
    simpa [prefixWord, tailWord_3760831, baseEnd_3760831] using wordTrace_append hprefix tailTrace_3760831
  have hstable : (prefixWord ++ tailWord_3760831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760831).length < 2 ^ (prefixWord ++ tailWord_3760831).sum := by decide
  have hdescent : baseEnd_3760831 < baseStart_3760831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760868 : List Nat := [2, 3, 1, 1, 1, 5, 2, 2, 1, 1, 4]
def baseStart_3760868 : Nat := 118140960795 + 3760868 * 2 ^ 59
def prefixEnd_3760868 : Nat := 4983230072969 + 3 ^ 40 * 3760868 * 2
def baseEnd_3760868 : Nat := 1931132962113496820354089

theorem tailTrace_3760868 : CollatzResearch.WordTrace tailWord_3760868 prefixEnd_3760868 1931132962113496820354089 := by
  unfold tailWord_3760868
  simp only [CollatzResearch.WordTrace]
  refine ⟨68585062469512507981493629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91446749959350010641991505 68585062469512507981493629)
  ·
    refine ⟨25719398426067190493060111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68585062469512507981493629 25719398426067190493060111)
    ·
      refine ⟨38579097639100785739590167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25719398426067190493060111 38579097639100785739590167)
      ·
        refine ⟨57868646458651178609385251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38579097639100785739590167 57868646458651178609385251)
        ·
          refine ⟨86802969687976767914077877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57868646458651178609385251 86802969687976767914077877)
          ·
            refine ⟨8137778408247821991944801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86802969687976767914077877 8137778408247821991944801)
            ·
              refine ⟨6103333806185866493958601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8137778408247821991944801 6103333806185866493958601)
              ·
                refine ⟨4577500354639399870468951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6103333806185866493958601 4577500354639399870468951)
                ·
                  refine ⟨6866250531959099805703427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4577500354639399870468951 6866250531959099805703427)
                  ·
                    refine ⟨10299375797938649708555141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6866250531959099805703427 10299375797938649708555141)
                    ·
                      refine ⟨1931132962113496820354089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10299375797938649708555141 1931132962113496820354089)
                      ·
                        rfl

theorem cell23_3760868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_3760868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760868 prefixEnd_3760868 := by exact prefixLift 3760868
  have htrace : WordTrace (prefixWord ++ tailWord_3760868) baseStart_3760868 baseEnd_3760868 := by
    simpa [prefixWord, tailWord_3760868, baseEnd_3760868] using wordTrace_append hprefix tailTrace_3760868
  have hstable : (prefixWord ++ tailWord_3760868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760868).length < 2 ^ (prefixWord ++ tailWord_3760868).sum := by decide
  have hdescent : baseEnd_3760868 < baseStart_3760868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760981 : List Nat := [1, 3, 2, 2, 2, 1, 3, 2, 7]
def baseStart_3760981 : Nat := 118140960795 + 3760981 * 2 ^ 59
def prefixEnd_3760981 : Nat := 4983230072969 + 3 ^ 40 * 3760981 * 2
def baseEnd_3760981 : Nat := 214576776158606097582341

theorem tailTrace_3760981 : CollatzResearch.WordTrace tailWord_3760981 prefixEnd_3760981 214576776158606097582341 := by
  unfold tailWord_3760981
  simp only [CollatzResearch.WordTrace]
  refine ⟨137174246387615636261850797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91449497591743757507900531 137174246387615636261850797)
  ·
    refine ⟨51440342395355863598194049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137174246387615636261850797 51440342395355863598194049)
    ·
      refine ⟨38580256796516897698645537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51440342395355863598194049 38580256796516897698645537)
      ·
        refine ⟨28935192597387673273984153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38580256796516897698645537 28935192597387673273984153)
        ·
          refine ⟨21701394448040754955488115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28935192597387673273984153 21701394448040754955488115)
          ·
            refine ⟨32552091672061132433232173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21701394448040754955488115 32552091672061132433232173)
            ·
              refine ⟨12207034377022924662462065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32552091672061132433232173 12207034377022924662462065)
              ·
                refine ⟨9155275782767193496846549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12207034377022924662462065 9155275782767193496846549)
                ·
                  refine ⟨214576776158606097582341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9155275782767193496846549 214576776158606097582341)
                  ·
                    rfl

theorem cell23_3760981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 7].length) (baseStart_3760981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760981 prefixEnd_3760981 := by exact prefixLift 3760981
  have htrace : WordTrace (prefixWord ++ tailWord_3760981) baseStart_3760981 baseEnd_3760981 := by
    simpa [prefixWord, tailWord_3760981, baseEnd_3760981] using wordTrace_append hprefix tailTrace_3760981
  have hstable : (prefixWord ++ tailWord_3760981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760981).length < 2 ^ (prefixWord ++ tailWord_3760981).sum := by decide
  have hdescent : baseEnd_3760981 < baseStart_3760981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760991 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 1, 5, 3]
def baseStart_3760991 : Nat := 118140960795 + 3760991 * 2 ^ 59
def prefixEnd_3760991 : Nat := 4983230072969 + 3 ^ 40 * 3760991 * 2
def baseEnd_3760991 : Nat := 1931196120233999839116023

theorem tailTrace_3760991 : CollatzResearch.WordTrace tailWord_3760991 prefixEnd_3760991 1931196120233999839116023 := by
  unfold tailWord_3760991
  simp only [CollatzResearch.WordTrace]
  refine ⟨137174611117579407969714827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91449740745052938646476551 137174611117579407969714827)
  ·
    refine ⟨205761916676369111954572241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137174611117579407969714827 205761916676369111954572241)
    ·
      refine ⟨154321437507276833965929181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205761916676369111954572241 154321437507276833965929181)
      ·
        refine ⟨57870539065228812737223443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154321437507276833965929181 57870539065228812737223443)
        ·
          refine ⟨86805808597843219105835165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57870539065228812737223443 86805808597843219105835165)
          ·
            refine ⟨32552178224191207164688187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86805808597843219105835165 32552178224191207164688187)
            ·
              refine ⟨48828267336286810747032281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32552178224191207164688187 48828267336286810747032281)
              ·
                refine ⟨36621200502215108060274211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48828267336286810747032281 36621200502215108060274211)
                ·
                  refine ⟨54931800753322662090411317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36621200502215108060274211 54931800753322662090411317)
                  ·
                    refine ⟨5149856320623999570976061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54931800753322662090411317 5149856320623999570976061)
                    ·
                      refine ⟨1931196120233999839116023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5149856320623999570976061 1931196120233999839116023)
                      ·
                        rfl

theorem cell23_3760991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_3760991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3760991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3760991 prefixEnd_3760991 := by exact prefixLift 3760991
  have htrace : WordTrace (prefixWord ++ tailWord_3760991) baseStart_3760991 baseEnd_3760991 := by
    simpa [prefixWord, tailWord_3760991, baseEnd_3760991] using wordTrace_append hprefix tailTrace_3760991
  have hstable : (prefixWord ++ tailWord_3760991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760991).length < 2 ^ (prefixWord ++ tailWord_3760991).sum := by decide
  have hdescent : baseEnd_3760991 < baseStart_3760991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761011 : List Nat := [1, 1, 1, 2, 2, 1, 4, 4, 2, 5]
def baseStart_3761011 : Nat := 118140960795 + 3761011 * 2 ^ 59
def prefixEnd_3761011 : Nat := 4983230072969 + 3 ^ 40 * 3761011 * 2
def baseEnd_3761011 : Nat := 643735463282363253621977

theorem tailTrace_3761011 : CollatzResearch.WordTrace tailWord_3761011 prefixEnd_3761011 643735463282363253621977 := by
  unfold tailWord_3761011
  simp only [CollatzResearch.WordTrace]
  refine ⟨137175340577506951385442887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91450227051671300923628591 137175340577506951385442887)
  ·
    refine ⟨205763010866260427078164331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137175340577506951385442887 205763010866260427078164331)
    ·
      refine ⟨308644516299390640617246497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205763010866260427078164331 308644516299390640617246497)
      ·
        refine ⟨231483387224542980462934873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308644516299390640617246497 231483387224542980462934873)
        ·
          refine ⟨173612540418407235347201155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231483387224542980462934873 173612540418407235347201155)
          ·
            refine ⟨260418810627610853020801733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173612540418407235347201155 260418810627610853020801733)
            ·
              refine ⟨48828526992677034941400325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 260418810627610853020801733 48828526992677034941400325)
              ·
                refine ⟨9155348811126944051512561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48828526992677034941400325 9155348811126944051512561)
                ·
                  refine ⟨6866511608345208038634421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9155348811126944051512561 6866511608345208038634421)
                  ·
                    refine ⟨643735463282363253621977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6866511608345208038634421 643735463282363253621977)
                    ·
                      rfl

theorem cell23_3761011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 5].length) (baseStart_3761011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761011 prefixEnd_3761011 := by exact prefixLift 3761011
  have htrace : WordTrace (prefixWord ++ tailWord_3761011) baseStart_3761011 baseEnd_3761011 := by
    simpa [prefixWord, tailWord_3761011, baseEnd_3761011] using wordTrace_append hprefix tailTrace_3761011
  have hstable : (prefixWord ++ tailWord_3761011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761011).length < 2 ^ (prefixWord ++ tailWord_3761011).sum := by decide
  have hdescent : baseEnd_3761011 < baseStart_3761011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761021 : List Nat := [1, 4, 1, 1, 2, 1, 2, 3, 1, 2, 5]
def baseStart_3761021 : Nat := 118140960795 + 3761021 * 2 ^ 59
def prefixEnd_3761021 : Nat := 4983230072969 + 3 ^ 40 * 3761021 * 2
def baseEnd_3761021 : Nat := 1931211524653634721740885

theorem tailTrace_3761021 : CollatzResearch.WordTrace tailWord_3761021 prefixEnd_3761021 1931211524653634721740885 := by
  unfold tailWord_3761021
  simp only [CollatzResearch.WordTrace]
  refine ⟨137175705307470723093306917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91450470204980482062204611 137175705307470723093306917)
  ·
    refine ⟨25720444745150760579995047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137175705307470723093306917 25720444745150760579995047)
    ·
      refine ⟨38580667117726140869992571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25720444745150760579995047 38580667117726140869992571)
      ·
        refine ⟨57871000676589211304988857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38580667117726140869992571 57871000676589211304988857)
        ·
          refine ⟨43403250507441908478741643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57871000676589211304988857 43403250507441908478741643)
          ·
            refine ⟨65104875761162862718112465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43403250507441908478741643 65104875761162862718112465)
            ·
              refine ⟨48828656820872147038584349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65104875761162862718112465 48828656820872147038584349)
              ·
                refine ⟨18310746307827055139469131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48828656820872147038584349 18310746307827055139469131)
                ·
                  refine ⟨27466119461740582709203697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18310746307827055139469131 27466119461740582709203697)
                  ·
                    refine ⟨20599589596305437031902773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27466119461740582709203697 20599589596305437031902773)
                    ·
                      refine ⟨1931211524653634721740885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20599589596305437031902773 1931211524653634721740885)
                      ·
                        rfl

theorem cell23_3761021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_3761021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761021 prefixEnd_3761021 := by exact prefixLift 3761021
  have htrace : WordTrace (prefixWord ++ tailWord_3761021) baseStart_3761021 baseEnd_3761021 := by
    simpa [prefixWord, tailWord_3761021, baseEnd_3761021] using wordTrace_append hprefix tailTrace_3761021
  have hstable : (prefixWord ++ tailWord_3761021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761021).length < 2 ^ (prefixWord ++ tailWord_3761021).sum := by decide
  have hdescent : baseEnd_3761021 < baseStart_3761021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761026 : List Nat := [3, 4, 2, 2, 1, 2, 1, 1, 1, 4, 2]
def baseStart_3761026 : Nat := 118140960795 + 3761026 * 2 ^ 59
def prefixEnd_3761026 : Nat := 4983230072969 + 3 ^ 40 * 3761026 * 2
def baseEnd_3761026 : Nat := 1931214092056907202178363

theorem tailTrace_3761026 : CollatzResearch.WordTrace tailWord_3761026 prefixEnd_3761026 1931214092056907202178363 := by
  unfold tailWord_3761026
  simp only [CollatzResearch.WordTrace]
  refine ⟨34293971918113152236809733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91450591781635072631492621 34293971918113152236809733)
  ·
    refine ⟨6430119734646216044401825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34293971918113152236809733 6430119734646216044401825)
    ·
      refine ⟨4822589800984662033301369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6430119734646216044401825 4822589800984662033301369)
      ·
        refine ⟨3616942350738496524976027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4822589800984662033301369 3616942350738496524976027)
        ·
          refine ⟨5425413526107744787464041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3616942350738496524976027 5425413526107744787464041)
          ·
            refine ⟨4069060144580808590598031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5425413526107744787464041 4069060144580808590598031)
            ·
              refine ⟨6103590216871212885897047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4069060144580808590598031 6103590216871212885897047)
              ·
                refine ⟨9155385325306819328845571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6103590216871212885897047 9155385325306819328845571)
                ·
                  refine ⟨13733077987960228993268357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9155385325306819328845571 13733077987960228993268357)
                  ·
                    refine ⟨2574952122742542936237817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13733077987960228993268357 2574952122742542936237817)
                    ·
                      refine ⟨1931214092056907202178363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2574952122742542936237817 1931214092056907202178363)
                      ·
                        rfl

theorem cell23_3761026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_3761026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761026 prefixEnd_3761026 := by exact prefixLift 3761026
  have htrace : WordTrace (prefixWord ++ tailWord_3761026) baseStart_3761026 baseEnd_3761026 := by
    simpa [prefixWord, tailWord_3761026, baseEnd_3761026] using wordTrace_append hprefix tailTrace_3761026
  have hstable : (prefixWord ++ tailWord_3761026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761026).length < 2 ^ (prefixWord ++ tailWord_3761026).sum := by decide
  have hdescent : baseEnd_3761026 < baseStart_3761026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761068 : List Nat := [2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 3]
def baseStart_3761068 : Nat := 118140960795 + 3761068 * 2 ^ 59
def prefixEnd_3761068 : Nat := 4983230072969 + 3 ^ 40 * 3761068 * 2
def baseEnd_3761068 : Nat := 1931235658244396037853169

theorem tailTrace_3761068 : CollatzResearch.WordTrace tailWord_3761068 prefixEnd_3761068 1931235658244396037853169 := by
  unfold tailWord_3761068
  simp only [CollatzResearch.WordTrace]
  refine ⟨68588709769150225060133929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91451613025533633413511905 68588709769150225060133929)
  ·
    refine ⟨51441532326862668795100447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68588709769150225060133929 51441532326862668795100447)
    ·
      refine ⟨77162298490294003192650671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51441532326862668795100447 77162298490294003192650671)
      ·
        refine ⟨115743447735441004788976007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77162298490294003192650671 115743447735441004788976007)
        ·
          refine ⟨173615171603161507183464011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115743447735441004788976007 173615171603161507183464011)
          ·
            refine ⟨260422757404742260775196017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173615171603161507183464011 260422757404742260775196017)
            ·
              refine ⟨195317068053556695581397013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260422757404742260775196017 195317068053556695581397013)
              ·
                refine ⟨9155487565010470105377985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 195317068053556695581397013 9155487565010470105377985)
                ·
                  refine ⟨6866615673757852579033489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9155487565010470105377985 6866615673757852579033489)
                  ·
                    refine ⟨5149961755318389434275117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6866615673757852579033489 5149961755318389434275117)
                    ·
                      refine ⟨1931235658244396037853169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5149961755318389434275117 1931235658244396037853169)
                      ·
                        rfl

theorem cell23_3761068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 3].length) (baseStart_3761068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761068 prefixEnd_3761068 := by exact prefixLift 3761068
  have htrace : WordTrace (prefixWord ++ tailWord_3761068) baseStart_3761068 baseEnd_3761068 := by
    simpa [prefixWord, tailWord_3761068, baseEnd_3761068] using wordTrace_append hprefix tailTrace_3761068
  have hstable : (prefixWord ++ tailWord_3761068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761068).length < 2 ^ (prefixWord ++ tailWord_3761068).sum := by decide
  have hdescent : baseEnd_3761068 < baseStart_3761068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761088 : List Nat := [2, 1, 1, 2, 3, 4, 1, 3, 6]
def baseStart_3761088 : Nat := 118140960795 + 3761088 * 2 ^ 59
def prefixEnd_3761088 : Nat := 4983230072969 + 3 ^ 40 * 3761088 * 2
def baseEnd_3761088 : Nat := 214582880873053995511453

theorem tailTrace_3761088 : CollatzResearch.WordTrace tailWord_3761088 prefixEnd_3761088 214582880873053995511453 := by
  unfold tailWord_3761088
  simp only [CollatzResearch.WordTrace]
  refine ⟨68589074499113996767997959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91452099332151995690663945 68589074499113996767997959)
  ·
    refine ⟨102883611748670995151996939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68589074499113996767997959 102883611748670995151996939)
    ·
      refine ⟨154325417623006492727995409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102883611748670995151996939 154325417623006492727995409)
      ·
        refine ⟨115744063217254869545996557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154325417623006492727995409 115744063217254869545996557)
        ·
          refine ⟨43404023706470576079748709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115744063217254869545996557 43404023706470576079748709)
          ·
            refine ⟨8138254444963233014952883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43404023706470576079748709 8138254444963233014952883)
            ·
              refine ⟨12207381667444849522429325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8138254444963233014952883 12207381667444849522429325)
              ·
                refine ⟨4577768125291818570910997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12207381667444849522429325 4577768125291818570910997)
                ·
                  refine ⟨214582880873053995511453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4577768125291818570910997 214582880873053995511453)
                  ·
                    rfl

theorem cell23_3761088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 6].length) (baseStart_3761088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761088 prefixEnd_3761088 := by exact prefixLift 3761088
  have htrace : WordTrace (prefixWord ++ tailWord_3761088) baseStart_3761088 baseEnd_3761088 := by
    simpa [prefixWord, tailWord_3761088, baseEnd_3761088] using wordTrace_append hprefix tailTrace_3761088
  have hstable : (prefixWord ++ tailWord_3761088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761088).length < 2 ^ (prefixWord ++ tailWord_3761088).sum := by decide
  have hdescent : baseEnd_3761088 < baseStart_3761088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761111 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 5]
def baseStart_3761111 : Nat := 118140960795 + 3761111 * 2 ^ 59
def prefixEnd_3761111 : Nat := 4983230072969 + 3 ^ 40 * 3761111 * 2
def baseEnd_3761111 : Nat := 1931257737912539369615471

theorem tailTrace_3761111 : CollatzResearch.WordTrace tailWord_3761111 prefixEnd_3761111 1931257737912539369615471 := by
  unfold tailWord_3761111
  simp only [CollatzResearch.WordTrace]
  refine ⟨137178987877144668464083187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91452658584763112309388791 137178987877144668464083187)
  ·
    refine ⟨205768481815717002696124781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137178987877144668464083187 205768481815717002696124781)
    ·
      refine ⟨77163180680893876011046793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205768481815717002696124781 77163180680893876011046793)
      ·
        refine ⟨57872385510670407008285095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77163180680893876011046793 57872385510670407008285095)
        ·
          refine ⟨86808578266005610512427643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57872385510670407008285095 86808578266005610512427643)
          ·
            refine ⟨130212867399008415768641465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86808578266005610512427643 130212867399008415768641465)
            ·
              refine ⟨97659650549256311826481099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130212867399008415768641465 97659650549256311826481099)
              ·
                refine ⟨146489475823884467739721649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97659650549256311826481099 146489475823884467739721649)
                ·
                  refine ⟨109867106867913350804791237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146489475823884467739721649 109867106867913350804791237)
                  ·
                    refine ⟨20600082537733753275898357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109867106867913350804791237 20600082537733753275898357)
                    ·
                      refine ⟨1931257737912539369615471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20600082537733753275898357 1931257737912539369615471)
                      ·
                        rfl

theorem cell23_3761111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_3761111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761111 prefixEnd_3761111 := by exact prefixLift 3761111
  have htrace : WordTrace (prefixWord ++ tailWord_3761111) baseStart_3761111 baseEnd_3761111 := by
    simpa [prefixWord, tailWord_3761111, baseEnd_3761111] using wordTrace_append hprefix tailTrace_3761111
  have hstable : (prefixWord ++ tailWord_3761111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761111).length < 2 ^ (prefixWord ++ tailWord_3761111).sum := by decide
  have hdescent : baseEnd_3761111 < baseStart_3761111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761122 : List Nat := [3, 3, 3, 1, 1, 2, 2, 2, 6]
def baseStart_3761122 : Nat := 118140960795 + 3761122 * 2 ^ 59
def prefixEnd_3761122 : Nat := 4983230072969 + 3 ^ 40 * 3761122 * 2
def baseEnd_3761122 : Nat := 214584820688859869619769

theorem tailTrace_3761122 : CollatzResearch.WordTrace tailWord_3761122 prefixEnd_3761122 214584820688859869619769 := by
  unfold tailWord_3761122
  simp only [CollatzResearch.WordTrace]
  refine ⟨34294847270026204335683405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91452926053403211561822413 34294847270026204335683405)
  ·
    refine ⟨12860567726259826625881277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34294847270026204335683405 12860567726259826625881277)
    ·
      refine ⟨4822712897347434984705479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12860567726259826625881277 4822712897347434984705479)
      ·
        refine ⟨7234069346021152477058219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4822712897347434984705479 7234069346021152477058219)
        ·
          refine ⟨10851104019031728715587329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7234069346021152477058219 10851104019031728715587329)
          ·
            refine ⟨8138328014273796536690497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10851104019031728715587329 8138328014273796536690497)
            ·
              refine ⟨6103746010705347402517873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8138328014273796536690497 6103746010705347402517873)
              ·
                refine ⟨4577809508029010551888405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6103746010705347402517873 4577809508029010551888405)
                ·
                  refine ⟨214584820688859869619769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4577809508029010551888405 214584820688859869619769)
                  ·
                    rfl

theorem cell23_3761122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_3761122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761122 prefixEnd_3761122 := by exact prefixLift 3761122
  have htrace : WordTrace (prefixWord ++ tailWord_3761122) baseStart_3761122 baseEnd_3761122 := by
    simpa [prefixWord, tailWord_3761122, baseEnd_3761122] using wordTrace_append hprefix tailTrace_3761122
  have hstable : (prefixWord ++ tailWord_3761122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761122).length < 2 ^ (prefixWord ++ tailWord_3761122).sum := by decide
  have hdescent : baseEnd_3761122 < baseStart_3761122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761148 : List Nat := [2, 2, 2, 1, 2, 3, 1, 3, 1, 6]
def baseStart_3761148 : Nat := 118140960795 + 3761148 * 2 ^ 59
def prefixEnd_3761148 : Nat := 4983230072969 + 3 ^ 40 * 3761148 * 2
def baseEnd_3761148 : Nat := 643758912232251908284267

theorem tailTrace_3761148 : CollatzResearch.WordTrace tailWord_3761148 prefixEnd_3761148 643758912232251908284267 := by
  unfold tailWord_3761148
  simp only [CollatzResearch.WordTrace]
  refine ⟨68590168689005311891590049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91453558252007082522120065 68590168689005311891590049)
  ·
    refine ⟨51442626516753983918692537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68590168689005311891590049 51442626516753983918692537)
    ·
      refine ⟨38581969887565487939019403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51442626516753983918692537 38581969887565487939019403)
      ·
        refine ⟨57872954831348231908529105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38581969887565487939019403 57872954831348231908529105)
        ·
          refine ⟨43404716123511173931396829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57872954831348231908529105 43404716123511173931396829)
          ·
            refine ⟨16276768546316690224273811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43404716123511173931396829 16276768546316690224273811)
            ·
              refine ⟨24415152819475035336410717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16276768546316690224273811 24415152819475035336410717)
              ·
                refine ⟨9155682307303138251154019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24415152819475035336410717 9155682307303138251154019)
                ·
                  refine ⟨13733523460954707376731029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9155682307303138251154019 13733523460954707376731029)
                  ·
                    refine ⟨643758912232251908284267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13733523460954707376731029 643758912232251908284267)
                    ·
                      rfl

theorem cell23_3761148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_3761148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761148 prefixEnd_3761148 := by exact prefixLift 3761148
  have htrace : WordTrace (prefixWord ++ tailWord_3761148) baseStart_3761148 baseEnd_3761148 := by
    simpa [prefixWord, tailWord_3761148, baseEnd_3761148] using wordTrace_append hprefix tailTrace_3761148
  have hstable : (prefixWord ++ tailWord_3761148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761148).length < 2 ^ (prefixWord ++ tailWord_3761148).sum := by decide
  have hdescent : baseEnd_3761148 < baseStart_3761148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761161 : List Nat := [1, 2, 1, 1, 3, 1, 1, 13]
def baseStart_3761161 : Nat := 118140960795 + 3761161 * 2 ^ 59
def prefixEnd_3761161 : Nat := 4983230072969 + 3 ^ 40 * 3761161 * 2
def baseEnd_3761161 : Nat := 71529015257232006444083

theorem tailTrace_3761161 : CollatzResearch.WordTrace tailWord_3761161 prefixEnd_3761161 71529015257232006444083 := by
  unfold tailWord_3761161
  simp only [CollatzResearch.WordTrace]
  refine ⟨137180811526963527003403337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91453874351309018002268891 137180811526963527003403337)
  ·
    refine ⟨102885608645222645252552503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137180811526963527003403337 102885608645222645252552503)
    ·
      refine ⟨154328412967833967878828755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102885608645222645252552503 154328412967833967878828755)
      ·
        refine ⟨231492619451750951818243133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154328412967833967878828755 231492619451750951818243133)
        ·
          refine ⟨86809732294406606931841175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231492619451750951818243133 86809732294406606931841175)
          ·
            refine ⟨130214598441609910397761763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86809732294406606931841175 130214598441609910397761763)
            ·
              refine ⟨195321897662414865596642645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130214598441609910397761763 195321897662414865596642645)
              ·
                refine ⟨71529015257232006444083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 195321897662414865596642645 71529015257232006444083)
                ·
                  rfl

theorem cell23_3761161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 13].length) (baseStart_3761161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761161 prefixEnd_3761161 := by exact prefixLift 3761161
  have htrace : WordTrace (prefixWord ++ tailWord_3761161) baseStart_3761161 baseEnd_3761161 := by
    simpa [prefixWord, tailWord_3761161, baseEnd_3761161] using wordTrace_append hprefix tailTrace_3761161
  have hstable : (prefixWord ++ tailWord_3761161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761161).length < 2 ^ (prefixWord ++ tailWord_3761161).sum := by decide
  have hdescent : baseEnd_3761161 < baseStart_3761161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761189 : List Nat := [1, 3, 1, 2, 2, 2, 1, 6, 1, 2, 2]
def baseStart_3761189 : Nat := 118140960795 + 3761189 * 2 ^ 59
def prefixEnd_3761189 : Nat := 4983230072969 + 3 ^ 40 * 3761189 * 2
def baseEnd_3761189 : Nat := 1931297789403590064440113

theorem tailTrace_3761189 : CollatzResearch.WordTrace tailWord_3761189 prefixEnd_3761189 1931297789403590064440113 := by
  unfold tailWord_3761189
  simp only [CollatzResearch.WordTrace]
  refine ⟨137181832770862087785422621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91454555180574725190281747 137181832770862087785422621)
  ·
    refine ⟨51443187289073282919533483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137181832770862087785422621 51443187289073282919533483)
    ·
      refine ⟨77164780933609924379300225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51443187289073282919533483 77164780933609924379300225)
      ·
        refine ⟨57873585700207443284475169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77164780933609924379300225 57873585700207443284475169)
        ·
          refine ⟨43405189275155582463356377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57873585700207443284475169 43405189275155582463356377)
          ·
            refine ⟨32553891956366686847517283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43405189275155582463356377 32553891956366686847517283)
            ·
              refine ⟨48830837934550030271275925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32553891956366686847517283 48830837934550030271275925)
              ·
                refine ⟨2288945528182032668966059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48830837934550030271275925 2288945528182032668966059)
                ·
                  refine ⟨3433418292273049003449089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2288945528182032668966059 3433418292273049003449089)
                  ·
                    refine ⟨2575063719204786752586817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3433418292273049003449089 2575063719204786752586817)
                    ·
                      refine ⟨1931297789403590064440113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2575063719204786752586817 1931297789403590064440113)
                      ·
                        rfl

theorem cell23_3761189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 6, 1, 2, 2].length) (baseStart_3761189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761189 prefixEnd_3761189 := by exact prefixLift 3761189
  have htrace : WordTrace (prefixWord ++ tailWord_3761189) baseStart_3761189 baseEnd_3761189 := by
    simpa [prefixWord, tailWord_3761189, baseEnd_3761189] using wordTrace_append hprefix tailTrace_3761189
  have hstable : (prefixWord ++ tailWord_3761189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761189).length < 2 ^ (prefixWord ++ tailWord_3761189).sum := by decide
  have hdescent : baseEnd_3761189 < baseStart_3761189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761228 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 1, 5, 4]
def baseStart_3761228 : Nat := 118140960795 + 3761228 * 2 ^ 59
def prefixEnd_3761228 : Nat := 4983230072969 + 3 ^ 40 * 3761228 * 2
def baseEnd_3761228 : Nat := 1931317815149115411852433

theorem tailTrace_3761228 : CollatzResearch.WordTrace tailWord_3761228 prefixEnd_3761228 1931317815149115411852433 := by
  unfold tailWord_3761228
  simp only [CollatzResearch.WordTrace]
  refine ⟨68591627608860398723046169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91455503478480531630728225 68591627608860398723046169)
  ·
    refine ⟨51443720706645299042284627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68591627608860398723046169 51443720706645299042284627)
    ·
      refine ⟨77165581059967948563426941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51443720706645299042284627 77165581059967948563426941)
      ·
        refine ⟨28937092897487980711285103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77165581059967948563426941 28937092897487980711285103)
        ·
          refine ⟨43405639346231971066927655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28937092897487980711285103 43405639346231971066927655)
          ·
            refine ⟨65108459019347956600391483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43405639346231971066927655 65108459019347956600391483)
            ·
              refine ⟨97662688529021934900587225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65108459019347956600391483 97662688529021934900587225)
              ·
                refine ⟨73247016396766451175440419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97662688529021934900587225 73247016396766451175440419)
                ·
                  refine ⟨109870524595149676763160629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73247016396766451175440419 109870524595149676763160629)
                  ·
                    refine ⟨10300361680795282196546309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109870524595149676763160629 10300361680795282196546309)
                    ·
                      refine ⟨1931317815149115411852433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10300361680795282196546309 1931317815149115411852433)
                      ·
                        rfl

theorem cell23_3761228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_3761228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761228 prefixEnd_3761228 := by exact prefixLift 3761228
  have htrace : WordTrace (prefixWord ++ tailWord_3761228) baseStart_3761228 baseEnd_3761228 := by
    simpa [prefixWord, tailWord_3761228, baseEnd_3761228] using wordTrace_append hprefix tailTrace_3761228
  have hstable : (prefixWord ++ tailWord_3761228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761228).length < 2 ^ (prefixWord ++ tailWord_3761228).sum := by decide
  have hdescent : baseEnd_3761228 < baseStart_3761228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761248 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 5]
def baseStart_3761248 : Nat := 118140960795 + 3761248 * 2 ^ 59
def prefixEnd_3761248 : Nat := 4983230072969 + 3 ^ 40 * 3761248 * 2
def baseEnd_3761248 : Nat := 1931328084762205333602341

theorem tailTrace_3761248 : CollatzResearch.WordTrace tailWord_3761248 prefixEnd_3761248 1931328084762205333602341 := by
  unfold tailWord_3761248
  simp only [CollatzResearch.WordTrace]
  refine ⟨68591992338824170430910199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91455989785098893907880265 68591992338824170430910199)
  ·
    refine ⟨102887988508236255646365299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68591992338824170430910199 102887988508236255646365299)
    ·
      refine ⟨154331982762354383469547949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102887988508236255646365299 154331982762354383469547949)
      ·
        refine ⟨57874493535882893801080481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154331982762354383469547949 57874493535882893801080481)
        ·
          refine ⟨43405870151912170350810361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57874493535882893801080481 43405870151912170350810361)
          ·
            refine ⟨32554402613934127763107771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43405870151912170350810361 32554402613934127763107771)
            ·
              refine ⟨48831603920901191644661657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32554402613934127763107771 48831603920901191644661657)
              ·
                refine ⟨36623702940675893733496243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48831603920901191644661657 36623702940675893733496243)
                ·
                  refine ⟨54935554411013840600244365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36623702940675893733496243 54935554411013840600244365)
                  ·
                    refine ⟨20600832904130190225091637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54935554411013840600244365 20600832904130190225091637)
                    ·
                      refine ⟨1931328084762205333602341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20600832904130190225091637 1931328084762205333602341)
                      ·
                        rfl

theorem cell23_3761248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_3761248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761248 prefixEnd_3761248 := by exact prefixLift 3761248
  have htrace : WordTrace (prefixWord ++ tailWord_3761248) baseStart_3761248 baseEnd_3761248 := by
    simpa [prefixWord, tailWord_3761248, baseEnd_3761248] using wordTrace_append hprefix tailTrace_3761248
  have hstable : (prefixWord ++ tailWord_3761248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761248).length < 2 ^ (prefixWord ++ tailWord_3761248).sum := by decide
  have hdescent : baseEnd_3761248 < baseStart_3761248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761256 : List Nat := [2, 1, 4, 4, 1, 1, 1, 3, 2, 1, 3]
def baseStart_3761256 : Nat := 118140960795 + 3761256 * 2 ^ 59
def prefixEnd_3761256 : Nat := 4983230072969 + 3 ^ 40 * 3761256 * 2
def baseEnd_3761256 : Nat := 1931332192607441302302305

theorem tailTrace_3761256 : CollatzResearch.WordTrace tailWord_3761256 prefixEnd_3761256 1931332192607441302302305 := by
  unfold tailWord_3761256
  simp only [CollatzResearch.WordTrace]
  refine ⟨68592138230809679114055811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91456184307746238818741081 68592138230809679114055811)
  ·
    refine ⟨102888207346214518671083717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68592138230809679114055811 102888207346214518671083717)
    ·
      refine ⟨19291538877415222250828197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102888207346214518671083717 19291538877415222250828197)
      ·
        refine ⟨3617163539515354172030287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19291538877415222250828197 3617163539515354172030287)
        ·
          refine ⟨5425745309273031258045431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3617163539515354172030287 5425745309273031258045431)
          ·
            refine ⟨8138617963909546887068147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5425745309273031258045431 8138617963909546887068147)
            ·
              refine ⟨12207926945864320330602221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8138617963909546887068147 12207926945864320330602221)
              ·
                refine ⟨4577972604699120123975833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12207926945864320330602221 4577972604699120123975833)
                ·
                  refine ⟨3433479453524340092981875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4577972604699120123975833 3433479453524340092981875)
                  ·
                    refine ⟨5150219180286510139472813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3433479453524340092981875 5150219180286510139472813)
                    ·
                      refine ⟨1931332192607441302302305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5150219180286510139472813 1931332192607441302302305)
                      ·
                        rfl

theorem cell23_3761256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_3761256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761256 prefixEnd_3761256 := by exact prefixLift 3761256
  have htrace : WordTrace (prefixWord ++ tailWord_3761256) baseStart_3761256 baseEnd_3761256 := by
    simpa [prefixWord, tailWord_3761256, baseEnd_3761256] using wordTrace_append hprefix tailTrace_3761256
  have hstable : (prefixWord ++ tailWord_3761256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761256).length < 2 ^ (prefixWord ++ tailWord_3761256).sum := by decide
  have hdescent : baseEnd_3761256 < baseStart_3761256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761328 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 2, 8]
def baseStart_3761328 : Nat := 118140960795 + 3761328 * 2 ^ 59
def prefixEnd_3761328 : Nat := 4983230072969 + 3 ^ 40 * 3761328 * 2
def baseEnd_3761328 : Nat := 643789721071521673533991

theorem tailTrace_3761328 : CollatzResearch.WordTrace tailWord_3761328 prefixEnd_3761328 643789721071521673533991 := by
  unfold tailWord_3761328
  simp only [CollatzResearch.WordTrace]
  refine ⟨68593451258679257262366319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91457935011572343016488425 68593451258679257262366319)
  ·
    refine ⟨102890176888018885893549479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68593451258679257262366319 102890176888018885893549479)
    ·
      refine ⟨154335265332028328840324219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102890176888018885893549479 154335265332028328840324219)
      ·
        refine ⟨231502897998042493260486329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154335265332028328840324219 231502897998042493260486329)
        ·
          refine ⟨173627173498531869945364747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231502897998042493260486329 173627173498531869945364747)
          ·
            refine ⟨260440760247797804918047121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173627173498531869945364747 260440760247797804918047121)
            ·
              refine ⟨195330570185848353688535341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260440760247797804918047121 195330570185848353688535341)
              ·
                refine ⟨73248963819693132633200753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195330570185848353688535341 73248963819693132633200753)
                ·
                  refine ⟨54936722864769849474900565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73248963819693132633200753 54936722864769849474900565)
                  ·
                    refine ⟨643789721071521673533991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54936722864769849474900565 643789721071521673533991)
                    ·
                      rfl

theorem cell23_3761328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 2, 8].length) (baseStart_3761328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761328 prefixEnd_3761328 := by exact prefixLift 3761328
  have htrace : WordTrace (prefixWord ++ tailWord_3761328) baseStart_3761328 baseEnd_3761328 := by
    simpa [prefixWord, tailWord_3761328, baseEnd_3761328] using wordTrace_append hprefix tailTrace_3761328
  have hstable : (prefixWord ++ tailWord_3761328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761328).length < 2 ^ (prefixWord ++ tailWord_3761328).sum := by decide
  have hdescent : baseEnd_3761328 < baseStart_3761328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761335 : List Nat := [1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 4]
def baseStart_3761335 : Nat := 118140960795 + 3761335 * 2 ^ 59
def prefixEnd_3761335 : Nat := 4983230072969 + 3 ^ 40 * 3761335 * 2
def baseEnd_3761335 : Nat := 1931372757579146493214441

theorem tailTrace_3761335 : CollatzResearch.WordTrace tailWord_3761335 prefixEnd_3761335 1931372757579146493214441 := by
  unfold tailWord_3761335
  simp only [CollatzResearch.WordTrace]
  refine ⟨137187157828333154720237459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91458105218888769813491639 137187157828333154720237459)
  ·
    refine ⟨205780736742499732080356189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137187157828333154720237459 205780736742499732080356189)
    ·
      refine ⟨77167776278437399530133571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205780736742499732080356189 77167776278437399530133571)
      ·
        refine ⟨115751664417656099295200357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77167776278437399530133571 115751664417656099295200357)
        ·
          refine ⟨21703437078310518617850067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115751664417656099295200357 21703437078310518617850067)
          ·
            refine ⟨32555155617465777926775101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21703437078310518617850067 32555155617465777926775101)
            ·
              refine ⟨12208183356549666722540663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32555155617465777926775101 12208183356549666722540663)
              ·
                refine ⟨18312275034824500083810995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12208183356549666722540663 18312275034824500083810995)
                ·
                  refine ⟨27468412552236750125716493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18312275034824500083810995 27468412552236750125716493)
                  ·
                    refine ⟨10300654707088781297143685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27468412552236750125716493 10300654707088781297143685)
                    ·
                      refine ⟨1931372757579146493214441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10300654707088781297143685 1931372757579146493214441)
                      ·
                        rfl

theorem cell23_3761335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_3761335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761335 prefixEnd_3761335 := by exact prefixLift 3761335
  have htrace : WordTrace (prefixWord ++ tailWord_3761335) baseStart_3761335 baseEnd_3761335 := by
    simpa [prefixWord, tailWord_3761335, baseEnd_3761335] using wordTrace_append hprefix tailTrace_3761335
  have hstable : (prefixWord ++ tailWord_3761335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761335).length < 2 ^ (prefixWord ++ tailWord_3761335).sum := by decide
  have hdescent : baseEnd_3761335 < baseStart_3761335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761352 : List Nat := [2, 1, 3, 1, 2, 1, 3, 2, 2, 4, 2]
def baseStart_3761352 : Nat := 118140960795 + 3761352 * 2 ^ 59
def prefixEnd_3761352 : Nat := 4983230072969 + 3 ^ 40 * 3761352 * 2
def baseEnd_3761352 : Nat := 1931381486750272926701863

theorem tailTrace_3761352 : CollatzResearch.WordTrace tailWord_3761352 prefixEnd_3761352 1931381486750272926701863 := by
  unfold tailWord_3761352
  simp only [CollatzResearch.WordTrace]
  refine ⟨68593888934635783311803155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91458518579514377749070873 68593888934635783311803155)
  ·
    refine ⟨102890833401953674967704733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68593888934635783311803155 102890833401953674967704733)
    ·
      refine ⟨38584062525732628112889275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102890833401953674967704733 38584062525732628112889275)
      ·
        refine ⟨57876093788598942169333913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38584062525732628112889275 57876093788598942169333913)
        ·
          refine ⟨43407070341449206627000435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57876093788598942169333913 43407070341449206627000435)
          ·
            refine ⟨65110605512173809940500653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43407070341449206627000435 65110605512173809940500653)
            ·
              refine ⟨24416477067065178727687745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65110605512173809940500653 24416477067065178727687745)
              ·
                refine ⟨18312357800298884045765809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24416477067065178727687745 18312357800298884045765809)
                ·
                  refine ⟨13734268350224163034324357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18312357800298884045765809 13734268350224163034324357)
                  ·
                    refine ⟨2575175315667030568935817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13734268350224163034324357 2575175315667030568935817)
                    ·
                      refine ⟨1931381486750272926701863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2575175315667030568935817 1931381486750272926701863)
                      ·
                        rfl

theorem cell23_3761352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 2, 4, 2].length) (baseStart_3761352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761352 prefixEnd_3761352 := by exact prefixLift 3761352
  have htrace : WordTrace (prefixWord ++ tailWord_3761352) baseStart_3761352 baseEnd_3761352 := by
    simpa [prefixWord, tailWord_3761352, baseEnd_3761352] using wordTrace_append hprefix tailTrace_3761352
  have hstable : (prefixWord ++ tailWord_3761352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761352).length < 2 ^ (prefixWord ++ tailWord_3761352).sum := by decide
  have hdescent : baseEnd_3761352 < baseStart_3761352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761375 : List Nat := [1, 1, 2, 3, 2, 1, 2, 5, 6]
def baseStart_3761375 : Nat := 118140960795 + 3761375 * 2 ^ 59
def prefixEnd_3761375 : Nat := 4983230072969 + 3 ^ 40 * 3761375 * 2
def baseEnd_3761375 : Nat := 214599255200591815190473

theorem tailTrace_3761375 : CollatzResearch.WordTrace tailWord_3761375 prefixEnd_3761375 214599255200591815190473 := by
  unfold tailWord_3761375
  simp only [CollatzResearch.WordTrace]
  refine ⟨137188616748188241551693579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91459077832125494367795719 137188616748188241551693579)
  ·
    refine ⟨205782925122282362327540369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137188616748188241551693579 205782925122282362327540369)
    ·
      refine ⟨154337193841711771745655277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205782925122282362327540369 154337193841711771745655277)
      ·
        refine ⟨57876447690641914404620729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154337193841711771745655277 57876447690641914404620729)
        ·
          refine ⟨43407335767981435803465547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57876447690641914404620729 43407335767981435803465547)
          ·
            refine ⟨65111003651972153705198321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43407335767981435803465547 65111003651972153705198321)
            ·
              refine ⟨48833252738979115278898741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65111003651972153705198321 48833252738979115278898741)
              ·
                refine ⟨4578117444279292057396757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48833252738979115278898741 4578117444279292057396757)
                ·
                  refine ⟨214599255200591815190473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4578117444279292057396757 214599255200591815190473)
                  ·
                    rfl

theorem cell23_3761375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 6].length) (baseStart_3761375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761375 prefixEnd_3761375 := by exact prefixLift 3761375
  have htrace : WordTrace (prefixWord ++ tailWord_3761375) baseStart_3761375 baseEnd_3761375 := by
    simpa [prefixWord, tailWord_3761375, baseEnd_3761375] using wordTrace_append hprefix tailTrace_3761375
  have hstable : (prefixWord ++ tailWord_3761375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761375).length < 2 ^ (prefixWord ++ tailWord_3761375).sum := by decide
  have hdescent : baseEnd_3761375 < baseStart_3761375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761405 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 7, 5]
def baseStart_3761405 : Nat := 118140960795 + 3761405 * 2 ^ 59
def prefixEnd_3761405 : Nat := 4983230072969 + 3 ^ 40 * 3761405 * 2
def baseEnd_3761405 : Nat := 643802900408320406446373

theorem tailTrace_3761405 : CollatzResearch.WordTrace tailWord_3761405 prefixEnd_3761405 643802900408320406446373 := by
  unfold tailWord_3761405
  simp only [CollatzResearch.WordTrace]
  refine ⟨137189710938079556675285669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91459807292053037783523779 137189710938079556675285669)
  ·
    refine ⟨25723070800889916876616063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137189710938079556675285669 25723070800889916876616063)
    ·
      refine ⟨38584606201334875314924095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25723070800889916876616063 38584606201334875314924095)
      ·
        refine ⟨57876909302002312972386143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38584606201334875314924095 57876909302002312972386143)
        ·
          refine ⟨86815363953003469458579215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57876909302002312972386143 86815363953003469458579215)
          ·
            refine ⟨130223045929505204187868823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86815363953003469458579215 130223045929505204187868823)
            ·
              refine ⟨195334568894257806281803235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130223045929505204187868823 195334568894257806281803235)
              ·
                refine ⟨293001853341386709422704853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195334568894257806281803235 293001853341386709422704853)
                ·
                  refine ⟨6867230937688751002094645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 293001853341386709422704853 6867230937688751002094645)
                  ·
                    refine ⟨643802900408320406446373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6867230937688751002094645 643802900408320406446373)
                    ·
                      rfl

theorem cell23_3761405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_3761405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761405 prefixEnd_3761405 := by exact prefixLift 3761405
  have htrace : WordTrace (prefixWord ++ tailWord_3761405) baseStart_3761405 baseEnd_3761405 := by
    simpa [prefixWord, tailWord_3761405, baseEnd_3761405] using wordTrace_append hprefix tailTrace_3761405
  have hstable : (prefixWord ++ tailWord_3761405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761405).length < 2 ^ (prefixWord ++ tailWord_3761405).sum := by decide
  have hdescent : baseEnd_3761405 < baseStart_3761405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761419 : List Nat := [1, 1, 1, 1, 5, 3, 3, 1, 3, 1, 3]
def baseStart_3761419 : Nat := 118140960795 + 3761419 * 2 ^ 59
def prefixEnd_3761419 : Nat := 4983230072969 + 3 ^ 40 * 3761419 * 2
def baseEnd_3761419 : Nat := 1931415889954124164564055

theorem tailTrace_3761419 : CollatzResearch.WordTrace tailWord_3761419 prefixEnd_3761419 1931415889954124164564055 := by
  unfold tailWord_3761419
  simp only [CollatzResearch.WordTrace]
  refine ⟨137190221560028837066295311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91460147706685891377530207 137190221560028837066295311)
  ·
    refine ⟨205785332340043255599442967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137190221560028837066295311 205785332340043255599442967)
    ·
      refine ⟨308677998510064883399164451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205785332340043255599442967 308677998510064883399164451)
      ·
        refine ⟨463016997765097325098746677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308677998510064883399164451 463016997765097325098746677)
        ·
          refine ⟨43407843540477874228007501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 463016997765097325098746677 43407843540477874228007501)
          ·
            refine ⟨16277941327679202835502813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43407843540477874228007501 16277941327679202835502813)
            ·
              refine ⟨6104227997879701063313555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16277941327679202835502813 6104227997879701063313555)
              ·
                refine ⟨9156341996819551594970333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6104227997879701063313555 9156341996819551594970333)
                ·
                  refine ⟨3433628248807331848113875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9156341996819551594970333 3433628248807331848113875)
                  ·
                    refine ⟨5150442373210997772170813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3433628248807331848113875 5150442373210997772170813)
                    ·
                      refine ⟨1931415889954124164564055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5150442373210997772170813 1931415889954124164564055)
                      ·
                        rfl

theorem cell23_3761419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 3, 1, 3].length) (baseStart_3761419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761419 prefixEnd_3761419 := by exact prefixLift 3761419
  have htrace : WordTrace (prefixWord ++ tailWord_3761419) baseStart_3761419 baseEnd_3761419 := by
    simpa [prefixWord, tailWord_3761419, baseEnd_3761419] using wordTrace_append hprefix tailTrace_3761419
  have hstable : (prefixWord ++ tailWord_3761419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761419).length < 2 ^ (prefixWord ++ tailWord_3761419).sum := by decide
  have hdescent : baseEnd_3761419 < baseStart_3761419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761426 : List Nat := [3, 2, 4, 2, 1, 1, 1, 3, 6]
def baseStart_3761426 : Nat := 118140960795 + 3761426 * 2 ^ 59
def prefixEnd_3761426 : Nat := 4983230072969 + 3 ^ 40 * 3761426 * 2
def baseEnd_3761426 : Nat := 214602164924300626352947

theorem tailTrace_3761426 : CollatzResearch.WordTrace tailWord_3761426 prefixEnd_3761426 214602164924300626352947 := by
  unfold tailWord_3761426
  simp only [CollatzResearch.WordTrace]
  refine ⟨34297619217750869315450033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91460317914002318174533421 34297619217750869315450033)
  ·
    refine ⟨25723214413313151986587525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34297619217750869315450033 25723214413313151986587525)
    ·
      refine ⟨4823102702496215997485161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25723214413313151986587525 4823102702496215997485161)
      ·
        refine ⟨3617327026872161998113871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4823102702496215997485161 3617327026872161998113871)
        ·
          refine ⟨5425990540308242997170807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3617327026872161998113871 5425990540308242997170807)
          ·
            refine ⟨8138985810462364495756211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5425990540308242997170807 8138985810462364495756211)
            ·
              refine ⟨12208478715693546743634317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8138985810462364495756211 12208478715693546743634317)
              ·
                refine ⟨4578179518385080028862869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12208478715693546743634317 4578179518385080028862869)
                ·
                  refine ⟨214602164924300626352947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4578179518385080028862869 214602164924300626352947)
                  ·
                    rfl

theorem cell23_3761426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 6].length) (baseStart_3761426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761426 prefixEnd_3761426 := by exact prefixLift 3761426
  have htrace : WordTrace (prefixWord ++ tailWord_3761426) baseStart_3761426 baseEnd_3761426 := by
    simpa [prefixWord, tailWord_3761426, baseEnd_3761426] using wordTrace_append hprefix tailTrace_3761426
  have hstable : (prefixWord ++ tailWord_3761426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761426).length < 2 ^ (prefixWord ++ tailWord_3761426).sum := by decide
  have hdescent : baseEnd_3761426 < baseStart_3761426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761435 : List Nat := [1, 1, 1, 1, 1, 1, 5, 5, 1, 6]
def baseStart_3761435 : Nat := 118140960795 + 3761435 * 2 ^ 59
def prefixEnd_3761435 : Nat := 4983230072969 + 3 ^ 40 * 3761435 * 2
def baseEnd_3761435 : Nat := 643808035214865367321327

theorem tailTrace_3761435 : CollatzResearch.WordTrace tailWord_3761435 prefixEnd_3761435 643808035214865367321327 := by
  unfold tailWord_3761435
  simp only [CollatzResearch.WordTrace]
  refine ⟨137190805127970871798877759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91460536751980581199251839 137190805127970871798877759)
  ·
    refine ⟨205786207691956307698316639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137190805127970871798877759 205786207691956307698316639)
    ·
      refine ⟨308679311537934461547474959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205786207691956307698316639 308679311537934461547474959)
      ·
        refine ⟨463018967306901692321212439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308679311537934461547474959 463018967306901692321212439)
        ·
          refine ⟨694528450960352538481818659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463018967306901692321212439 694528450960352538481818659)
          ·
            refine ⟨1041792676440528807722727989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 694528450960352538481818659 1041792676440528807722727989)
            ·
              refine ⟨97668063416299575724005749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1041792676440528807722727989 97668063416299575724005749)
              ·
                refine ⟨9156380945278085224125539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97668063416299575724005749 9156380945278085224125539)
                ·
                  refine ⟨13734571417917127836188309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9156380945278085224125539 13734571417917127836188309)
                  ·
                    refine ⟨643808035214865367321327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13734571417917127836188309 643808035214865367321327)
                    ·
                      rfl

theorem cell23_3761435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 6].length) (baseStart_3761435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761435 prefixEnd_3761435 := by exact prefixLift 3761435
  have htrace : WordTrace (prefixWord ++ tailWord_3761435) baseStart_3761435 baseEnd_3761435 := by
    simpa [prefixWord, tailWord_3761435, baseEnd_3761435] using wordTrace_append hprefix tailTrace_3761435
  have hstable : (prefixWord ++ tailWord_3761435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761435).length < 2 ^ (prefixWord ++ tailWord_3761435).sum := by decide
  have hdescent : baseEnd_3761435 < baseStart_3761435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761465 : List Nat := [1, 2, 1, 6, 13]
def baseStart_3761465 : Nat := 118140960795 + 3761465 * 2 ^ 59
def prefixEnd_3761465 : Nat := 4983230072969 + 3 ^ 40 * 3761465 * 2
def baseEnd_3761465 : Nat := 2649436913668355260067

theorem tailTrace_3761465 : CollatzResearch.WordTrace tailWord_3761465 prefixEnd_3761465 2649436913668355260067 := by
  unfold tailWord_3761465
  simp only [CollatzResearch.WordTrace]
  refine ⟨137191899317862186922469849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91461266211908124614979899 137191899317862186922469849)
  ·
    refine ⟨102893924488396640191852387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137191899317862186922469849 102893924488396640191852387)
    ·
      refine ⟨154340886732594960287778581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102893924488396640191852387 154340886732594960287778581)
      ·
        refine ⟨7234729065590388763489621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 154340886732594960287778581 7234729065590388763489621)
        ·
          refine ⟨2649436913668355260067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 7234729065590388763489621 2649436913668355260067)
          ·
            rfl

theorem cell23_3761465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 13].length) (baseStart_3761465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761465 prefixEnd_3761465 := by exact prefixLift 3761465
  have htrace : WordTrace (prefixWord ++ tailWord_3761465) baseStart_3761465 baseEnd_3761465 := by
    simpa [prefixWord, tailWord_3761465, baseEnd_3761465] using wordTrace_append hprefix tailTrace_3761465
  have hstable : (prefixWord ++ tailWord_3761465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761465).length < 2 ^ (prefixWord ++ tailWord_3761465).sum := by decide
  have hdescent : baseEnd_3761465 < baseStart_3761465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761509 : List Nat := [1, 3, 1, 3, 1, 2, 2, 2, 4, 1, 3]
def baseStart_3761509 : Nat := 118140960795 + 3761509 * 2 ^ 59
def prefixEnd_3761509 : Nat := 4983230072969 + 3 ^ 40 * 3761509 * 2
def baseEnd_3761509 : Nat := 1931462103213028812438641

theorem tailTrace_3761509 : CollatzResearch.WordTrace tailWord_3761509 prefixEnd_3761509 1931462103213028812438641 := by
  unfold tailWord_3761509
  simp only [CollatzResearch.WordTrace]
  refine ⟨137193504129702782437071581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91462336086468521624714387 137193504129702782437071581)
  ·
    refine ⟨51447564048638543413901843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137193504129702782437071581 51447564048638543413901843)
    ·
      refine ⟨77171346072957815120852765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51447564048638543413901843 77171346072957815120852765)
      ·
        refine ⟨28939254777359180670319787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77171346072957815120852765 28939254777359180670319787)
        ·
          refine ⟨43408882166038771005479681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28939254777359180670319787 43408882166038771005479681)
          ·
            refine ⟨32556661624529078254109761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43408882166038771005479681 32556661624529078254109761)
            ·
              refine ⟨24417496218396808690582321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32556661624529078254109761 24417496218396808690582321)
              ·
                refine ⟨18313122163797606517936741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24417496218396808690582321 18313122163797606517936741)
                ·
                  refine ⟨3433710405712051222113139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18313122163797606517936741 3433710405712051222113139)
                  ·
                    refine ⟨5150565608568076833169709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3433710405712051222113139 5150565608568076833169709)
                    ·
                      refine ⟨1931462103213028812438641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5150565608568076833169709 1931462103213028812438641)
                      ·
                        rfl

theorem cell23_3761509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_3761509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761509 prefixEnd_3761509 := by exact prefixLift 3761509
  have htrace : WordTrace (prefixWord ++ tailWord_3761509) baseStart_3761509 baseEnd_3761509 := by
    simpa [prefixWord, tailWord_3761509, baseEnd_3761509] using wordTrace_append hprefix tailTrace_3761509
  have hstable : (prefixWord ++ tailWord_3761509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761509).length < 2 ^ (prefixWord ++ tailWord_3761509).sum := by decide
  have hdescent : baseEnd_3761509 < baseStart_3761509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761543 : List Nat := [1, 1, 4, 2, 2, 3, 3, 1, 2, 1, 3]
def baseStart_3761543 : Nat := 118140960795 + 3761543 * 2 ^ 59
def prefixEnd_3761543 : Nat := 4983230072969 + 3 ^ 40 * 3761543 * 2
def baseEnd_3761543 : Nat := 1931479561555281679413485

theorem tailTrace_3761543 : CollatzResearch.WordTrace tailWord_3761543 prefixEnd_3761543 1931479561555281679413485 := by
  unfold tailWord_3761543
  simp only [CollatzResearch.WordTrace]
  refine ⟨137194744211579606243809283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91463162807719737495872855 137194744211579606243809283)
  ·
    refine ⟨205792116317369409365713925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137194744211579606243809283 205792116317369409365713925)
    ·
      refine ⟨38586021809506764256071361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205792116317369409365713925 38586021809506764256071361)
      ·
        refine ⟨28939516357130073192053521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38586021809506764256071361 28939516357130073192053521)
        ·
          refine ⟨21704637267847554894040141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28939516357130073192053521 21704637267847554894040141)
          ·
            refine ⟨8139238975442833085265053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21704637267847554894040141 8139238975442833085265053)
            ·
              refine ⟨3052214615791062406974395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8139238975442833085265053 3052214615791062406974395)
              ·
                refine ⟨4578321923686593610461593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3052214615791062406974395 4578321923686593610461593)
                ·
                  refine ⟨3433741442764945207846195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4578321923686593610461593 3433741442764945207846195)
                  ·
                    refine ⟨5150612164147417811769293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3433741442764945207846195 5150612164147417811769293)
                    ·
                      refine ⟨1931479561555281679413485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5150612164147417811769293 1931479561555281679413485)
                      ·
                        rfl

theorem cell23_3761543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_3761543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761543 prefixEnd_3761543 := by exact prefixLift 3761543
  have htrace : WordTrace (prefixWord ++ tailWord_3761543) baseStart_3761543 baseEnd_3761543 := by
    simpa [prefixWord, tailWord_3761543, baseEnd_3761543] using wordTrace_append hprefix tailTrace_3761543
  have hstable : (prefixWord ++ tailWord_3761543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761543).length < 2 ^ (prefixWord ++ tailWord_3761543).sum := by decide
  have hdescent : baseEnd_3761543 < baseStart_3761543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761589 : List Nat := [1, 3, 3, 2, 2, 1, 3, 1, 7]
def baseStart_3761589 : Nat := 118140960795 + 3761589 * 2 ^ 59
def prefixEnd_3761589 : Nat := 4983230072969 + 3 ^ 40 * 3761589 * 2
def baseEnd_3761589 : Nat := 214611464629487611048697

theorem tailTrace_3761589 : CollatzResearch.WordTrace tailWord_3761589 prefixEnd_3761589 214611464629487611048697 := by
  unfold tailWord_3761589
  simp only [CollatzResearch.WordTrace]
  refine ⟨137196421969412956099983821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91464281312941970733322547 137196421969412956099983821)
  ·
    refine ⟨51448658238529858537493933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137196421969412956099983821 51448658238529858537493933)
    ·
      refine ⟨19293246839448696951560225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51448658238529858537493933 19293246839448696951560225)
      ·
        refine ⟨14469935129586522713670169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19293246839448696951560225 14469935129586522713670169)
        ·
          refine ⟨10852451347189892035252627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14469935129586522713670169 10852451347189892035252627)
          ·
            refine ⟨16278677020784838052878941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10852451347189892035252627 16278677020784838052878941)
            ·
              refine ⟨6104503882794314269829603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16278677020784838052878941 6104503882794314269829603)
              ·
                refine ⟨9156755824191471404744405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6104503882794314269829603 9156755824191471404744405)
                ·
                  refine ⟨214611464629487611048697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9156755824191471404744405 214611464629487611048697)
                  ·
                    rfl

theorem cell23_3761589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 7].length) (baseStart_3761589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761589 prefixEnd_3761589 := by exact prefixLift 3761589
  have htrace : WordTrace (prefixWord ++ tailWord_3761589) baseStart_3761589 baseEnd_3761589 := by
    simpa [prefixWord, tailWord_3761589, baseEnd_3761589] using wordTrace_append hprefix tailTrace_3761589
  have hstable : (prefixWord ++ tailWord_3761589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761589).length < 2 ^ (prefixWord ++ tailWord_3761589).sum := by decide
  have hdescent : baseEnd_3761589 < baseStart_3761589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761629 : List Nat := [1, 4, 3, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_3761629 : Nat := 118140960795 + 3761629 * 2 ^ 59
def prefixEnd_3761629 : Nat := 4983230072969 + 3 ^ 40 * 3761629 * 2
def baseEnd_3761629 : Nat := 1931523720891568342938089

theorem tailTrace_3761629 : CollatzResearch.WordTrace tailWord_3761629 prefixEnd_3761629 1931523720891568342938089 := by
  unfold tailWord_3761629
  simp only [CollatzResearch.WordTrace]
  refine ⟨137197880889268042931439941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91465253926178695287626627 137197880889268042931439941)
  ·
    refine ⟨25724602666737758049644989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137197880889268042931439941 25724602666737758049644989)
    ·
      refine ⟨9646726000026659268616871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25724602666737758049644989 9646726000026659268616871)
      ·
        refine ⟨14470089000039988902925307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9646726000026659268616871 14470089000039988902925307)
        ·
          refine ⟨21705133500059983354387961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14470089000039988902925307 21705133500059983354387961)
          ·
            refine ⟨16278850125044987515790971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21705133500059983354387961 16278850125044987515790971)
            ·
              refine ⟨24418275187567481273686457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16278850125044987515790971 24418275187567481273686457)
              ·
                refine ⟨18313706390675610955264843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24418275187567481273686457 18313706390675610955264843)
                ·
                  refine ⟨27470559586013416432897265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18313706390675610955264843 27470559586013416432897265)
                  ·
                    refine ⟨20602919689510062324672949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27470559586013416432897265 20602919689510062324672949)
                    ·
                      refine ⟨1931523720891568342938089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20602919689510062324672949 1931523720891568342938089)
                      ·
                        rfl

theorem cell23_3761629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_3761629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761629 prefixEnd_3761629 := by exact prefixLift 3761629
  have htrace : WordTrace (prefixWord ++ tailWord_3761629) baseStart_3761629 baseEnd_3761629 := by
    simpa [prefixWord, tailWord_3761629, baseEnd_3761629] using wordTrace_append hprefix tailTrace_3761629
  have hstable : (prefixWord ++ tailWord_3761629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761629).length < 2 ^ (prefixWord ++ tailWord_3761629).sum := by decide
  have hdescent : baseEnd_3761629 < baseStart_3761629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761656 : List Nat := [2, 1, 2, 1, 1, 6, 1, 1, 2, 4, 2]
def baseStart_3761656 : Nat := 118140960795 + 3761656 * 2 ^ 59
def prefixEnd_3761656 : Nat := 4983230072969 + 3 ^ 40 * 3761656 * 2
def baseEnd_3761656 : Nat := 1931537584869239737300465

theorem tailTrace_3761656 : CollatzResearch.WordTrace tailWord_3761656 prefixEnd_3761656 1931537584869239737300465 := by
  unfold tailWord_3761656
  simp only [CollatzResearch.WordTrace]
  refine ⟨68599432830085113271336411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91465910440113484361781881 68599432830085113271336411)
  ·
    refine ⟨102899149245127669907004617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68599432830085113271336411 102899149245127669907004617)
    ·
      refine ⟨77174361933845752430253463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102899149245127669907004617 77174361933845752430253463)
      ·
        refine ⟨115761542900768628645380195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77174361933845752430253463 115761542900768628645380195)
        ·
          refine ⟨173642314351152942968070293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115761542900768628645380195 173642314351152942968070293)
          ·
            refine ⟨8139483485210294201628295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 173642314351152942968070293 8139483485210294201628295)
            ·
              refine ⟨12209225227815441302442443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8139483485210294201628295 12209225227815441302442443)
              ·
                refine ⟨18313837841723161953663665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12209225227815441302442443 18313837841723161953663665)
                ·
                  refine ⟨13735378381292371465247749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18313837841723161953663665 13735378381292371465247749)
                  ·
                    refine ⟨2575383446492319649733953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13735378381292371465247749 2575383446492319649733953)
                    ·
                      refine ⟨1931537584869239737300465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2575383446492319649733953 1931537584869239737300465)
                      ·
                        rfl

theorem cell23_3761656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 2, 4, 2].length) (baseStart_3761656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761656 prefixEnd_3761656 := by exact prefixLift 3761656
  have htrace : WordTrace (prefixWord ++ tailWord_3761656) baseStart_3761656 baseEnd_3761656 := by
    simpa [prefixWord, tailWord_3761656, baseEnd_3761656] using wordTrace_append hprefix tailTrace_3761656
  have hstable : (prefixWord ++ tailWord_3761656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761656).length < 2 ^ (prefixWord ++ tailWord_3761656).sum := by decide
  have hdescent : baseEnd_3761656 < baseStart_3761656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761670 : List Nat := [6, 2, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_3761670 : Nat := 118140960795 + 3761670 * 2 ^ 59
def prefixEnd_3761670 : Nat := 4983230072969 + 3 ^ 40 * 3761670 * 2
def baseEnd_3761670 : Nat := 643848257866134227508467

theorem tailTrace_3761670 : CollatzResearch.WordTrace tailWord_3761670 prefixEnd_3761670 643848257866134227508467 := by
  unfold tailWord_3761670
  simp only [CollatzResearch.WordTrace]
  refine ⟨4287480508816234591677577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 91466250854746337955788309 4287480508816234591677577)
  ·
    refine ⟨3215610381612175943758183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4287480508816234591677577 3215610381612175943758183)
    ·
      refine ⟨4823415572418263915637275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3215610381612175943758183 4823415572418263915637275)
      ·
        refine ⟨7235123358627395873455913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4823415572418263915637275 7235123358627395873455913)
        ·
          refine ⟨5426342518970546905091935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7235123358627395873455913 5426342518970546905091935)
          ·
            refine ⟨8139513778455820357637903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5426342518970546905091935 8139513778455820357637903)
            ·
              refine ⟨12209270667683730536456855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8139513778455820357637903 12209270667683730536456855)
              ·
                refine ⟨18313906001525595804685283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12209270667683730536456855 18313906001525595804685283)
                ·
                  refine ⟨27470859002288393707027925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18313906001525595804685283 27470859002288393707027925)
                  ·
                    refine ⟨643848257866134227508467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27470859002288393707027925 643848257866134227508467)
                    ·
                      rfl

theorem cell23_3761670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_3761670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761670 prefixEnd_3761670 := by exact prefixLift 3761670
  have htrace : WordTrace (prefixWord ++ tailWord_3761670) baseStart_3761670 baseEnd_3761670 := by
    simpa [prefixWord, tailWord_3761670, baseEnd_3761670] using wordTrace_append hprefix tailTrace_3761670
  have hstable : (prefixWord ++ tailWord_3761670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761670).length < 2 ^ (prefixWord ++ tailWord_3761670).sum := by decide
  have hdescent : baseEnd_3761670 < baseStart_3761670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761676 : List Nat := [2, 2, 1, 2, 5, 1, 1, 1, 1, 4, 3]
def baseStart_3761676 : Nat := 118140960795 + 3761676 * 2 ^ 59
def prefixEnd_3761676 : Nat := 4983230072969 + 3 ^ 40 * 3761676 * 2
def baseEnd_3761676 : Nat := 1931547854482329659050373

theorem tailTrace_3761676 : CollatzResearch.WordTrace tailWord_3761676 prefixEnd_3761676 1931547854482329659050373 := by
  unfold tailWord_3761676
  simp only [CollatzResearch.WordTrace]
  refine ⟨68599797560048884979200441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91466396746731846638933921 68599797560048884979200441)
  ·
    refine ⟨51449848170036663734400331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68599797560048884979200441 51449848170036663734400331)
    ·
      refine ⟨77174772255054995601600497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51449848170036663734400331 77174772255054995601600497)
      ·
        refine ⟨57881079191291246701200373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77174772255054995601600497 57881079191291246701200373)
        ·
          refine ⟨5426351174183554378237535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57881079191291246701200373 5426351174183554378237535)
          ·
            refine ⟨8139526761275331567356303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5426351174183554378237535 8139526761275331567356303)
            ·
              refine ⟨12209290141912997351034455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8139526761275331567356303 12209290141912997351034455)
              ·
                refine ⟨18313935212869496026551683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12209290141912997351034455 18313935212869496026551683)
                ·
                  refine ⟨27470902819304244039827525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18313935212869496026551683 27470902819304244039827525)
                  ·
                    refine ⟨5150794278619545757467661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27470902819304244039827525 5150794278619545757467661)
                    ·
                      refine ⟨1931547854482329659050373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5150794278619545757467661 1931547854482329659050373)
                      ·
                        rfl

theorem cell23_3761676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_3761676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761676 prefixEnd_3761676 := by exact prefixLift 3761676
  have htrace : WordTrace (prefixWord ++ tailWord_3761676) baseStart_3761676 baseEnd_3761676 := by
    simpa [prefixWord, tailWord_3761676, baseEnd_3761676] using wordTrace_append hprefix tailTrace_3761676
  have hstable : (prefixWord ++ tailWord_3761676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761676).length < 2 ^ (prefixWord ++ tailWord_3761676).sum := by decide
  have hdescent : baseEnd_3761676 < baseStart_3761676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761683 : List Nat := [1, 1, 1, 2, 1, 7, 2, 3, 1, 4]
def baseStart_3761683 : Nat := 118140960795 + 3761683 * 2 ^ 59
def prefixEnd_3761683 : Nat := 4983230072969 + 3 ^ 40 * 3761683 * 2
def baseEnd_3761683 : Nat := 643850482948970377220947

theorem tailTrace_3761683 : CollatzResearch.WordTrace tailWord_3761683 prefixEnd_3761683 643850482948970377220947 := by
  unfold tailWord_3761683
  simp only [CollatzResearch.WordTrace]
  refine ⟨137199850431072410153905703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91466566954048273435937135 137199850431072410153905703)
  ·
    refine ⟨205799775646608615230858555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137199850431072410153905703 205799775646608615230858555)
    ·
      refine ⟨308699663469912922846287833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205799775646608615230858555 308699663469912922846287833)
      ·
        refine ⟨231524747602434692134715875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308699663469912922846287833 231524747602434692134715875)
        ·
          refine ⟨347287121403652038202073813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231524747602434692134715875 347287121403652038202073813)
          ·
            refine ⟨8139541907898094645361105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 347287121403652038202073813 8139541907898094645361105)
            ·
              refine ⟨6104656430923570984020829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8139541907898094645361105 6104656430923570984020829)
              ·
                refine ⟨2289246161596339119007811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6104656430923570984020829 2289246161596339119007811)
                ·
                  refine ⟨3433869242394508678511717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2289246161596339119007811 3433869242394508678511717)
                  ·
                    refine ⟨643850482948970377220947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3433869242394508678511717 643850482948970377220947)
                    ·
                      rfl

theorem cell23_3761683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 3, 1, 4].length) (baseStart_3761683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761683 prefixEnd_3761683 := by exact prefixLift 3761683
  have htrace : WordTrace (prefixWord ++ tailWord_3761683) baseStart_3761683 baseEnd_3761683 := by
    simpa [prefixWord, tailWord_3761683, baseEnd_3761683] using wordTrace_append hprefix tailTrace_3761683
  have hstable : (prefixWord ++ tailWord_3761683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761683).length < 2 ^ (prefixWord ++ tailWord_3761683).sum := by decide
  have hdescent : baseEnd_3761683 < baseStart_3761683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761696 : List Nat := [2, 1, 1, 6, 1, 1, 3, 2, 6]
def baseStart_3761696 : Nat := 118140960795 + 3761696 * 2 ^ 59
def prefixEnd_3761696 : Nat := 4983230072969 + 3 ^ 40 * 3761696 * 2
def baseEnd_3761696 : Nat := 214617569343935508977809

theorem tailTrace_3761696 : CollatzResearch.WordTrace tailWord_3761696 prefixEnd_3761696 214617569343935508977809 := by
  unfold tailWord_3761696
  simp only [CollatzResearch.WordTrace]
  refine ⟨68600162290012656687064471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91466883053350208916085961 68600162290012656687064471)
  ·
    refine ⟨102900243435018985030596707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68600162290012656687064471 102900243435018985030596707)
    ·
      refine ⟨154350365152528477545895061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102900243435018985030596707 154350365152528477545895061)
      ·
        refine ⟨7235173366524772384963831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 154350365152528477545895061 7235173366524772384963831)
        ·
          refine ⟨10852760049787158577445747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7235173366524772384963831 10852760049787158577445747)
          ·
            refine ⟨16279140074680737866168621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10852760049787158577445747 16279140074680737866168621)
            ·
              refine ⟨6104677528005276699813233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16279140074680737866168621 6104677528005276699813233)
              ·
                refine ⟨4578508146003957524859925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6104677528005276699813233 4578508146003957524859925)
                ·
                  refine ⟨214617569343935508977809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4578508146003957524859925 214617569343935508977809)
                  ·
                    rfl

theorem cell23_3761696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 6].length) (baseStart_3761696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761696 prefixEnd_3761696 := by exact prefixLift 3761696
  have htrace : WordTrace (prefixWord ++ tailWord_3761696) baseStart_3761696 baseEnd_3761696 := by
    simpa [prefixWord, tailWord_3761696, baseEnd_3761696] using wordTrace_append hprefix tailTrace_3761696
  have hstable : (prefixWord ++ tailWord_3761696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761696).length < 2 ^ (prefixWord ++ tailWord_3761696).sum := by decide
  have hdescent : baseEnd_3761696 < baseStart_3761696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761734 : List Nat := [6, 1, 1, 1, 3, 2, 1, 3, 1, 4]
def baseStart_3761734 : Nat := 118140960795 + 3761734 * 2 ^ 59
def prefixEnd_3761734 : Nat := 4983230072969 + 3 ^ 40 * 3761734 * 2
def baseEnd_3761734 : Nat := 643859212120096810708369

theorem tailTrace_3761734 : CollatzResearch.WordTrace tailWord_3761734 prefixEnd_3761734 643859212120096810708369 := by
  unfold tailWord_3761734
  simp only [CollatzResearch.WordTrace]
  refine ⟨4287553454808988933250383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 91467807035925097242674837 4287553454808988933250383)
  ·
    refine ⟨6431330182213483399875575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4287553454808988933250383 6431330182213483399875575)
    ·
      refine ⟨9646995273320225099813363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6431330182213483399875575 9646995273320225099813363)
      ·
        refine ⟨14470492909980337649720045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9646995273320225099813363 14470492909980337649720045)
        ·
          refine ⟨5426434841242626618645017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14470492909980337649720045 5426434841242626618645017)
          ·
            refine ⟨4069826130931969963983763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5426434841242626618645017 4069826130931969963983763)
            ·
              refine ⟨6104739196397954945975645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4069826130931969963983763 6104739196397954945975645)
              ·
                refine ⟨2289277198649233104740867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6104739196397954945975645 2289277198649233104740867)
                ·
                  refine ⟨3433915797973849657111301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2289277198649233104740867 3433915797973849657111301)
                  ·
                    refine ⟨643859212120096810708369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3433915797973849657111301 643859212120096810708369)
                    ·
                      rfl

theorem cell23_3761734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_3761734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761734 prefixEnd_3761734 := by exact prefixLift 3761734
  have htrace : WordTrace (prefixWord ++ tailWord_3761734) baseStart_3761734 baseEnd_3761734 := by
    simpa [prefixWord, tailWord_3761734, baseEnd_3761734] using wordTrace_append hprefix tailTrace_3761734
  have hstable : (prefixWord ++ tailWord_3761734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761734).length < 2 ^ (prefixWord ++ tailWord_3761734).sum := by decide
  have hdescent : baseEnd_3761734 < baseStart_3761734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761740 : List Nat := [2, 2, 1, 3, 1, 3, 3, 3, 1, 1, 3]
def baseStart_3761740 : Nat := 118140960795 + 3761740 * 2 ^ 59
def prefixEnd_3761740 : Nat := 4983230072969 + 3 ^ 40 * 3761740 * 2
def baseEnd_3761740 : Nat := 1931580717244217408650079

theorem tailTrace_3761740 : CollatzResearch.WordTrace tailWord_3761740 prefixEnd_3761740 1931580717244217408650079 := by
  unfold tailWord_3761740
  simp only [CollatzResearch.WordTrace]
  refine ⟨68600964695932954444365337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91467952927910605925820449 68600964695932954444365337)
  ·
    refine ⟨51450723521949715833274003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68600964695932954444365337 51450723521949715833274003)
    ·
      refine ⟨77176085282924573749911005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51450723521949715833274003 77176085282924573749911005)
      ·
        refine ⟨28941031981096715156216627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77176085282924573749911005 28941031981096715156216627)
        ·
          refine ⟨43411547971645072734324941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28941031981096715156216627 43411547971645072734324941)
          ·
            refine ⟨16279330489366902275371853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43411547971645072734324941 16279330489366902275371853)
            ·
              refine ⟨6104748933512588353264445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16279330489366902275371853 6104748933512588353264445)
              ·
                refine ⟨2289280850067220632474167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6104748933512588353264445 2289280850067220632474167)
                ·
                  refine ⟨3433921275100830948711251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2289280850067220632474167 3433921275100830948711251)
                  ·
                    refine ⟨5150881912651246423066877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3433921275100830948711251 5150881912651246423066877)
                    ·
                      refine ⟨1931580717244217408650079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5150881912651246423066877 1931580717244217408650079)
                      ·
                        rfl

theorem cell23_3761740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_3761740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761740 prefixEnd_3761740 := by exact prefixLift 3761740
  have htrace : WordTrace (prefixWord ++ tailWord_3761740) baseStart_3761740 baseEnd_3761740 := by
    simpa [prefixWord, tailWord_3761740, baseEnd_3761740] using wordTrace_append hprefix tailTrace_3761740
  have hstable : (prefixWord ++ tailWord_3761740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761740).length < 2 ^ (prefixWord ++ tailWord_3761740).sum := by decide
  have hdescent : baseEnd_3761740 < baseStart_3761740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761800 : List Nat := [2, 1, 3, 5, 1, 2, 1, 1, 1, 1, 5]
def baseStart_3761800 : Nat := 118140960795 + 3761800 * 2 ^ 59
def prefixEnd_3761800 : Nat := 4983230072969 + 3 ^ 40 * 3761800 * 2
def baseEnd_3761800 : Nat := 1931611526083487173899803

theorem tailTrace_3761800 : CollatzResearch.WordTrace tailWord_3761800 prefixEnd_3761800 1931611526083487173899803 := by
  unfold tailWord_3761800
  simp only [CollatzResearch.WordTrace]
  refine ⟨68602058885824269567957427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91469411847765692757276569 68602058885824269567957427)
  ·
    refine ⟨102903088328736404351936141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68602058885824269567957427 102903088328736404351936141)
    ·
      refine ⟨38588658123276151631976053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102903088328736404351936141 38588658123276151631976053)
      ·
        refine ⟨3617686699057139215497755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38588658123276151631976053 3617686699057139215497755)
        ·
          refine ⟨5426530048585708823246633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3617686699057139215497755 5426530048585708823246633)
          ·
            refine ⟨4069897536439281617434975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5426530048585708823246633 4069897536439281617434975)
            ·
              refine ⟨6104846304658922426152463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4069897536439281617434975 6104846304658922426152463)
              ·
                refine ⟨9157269456988383639228695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6104846304658922426152463 9157269456988383639228695)
                ·
                  refine ⟨13735904185482575458843043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9157269456988383639228695 13735904185482575458843043)
                  ·
                    refine ⟨20603856278223863188264565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13735904185482575458843043 20603856278223863188264565)
                    ·
                      refine ⟨1931611526083487173899803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20603856278223863188264565 1931611526083487173899803)
                      ·
                        rfl

theorem cell23_3761800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_3761800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761800 prefixEnd_3761800 := by exact prefixLift 3761800
  have htrace : WordTrace (prefixWord ++ tailWord_3761800) baseStart_3761800 baseEnd_3761800 := by
    simpa [prefixWord, tailWord_3761800, baseEnd_3761800] using wordTrace_append hprefix tailTrace_3761800
  have hstable : (prefixWord ++ tailWord_3761800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761800).length < 2 ^ (prefixWord ++ tailWord_3761800).sum := by decide
  have hdescent : baseEnd_3761800 < baseStart_3761800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761829 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 1, 8]
def baseStart_3761829 : Nat := 118140960795 + 3761829 * 2 ^ 59
def prefixEnd_3761829 : Nat := 4983230072969 + 3 ^ 40 * 3761829 * 2
def baseEnd_3761829 : Nat := 643875472340822520145723

theorem tailTrace_3761829 : CollatzResearch.WordTrace tailWord_3761829 prefixEnd_3761829 643875472340822520145723 := by
  unfold tailWord_3761829
  simp only [CollatzResearch.WordTrace]
  refine ⟨137205175488543477088720541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91470116992362318059147027 137205175488543477088720541)
  ·
    refine ⟨51451940808203803908270203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137205175488543477088720541 51451940808203803908270203)
    ·
      refine ⟨77177911212305705862405305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51451940808203803908270203 77177911212305705862405305)
      ·
        refine ⟨57883433409229279396803979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77177911212305705862405305 57883433409229279396803979)
        ·
          refine ⟨86825150113843919095205969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57883433409229279396803979 86825150113843919095205969)
          ·
            refine ⟨65118862585382939321404477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86825150113843919095205969 65118862585382939321404477)
            ·
              refine ⟨24419573469518602245526679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65118862585382939321404477 24419573469518602245526679)
              ·
                refine ⟨36629360204277903368290019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24419573469518602245526679 36629360204277903368290019)
                ·
                  refine ⟨54944040306416855052435029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36629360204277903368290019 54944040306416855052435029)
                  ·
                    refine ⟨643875472340822520145723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54944040306416855052435029 643875472340822520145723)
                    ·
                      rfl

theorem cell23_3761829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 8].length) (baseStart_3761829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761829 prefixEnd_3761829 := by exact prefixLift 3761829
  have htrace : WordTrace (prefixWord ++ tailWord_3761829) baseStart_3761829 baseEnd_3761829 := by
    simpa [prefixWord, tailWord_3761829, baseEnd_3761829] using wordTrace_append hprefix tailTrace_3761829
  have hstable : (prefixWord ++ tailWord_3761829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761829).length < 2 ^ (prefixWord ++ tailWord_3761829).sum := by decide
  have hdescent : baseEnd_3761829 < baseStart_3761829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761853 : List Nat := [1, 4, 1, 2, 1, 2, 1, 4, 1, 4, 2]
def baseStart_3761853 : Nat := 118140960795 + 3761853 * 2 ^ 59
def prefixEnd_3761853 : Nat := 4983230072969 + 3 ^ 40 * 3761853 * 2
def baseEnd_3761853 : Nat := 1931638740558175466537059

theorem tailTrace_3761853 : CollatzResearch.WordTrace tailWord_3761853 prefixEnd_3761853 1931638740558175466537059 := by
  unfold tailWord_3761853
  simp only [CollatzResearch.WordTrace]
  refine ⟨137206050840456529187594213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91470700560304352791729475 137206050840456529187594213)
  ·
    refine ⟨25726134532585599222673915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137206050840456529187594213 25726134532585599222673915)
    ·
      refine ⟨38589201798878398834010873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25726134532585599222673915 38589201798878398834010873)
      ·
        refine ⟨28941901349158799125508155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38589201798878398834010873 28941901349158799125508155)
        ·
          refine ⟨43412852023738198688262233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28941901349158799125508155 43412852023738198688262233)
          ·
            refine ⟨32559639017803649016196675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43412852023738198688262233 32559639017803649016196675)
            ·
              refine ⟨48839458526705473524295013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32559639017803649016196675 48839458526705473524295013)
              ·
                refine ⟨9157398473757276285805315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48839458526705473524295013 9157398473757276285805315)
                ·
                  refine ⟨13736097710635914428707973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9157398473757276285805315 13736097710635914428707973)
                  ·
                    refine ⟨2575518320744233955382745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13736097710635914428707973 2575518320744233955382745)
                    ·
                      refine ⟨1931638740558175466537059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2575518320744233955382745 1931638740558175466537059)
                      ·
                        rfl

theorem cell23_3761853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_3761853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761853 prefixEnd_3761853 := by exact prefixLift 3761853
  have htrace : WordTrace (prefixWord ++ tailWord_3761853) baseStart_3761853 baseEnd_3761853 := by
    simpa [prefixWord, tailWord_3761853, baseEnd_3761853] using wordTrace_append hprefix tailTrace_3761853
  have hstable : (prefixWord ++ tailWord_3761853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761853).length < 2 ^ (prefixWord ++ tailWord_3761853).sum := by decide
  have hdescent : baseEnd_3761853 < baseStart_3761853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761870 : List Nat := [4, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2]
def baseStart_3761870 : Nat := 118140960795 + 3761870 * 2 ^ 59
def prefixEnd_3761870 : Nat := 4983230072969 + 3 ^ 40 * 3761870 * 2
def baseEnd_3761870 : Nat := 1931647469729301900024481

theorem tailTrace_3761870 : CollatzResearch.WordTrace tailWord_3761870 prefixEnd_3761870 1931647469729301900024481 := by
  unfold tailWord_3761870
  simp only [CollatzResearch.WordTrace]
  refine ⟨17150833860174367636370383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91471113920929960727308709 17150833860174367636370383)
  ·
    refine ⟨25726250790261551454555575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17150833860174367636370383 25726250790261551454555575)
    ·
      refine ⟨38589376185392327181833363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25726250790261551454555575 38589376185392327181833363)
      ·
        refine ⟨57884064278088490772750045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38589376185392327181833363 57884064278088490772750045)
        ·
          refine ⟨21706524104283184039781267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57884064278088490772750045 21706524104283184039781267)
          ·
            refine ⟨32559786156424776059671901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21706524104283184039781267 32559786156424776059671901)
            ·
              refine ⟨12209919808659291022376963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32559786156424776059671901 12209919808659291022376963)
              ·
                refine ⟨18314879712988936533565445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12209919808659291022376963 18314879712988936533565445)
                ·
                  refine ⟨3434039946185425600043521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18314879712988936533565445 3434039946185425600043521)
                  ·
                    refine ⟨2575529959639069200032641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3434039946185425600043521 2575529959639069200032641)
                    ·
                      refine ⟨1931647469729301900024481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2575529959639069200032641 1931647469729301900024481)
                      ·
                        rfl

theorem cell23_3761870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2].length) (baseStart_3761870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761870 prefixEnd_3761870 := by exact prefixLift 3761870
  have htrace : WordTrace (prefixWord ++ tailWord_3761870) baseStart_3761870 baseEnd_3761870 := by
    simpa [prefixWord, tailWord_3761870, baseEnd_3761870] using wordTrace_append hprefix tailTrace_3761870
  have hstable : (prefixWord ++ tailWord_3761870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761870).length < 2 ^ (prefixWord ++ tailWord_3761870).sum := by decide
  have hdescent : baseEnd_3761870 < baseStart_3761870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761887 : List Nat := [1, 1, 2, 3, 2, 2, 5, 1, 2, 2, 2]
def baseStart_3761887 : Nat := 118140960795 + 3761887 * 2 ^ 59
def prefixEnd_3761887 : Nat := 4983230072969 + 3 ^ 40 * 3761887 * 2
def baseEnd_3761887 : Nat := 1931656198900428333511903

theorem tailTrace_3761887 : CollatzResearch.WordTrace tailWord_3761887 prefixEnd_3761887 1931656198900428333511903 := by
  unfold tailWord_3761887
  simp only [CollatzResearch.WordTrace]
  refine ⟨137207290922333352994331915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91471527281555568662887943 137207290922333352994331915)
  ·
    refine ⟨205810936383500029491497873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137207290922333352994331915 205810936383500029491497873)
    ·
      refine ⟨154358202287625022118623405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205810936383500029491497873 154358202287625022118623405)
      ·
        refine ⟨57884325857859383294483777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154358202287625022118623405 57884325857859383294483777)
        ·
          refine ⟨43413244393394537470862833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57884325857859383294483777 43413244393394537470862833)
          ·
            refine ⟨32559933295045903103147125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43413244393394537470862833 32559933295045903103147125)
            ·
              refine ⟨3052493746410553415920043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32559933295045903103147125 3052493746410553415920043)
              ·
                refine ⟨4578740619615830123880065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3052493746410553415920043 4578740619615830123880065)
                ·
                  refine ⟨3434055464711872592910049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4578740619615830123880065 3434055464711872592910049)
                  ·
                    refine ⟨2575541598533904444682537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3434055464711872592910049 2575541598533904444682537)
                    ·
                      refine ⟨1931656198900428333511903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2575541598533904444682537 1931656198900428333511903)
                      ·
                        rfl

theorem cell23_3761887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 2, 2, 2].length) (baseStart_3761887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761887 prefixEnd_3761887 := by exact prefixLift 3761887
  have htrace : WordTrace (prefixWord ++ tailWord_3761887) baseStart_3761887 baseEnd_3761887 := by
    simpa [prefixWord, tailWord_3761887, baseEnd_3761887] using wordTrace_append hprefix tailTrace_3761887
  have hstable : (prefixWord ++ tailWord_3761887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761887).length < 2 ^ (prefixWord ++ tailWord_3761887).sum := by decide
  have hdescent : baseEnd_3761887 < baseStart_3761887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761906 : List Nat := [3, 2, 1, 3, 1, 1, 1, 3, 1, 7]
def baseStart_3761906 : Nat := 118140960795 + 3761906 * 2 ^ 59
def prefixEnd_3761906 : Nat := 4983230072969 + 3 ^ 40 * 3761906 * 2
def baseEnd_3761906 : Nat := 643888651677621253058105

theorem tailTrace_3761906 : CollatzResearch.WordTrace tailWord_3761906 prefixEnd_3761906 643888651677621253058105 := by
  unfold tailWord_3761906
  simp only [CollatzResearch.WordTrace]
  refine ⟨34301995977316129809818393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91471989272843012826182381 34301995977316129809818393)
  ·
    refine ⟨25726496982987097357363795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34301995977316129809818393 25726496982987097357363795)
    ·
      refine ⟨38589745474480646036045693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25726496982987097357363795 38589745474480646036045693)
      ·
        refine ⟨14471154552930242263517135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38589745474480646036045693 14471154552930242263517135)
        ·
          refine ⟨21706731829395363395275703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14471154552930242263517135 21706731829395363395275703)
          ·
            refine ⟨32560097744093045092913555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21706731829395363395275703 32560097744093045092913555)
            ·
              refine ⟨48840146616139567639370333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32560097744093045092913555 48840146616139567639370333)
              ·
                refine ⟨18315054981052337864763875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48840146616139567639370333 18315054981052337864763875)
                ·
                  refine ⟨27472582471578506797145813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18315054981052337864763875 27472582471578506797145813)
                  ·
                    refine ⟨643888651677621253058105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27472582471578506797145813 643888651677621253058105)
                    ·
                      rfl

theorem cell23_3761906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_3761906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761906 prefixEnd_3761906 := by exact prefixLift 3761906
  have htrace : WordTrace (prefixWord ++ tailWord_3761906) baseStart_3761906 baseEnd_3761906 := by
    simpa [prefixWord, tailWord_3761906, baseEnd_3761906] using wordTrace_append hprefix tailTrace_3761906
  have hstable : (prefixWord ++ tailWord_3761906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761906).length < 2 ^ (prefixWord ++ tailWord_3761906).sum := by decide
  have hdescent : baseEnd_3761906 < baseStart_3761906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761910 : List Nat := [5, 1, 1, 1, 1, 3, 3, 3, 5]
def baseStart_3761910 : Nat := 118140960795 + 3761910 * 2 ^ 59
def prefixEnd_3761910 : Nat := 4983230072969 + 3 ^ 40 * 3761910 * 2
def baseEnd_3761910 : Nat := 214629778772831304836033

theorem tailTrace_3761910 : CollatzResearch.WordTrace tailWord_3761910 prefixEnd_3761910 214629778772831304836033 := by
  unfold tailWord_3761910
  simp only [CollatzResearch.WordTrace]
  refine ⟨8575508112578126745151199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91472086534166685281612789 8575508112578126745151199)
  ·
    refine ⟨12863262168867190117726799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8575508112578126745151199 12863262168867190117726799)
    ·
      refine ⟨19294893253300785176590199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12863262168867190117726799 19294893253300785176590199)
      ·
        refine ⟨28942339879951177764885299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19294893253300785176590199 28942339879951177764885299)
        ·
          refine ⟨43413509819926766647327949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28942339879951177764885299 43413509819926766647327949)
          ·
            refine ⟨16280066182472537492747981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43413509819926766647327949 16280066182472537492747981)
            ·
              refine ⟨6105024818427201559780493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16280066182472537492747981 6105024818427201559780493)
              ·
                refine ⟨2289384306910200584917685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6105024818427201559780493 2289384306910200584917685)
                ·
                  refine ⟨214629778772831304836033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2289384306910200584917685 214629778772831304836033)
                  ·
                    rfl

theorem cell23_3761910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_3761910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761910 prefixEnd_3761910 := by exact prefixLift 3761910
  have htrace : WordTrace (prefixWord ++ tailWord_3761910) baseStart_3761910 baseEnd_3761910 := by
    simpa [prefixWord, tailWord_3761910, baseEnd_3761910] using wordTrace_append hprefix tailTrace_3761910
  have hstable : (prefixWord ++ tailWord_3761910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761910).length < 2 ^ (prefixWord ++ tailWord_3761910).sum := by decide
  have hdescent : baseEnd_3761910 < baseStart_3761910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761916 : List Nat := [2, 2, 2, 1, 3, 1, 2, 2, 1, 2, 5]
def baseStart_3761916 : Nat := 118140960795 + 3761916 * 2 ^ 59
def prefixEnd_3761916 : Nat := 4983230072969 + 3 ^ 40 * 3761916 * 2
def baseEnd_3761916 : Nat := 1931671089839408720049269

theorem tailTrace_3761916 : CollatzResearch.WordTrace tailWord_3761916 prefixEnd_3761916 1931671089839408720049269 := by
  unfold tailWord_3761916
  simp only [CollatzResearch.WordTrace]
  refine ⟨68604174319614145473568801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91472232426152193964758401 68604174319614145473568801)
  ·
    refine ⟨51453130739710609105176601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68604174319614145473568801 51453130739710609105176601)
    ·
      refine ⟨38589848054782956828882451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51453130739710609105176601 38589848054782956828882451)
      ·
        refine ⟨57884772082174435243323677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38589848054782956828882451 57884772082174435243323677)
        ·
          refine ⟨21706789530815413216246379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57884772082174435243323677 21706789530815413216246379)
          ·
            refine ⟨32560184296223119824369569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21706789530815413216246379 32560184296223119824369569)
            ·
              refine ⟨24420138222167339868277177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32560184296223119824369569 24420138222167339868277177)
              ·
                refine ⟨18315103666625504901207883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24420138222167339868277177 18315103666625504901207883)
                ·
                  refine ⟨27472655499938257351811825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18315103666625504901207883 27472655499938257351811825)
                  ·
                    refine ⟨20604491624953693013858869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27472655499938257351811825 20604491624953693013858869)
                    ·
                      refine ⟨1931671089839408720049269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20604491624953693013858869 1931671089839408720049269)
                      ·
                        rfl

theorem cell23_3761916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_3761916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761916 prefixEnd_3761916 := by exact prefixLift 3761916
  have htrace : WordTrace (prefixWord ++ tailWord_3761916) baseStart_3761916 baseEnd_3761916 := by
    simpa [prefixWord, tailWord_3761916, baseEnd_3761916] using wordTrace_append hprefix tailTrace_3761916
  have hstable : (prefixWord ++ tailWord_3761916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761916).length < 2 ^ (prefixWord ++ tailWord_3761916).sum := by decide
  have hdescent : baseEnd_3761916 < baseStart_3761916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761927 : List Nat := [1, 1, 4, 4, 2, 1, 3, 2, 5]
def baseStart_3761927 : Nat := 118140960795 + 3761927 * 2 ^ 59
def prefixEnd_3761927 : Nat := 4983230072969 + 3 ^ 40 * 3761927 * 2
def baseEnd_3761927 : Nat := 214630748680734241890191

theorem tailTrace_3761927 : CollatzResearch.WordTrace tailWord_3761927 prefixEnd_3761927 214630748680734241890191 := by
  unfold tailWord_3761927
  simp only [CollatzResearch.WordTrace]
  refine ⟨137208749842188439825788035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91472499894792293217192023 137208749842188439825788035)
  ·
    refine ⟨205813124763282659738682053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137208749842188439825788035 205813124763282659738682053)
    ·
      refine ⟨38589960893115498701002885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205813124763282659738682053 38589960893115498701002885)
      ·
        refine ⟨7235617667459156006438041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38589960893115498701002885 7235617667459156006438041)
        ·
          refine ⟨5426713250594367004828531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7235617667459156006438041 5426713250594367004828531)
          ·
            refine ⟨8140069875891550507242797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5426713250594367004828531 8140069875891550507242797)
            ·
              refine ⟨3052526203459331440216049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8140069875891550507242797 3052526203459331440216049)
              ·
                refine ⟨2289394652594498580162037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3052526203459331440216049 2289394652594498580162037)
                ·
                  refine ⟨214630748680734241890191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2289394652594498580162037 214630748680734241890191)
                  ·
                    rfl

theorem cell23_3761927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 2, 5].length) (baseStart_3761927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761927 prefixEnd_3761927 := by exact prefixLift 3761927
  have htrace : WordTrace (prefixWord ++ tailWord_3761927) baseStart_3761927 baseEnd_3761927 := by
    simpa [prefixWord, tailWord_3761927, baseEnd_3761927] using wordTrace_append hprefix tailTrace_3761927
  have hstable : (prefixWord ++ tailWord_3761927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761927).length < 2 ^ (prefixWord ++ tailWord_3761927).sum := by decide
  have hdescent : baseEnd_3761927 < baseStart_3761927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761960 : List Nat := [2, 1, 5, 1, 1, 3, 2, 1, 2, 1, 4]
def baseStart_3761960 : Nat := 118140960795 + 3761960 * 2 ^ 59
def prefixEnd_3761960 : Nat := 4983230072969 + 3 ^ 40 * 3761960 * 2
def baseEnd_3761960 : Nat := 1931693682988206547899067

theorem tailTrace_3761960 : CollatzResearch.WordTrace tailWord_3761960 prefixEnd_3761960 1931693682988206547899067 := by
  unfold tailWord_3761960
  simp only [CollatzResearch.WordTrace]
  refine ⟨68604976725534443230869667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91473302300712590974492889 68604976725534443230869667)
  ·
    refine ⟨102907465088301664846304501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68604976725534443230869667 102907465088301664846304501)
    ·
      refine ⟨9647574852028281079341047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102907465088301664846304501 9647574852028281079341047)
      ·
        refine ⟨14471362278042421619011571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9647574852028281079341047 14471362278042421619011571)
        ·
          refine ⟨21707043417063632428517357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14471362278042421619011571 21707043417063632428517357)
          ·
            refine ⟨8140141281398862160694009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21707043417063632428517357 8140141281398862160694009)
            ·
              refine ⟨6105105961049146620520507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8140141281398862160694009 6105105961049146620520507)
              ·
                refine ⟨9157658941573719930780761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6105105961049146620520507 9157658941573719930780761)
                ·
                  refine ⟨6868244206180289948085571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9157658941573719930780761 6868244206180289948085571)
                  ·
                    refine ⟨10302366309270434922128357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6868244206180289948085571 10302366309270434922128357)
                    ·
                      refine ⟨1931693682988206547899067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10302366309270434922128357 1931693682988206547899067)
                      ·
                        rfl

theorem cell23_3761960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_3761960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761960 prefixEnd_3761960 := by exact prefixLift 3761960
  have htrace : WordTrace (prefixWord ++ tailWord_3761960) baseStart_3761960 baseEnd_3761960 := by
    simpa [prefixWord, tailWord_3761960, baseEnd_3761960] using wordTrace_append hprefix tailTrace_3761960
  have hstable : (prefixWord ++ tailWord_3761960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761960).length < 2 ^ (prefixWord ++ tailWord_3761960).sum := by decide
  have hdescent : baseEnd_3761960 < baseStart_3761960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761987 : List Nat := [1, 1, 1, 3, 1, 5, 4, 2, 1, 4]
def baseStart_3761987 : Nat := 118140960795 + 3761987 * 2 ^ 59
def prefixEnd_3761987 : Nat := 4983230072969 + 3 ^ 40 * 3761987 * 2
def baseEnd_3761987 : Nat := 643902515655292647420481

theorem tailTrace_3761987 : CollatzResearch.WordTrace tailWord_3761987 prefixEnd_3761987 643902515655292647420481 := by
  unfold tailWord_3761987
  simp only [CollatzResearch.WordTrace]
  refine ⟨137210938221971070072972215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91473958814647380048648143 137210938221971070072972215)
  ·
    refine ⟨205816407332956605109458323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137210938221971070072972215 205816407332956605109458323)
    ·
      refine ⟨308724610999434907664187485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205816407332956605109458323 308724610999434907664187485)
      ·
        refine ⟨115771729124788090374070307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308724610999434907664187485 115771729124788090374070307)
        ·
          refine ⟨173657593687182135561105461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115771729124788090374070307 173657593687182135561105461)
          ·
            refine ⟨16280399408173325208853637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173657593687182135561105461 16280399408173325208853637)
            ·
              refine ⟨3052574889032498476660057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16280399408173325208853637 3052574889032498476660057)
              ·
                refine ⟨2289431166774373857495043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3052574889032498476660057 2289431166774373857495043)
                ·
                  refine ⟨3434146750161560786242565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2289431166774373857495043 3434146750161560786242565)
                  ·
                    refine ⟨643902515655292647420481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3434146750161560786242565 643902515655292647420481)
                    ·
                      rfl

theorem cell23_3761987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 2, 1, 4].length) (baseStart_3761987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3761987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3761987 prefixEnd_3761987 := by exact prefixLift 3761987
  have htrace : WordTrace (prefixWord ++ tailWord_3761987) baseStart_3761987 baseEnd_3761987 := by
    simpa [prefixWord, tailWord_3761987, baseEnd_3761987] using wordTrace_append hprefix tailTrace_3761987
  have hstable : (prefixWord ++ tailWord_3761987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761987).length < 2 ^ (prefixWord ++ tailWord_3761987).sum := by decide
  have hdescent : baseEnd_3761987 < baseStart_3761987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762010 : List Nat := [3, 1, 1, 2, 1, 3, 3, 2, 3, 1, 3]
def baseStart_3762010 : Nat := 118140960795 + 3762010 * 2 ^ 59
def prefixEnd_3762010 : Nat := 4983230072969 + 3 ^ 40 * 3762010 * 2
def baseEnd_3762010 : Nat := 1931719357020931352273837

theorem tailTrace_3762010 : CollatzResearch.WordTrace tailWord_3762010 prefixEnd_3762010 1931719357020931352273837 := by
  unfold tailWord_3762010
  simp only [CollatzResearch.WordTrace]
  refine ⟨34302944275221936250264871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91474518067258496667372989 34302944275221936250264871)
  ·
    refine ⟨51454416412832904375397307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34302944275221936250264871 51454416412832904375397307)
    ·
      refine ⟨77181624619249356563095961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51454416412832904375397307 77181624619249356563095961)
      ·
        refine ⟨57886218464437017422321971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77181624619249356563095961 57886218464437017422321971)
        ·
          refine ⟨86829327696655526133482957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57886218464437017422321971 86829327696655526133482957)
          ·
            refine ⟨32560997886245822300056109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86829327696655526133482957 32560997886245822300056109)
            ·
              refine ⟨12210374207342183362521041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32560997886245822300056109 12210374207342183362521041)
              ·
                refine ⟨9157780655506637521890781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12210374207342183362521041 9157780655506637521890781)
                ·
                  refine ⟨3434167745814989070709043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9157780655506637521890781 3434167745814989070709043)
                  ·
                    refine ⟨5151251618722483606063565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3434167745814989070709043 5151251618722483606063565)
                    ·
                      refine ⟨1931719357020931352273837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5151251618722483606063565 1931719357020931352273837)
                      ·
                        rfl

theorem cell23_3762010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 3, 1, 3].length) (baseStart_3762010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762010 prefixEnd_3762010 := by exact prefixLift 3762010
  have htrace : WordTrace (prefixWord ++ tailWord_3762010) baseStart_3762010 baseEnd_3762010 := by
    simpa [prefixWord, tailWord_3762010, baseEnd_3762010] using wordTrace_append hprefix tailTrace_3762010
  have hstable : (prefixWord ++ tailWord_3762010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762010).length < 2 ^ (prefixWord ++ tailWord_3762010).sum := by decide
  have hdescent : baseEnd_3762010 < baseStart_3762010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762053 : List Nat := [1, 3, 1, 1, 3, 2, 3, 2, 1, 1, 5]
def baseStart_3762053 : Nat := 118140960795 + 3762053 * 2 ^ 59
def prefixEnd_3762053 : Nat := 4983230072969 + 3 ^ 40 * 3762053 * 2
def baseEnd_3762053 : Nat := 1931741436689074684036139

theorem tailTrace_3762053 : CollatzResearch.WordTrace tailWord_3762053 prefixEnd_3762053 1931741436689074684036139 := by
  unfold tailWord_3762053
  simp only [CollatzResearch.WordTrace]
  refine ⟨137213345439731963344874813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91475563626487975563249875 137213345439731963344874813)
  ·
    refine ⟨51455004539899486254328055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137213345439731963344874813 51455004539899486254328055)
    ·
      refine ⟨77182506809849229381492083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51455004539899486254328055 77182506809849229381492083)
      ·
        refine ⟨115773760214773844072238125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77182506809849229381492083 115773760214773844072238125)
        ·
          refine ⟨43415160080540191527089297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115773760214773844072238125 43415160080540191527089297)
          ·
            refine ⟨32561370060405143645316973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43415160080540191527089297 32561370060405143645316973)
            ·
              refine ⟨12210513772651928866993865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32561370060405143645316973 12210513772651928866993865)
              ·
                refine ⟨9157885329488946650245399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12210513772651928866993865 9157885329488946650245399)
                ·
                  refine ⟨13736827994233419975368099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9157885329488946650245399 13736827994233419975368099)
                  ·
                    refine ⟨20605241991350129963052149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13736827994233419975368099 20605241991350129963052149)
                    ·
                      refine ⟨1931741436689074684036139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20605241991350129963052149 1931741436689074684036139)
                      ·
                        rfl

theorem cell23_3762053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 1, 5].length) (baseStart_3762053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762053 prefixEnd_3762053 := by exact prefixLift 3762053
  have htrace : WordTrace (prefixWord ++ tailWord_3762053) baseStart_3762053 baseEnd_3762053 := by
    simpa [prefixWord, tailWord_3762053, baseEnd_3762053] using wordTrace_append hprefix tailTrace_3762053
  have hstable : (prefixWord ++ tailWord_3762053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762053).length < 2 ^ (prefixWord ++ tailWord_3762053).sum := by decide
  have hdescent : baseEnd_3762053 < baseStart_3762053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762073 : List Nat := [1, 2, 1, 2, 1, 3, 6, 7]
def baseStart_3762073 : Nat := 118140960795 + 3762073 * 2 ^ 59
def prefixEnd_3762073 : Nat := 4983230072969 + 3 ^ 40 * 3762073 * 2
def baseEnd_3762073 : Nat := 71546359492672763177261

theorem tailTrace_3762073 : CollatzResearch.WordTrace tailWord_3762073 prefixEnd_3762073 71546359492672763177261 := by
  unfold tailWord_3762073
  simp only [CollatzResearch.WordTrace]
  refine ⟨137214074899659506760602873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91476049933106337840401915 137214074899659506760602873)
  ·
    refine ⟨102910556174744630070452155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137214074899659506760602873 102910556174744630070452155)
    ·
      refine ⟨154365834262116945105678233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102910556174744630070452155 154365834262116945105678233)
      ·
        refine ⟨115774375696587708829258675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154365834262116945105678233 115774375696587708829258675)
        ·
          refine ⟨173661563544881563243888013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115774375696587708829258675 173661563544881563243888013)
          ·
            refine ⟨65123086329330586216458005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173661563544881563243888013 65123086329330586216458005)
            ·
              refine ⟨3052644671687371228896469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 65123086329330586216458005 3052644671687371228896469)
              ·
                refine ⟨71546359492672763177261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3052644671687371228896469 71546359492672763177261)
                ·
                  rfl

theorem cell23_3762073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 7].length) (baseStart_3762073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762073 prefixEnd_3762073 := by exact prefixLift 3762073
  have htrace : WordTrace (prefixWord ++ tailWord_3762073) baseStart_3762073 baseEnd_3762073 := by
    simpa [prefixWord, tailWord_3762073, baseEnd_3762073] using wordTrace_append hprefix tailTrace_3762073
  have hstable : (prefixWord ++ tailWord_3762073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762073).length < 2 ^ (prefixWord ++ tailWord_3762073).sum := by decide
  have hdescent : baseEnd_3762073 < baseStart_3762073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762083 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 3, 3, 3]
def baseStart_3762083 : Nat := 118140960795 + 3762083 * 2 ^ 59
def prefixEnd_3762083 : Nat := 4983230072969 + 3 ^ 40 * 3762083 * 2
def baseEnd_3762083 : Nat := 1931756841108709566661001

theorem tailTrace_3762083 : CollatzResearch.WordTrace tailWord_3762083 prefixEnd_3762083 1931756841108709566661001 := by
  unfold tailWord_3762083
  simp only [CollatzResearch.WordTrace]
  refine ⟨137214439629623278468466903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91476293086415518978977935 137214439629623278468466903)
  ·
    refine ⟨205821659444434917702700355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137214439629623278468466903 205821659444434917702700355)
    ·
      refine ⟨308732489166652376554050533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205821659444434917702700355 308732489166652376554050533)
      ·
        refine ⟨57887341718747320603884475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 308732489166652376554050533 57887341718747320603884475)
        ·
          refine ⟨86831012578120980905826713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57887341718747320603884475 86831012578120980905826713)
          ·
            refine ⟨65123259433590735679370035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86831012578120980905826713 65123259433590735679370035)
            ·
              refine ⟨97684889150386103519055053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65123259433590735679370035 97684889150386103519055053)
              ·
                refine ⟨36631833431394788819645645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97684889150386103519055053 36631833431394788819645645)
                ·
                  refine ⟨13736937536773045807367117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36631833431394788819645645 13736937536773045807367117)
                  ·
                    refine ⟨5151351576289892177762669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13736937536773045807367117 5151351576289892177762669)
                    ·
                      refine ⟨1931756841108709566661001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5151351576289892177762669 1931756841108709566661001)
                      ·
                        rfl

theorem cell23_3762083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_3762083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762083 prefixEnd_3762083 := by exact prefixLift 3762083
  have htrace : WordTrace (prefixWord ++ tailWord_3762083) baseStart_3762083 baseEnd_3762083 := by
    simpa [prefixWord, tailWord_3762083, baseEnd_3762083] using wordTrace_append hprefix tailTrace_3762083
  have hstable : (prefixWord ++ tailWord_3762083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762083).length < 2 ^ (prefixWord ++ tailWord_3762083).sum := by decide
  have hdescent : baseEnd_3762083 < baseStart_3762083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762087 : List Nat := [1, 1, 6, 1, 2, 1, 2, 3, 1, 2, 3]
def baseStart_3762087 : Nat := 118140960795 + 3762087 * 2 ^ 59
def prefixEnd_3762087 : Nat := 4983230072969 + 3 ^ 40 * 3762087 * 2
def baseEnd_3762087 : Nat := 1931758895031327551010983

theorem tailTrace_3762087 : CollatzResearch.WordTrace tailWord_3762087 prefixEnd_3762087 1931758895031327551010983 := by
  unfold tailWord_3762087
  simp only [CollatzResearch.WordTrace]
  refine ⟨137214585521608787151612515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91476390347739191434408343 137214585521608787151612515)
  ·
    refine ⟨205821878282413180727418773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137214585521608787151612515 205821878282413180727418773)
    ·
      refine ⟨9647900544488117846597755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 205821878282413180727418773 9647900544488117846597755)
      ·
        refine ⟨14471850816732176769896633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9647900544488117846597755 14471850816732176769896633)
        ·
          refine ⟨10853888112549132577422475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14471850816732176769896633 10853888112549132577422475)
          ·
            refine ⟨16280832168823698866133713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10853888112549132577422475 16280832168823698866133713)
            ·
              refine ⟨12210624126617774149600285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16280832168823698866133713 12210624126617774149600285)
              ·
                refine ⟨4578984047481665306100107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12210624126617774149600285 4578984047481665306100107)
                ·
                  refine ⟨6868476071222497959150161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4578984047481665306100107 6868476071222497959150161)
                  ·
                    refine ⟨5151357053416873469362621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6868476071222497959150161 5151357053416873469362621)
                    ·
                      refine ⟨1931758895031327551010983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5151357053416873469362621 1931758895031327551010983)
                      ·
                        rfl

theorem cell23_3762087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_3762087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762087 prefixEnd_3762087 := by exact prefixLift 3762087
  have htrace : WordTrace (prefixWord ++ tailWord_3762087) baseStart_3762087 baseEnd_3762087 := by
    simpa [prefixWord, tailWord_3762087, baseEnd_3762087] using wordTrace_append hprefix tailTrace_3762087
  have hstable : (prefixWord ++ tailWord_3762087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762087).length < 2 ^ (prefixWord ++ tailWord_3762087).sum := by decide
  have hdescent : baseEnd_3762087 < baseStart_3762087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762134 : List Nat := [5, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3]
def baseStart_3762134 : Nat := 118140960795 + 3762134 * 2 ^ 59
def prefixEnd_3762134 : Nat := 4983230072969 + 3 ^ 40 * 3762134 * 2
def baseEnd_3762134 : Nat := 1931783028622088867123267

theorem tailTrace_3762134 : CollatzResearch.WordTrace tailWord_3762134 prefixEnd_3762134 1931783028622088867123267 := by
  unfold tailWord_3762134
  simp only [CollatzResearch.WordTrace]
  refine ⟨8576018734527407136160841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91477533168292342785715637 8576018734527407136160841)
  ·
    refine ⟨6432014050895555352120631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8576018734527407136160841 6432014050895555352120631)
    ·
      refine ⟨9648021076343333028180947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6432014050895555352120631 9648021076343333028180947)
      ·
        refine ⟨14472031614514999542271421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9648021076343333028180947 14472031614514999542271421)
        ·
          refine ⟨5427011855443124828351783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14472031614514999542271421 5427011855443124828351783)
          ·
            refine ⟨8140517783164687242527675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5427011855443124828351783 8140517783164687242527675)
            ·
              refine ⟨12210776674747030863791513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8140517783164687242527675 12210776674747030863791513)
              ·
                refine ⟨9158082506060273147843635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12210776674747030863791513 9158082506060273147843635)
                ·
                  refine ⟨13737123759090409721765453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9158082506060273147843635 13737123759090409721765453)
                  ·
                    refine ⟨5151421409658903645662045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13737123759090409721765453 5151421409658903645662045)
                    ·
                      refine ⟨1931783028622088867123267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5151421409658903645662045 1931783028622088867123267)
                      ·
                        rfl

theorem cell23_3762134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_3762134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762134 prefixEnd_3762134 := by exact prefixLift 3762134
  have htrace : WordTrace (prefixWord ++ tailWord_3762134) baseStart_3762134 baseEnd_3762134 := by
    simpa [prefixWord, tailWord_3762134, baseEnd_3762134] using wordTrace_append hprefix tailTrace_3762134
  have hstable : (prefixWord ++ tailWord_3762134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762134).length < 2 ^ (prefixWord ++ tailWord_3762134).sum := by decide
  have hdescent : baseEnd_3762134 < baseStart_3762134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762174 : List Nat := [4, 2, 2, 2, 1, 1, 1, 3, 1, 4, 2]
def baseStart_3762174 : Nat := 118140960795 + 3762174 * 2 ^ 59
def prefixEnd_3762174 : Nat := 4983230072969 + 3 ^ 40 * 3762174 * 2
def baseEnd_3762174 : Nat := 1931803567848268710623083

theorem tailTrace_3762174 : CollatzResearch.WordTrace tailWord_3762174 prefixEnd_3762174 1931803567848268710623083 := by
  unfold tailWord_3762174
  simp only [CollatzResearch.WordTrace]
  refine ⟨17152219834036700126253697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91478505781529067340019717 17152219834036700126253697)
  ·
    refine ⟨12864164875527525094690273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17152219834036700126253697 12864164875527525094690273)
    ·
      refine ⟨9648123656645643821017705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12864164875527525094690273 9648123656645643821017705)
      ·
        refine ⟨7236092742484232865763279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9648123656645643821017705 7236092742484232865763279)
        ·
          refine ⟨10854139113726349298644919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7236092742484232865763279 10854139113726349298644919)
          ·
            refine ⟨16281208670589523947967379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10854139113726349298644919 16281208670589523947967379)
            ·
              refine ⟨24421813005884285921951069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16281208670589523947967379 24421813005884285921951069)
              ·
                refine ⟨9158179877206607220731651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24421813005884285921951069 9158179877206607220731651)
                ·
                  refine ⟨13737269815809910831097477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9158179877206607220731651 13737269815809910831097477)
                  ·
                    refine ⟨2575738090464358280830777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13737269815809910831097477 2575738090464358280830777)
                    ·
                      refine ⟨1931803567848268710623083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2575738090464358280830777 1931803567848268710623083)
                      ·
                        rfl

theorem cell23_3762174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_3762174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762174 prefixEnd_3762174 := by exact prefixLift 3762174
  have htrace : WordTrace (prefixWord ++ tailWord_3762174) baseStart_3762174 baseEnd_3762174 := by
    simpa [prefixWord, tailWord_3762174, baseEnd_3762174] using wordTrace_append hprefix tailTrace_3762174
  have hstable : (prefixWord ++ tailWord_3762174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762174).length < 2 ^ (prefixWord ++ tailWord_3762174).sum := by decide
  have hdescent : baseEnd_3762174 < baseStart_3762174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762190 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3]
def baseStart_3762190 : Nat := 118140960795 + 3762190 * 2 ^ 59
def prefixEnd_3762190 : Nat := 4983230072969 + 3 ^ 40 * 3762190 * 2
def baseEnd_3762190 : Nat := 1931811783538740648023009

theorem tailTrace_3762190 : CollatzResearch.WordTrace tailWord_3762190 prefixEnd_3762190 1931811783538740648023009 := by
  unfold tailWord_3762190
  simp only [CollatzResearch.WordTrace]
  refine ⟨17152292780029454467826503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91478894826823757161741349 17152292780029454467826503)
  ·
    refine ⟨25728439170044181701739755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17152292780029454467826503 25728439170044181701739755)
    ·
      refine ⟨38592658755066272552609633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25728439170044181701739755 38592658755066272552609633)
      ·
        refine ⟨28944494066299704414457225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38592658755066272552609633 28944494066299704414457225)
        ·
          refine ⟨21708370549724778310842919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28944494066299704414457225 21708370549724778310842919)
          ·
            refine ⟨32562555824587167466264379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21708370549724778310842919 32562555824587167466264379)
            ·
              refine ⟨48843833736880751199396569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32562555824587167466264379 48843833736880751199396569)
              ·
                refine ⟨36632875302660563399547427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48843833736880751199396569 36632875302660563399547427)
                ·
                  refine ⟨54949312953990845099321141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36632875302660563399547427 54949312953990845099321141)
                  ·
                    refine ⟨5151498089436641728061357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54949312953990845099321141 5151498089436641728061357)
                    ·
                      refine ⟨1931811783538740648023009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5151498089436641728061357 1931811783538740648023009)
                      ·
                        rfl

theorem cell23_3762190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_3762190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762190 prefixEnd_3762190 := by exact prefixLift 3762190
  have htrace : WordTrace (prefixWord ++ tailWord_3762190) baseStart_3762190 baseEnd_3762190 := by
    simpa [prefixWord, tailWord_3762190, baseEnd_3762190] using wordTrace_append hprefix tailTrace_3762190
  have hstable : (prefixWord ++ tailWord_3762190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762190).length < 2 ^ (prefixWord ++ tailWord_3762190).sum := by decide
  have hdescent : baseEnd_3762190 < baseStart_3762190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762203 : List Nat := [1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 5]
def baseStart_3762203 : Nat := 118140960795 + 3762203 * 2 ^ 59
def prefixEnd_3762203 : Nat := 4983230072969 + 3 ^ 40 * 3762203 * 2
def baseEnd_3762203 : Nat := 1931818458787249097160449

theorem tailTrace_3762203 : CollatzResearch.WordTrace tailWord_3762203 prefixEnd_3762203 1931818458787249097160449 := by
  unfold tailWord_3762203
  simp only [CollatzResearch.WordTrace]
  refine ⟨137218816389188538962835263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91479210926125692641890175 137218816389188538962835263)
  ·
    refine ⟨205828224583782808444252895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137218816389188538962835263 205828224583782808444252895)
    ·
      refine ⟨308742336875674212666379343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205828224583782808444252895 308742336875674212666379343)
      ·
        refine ⟨463113505313511318999569015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308742336875674212666379343 463113505313511318999569015)
        ·
          refine ⟨694670257970266978499353523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463113505313511318999569015 694670257970266978499353523)
          ·
            refine ⟨1042005386955400467749030285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 694670257970266978499353523 1042005386955400467749030285)
            ·
              refine ⟨390752020108275175405886357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1042005386955400467749030285 390752020108275175405886357)
              ·
                refine ⟨18316500942575398847150923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 390752020108275175405886357 18316500942575398847150923)
                ·
                  refine ⟨27474751413863098270726385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18316500942575398847150923 27474751413863098270726385)
                  ·
                    refine ⟨20606063560397323703044789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27474751413863098270726385 20606063560397323703044789)
                    ·
                      refine ⟨1931818458787249097160449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20606063560397323703044789 1931818458787249097160449)
                      ·
                        rfl

theorem cell23_3762203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 5].length) (baseStart_3762203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762203 prefixEnd_3762203 := by exact prefixLift 3762203
  have htrace : WordTrace (prefixWord ++ tailWord_3762203) baseStart_3762203 baseEnd_3762203 := by
    simpa [prefixWord, tailWord_3762203, baseEnd_3762203] using wordTrace_append hprefix tailTrace_3762203
  have hstable : (prefixWord ++ tailWord_3762203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762203).length < 2 ^ (prefixWord ++ tailWord_3762203).sum := by decide
  have hdescent : baseEnd_3762203 < baseStart_3762203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762210 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 4, 5]
def baseStart_3762210 : Nat := 118140960795 + 3762210 * 2 ^ 59
def prefixEnd_3762210 : Nat := 4983230072969 + 3 ^ 40 * 3762210 * 2
def baseEnd_3762210 : Nat := 643940684383943523257639

theorem tailTrace_3762210 : CollatzResearch.WordTrace tailWord_3762210 prefixEnd_3762210 643940684383943523257639 := by
  unfold tailWord_3762210
  simp only [CollatzResearch.WordTrace]
  refine ⟨34304767925040794789585021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91479381133442119438893389 34304767925040794789585021)
  ·
    refine ⟨12864287971890298046094383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34304767925040794789585021 12864287971890298046094383)
    ·
      refine ⟨19296431957835447069141575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12864287971890298046094383 19296431957835447069141575)
      ·
        refine ⟨28944647936753170603712363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19296431957835447069141575 28944647936753170603712363)
        ·
          refine ⟨43416971905129755905568545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28944647936753170603712363 43416971905129755905568545)
          ·
            refine ⟨32562728928847316929176409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43416971905129755905568545 32562728928847316929176409)
            ·
              refine ⟨24422046696635487696882307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32562728928847316929176409 24422046696635487696882307)
              ·
                refine ⟨36633070044953231545323461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24422046696635487696882307 36633070044953231545323461)
                ·
                  refine ⟨6868700633428730914748149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36633070044953231545323461 6868700633428730914748149)
                  ·
                    refine ⟨643940684383943523257639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6868700633428730914748149 643940684383943523257639)
                    ·
                      rfl

theorem cell23_3762210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_3762210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762210 prefixEnd_3762210 := by exact prefixLift 3762210
  have htrace : WordTrace (prefixWord ++ tailWord_3762210) baseStart_3762210 baseEnd_3762210 := by
    simpa [prefixWord, tailWord_3762210, baseEnd_3762210] using wordTrace_append hprefix tailTrace_3762210
  have hstable : (prefixWord ++ tailWord_3762210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762210).length < 2 ^ (prefixWord ++ tailWord_3762210).sum := by decide
  have hdescent : baseEnd_3762210 < baseStart_3762210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762243 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 6]
def baseStart_3762243 : Nat := 118140960795 + 3762243 * 2 ^ 59
def prefixEnd_3762243 : Nat := 4983230072969 + 3 ^ 40 * 3762243 * 2
def baseEnd_3762243 : Nat := 1931838998013428940660265

theorem tailTrace_3762243 : CollatzResearch.WordTrace tailWord_3762243 prefixEnd_3762243 1931838998013428940660265 := by
  unfold tailWord_3762243
  simp only [CollatzResearch.WordTrace]
  refine ⟨137220275309043625794291383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91480183539362417196194255 137220275309043625794291383)
  ·
    refine ⟨205830412963565438691437075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137220275309043625794291383 205830412963565438691437075)
    ·
      refine ⟨308745619445348158037155613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205830412963565438691437075 308745619445348158037155613)
      ·
        refine ⟨115779607292005559263933355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308745619445348158037155613 115779607292005559263933355)
        ·
          refine ⟨173669410938008338895900033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115779607292005559263933355 173669410938008338895900033)
          ·
            refine ⟨130252058203506254171925025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173669410938008338895900033 130252058203506254171925025)
            ·
              refine ⟨97689043652629690628943769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130252058203506254171925025 97689043652629690628943769)
              ·
                refine ⟨73266782739472267971707827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97689043652629690628943769 73266782739472267971707827)
                ·
                  refine ⟨109900174109208401957561741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73266782739472267971707827 109900174109208401957561741)
                  ·
                    refine ⟨41212565290953150734085653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109900174109208401957561741 41212565290953150734085653)
                    ·
                      refine ⟨1931838998013428940660265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41212565290953150734085653 1931838998013428940660265)
                      ·
                        rfl

theorem cell23_3762243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_3762243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762243 prefixEnd_3762243 := by exact prefixLift 3762243
  have htrace : WordTrace (prefixWord ++ tailWord_3762243) baseStart_3762243 baseEnd_3762243 := by
    simpa [prefixWord, tailWord_3762243, baseEnd_3762243] using wordTrace_append hprefix tailTrace_3762243
  have hstable : (prefixWord ++ tailWord_3762243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762243).length < 2 ^ (prefixWord ++ tailWord_3762243).sum := by decide
  have hdescent : baseEnd_3762243 < baseStart_3762243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762287 : List Nat := [1, 1, 2, 1, 3, 4, 4, 1, 6]
def baseStart_3762287 : Nat := 118140960795 + 3762287 * 2 ^ 59
def prefixEnd_3762287 : Nat := 4983230072969 + 3 ^ 40 * 3762287 * 2
def baseEnd_3762287 : Nat := 214651287906914085390007

theorem tailTrace_3762287 : CollatzResearch.WordTrace tailWord_3762287 prefixEnd_3762287 214651287906914085390007 := by
  unfold tailWord_3762287
  simp only [CollatzResearch.WordTrace]
  refine ⟨137221880120884221308893115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91481253413922814205928743 137221880120884221308893115)
  ·
    refine ⟨205832820181326331963339673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137221880120884221308893115 205832820181326331963339673)
    ·
      refine ⟨154374615135994748972504755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205832820181326331963339673 154374615135994748972504755)
      ·
        refine ⟨231561922703992123458757133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154374615135994748972504755 231561922703992123458757133)
        ·
          refine ⟨86835721013997046297033925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231561922703992123458757133 86835721013997046297033925)
          ·
            refine ⟨16281697690124446180693861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86835721013997046297033925 16281697690124446180693861)
            ·
              refine ⟨3052818316898333658880099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16281697690124446180693861 3052818316898333658880099)
              ·
                refine ⟨4579227475347500488320149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3052818316898333658880099 4579227475347500488320149)
                ·
                  refine ⟨214651287906914085390007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4579227475347500488320149 214651287906914085390007)
                  ·
                    rfl

theorem cell23_3762287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 6].length) (baseStart_3762287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762287 prefixEnd_3762287 := by exact prefixLift 3762287
  have htrace : WordTrace (prefixWord ++ tailWord_3762287) baseStart_3762287 baseEnd_3762287 := by
    simpa [prefixWord, tailWord_3762287, baseEnd_3762287] using wordTrace_append hprefix tailTrace_3762287
  have hstable : (prefixWord ++ tailWord_3762287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762287).length < 2 ^ (prefixWord ++ tailWord_3762287).sum := by decide
  have hdescent : baseEnd_3762287 < baseStart_3762287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762337 : List Nat := [1, 2, 3, 3, 1, 2, 1, 2, 3, 1, 4]
def baseStart_3762337 : Nat := 118140960795 + 3762337 * 2 ^ 59
def prefixEnd_3762337 : Nat := 4983230072969 + 3 ^ 40 * 3762337 * 2
def baseEnd_3762337 : Nat := 1931887265194951572884833

theorem tailTrace_3762337 : CollatzResearch.WordTrace tailWord_3762337 prefixEnd_3762337 1931887265194951572884833 := by
  unfold tailWord_3762337
  simp only [CollatzResearch.WordTrace]
  refine ⟨137223703770703079848213265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91482469180468719898808843 137223703770703079848213265)
  ·
    refine ⟨102917777828027309886159949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137223703770703079848213265 102917777828027309886159949)
    ·
      refine ⟨38594166685510241207309981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102917777828027309886159949 38594166685510241207309981)
      ·
        refine ⟨14472812507066340452741243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38594166685510241207309981 14472812507066340452741243)
        ·
          refine ⟨21709218760599510679111865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14472812507066340452741243 21709218760599510679111865)
          ·
            refine ⟨16281914070449633009333899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21709218760599510679111865 16281914070449633009333899)
            ·
              refine ⟨24422871105674449514000849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16281914070449633009333899 24422871105674449514000849)
              ·
                refine ⟨18317153329255837135500637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24422871105674449514000849 18317153329255837135500637)
                ·
                  refine ⟨6868932498470938925812739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18317153329255837135500637 6868932498470938925812739)
                  ·
                    refine ⟨10303398747706408388719109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6868932498470938925812739 10303398747706408388719109)
                    ·
                      refine ⟨1931887265194951572884833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10303398747706408388719109 1931887265194951572884833)
                      ·
                        rfl

theorem cell23_3762337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_3762337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762337 prefixEnd_3762337 := by exact prefixLift 3762337
  have htrace : WordTrace (prefixWord ++ tailWord_3762337) baseStart_3762337 baseEnd_3762337 := by
    simpa [prefixWord, tailWord_3762337, baseEnd_3762337] using wordTrace_append hprefix tailTrace_3762337
  have hstable : (prefixWord ++ tailWord_3762337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762337).length < 2 ^ (prefixWord ++ tailWord_3762337).sum := by decide
  have hdescent : baseEnd_3762337 < baseStart_3762337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762504 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 2, 5, 2]
def baseStart_3762504 : Nat := 118140960795 + 3762504 * 2 ^ 59
def prefixEnd_3762504 : Nat := 4983230072969 + 3 ^ 40 * 3762504 * 2
def baseEnd_3762504 : Nat := 1931973016464252419496565

theorem tailTrace_3762504 : CollatzResearch.WordTrace tailWord_3762504 prefixEnd_3762504 1931973016464252419496565 := by
  unfold tailWord_3762504
  simp only [CollatzResearch.WordTrace]
  refine ⟨68614897380549033684771283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91486529840732044913028377 68614897380549033684771283)
  ·
    refine ⟨102922346070823550527156925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68614897380549033684771283 102922346070823550527156925)
    ·
      refine ⟨38595879776558831447683847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102922346070823550527156925 38595879776558831447683847)
      ·
        refine ⟨57893819664838247171525771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38595879776558831447683847 57893819664838247171525771)
        ·
          refine ⟨86840729497257370757288657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57893819664838247171525771 86840729497257370757288657)
          ·
            refine ⟨65130547122943028067966493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86840729497257370757288657 65130547122943028067966493)
            ·
              refine ⟨24423955171103635525487435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65130547122943028067966493 24423955171103635525487435)
              ·
                refine ⟨36635932756655453288231153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24423955171103635525487435 36635932756655453288231153)
                ·
                  refine ⟨27476949567491589966173365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36635932756655453288231153 27476949567491589966173365)
                  ·
                    refine ⟨2575964021952336559328753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27476949567491589966173365 2575964021952336559328753)
                    ·
                      refine ⟨1931973016464252419496565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2575964021952336559328753 1931973016464252419496565)
                      ·
                        rfl

theorem cell23_3762504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 2, 5, 2].length) (baseStart_3762504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762504 prefixEnd_3762504 := by exact prefixLift 3762504
  have htrace : WordTrace (prefixWord ++ tailWord_3762504) baseStart_3762504 baseEnd_3762504 := by
    simpa [prefixWord, tailWord_3762504, baseEnd_3762504] using wordTrace_append hprefix tailTrace_3762504
  have hstable : (prefixWord ++ tailWord_3762504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762504).length < 2 ^ (prefixWord ++ tailWord_3762504).sum := by decide
  have hdescent : baseEnd_3762504 < baseStart_3762504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762561 : List Nat := [1, 2, 4, 3, 1, 1, 1, 3, 3, 4]
def baseStart_3762561 : Nat := 118140960795 + 3762561 * 2 ^ 59
def prefixEnd_3762561 : Nat := 4983230072969 + 3 ^ 40 * 3762561 * 2
def baseEnd_3762561 : Nat := 644000761620519565494601

theorem tailTrace_3762561 : CollatzResearch.WordTrace tailWord_3762561 prefixEnd_3762561 644000761620519565494601 := by
  unfold tailWord_3762561
  simp only [CollatzResearch.WordTrace]
  refine ⟨137231873721891566104367537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91487915814594377402911691 137231873721891566104367537)
  ·
    refine ⟨102923905291418674578275653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137231873721891566104367537 102923905291418674578275653)
    ·
      refine ⟨19298232242141001483426685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102923905291418674578275653 19298232242141001483426685)
      ·
        refine ⟨7236837090802875556285007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19298232242141001483426685 7236837090802875556285007)
        ·
          refine ⟨10855255636204313334427511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7236837090802875556285007 10855255636204313334427511)
          ·
            refine ⟨16282883454306470001641267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10855255636204313334427511 16282883454306470001641267)
            ·
              refine ⟨24424325181459705002461901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16282883454306470001641267 24424325181459705002461901)
              ·
                refine ⟨9159121943047389375923213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24424325181459705002461901 9159121943047389375923213)
                ·
                  refine ⟨3434670728642771015971205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9159121943047389375923213 3434670728642771015971205)
                  ·
                    refine ⟨644000761620519565494601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3434670728642771015971205 644000761620519565494601)
                    ·
                      rfl

theorem cell23_3762561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_3762561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762561 prefixEnd_3762561 := by exact prefixLift 3762561
  have htrace : WordTrace (prefixWord ++ tailWord_3762561) baseStart_3762561 baseEnd_3762561 := by
    simpa [prefixWord, tailWord_3762561, baseEnd_3762561] using wordTrace_append hprefix tailTrace_3762561
  have hstable : (prefixWord ++ tailWord_3762561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762561).length < 2 ^ (prefixWord ++ tailWord_3762561).sum := by decide
  have hdescent : baseEnd_3762561 < baseStart_3762561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762612 : List Nat := [2, 5, 2, 2, 1, 2, 1, 1, 3, 4]
def baseStart_3762612 : Nat := 118140960795 + 3762612 * 2 ^ 59
def prefixEnd_3762612 : Nat := 4983230072969 + 3 ^ 40 * 3762612 * 2
def baseEnd_3762612 : Nat := 644009490791645998982023

theorem tailTrace_3762612 : CollatzResearch.WordTrace tailWord_3762612 prefixEnd_3762612 644009490791645998982023 := by
  unfold tailWord_3762612
  simp only [CollatzResearch.WordTrace]
  refine ⟨68616866922353400907237045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91489155896471201209649393 68616866922353400907237045)
  ·
    refine ⟨6432831273970631335053473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68616866922353400907237045 6432831273970631335053473)
    ·
      refine ⟨4824623455477973501290105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6432831273970631335053473 4824623455477973501290105)
      ·
        refine ⟨3618467591608480125967579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4824623455477973501290105 3618467591608480125967579)
        ·
          refine ⟨5427701387412720188951369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3618467591608480125967579 5427701387412720188951369)
          ·
            refine ⟨4070776040559540141713527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5427701387412720188951369 4070776040559540141713527)
            ·
              refine ⟨6106164060839310212570291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4070776040559540141713527 6106164060839310212570291)
              ·
                refine ⟨9159246091258965318855437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6106164060839310212570291 9159246091258965318855437)
                ·
                  refine ⟨3434717284222111994570789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9159246091258965318855437 3434717284222111994570789)
                  ·
                    refine ⟨644009490791645998982023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3434717284222111994570789 644009490791645998982023)
                    ·
                      rfl

theorem cell23_3762612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_3762612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762612 prefixEnd_3762612 := by exact prefixLift 3762612
  have htrace : WordTrace (prefixWord ++ tailWord_3762612) baseStart_3762612 baseEnd_3762612 := by
    simpa [prefixWord, tailWord_3762612, baseEnd_3762612] using wordTrace_append hprefix tailTrace_3762612
  have hstable : (prefixWord ++ tailWord_3762612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762612).length < 2 ^ (prefixWord ++ tailWord_3762612).sum := by decide
  have hdescent : baseEnd_3762612 < baseStart_3762612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762618 : List Nat := [3, 1, 1, 1, 2, 1, 1, 8, 1, 1, 3]
def baseStart_3762618 : Nat := 118140960795 + 3762618 * 2 ^ 59
def prefixEnd_3762618 : Nat := 4983230072969 + 3 ^ 40 * 3762618 * 2
def baseEnd_3762618 : Nat := 1932031553258864973471041

theorem tailTrace_3762618 : CollatzResearch.WordTrace tailWord_3762618 prefixEnd_3762618 1932031553258864973471041 := by
  unfold tailWord_3762618
  simp only [CollatzResearch.WordTrace]
  refine ⟨34308488170671266209798127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91489301788456709892795005 34308488170671266209798127)
  ·
    refine ⟨51462732256006899314697191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34308488170671266209798127 51462732256006899314697191)
    ·
      refine ⟨77194098384010348972045787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51462732256006899314697191 77194098384010348972045787)
      ·
        refine ⟨115791147576015523458068681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77194098384010348972045787 115791147576015523458068681)
        ·
          refine ⟨86843360682011642593551511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115791147576015523458068681 86843360682011642593551511)
          ·
            refine ⟨130265041023017463890327267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86843360682011642593551511 130265041023017463890327267)
            ·
              refine ⟨195397561534526195835490901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130265041023017463890327267 195397561534526195835490901)
              ·
                refine ⟨2289815174232728857447159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 195397561534526195835490901 2289815174232728857447159)
                ·
                  refine ⟨3434722761349093286170739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2289815174232728857447159 3434722761349093286170739)
                  ·
                    refine ⟨5152084142023639929256109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3434722761349093286170739 5152084142023639929256109)
                    ·
                      refine ⟨1932031553258864973471041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5152084142023639929256109 1932031553258864973471041)
                      ·
                        rfl

theorem cell23_3762618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 8, 1, 1, 3].length) (baseStart_3762618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762618 prefixEnd_3762618 := by exact prefixLift 3762618
  have htrace : WordTrace (prefixWord ++ tailWord_3762618) baseStart_3762618 baseEnd_3762618 := by
    simpa [prefixWord, tailWord_3762618, baseEnd_3762618] using wordTrace_append hprefix tailTrace_3762618
  have hstable : (prefixWord ++ tailWord_3762618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762618).length < 2 ^ (prefixWord ++ tailWord_3762618).sum := by decide
  have hdescent : baseEnd_3762618 < baseStart_3762618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762624 : List Nat := [2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 4]
def baseStart_3762624 : Nat := 118140960795 + 3762624 * 2 ^ 59
def prefixEnd_3762624 : Nat := 4983230072969 + 3 ^ 40 * 3762624 * 2
def baseEnd_3762624 : Nat := 1932034634142791949996013

theorem tailTrace_3762624 : CollatzResearch.WordTrace tailWord_3762624 prefixEnd_3762624 1932034634142791949996013 := by
  unfold tailWord_3762624
  simp only [CollatzResearch.WordTrace]
  refine ⟨68617085760331663931955463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91489447680442218575940617 68617085760331663931955463)
  ·
    refine ⟨102925628640497495897933195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68617085760331663931955463 102925628640497495897933195)
    ·
      refine ⟨154388442960746243846899793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102925628640497495897933195 154388442960746243846899793)
      ·
        refine ⟨115791332220559682885174845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154388442960746243846899793 115791332220559682885174845)
        ·
          refine ⟨43421749582709881081940567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115791332220559682885174845 43421749582709881081940567)
          ·
            refine ⟨65132624374064821622910851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43421749582709881081940567 65132624374064821622910851)
            ·
              refine ⟨97698936561097232434366277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65132624374064821622910851 97698936561097232434366277)
              ·
                refine ⟨18318550605205731081443677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97698936561097232434366277 18318550605205731081443677)
                ·
                  refine ⟨6869456476952149155541379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18318550605205731081443677 6869456476952149155541379)
                  ·
                    refine ⟨10304184715428223733312069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6869456476952149155541379 10304184715428223733312069)
                    ·
                      refine ⟨1932034634142791949996013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10304184715428223733312069 1932034634142791949996013)
                      ·
                        rfl

theorem cell23_3762624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 4].length) (baseStart_3762624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762624 prefixEnd_3762624 := by exact prefixLift 3762624
  have htrace : WordTrace (prefixWord ++ tailWord_3762624) baseStart_3762624 baseEnd_3762624 := by
    simpa [prefixWord, tailWord_3762624, baseEnd_3762624] using wordTrace_append hprefix tailTrace_3762624
  have hstable : (prefixWord ++ tailWord_3762624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762624).length < 2 ^ (prefixWord ++ tailWord_3762624).sum := by decide
  have hdescent : baseEnd_3762624 < baseStart_3762624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762625 : List Nat := [1, 2, 7, 1, 1, 1, 1, 3, 6]
def baseStart_3762625 : Nat := 118140960795 + 3762625 * 2 ^ 59
def prefixEnd_3762625 : Nat := 4983230072969 + 3 ^ 40 * 3762625 * 2
def baseEnd_3762625 : Nat := 214670571958160716231501

theorem tailTrace_3762625 : CollatzResearch.WordTrace tailWord_3762625 prefixEnd_3762625 214670571958160716231501 := by
  unfold tailWord_3762625
  simp only [CollatzResearch.WordTrace]
  refine ⟨137234207993659705034697329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91489471995773136689798219 137234207993659705034697329)
  ·
    refine ⟨102925655995244778776022997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137234207993659705034697329 102925655995244778776022997)
    ·
      refine ⟨2412320062388549502563039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 102925655995244778776022997 2412320062388549502563039)
      ·
        refine ⟨3618480093582824253844559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2412320062388549502563039 3618480093582824253844559)
        ·
          refine ⟨5427720140374236380766839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3618480093582824253844559 5427720140374236380766839)
          ·
            refine ⟨8141580210561354571150259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5427720140374236380766839 8141580210561354571150259)
            ·
              refine ⟨12212370315842031856725389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8141580210561354571150259 12212370315842031856725389)
              ·
                refine ⟨4579638868440761946272021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12212370315842031856725389 4579638868440761946272021)
                ·
                  refine ⟨214670571958160716231501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4579638868440761946272021 214670571958160716231501)
                  ·
                    rfl

theorem cell23_3762625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 6].length) (baseStart_3762625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762625 prefixEnd_3762625 := by exact prefixLift 3762625
  have htrace : WordTrace (prefixWord ++ tailWord_3762625) baseStart_3762625 baseEnd_3762625 := by
    simpa [prefixWord, tailWord_3762625, baseEnd_3762625] using wordTrace_append hprefix tailTrace_3762625
  have hstable : (prefixWord ++ tailWord_3762625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762625).length < 2 ^ (prefixWord ++ tailWord_3762625).sum := by decide
  have hdescent : baseEnd_3762625 < baseStart_3762625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762634 : List Nat := [3, 1, 2, 1, 2, 2, 2, 3, 1, 6]
def baseStart_3762634 : Nat := 118140960795 + 3762634 * 2 ^ 59
def prefixEnd_3762634 : Nat := 4983230072969 + 3 ^ 40 * 3762634 * 2
def baseEnd_3762634 : Nat := 644013256316445636956989

theorem tailTrace_3762634 : CollatzResearch.WordTrace tailWord_3762634 prefixEnd_3762634 644013256316445636956989 := by
  unfold tailWord_3762634
  simp only [CollatzResearch.WordTrace]
  refine ⟨34308634062656774892943739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91489690833751399714516637 34308634062656774892943739)
  ·
    refine ⟨51462951093985162339415609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34308634062656774892943739 51462951093985162339415609)
    ·
      refine ⟨38597213320488871754561707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51462951093985162339415609 38597213320488871754561707)
      ·
        refine ⟨57895819980733307631842561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38597213320488871754561707 57895819980733307631842561)
        ·
          refine ⟨43421864985549980723881921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57895819980733307631842561 43421864985549980723881921)
          ·
            refine ⟨32566398739162485542911441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43421864985549980723881921 32566398739162485542911441)
            ·
              refine ⟨24424799054371864157183581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32566398739162485542911441 24424799054371864157183581)
              ·
                refine ⟨9159299645389449058943843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24424799054371864157183581 9159299645389449058943843)
                ·
                  refine ⟨13738949468084173588415765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9159299645389449058943843 13738949468084173588415765)
                  ·
                    refine ⟨644013256316445636956989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13738949468084173588415765 644013256316445636956989)
                    ·
                      rfl

theorem cell23_3762634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_3762634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762634 prefixEnd_3762634 := by exact prefixLift 3762634
  have htrace : WordTrace (prefixWord ++ tailWord_3762634) baseStart_3762634 baseEnd_3762634 := by
    simpa [prefixWord, tailWord_3762634, baseEnd_3762634] using wordTrace_append hprefix tailTrace_3762634
  have hstable : (prefixWord ++ tailWord_3762634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762634).length < 2 ^ (prefixWord ++ tailWord_3762634).sum := by decide
  have hdescent : baseEnd_3762634 < baseStart_3762634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762669 : List Nat := [1, 5, 1, 3, 1, 3, 2, 2, 1, 1, 3]
def baseStart_3762669 : Nat := 118140960795 + 3762669 * 2 ^ 59
def prefixEnd_3762669 : Nat := 4983230072969 + 3 ^ 40 * 3762669 * 2
def baseEnd_3762669 : Nat := 1932057740772244273933307

theorem tailTrace_3762669 : CollatzResearch.WordTrace tailWord_3762669 prefixEnd_3762669 1932057740772244273933307 := by
  unfold tailWord_3762669
  simp only [CollatzResearch.WordTrace]
  refine ⟨137235812805500300549299061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91490541870333533699532707 137235812805500300549299061)
  ·
    refine ⟨12865857450515653176496787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137235812805500300549299061 12865857450515653176496787)
    ·
      refine ⟨19298786175773479764745181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12865857450515653176496787 19298786175773479764745181)
      ·
        refine ⟨7237044815915054911779443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19298786175773479764745181 7237044815915054911779443)
        ·
          refine ⟨10855567223872582367669165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7237044815915054911779443 10855567223872582367669165)
          ·
            refine ⟨4070837708952218387875937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10855567223872582367669165 4070837708952218387875937)
            ·
              refine ⟨3053128281714163790906953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4070837708952218387875937 3053128281714163790906953)
              ·
                refine ⟨2289846211285622843180215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3053128281714163790906953 2289846211285622843180215)
                ·
                  refine ⟨3434769316928434264770323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2289846211285622843180215 3434769316928434264770323)
                  ·
                    refine ⟨5152153975392651397155485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3434769316928434264770323 5152153975392651397155485)
                    ·
                      refine ⟨1932057740772244273933307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5152153975392651397155485 1932057740772244273933307)
                      ·
                        rfl

theorem cell23_3762669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_3762669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762669 prefixEnd_3762669 := by exact prefixLift 3762669
  have htrace : WordTrace (prefixWord ++ tailWord_3762669) baseStart_3762669 baseEnd_3762669 := by
    simpa [prefixWord, tailWord_3762669, baseEnd_3762669] using wordTrace_append hprefix tailTrace_3762669
  have hstable : (prefixWord ++ tailWord_3762669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762669).length < 2 ^ (prefixWord ++ tailWord_3762669).sum := by decide
  have hdescent : baseEnd_3762669 < baseStart_3762669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762675 : List Nat := [1, 1, 1, 2, 2, 2, 5, 4, 1, 2, 2]
def baseStart_3762675 : Nat := 118140960795 + 3762675 * 2 ^ 59
def prefixEnd_3762675 : Nat := 4983230072969 + 3 ^ 40 * 3762675 * 2
def baseEnd_3762675 : Nat := 1932060821656171250458279

theorem tailTrace_3762675 : CollatzResearch.WordTrace tailWord_3762675 prefixEnd_3762675 1932060821656171250458279 := by
  unfold tailWord_3762675
  simp only [CollatzResearch.WordTrace]
  refine ⟨137236031643478563574017479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91490687762319042382678319 137236031643478563574017479)
  ·
    refine ⟨205854047465217845361026219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137236031643478563574017479 205854047465217845361026219)
    ·
      refine ⟨308781071197826768041539329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205854047465217845361026219 308781071197826768041539329)
      ·
        refine ⟨231585803398370076031154497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308781071197826768041539329 231585803398370076031154497)
        ·
          refine ⟨173689352548777557023365873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231585803398370076031154497 173689352548777557023365873)
          ·
            refine ⟨130267014411583167767524405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173689352548777557023365873 130267014411583167767524405)
            ·
              refine ⟨12212532601085921978205413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130267014411583167767524405 12212532601085921978205413)
              ·
                refine ⟨2289849862703610370913515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12212532601085921978205413 2289849862703610370913515)
                ·
                  refine ⟨3434774794055415556370273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2289849862703610370913515 3434774794055415556370273)
                  ·
                    refine ⟨2576081095541561667277705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3434774794055415556370273 2576081095541561667277705)
                    ·
                      refine ⟨1932060821656171250458279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2576081095541561667277705 1932060821656171250458279)
                      ·
                        rfl

theorem cell23_3762675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 4, 1, 2, 2].length) (baseStart_3762675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762675 prefixEnd_3762675 := by exact prefixLift 3762675
  have htrace : WordTrace (prefixWord ++ tailWord_3762675) baseStart_3762675 baseEnd_3762675 := by
    simpa [prefixWord, tailWord_3762675, baseEnd_3762675] using wordTrace_append hprefix tailTrace_3762675
  have hstable : (prefixWord ++ tailWord_3762675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762675).length < 2 ^ (prefixWord ++ tailWord_3762675).sum := by decide
  have hdescent : baseEnd_3762675 < baseStart_3762675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762691 : List Nat := [1, 1, 1, 3, 2, 1, 6, 1, 1, 3, 3]
def baseStart_3762691 : Nat := 118140960795 + 3762691 * 2 ^ 59
def prefixEnd_3762691 : Nat := 4983230072969 + 3 ^ 40 * 3762691 * 2
def baseEnd_3762691 : Nat := 1932069037346643187858205

theorem tailTrace_3762691 : CollatzResearch.WordTrace tailWord_3762691 prefixEnd_3762691 1932069037346643187858205 := by
  unfold tailWord_3762691
  simp only [CollatzResearch.WordTrace]
  refine ⟨137236615211420598306599927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91491076807613732204399951 137236615211420598306599927)
  ·
    refine ⟨205854922817130897459899891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137236615211420598306599927 205854922817130897459899891)
    ·
      refine ⟨308782384225696346189849837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205854922817130897459899891 308782384225696346189849837)
      ·
        refine ⟨115793394084636129821193689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308782384225696346189849837 115793394084636129821193689)
        ·
          refine ⟨86845045563477097365895267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115793394084636129821193689 86845045563477097365895267)
          ·
            refine ⟨130267568345215646048842901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86845045563477097365895267 130267568345215646048842901)
            ·
              refine ⟨6106292266181983408539511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 130267568345215646048842901 6106292266181983408539511)
              ·
                refine ⟨9159438399272975112809267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6106292266181983408539511 9159438399272975112809267)
                ·
                  refine ⟨13739157598909462669213901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9159438399272975112809267 13739157598909462669213901)
                  ·
                    refine ⟨5152184099591048500955213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13739157598909462669213901 5152184099591048500955213)
                    ·
                      refine ⟨1932069037346643187858205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5152184099591048500955213 1932069037346643187858205)
                      ·
                        rfl

theorem cell23_3762691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 3, 3].length) (baseStart_3762691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762691 prefixEnd_3762691 := by exact prefixLift 3762691
  have htrace : WordTrace (prefixWord ++ tailWord_3762691) baseStart_3762691 baseEnd_3762691 := by
    simpa [prefixWord, tailWord_3762691, baseEnd_3762691] using wordTrace_append hprefix tailTrace_3762691
  have hstable : (prefixWord ++ tailWord_3762691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762691).length < 2 ^ (prefixWord ++ tailWord_3762691).sum := by decide
  have hdescent : baseEnd_3762691 < baseStart_3762691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762731 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 3, 4, 2]
def baseStart_3762731 : Nat := 118140960795 + 3762731 * 2 ^ 59
def prefixEnd_3762731 : Nat := 4983230072969 + 3 ^ 40 * 3762731 * 2
def baseEnd_3762731 : Nat := 1932089576572823031358021

theorem tailTrace_3762731 : CollatzResearch.WordTrace tailWord_3762731 prefixEnd_3762731 1932089576572823031358021 := by
  unfold tailWord_3762731
  simp only [CollatzResearch.WordTrace]
  refine ⟨137238074131275685138056047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91492049420850456758704031 137238074131275685138056047)
  ·
    refine ⟨205857111196913527707084071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137238074131275685138056047 205857111196913527707084071)
    ·
      refine ⟨308785666795370291560626107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205857111196913527707084071 308785666795370291560626107)
      ·
        refine ⟨463178500193055437340939161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308785666795370291560626107 463178500193055437340939161)
        ·
          refine ⟨347383875144791578005704371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463178500193055437340939161 347383875144791578005704371)
          ·
            refine ⟨521075812717187367008556557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347383875144791578005704371 521075812717187367008556557)
            ·
              refine ⟨195403429768945262628208709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 521075812717187367008556557 195403429768945262628208709)
              ·
                refine ⟨36638143081677236742789133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195403429768945262628208709 36638143081677236742789133)
                ·
                  refine ⟨13739303655628963778545925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36638143081677236742789133 13739303655628963778545925)
                  ·
                    refine ⟨2576119435430430708477361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13739303655628963778545925 2576119435430430708477361)
                    ·
                      refine ⟨1932089576572823031358021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2576119435430430708477361 1932089576572823031358021)
                      ·
                        rfl

theorem cell23_3762731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 3, 4, 2].length) (baseStart_3762731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762731 prefixEnd_3762731 := by exact prefixLift 3762731
  have htrace : WordTrace (prefixWord ++ tailWord_3762731) baseStart_3762731 baseEnd_3762731 := by
    simpa [prefixWord, tailWord_3762731, baseEnd_3762731] using wordTrace_append hprefix tailTrace_3762731
  have hstable : (prefixWord ++ tailWord_3762731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762731).length < 2 ^ (prefixWord ++ tailWord_3762731).sum := by decide
  have hdescent : baseEnd_3762731 < baseStart_3762731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762831 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 5, 4]
def baseStart_3762831 : Nat := 118140960795 + 3762831 * 2 ^ 59
def prefixEnd_3762831 : Nat := 4983230072969 + 3 ^ 40 * 3762831 * 2
def baseEnd_3762831 : Nat := 644046974879424213369187

theorem tailTrace_3762831 : CollatzResearch.WordTrace tailWord_3762831 prefixEnd_3762831 644046974879424213369187 := by
  unfold tailWord_3762831
  simp only [CollatzResearch.WordTrace]
  refine ⟨137241721430913402216696347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91494480953942268144464231 137241721430913402216696347)
  ·
    refine ⟨205862582146370103325044521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137241721430913402216696347 205862582146370103325044521)
    ·
      refine ⟨154396936609777577493783391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205862582146370103325044521 154396936609777577493783391)
      ·
        refine ⟨231595404914666366240675087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154396936609777577493783391 231595404914666366240675087)
        ·
          refine ⟨347393107371999549361012631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231595404914666366240675087 347393107371999549361012631)
          ·
            refine ⟨521089661057999324041518947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347393107371999549361012631 521089661057999324041518947)
            ·
              refine ⟨781634491586998986062278421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521089661057999324041518947 781634491586998986062278421)
              ·
                refine ⟨36639116793140577471669301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 781634491586998986062278421 36639116793140577471669301)
                ·
                  refine ⟨3434917199356929137968997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36639116793140577471669301 3434917199356929137968997)
                  ·
                    refine ⟨644046974879424213369187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3434917199356929137968997 644046974879424213369187)
                    ·
                      rfl

theorem cell23_3762831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 5, 4].length) (baseStart_3762831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762831 prefixEnd_3762831 := by exact prefixLift 3762831
  have htrace : WordTrace (prefixWord ++ tailWord_3762831) baseStart_3762831 baseEnd_3762831 := by
    simpa [prefixWord, tailWord_3762831, baseEnd_3762831] using wordTrace_append hprefix tailTrace_3762831
  have hstable : (prefixWord ++ tailWord_3762831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762831).length < 2 ^ (prefixWord ++ tailWord_3762831).sum := by decide
  have hdescent : baseEnd_3762831 < baseStart_3762831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762905 : List Nat := [1, 2, 1, 2, 3, 2, 4, 1, 3, 1, 3]
def baseStart_3762905 : Nat := 118140960795 + 3762905 * 2 ^ 59
def prefixEnd_3762905 : Nat := 4983230072969 + 3 ^ 40 * 3762905 * 2
def baseEnd_3762905 : Nat := 1932178922206705350582221

theorem tailTrace_3762905 : CollatzResearch.WordTrace tailWord_3762905 prefixEnd_3762905 1932178922206705350582221 := by
  unfold tailWord_3762905
  simp only [CollatzResearch.WordTrace]
  refine ⟨137244420432645312854890169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91496280288430208569926779 137244420432645312854890169)
  ·
    refine ⟨102933315324483984641167627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137244420432645312854890169 102933315324483984641167627)
    ·
      refine ⟨154399972986725976961751441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102933315324483984641167627 154399972986725976961751441)
      ·
        refine ⟨115799979740044482721313581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154399972986725976961751441 115799979740044482721313581)
        ·
          refine ⟨43424992402516681020492593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115799979740044482721313581 43424992402516681020492593)
          ·
            refine ⟨32568744301887510765369445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43424992402516681020492593 32568744301887510765369445)
            ·
              refine ⟨6106639556603908268506771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32568744301887510765369445 6106639556603908268506771)
              ·
                refine ⟨9159959334905862402760157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6106639556603908268506771 9159959334905862402760157)
                ·
                  refine ⟨3434984750589698401035059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9159959334905862402760157 3434984750589698401035059)
                  ·
                    refine ⟨5152477125884547601552589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3434984750589698401035059 5152477125884547601552589)
                    ·
                      refine ⟨1932178922206705350582221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5152477125884547601552589 1932178922206705350582221)
                      ·
                        rfl

theorem cell23_3762905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 3, 1, 3].length) (baseStart_3762905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762905 prefixEnd_3762905 := by exact prefixLift 3762905
  have htrace : WordTrace (prefixWord ++ tailWord_3762905) baseStart_3762905 baseEnd_3762905 := by
    simpa [prefixWord, tailWord_3762905, baseEnd_3762905] using wordTrace_append hprefix tailTrace_3762905
  have hstable : (prefixWord ++ tailWord_3762905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762905).length < 2 ^ (prefixWord ++ tailWord_3762905).sum := by decide
  have hdescent : baseEnd_3762905 < baseStart_3762905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762915 : List Nat := [1, 1, 1, 7, 1, 1, 1, 2, 1, 5, 2]
def baseStart_3762915 : Nat := 118140960795 + 3762915 * 2 ^ 59
def prefixEnd_3762915 : Nat := 4983230072969 + 3 ^ 40 * 3762915 * 2
def baseEnd_3762915 : Nat := 1932184057013250311457175

theorem tailTrace_3762915 : CollatzResearch.WordTrace tailWord_3762915 prefixEnd_3762915 1932184057013250311457175 := by
  unfold tailWord_3762915
  simp only [CollatzResearch.WordTrace]
  refine ⟨137244785162609084562754199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91496523441739389708502799 137244785162609084562754199)
  ·
    refine ⟨205867177743913626844131299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137244785162609084562754199 205867177743913626844131299)
    ·
      refine ⟨308800766615870440266196949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205867177743913626844131299 308800766615870440266196949)
      ·
        refine ⟨7237517967559463443738991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 308800766615870440266196949 7237517967559463443738991)
        ·
          refine ⟨10856276951339195165608487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7237517967559463443738991 10856276951339195165608487)
          ·
            refine ⟨16284415427008792748412731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10856276951339195165608487 16284415427008792748412731)
            ·
              refine ⟨24426623140513189122619097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16284415427008792748412731 24426623140513189122619097)
              ·
                refine ⟨18319967355384891841964323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24426623140513189122619097 18319967355384891841964323)
                ·
                  refine ⟨27479951033077337762946485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18319967355384891841964323 27479951033077337762946485)
                  ·
                    refine ⟨2576245409351000415276233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27479951033077337762946485 2576245409351000415276233)
                    ·
                      refine ⟨1932184057013250311457175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2576245409351000415276233 1932184057013250311457175)
                      ·
                        rfl

theorem cell23_3762915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_3762915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762915 prefixEnd_3762915 := by exact prefixLift 3762915
  have htrace : WordTrace (prefixWord ++ tailWord_3762915) baseStart_3762915 baseEnd_3762915 := by
    simpa [prefixWord, tailWord_3762915, baseEnd_3762915] using wordTrace_append hprefix tailTrace_3762915
  have hstable : (prefixWord ++ tailWord_3762915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762915).length < 2 ^ (prefixWord ++ tailWord_3762915).sum := by decide
  have hdescent : baseEnd_3762915 < baseStart_3762915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762925 : List Nat := [1, 5, 1, 2, 1, 1, 4, 2, 1, 5]
def baseStart_3762925 : Nat := 118140960795 + 3762925 * 2 ^ 59
def prefixEnd_3762925 : Nat := 4983230072969 + 3 ^ 40 * 3762925 * 2
def baseEnd_3762925 : Nat := 644063063939931757444043

theorem tailTrace_3762925 : CollatzResearch.WordTrace tailWord_3762925 prefixEnd_3762925 644063063939931757444043 := by
  unfold tailWord_3762925
  simp only [CollatzResearch.WordTrace]
  refine ⟨137245149892572856270618229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91496766595048570847078819 137245149892572856270618229)
  ·
    refine ⟨12866732802428705275370459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137245149892572856270618229 12866732802428705275370459)
    ·
      refine ⟨19300099203643057913055689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12866732802428705275370459 19300099203643057913055689)
      ·
        refine ⟨14475074402732293434791767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19300099203643057913055689 14475074402732293434791767)
        ·
          refine ⟨21712611604098440152187651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14475074402732293434791767 21712611604098440152187651)
          ·
            refine ⟨32568917406147660228281477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21712611604098440152187651 32568917406147660228281477)
            ·
              refine ⟨6106672013652686292802777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32568917406147660228281477 6106672013652686292802777)
              ·
                refine ⟨4580004010239514719602083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6106672013652686292802777 4580004010239514719602083)
                ·
                  refine ⟨6870006015359272079403125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4580004010239514719602083 6870006015359272079403125)
                  ·
                    refine ⟨644063063939931757444043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6870006015359272079403125 644063063939931757444043)
                    ·
                      rfl

theorem cell23_3762925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_3762925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762925 prefixEnd_3762925 := by exact prefixLift 3762925
  have htrace : WordTrace (prefixWord ++ tailWord_3762925) baseStart_3762925 baseEnd_3762925 := by
    simpa [prefixWord, tailWord_3762925, baseEnd_3762925] using wordTrace_append hprefix tailTrace_3762925
  have hstable : (prefixWord ++ tailWord_3762925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762925).length < 2 ^ (prefixWord ++ tailWord_3762925).sum := by decide
  have hdescent : baseEnd_3762925 < baseStart_3762925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762928 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 2, 6, 2]
def baseStart_3762928 : Nat := 118140960795 + 3762928 * 2 ^ 59
def prefixEnd_3762928 : Nat := 4983230072969 + 3 ^ 40 * 3762928 * 2
def baseEnd_3762928 : Nat := 1932190732261758760594615

theorem tailTrace_3762928 : CollatzResearch.WordTrace tailWord_3762928 prefixEnd_3762928 1932190732261758760594615 := by
  unfold tailWord_3762928
  simp only [CollatzResearch.WordTrace]
  refine ⟨68622629655780993891488719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91496839541041325188651625 68622629655780993891488719)
  ·
    refine ⟨102933944483671490837233079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68622629655780993891488719 102933944483671490837233079)
    ·
      refine ⟨154400916725507236255849619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102933944483671490837233079 154400916725507236255849619)
      ·
        refine ⟨231601375088260854383774429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154400916725507236255849619 231601375088260854383774429)
        ·
          refine ⟨86850515658097820393915411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231601375088260854383774429 86850515658097820393915411)
          ·
            refine ⟨130275773487146730590873117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86850515658097820393915411 130275773487146730590873117)
            ·
              refine ⟨48853415057680023971577419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130275773487146730590873117 48853415057680023971577419)
              ·
                refine ⟨73280122586520035957366129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48853415057680023971577419 73280122586520035957366129)
                ·
                  refine ⟨54960091939890026968024597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73280122586520035957366129 54960091939890026968024597)
                  ·
                    refine ⟨2576254309682345014126153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 54960091939890026968024597 2576254309682345014126153)
                    ·
                      refine ⟨1932190732261758760594615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2576254309682345014126153 1932190732261758760594615)
                      ·
                        rfl

theorem cell23_3762928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 2, 6, 2].length) (baseStart_3762928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762928 prefixEnd_3762928 := by exact prefixLift 3762928
  have htrace : WordTrace (prefixWord ++ tailWord_3762928) baseStart_3762928 baseEnd_3762928 := by
    simpa [prefixWord, tailWord_3762928, baseEnd_3762928] using wordTrace_append hprefix tailTrace_3762928
  have hstable : (prefixWord ++ tailWord_3762928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762928).length < 2 ^ (prefixWord ++ tailWord_3762928).sum := by decide
  have hdescent : baseEnd_3762928 < baseStart_3762928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762931 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 5]
def baseStart_3762931 : Nat := 118140960795 + 3762931 * 2 ^ 59
def prefixEnd_3762931 : Nat := 4983230072969 + 3 ^ 40 * 3762931 * 2
def baseEnd_3762931 : Nat := 1932192272703722248857101

theorem tailTrace_3762931 : CollatzResearch.WordTrace tailWord_3762931 prefixEnd_3762931 1932192272703722248857101 := by
  unfold tailWord_3762931
  simp only [CollatzResearch.WordTrace]
  refine ⟨137245368730551119295336647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91496912487034079530224431 137245368730551119295336647)
  ·
    refine ⟨205868053095826678943004971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137245368730551119295336647 205868053095826678943004971)
    ·
      refine ⟨308802079643740018414507457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205868053095826678943004971 308802079643740018414507457)
      ·
        refine ⟨231601559732805013810880593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308802079643740018414507457 231601559732805013810880593)
        ·
          refine ⟨173701169799603760358160445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231601559732805013810880593 173701169799603760358160445)
          ·
            refine ⟨65137938674851410134310167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173701169799603760358160445 65137938674851410134310167)
            ·
              refine ⟨97706908012277115201465251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65137938674851410134310167 97706908012277115201465251)
              ·
                refine ⟨146560362018415672802197877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97706908012277115201465251 146560362018415672802197877)
                ·
                  refine ⟨13740033939226469325206051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 146560362018415672802197877 13740033939226469325206051)
                  ·
                    refine ⟨20610050908839703987809077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13740033939226469325206051 20610050908839703987809077)
                    ·
                      refine ⟨1932192272703722248857101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20610050908839703987809077 1932192272703722248857101)
                      ·
                        rfl

theorem cell23_3762931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 5].length) (baseStart_3762931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762931 prefixEnd_3762931 := by exact prefixLift 3762931
  have htrace : WordTrace (prefixWord ++ tailWord_3762931) baseStart_3762931 baseEnd_3762931 := by
    simpa [prefixWord, tailWord_3762931, baseEnd_3762931] using wordTrace_append hprefix tailTrace_3762931
  have hstable : (prefixWord ++ tailWord_3762931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762931).length < 2 ^ (prefixWord ++ tailWord_3762931).sum := by decide
  have hdescent : baseEnd_3762931 < baseStart_3762931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762933 : List Nat := [1, 3, 6, 1, 1, 2, 1, 3, 1, 4]
def baseStart_3762933 : Nat := 118140960795 + 3762933 * 2 ^ 59
def prefixEnd_3762933 : Nat := 4983230072969 + 3 ^ 40 * 3762933 * 2
def baseEnd_3762933 : Nat := 644064433221677080344031

theorem tailTrace_3762933 : CollatzResearch.WordTrace tailWord_3762933 prefixEnd_3762933 644064433221677080344031 := by
  unfold tailWord_3762933
  simp only [CollatzResearch.WordTrace]
  refine ⟨137245441676543873636909453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91496961117695915757939635 137245441676543873636909453)
  ·
    refine ⟨51467040628703952613841045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137245441676543873636909453 51467040628703952613841045)
    ·
      refine ⟨2412517529470497778773799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51467040628703952613841045 2412517529470497778773799)
      ·
        refine ⟨3618776294205746668160699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2412517529470497778773799 3618776294205746668160699)
        ·
          refine ⟨5428164441308620002241049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3618776294205746668160699 5428164441308620002241049)
          ·
            refine ⟨4071123330981465001680787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5428164441308620002241049 4071123330981465001680787)
            ·
              refine ⟨6106684996472197502521181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4071123330981465001680787 6106684996472197502521181)
              ·
                refine ⟨2290006873677074063445443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6106684996472197502521181 2290006873677074063445443)
                ·
                  refine ⟨3435010310515611095168165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2290006873677074063445443 3435010310515611095168165)
                  ·
                    refine ⟨644064433221677080344031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3435010310515611095168165 644064433221677080344031)
                    ·
                      rfl

theorem cell23_3762933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_3762933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762933 prefixEnd_3762933 := by exact prefixLift 3762933
  have htrace : WordTrace (prefixWord ++ tailWord_3762933) baseStart_3762933 baseEnd_3762933 := by
    simpa [prefixWord, tailWord_3762933, baseEnd_3762933] using wordTrace_append hprefix tailTrace_3762933
  have hstable : (prefixWord ++ tailWord_3762933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762933).length < 2 ^ (prefixWord ++ tailWord_3762933).sum := by decide
  have hdescent : baseEnd_3762933 < baseStart_3762933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762938 : List Nat := [3, 1, 1, 1, 1, 3, 3, 2, 4, 4]
def baseStart_3762938 : Nat := 118140960795 + 3762938 * 2 ^ 59
def prefixEnd_3762938 : Nat := 4983230072969 + 3 ^ 40 * 3762938 * 2
def baseEnd_3762938 : Nat := 644065289022767907156523

theorem tailTrace_3762938 : CollatzResearch.WordTrace tailWord_3762938 prefixEnd_3762938 644065289022767907156523 := by
  unfold tailWord_3762938
  simp only [CollatzResearch.WordTrace]
  refine ⟨34311406010381439872710367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91497082694350506327227645 34311406010381439872710367)
  ·
    refine ⟨51467109015572159809065551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34311406010381439872710367 51467109015572159809065551)
    ·
      refine ⟨77200663523358239713598327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51467109015572159809065551 77200663523358239713598327)
      ·
        refine ⟨115800995285037359570397491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77200663523358239713598327 115800995285037359570397491)
        ·
          refine ⟨173701492927556039355596237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115800995285037359570397491 173701492927556039355596237)
          ·
            refine ⟨65138059847833514758348589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173701492927556039355596237 65138059847833514758348589)
            ·
              refine ⟨24426772442937568034380721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65138059847833514758348589 24426772442937568034380721)
              ·
                refine ⟨18320079332203176025785541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24426772442937568034380721 18320079332203176025785541)
                ·
                  refine ⟨3435014874788095504834789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18320079332203176025785541 3435014874788095504834789)
                  ·
                    refine ⟨644065289022767907156523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3435014874788095504834789 644065289022767907156523)
                    ·
                      rfl

theorem cell23_3762938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 4, 4].length) (baseStart_3762938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762938 prefixEnd_3762938 := by exact prefixLift 3762938
  have htrace : WordTrace (prefixWord ++ tailWord_3762938) baseStart_3762938 baseEnd_3762938 := by
    simpa [prefixWord, tailWord_3762938, baseEnd_3762938] using wordTrace_append hprefix tailTrace_3762938
  have hstable : (prefixWord ++ tailWord_3762938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762938).length < 2 ^ (prefixWord ++ tailWord_3762938).sum := by decide
  have hdescent : baseEnd_3762938 < baseStart_3762938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762972 : List Nat := [2, 2, 3, 1, 1, 3, 4, 1, 2, 4]
def baseStart_3762972 : Nat := 118140960795 + 3762972 * 2 ^ 59
def prefixEnd_3762972 : Nat := 4983230072969 + 3 ^ 40 * 3762972 * 2
def baseEnd_3762972 : Nat := 644071108470185529481471

theorem tailTrace_3762972 : CollatzResearch.WordTrace tailWord_3762972 prefixEnd_3762972 644071108470185529481471 := by
  unfold tailWord_3762972
  simp only [CollatzResearch.WordTrace]
  refine ⟨68623432061701291648789585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91497909415601722198386113 68623432061701291648789585)
  ·
    refine ⟨51467574046275968736592189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68623432061701291648789585 51467574046275968736592189)
    ·
      refine ⟨19300340267353488276222071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51467574046275968736592189 19300340267353488276222071)
      ·
        refine ⟨28950510401030232414333107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19300340267353488276222071 28950510401030232414333107)
        ·
          refine ⟨43425765601545348621499661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28950510401030232414333107 43425765601545348621499661)
          ·
            refine ⟨16284662100579505733062373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43425765601545348621499661 16284662100579505733062373)
            ·
              refine ⟨3053374143858657324949195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16284662100579505733062373 3053374143858657324949195)
              ·
                refine ⟨4580061215787985987423793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3053374143858657324949195 4580061215787985987423793)
                ·
                  refine ⟨3435045911840989490567845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4580061215787985987423793 3435045911840989490567845)
                  ·
                    refine ⟨644071108470185529481471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3435045911840989490567845 644071108470185529481471)
                    ·
                      rfl

theorem cell23_3762972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_3762972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762972 prefixEnd_3762972 := by exact prefixLift 3762972
  have htrace : WordTrace (prefixWord ++ tailWord_3762972) baseStart_3762972 baseEnd_3762972 := by
    simpa [prefixWord, tailWord_3762972, baseEnd_3762972] using wordTrace_append hprefix tailTrace_3762972
  have hstable : (prefixWord ++ tailWord_3762972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762972).length < 2 ^ (prefixWord ++ tailWord_3762972).sum := by decide
  have hdescent : baseEnd_3762972 < baseStart_3762972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762995 : List Nat := [1, 1, 1, 2, 6, 2, 1, 2, 1, 3, 3]
def baseStart_3762995 : Nat := 118140960795 + 3762995 * 2 ^ 59
def prefixEnd_3762995 : Nat := 4983230072969 + 3 ^ 40 * 3762995 * 2
def baseEnd_3762995 : Nat := 1932225135465609998456807

theorem tailTrace_3762995 : CollatzResearch.WordTrace tailWord_3762995 prefixEnd_3762995 1932225135465609998456807 := by
  unfold tailWord_3762995
  simp only [CollatzResearch.WordTrace]
  refine ⟨137247703002319258225666439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91498468668212838817110959 137247703002319258225666439)
  ·
    refine ⟨205871554503478887338499659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137247703002319258225666439 205871554503478887338499659)
    ·
      refine ⟨308807331755218331007749489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205871554503478887338499659 308807331755218331007749489)
      ·
        refine ⟨231605498816413748255812117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308807331755218331007749489 231605498816413748255812117)
        ·
          refine ⟨10856507757019394449491193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 231605498816413748255812117 10856507757019394449491193)
          ·
            refine ⟨8142380817764545837118395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10856507757019394449491193 8142380817764545837118395)
            ·
              refine ⟨12213571226646818755677593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8142380817764545837118395 12213571226646818755677593)
              ·
                refine ⟨9160178419985114066758195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12213571226646818755677593 9160178419985114066758195)
                ·
                  refine ⟨13740267629977671100137293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9160178419985114066758195 13740267629977671100137293)
                  ·
                    refine ⟨5152600361241626662551485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13740267629977671100137293 5152600361241626662551485)
                    ·
                      refine ⟨1932225135465609998456807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5152600361241626662551485 1932225135465609998456807)
                      ·
                        rfl

theorem cell23_3762995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 3, 3].length) (baseStart_3762995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3762995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3762995 prefixEnd_3762995 := by exact prefixLift 3762995
  have htrace : WordTrace (prefixWord ++ tailWord_3762995) baseStart_3762995 baseEnd_3762995 := by
    simpa [prefixWord, tailWord_3762995, baseEnd_3762995] using wordTrace_append hprefix tailTrace_3762995
  have hstable : (prefixWord ++ tailWord_3762995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762995).length < 2 ^ (prefixWord ++ tailWord_3762995).sum := by decide
  have hdescent : baseEnd_3762995 < baseStart_3762995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763052 : List Nat := [2, 2, 1, 1, 4, 1, 2, 2, 4, 2, 2]
def baseStart_3763052 : Nat := 118140960795 + 3763052 * 2 ^ 59
def prefixEnd_3763052 : Nat := 4983230072969 + 3 ^ 40 * 3763052 * 2
def baseEnd_3763052 : Nat := 1932254403862916275444045

theorem tailTrace_3763052 : CollatzResearch.WordTrace tailWord_3763052 prefixEnd_3763052 1932254403862916275444045 := by
  unfold tailWord_3763052
  simp only [CollatzResearch.WordTrace]
  refine ⟨68624890981556378480245705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91499854642075171306994273 68624890981556378480245705)
  ·
    refine ⟨51468668236167283860184279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68624890981556378480245705 51468668236167283860184279)
    ·
      refine ⟨77203002354250925790276419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51468668236167283860184279 77203002354250925790276419)
      ·
        refine ⟨115804503531376388685414629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77203002354250925790276419 115804503531376388685414629)
        ·
          refine ⟨21713344412133072878515243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115804503531376388685414629 21713344412133072878515243)
          ·
            refine ⟨32570016618199609317772865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21713344412133072878515243 32570016618199609317772865)
            ·
              refine ⟨24427512463649706988329649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32570016618199609317772865 24427512463649706988329649)
              ·
                refine ⟨18320634347737280241247237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24427512463649706988329649 18320634347737280241247237)
                ·
                  refine ⟨3435118940200740045233857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18320634347737280241247237 3435118940200740045233857)
                  ·
                    refine ⟨2576339205150555033925393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3435118940200740045233857 2576339205150555033925393)
                    ·
                      refine ⟨1932254403862916275444045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2576339205150555033925393 1932254403862916275444045)
                      ·
                        rfl

theorem cell23_3763052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 2, 2].length) (baseStart_3763052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3763052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3763052 prefixEnd_3763052 := by exact prefixLift 3763052
  have htrace : WordTrace (prefixWord ++ tailWord_3763052) baseStart_3763052 baseEnd_3763052 := by
    simpa [prefixWord, tailWord_3763052, baseEnd_3763052] using wordTrace_append hprefix tailTrace_3763052
  have hstable : (prefixWord ++ tailWord_3763052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763052).length < 2 ^ (prefixWord ++ tailWord_3763052).sum := by decide
  have hdescent : baseEnd_3763052 < baseStart_3763052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763069 : List Nat := [1, 4, 1, 1, 2, 1, 5, 2, 2, 2, 2]
def baseStart_3763069 : Nat := 118140960795 + 3763069 * 2 ^ 59
def prefixEnd_3763069 : Nat := 4983230072969 + 3 ^ 40 * 3763069 * 2
def baseEnd_3763069 : Nat := 1932263133034042708931467

theorem tailTrace_3763069 : CollatzResearch.WordTrace tailWord_3763069 prefixEnd_3763069 1932263133034042708931467 := by
  unfold tailWord_3763069
  simp only [CollatzResearch.WordTrace]
  refine ⟨137250402004051168863860261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91500268002700779242573507 137250402004051168863860261)
  ·
    refine ⟨25734450375759594161973799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137250402004051168863860261 25734450375759594161973799)
    ·
      refine ⟨38601675563639391242960699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25734450375759594161973799 38601675563639391242960699)
      ·
        refine ⟨57902513345459086864441049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38601675563639391242960699 57902513345459086864441049)
        ·
          refine ⟨43426885009094315148330787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57902513345459086864441049 43426885009094315148330787)
          ·
            refine ⟨65140327513641472722496181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43426885009094315148330787 65140327513641472722496181)
            ·
              refine ⟨6106905704403888067734017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65140327513641472722496181 6106905704403888067734017)
              ·
                refine ⟨4580179278302916050800513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6106905704403888067734017 4580179278302916050800513)
                ·
                  refine ⟨3435134458727187038100385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4580179278302916050800513 3435134458727187038100385)
                  ·
                    refine ⟨2576350844045390278575289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3435134458727187038100385 2576350844045390278575289)
                    ·
                      refine ⟨1932263133034042708931467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2576350844045390278575289 1932263133034042708931467)
                      ·
                        rfl

theorem cell23_3763069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 2, 2, 2, 2].length) (baseStart_3763069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3763069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3763069 prefixEnd_3763069 := by exact prefixLift 3763069
  have htrace : WordTrace (prefixWord ++ tailWord_3763069) baseStart_3763069 baseEnd_3763069 := by
    simpa [prefixWord, tailWord_3763069, baseEnd_3763069] using wordTrace_append hprefix tailTrace_3763069
  have hstable : (prefixWord ++ tailWord_3763069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763069).length < 2 ^ (prefixWord ++ tailWord_3763069).sum := by decide
  have hdescent : baseEnd_3763069 < baseStart_3763069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763075 : List Nat := [1, 1, 1, 3, 4, 1, 1, 6, 5]
def baseStart_3763075 : Nat := 118140960795 + 3763075 * 2 ^ 59
def prefixEnd_3763075 : Nat := 4983230072969 + 3 ^ 40 * 3763075 * 2
def baseEnd_3763075 : Nat := 214696245990885520606271

theorem tailTrace_3763075 : CollatzResearch.WordTrace tailWord_3763075 prefixEnd_3763075 214696245990885520606271 := by
  unfold tailWord_3763075
  simp only [CollatzResearch.WordTrace]
  refine ⟨137250620842029431888578679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91500413894686287925719119 137250620842029431888578679)
  ·
    refine ⟨205875931263044147832868019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137250620842029431888578679 205875931263044147832868019)
    ·
      refine ⟨308813896894566221749302029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205875931263044147832868019 308813896894566221749302029)
      ·
        refine ⟨115805211335462333155988261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308813896894566221749302029 115805211335462333155988261)
        ·
          refine ⟨21713477125399187466747799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115805211335462333155988261 21713477125399187466747799)
          ·
            refine ⟨32570215688098781200121699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21713477125399187466747799 32570215688098781200121699)
            ·
              refine ⟨48855323532148171800182549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32570215688098781200121699 48855323532148171800182549)
              ·
                refine ⟨2290093290569445553133557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48855323532148171800182549 2290093290569445553133557)
                ·
                  refine ⟨214696245990885520606271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2290093290569445553133557 214696245990885520606271)
                  ·
                    rfl

theorem cell23_3763075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 6, 5].length) (baseStart_3763075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3763075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3763075 prefixEnd_3763075 := by exact prefixLift 3763075
  have htrace : WordTrace (prefixWord ++ tailWord_3763075) baseStart_3763075 baseEnd_3763075 := by
    simpa [prefixWord, tailWord_3763075, baseEnd_3763075] using wordTrace_append hprefix tailTrace_3763075
  have hstable : (prefixWord ++ tailWord_3763075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763075).length < 2 ^ (prefixWord ++ tailWord_3763075).sum := by decide
  have hdescent : baseEnd_3763075 < baseStart_3763075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763105 : List Nat := [1, 2, 3, 4, 1, 1, 2, 1, 1, 7]
def baseStart_3763105 : Nat := 118140960795 + 3763105 * 2 ^ 59
def prefixEnd_3763105 : Nat := 4983230072969 + 3 ^ 40 * 3763105 * 2
def baseEnd_3763105 : Nat := 644093872779201522693767

theorem tailTrace_3763105 : CollatzResearch.WordTrace tailWord_3763105 prefixEnd_3763105 644093872779201522693767 := by
  unfold tailWord_3763105
  simp only [CollatzResearch.WordTrace]
  refine ⟨137251715031920747012170769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91501143354613831341447179 137251715031920747012170769)
  ·
    refine ⟨102938786273940560259128077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137251715031920747012170769 102938786273940560259128077)
    ·
      refine ⟨38602044852727710097173029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102938786273940560259128077 38602044852727710097173029)
      ·
        refine ⟨7237883409886445643219943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38602044852727710097173029 7237883409886445643219943)
        ·
          refine ⟨10856825114829668464829915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7237883409886445643219943 10856825114829668464829915)
          ·
            refine ⟨16285237672244502697244873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10856825114829668464829915 16285237672244502697244873)
            ·
              refine ⟨12213928254183377022933655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16285237672244502697244873 12213928254183377022933655)
              ·
                refine ⟨18320892381275065534400483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12213928254183377022933655 18320892381275065534400483)
                ·
                  refine ⟨27481338571912598301600725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18320892381275065534400483 27481338571912598301600725)
                  ·
                    refine ⟨644093872779201522693767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27481338571912598301600725 644093872779201522693767)
                    ·
                      rfl

theorem cell23_3763105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_3763105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3763105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3763105 prefixEnd_3763105 := by exact prefixLift 3763105
  have htrace : WordTrace (prefixWord ++ tailWord_3763105) baseStart_3763105 baseEnd_3763105 := by
    simpa [prefixWord, tailWord_3763105, baseEnd_3763105] using wordTrace_append hprefix tailTrace_3763105
  have hstable : (prefixWord ++ tailWord_3763105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763105).length < 2 ^ (prefixWord ++ tailWord_3763105).sum := by decide
  have hdescent : baseEnd_3763105 < baseStart_3763105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763135 : List Nat := [1, 1, 2, 2, 2, 1, 2, 5, 3, 4]
def baseStart_3763135 : Nat := 118140960795 + 3763135 * 2 ^ 59
def prefixEnd_3763135 : Nat := 4983230072969 + 3 ^ 40 * 3763135 * 2
def baseEnd_3763135 : Nat := 644099007585746483568721

theorem tailTrace_3763135 : CollatzResearch.WordTrace tailWord_3763135 prefixEnd_3763135 644099007585746483568721 := by
  unfold tailWord_3763135
  simp only [CollatzResearch.WordTrace]
  refine ⟨137252809221812062135762859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91501872814541374757175239 137252809221812062135762859)
  ·
    refine ⟨205879213832718093203644289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137252809221812062135762859 205879213832718093203644289)
    ·
      refine ⟨154409410374538569902733217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205879213832718093203644289 154409410374538569902733217)
      ·
        refine ⟨115807057780903927427049913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154409410374538569902733217 115807057780903927427049913)
        ·
          refine ⟨86855293335677945570287435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115807057780903927427049913 86855293335677945570287435)
          ·
            refine ⟨130282940003516918355431153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86855293335677945570287435 130282940003516918355431153)
            ·
              refine ⟨97712205002637688766573365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130282940003516918355431153 97712205002637688766573365)
              ·
                refine ⟨9160519218997283321866253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97712205002637688766573365 9160519218997283321866253)
                ·
                  refine ⟨3435194707123981245699845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9160519218997283321866253 3435194707123981245699845)
                  ·
                    refine ⟨644099007585746483568721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3435194707123981245699845 644099007585746483568721)
                    ·
                      rfl

theorem cell23_3763135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 3, 4].length) (baseStart_3763135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3763135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3763135 prefixEnd_3763135 := by exact prefixLift 3763135
  have htrace : WordTrace (prefixWord ++ tailWord_3763135) baseStart_3763135 baseEnd_3763135 := by
    simpa [prefixWord, tailWord_3763135, baseEnd_3763135] using wordTrace_append hprefix tailTrace_3763135
  have hstable : (prefixWord ++ tailWord_3763135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763135).length < 2 ^ (prefixWord ++ tailWord_3763135).sum := by decide
  have hdescent : baseEnd_3763135 < baseStart_3763135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763162 : List Nat := [3, 1, 1, 2, 4, 1, 1, 3, 2, 2, 3]
def baseStart_3763162 : Nat := 118140960795 + 3763162 * 2 ^ 59
def prefixEnd_3763162 : Nat := 4983230072969 + 3 ^ 40 * 3763162 * 2
def baseEnd_3763162 : Nat := 1932310886734910845068539

theorem tailTrace_3763162 : CollatzResearch.WordTrace tailWord_3763162 prefixEnd_3763162 1932310886734910845068539 := by
  unfold tailWord_3763162
  simp only [CollatzResearch.WordTrace]
  refine ⟨34313448498178561436748935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91502529328476163831330493 34313448498178561436748935)
  ·
    refine ⟨51470172747267842155123403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34313448498178561436748935 51470172747267842155123403)
    ·
      refine ⟨77205259120901763232685105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51470172747267842155123403 77205259120901763232685105)
      ·
        refine ⟨57903944340676322424513829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77205259120901763232685105 57903944340676322424513829)
        ·
          refine ⟨10856989563876810454596343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57903944340676322424513829 10856989563876810454596343)
          ·
            refine ⟨16285484345815215681894515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10856989563876810454596343 16285484345815215681894515)
            ·
              refine ⟨24428226518722823522841773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16285484345815215681894515 24428226518722823522841773)
              ·
                refine ⟨9160584944521058821065665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24428226518722823522841773 9160584944521058821065665)
                ·
                  refine ⟨6870438708390794115799249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9160584944521058821065665 6870438708390794115799249)
                  ·
                    refine ⟨5152829031293095586849437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6870438708390794115799249 5152829031293095586849437)
                    ·
                      refine ⟨1932310886734910845068539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5152829031293095586849437 1932310886734910845068539)
                      ·
                        rfl

theorem cell23_3763162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_3763162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3763162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3763162 prefixEnd_3763162 := by exact prefixLift 3763162
  have htrace : WordTrace (prefixWord ++ tailWord_3763162) baseStart_3763162 baseEnd_3763162 := by
    simpa [prefixWord, tailWord_3763162, baseEnd_3763162] using wordTrace_append hprefix tailTrace_3763162
  have hstable : (prefixWord ++ tailWord_3763162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763162).length < 2 ^ (prefixWord ++ tailWord_3763162).sum := by decide
  have hdescent : baseEnd_3763162 < baseStart_3763162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763168 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 8]
def baseStart_3763168 : Nat := 118140960795 + 3763168 * 2 ^ 59
def prefixEnd_3763168 : Nat := 4983230072969 + 3 ^ 40 * 3763168 * 2
def baseEnd_3763168 : Nat := 1932313967618837821593511

theorem tailTrace_3763168 : CollatzResearch.WordTrace tailWord_3763168 prefixEnd_3763168 1932313967618837821593511 := by
  unfold tailWord_3763168
  simp only [CollatzResearch.WordTrace]
  refine ⟨68627006415346254385857079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91502675220461672514476105 68627006415346254385857079)
  ·
    refine ⟨102940509623019381578785619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68627006415346254385857079 102940509623019381578785619)
    ·
      refine ⟨154410764434529072368178429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102940509623019381578785619 154410764434529072368178429)
      ·
        refine ⟨57904036662948402138066911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154410764434529072368178429 57904036662948402138066911)
        ·
          refine ⟨86856054994422603207100367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57904036662948402138066911 86856054994422603207100367)
          ·
            refine ⟨130284082491633904810650551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86856054994422603207100367 130284082491633904810650551)
            ·
              refine ⟨195426123737450857215975827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130284082491633904810650551 195426123737450857215975827)
              ·
                refine ⟨293139185606176285823963741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195426123737450857215975827 293139185606176285823963741)
                ·
                  refine ⟨109927194602316107183986403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 293139185606176285823963741 109927194602316107183986403)
                  ·
                    refine ⟨164890791903474160775979605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109927194602316107183986403 164890791903474160775979605)
                    ·
                      refine ⟨1932313967618837821593511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 164890791903474160775979605 1932313967618837821593511)
                      ·
                        rfl

theorem cell23_3763168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_3763168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3763168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3763168 prefixEnd_3763168 := by exact prefixLift 3763168
  have htrace : WordTrace (prefixWord ++ tailWord_3763168) baseStart_3763168 baseEnd_3763168 := by
    simpa [prefixWord, tailWord_3763168, baseEnd_3763168] using wordTrace_append hprefix tailTrace_3763168
  have hstable : (prefixWord ++ tailWord_3763168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763168).length < 2 ^ (prefixWord ++ tailWord_3763168).sum := by decide
  have hdescent : baseEnd_3763168 < baseStart_3763168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763192 : List Nat := [2, 1, 2, 1, 1, 3, 1, 5, 3, 1, 3]
def baseStart_3763192 : Nat := 118140960795 + 3763192 * 2 ^ 59
def prefixEnd_3763192 : Nat := 4983230072969 + 3 ^ 40 * 3763192 * 2
def baseEnd_3763192 : Nat := 1932326291154545727693401

theorem tailTrace_3763192 : CollatzResearch.WordTrace tailWord_3763192 prefixEnd_3763192 1932326291154545727693401 := by
  unfold tailWord_3763192
  simp only [CollatzResearch.WordTrace]
  refine ⟨68627444091302780435293915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91503258788403707247058553 68627444091302780435293915)
  ·
    refine ⟨102941166136954170652940873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68627444091302780435293915 102941166136954170652940873)
    ·
      refine ⟨77205874602715627989705655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102941166136954170652940873 77205874602715627989705655)
      ·
        refine ⟨115808811904073441984558483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77205874602715627989705655 115808811904073441984558483)
        ·
          refine ⟨173713217856110162976837725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115808811904073441984558483 173713217856110162976837725)
          ·
            refine ⟨65142456696041311116314147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173713217856110162976837725 65142456696041311116314147)
            ·
              refine ⟨97713685044061966674471221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65142456696041311116314147 97713685044061966674471221)
              ·
                refine ⟨9160657972880809375731677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97713685044061966674471221 9160657972880809375731677)
                ·
                  refine ⟨3435246739830303515899379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9160657972880809375731677 3435246739830303515899379)
                  ·
                    refine ⟨5152870109745455273849069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3435246739830303515899379 5152870109745455273849069)
                    ·
                      refine ⟨1932326291154545727693401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5152870109745455273849069 1932326291154545727693401)
                      ·
                        rfl

theorem cell23_3763192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 3, 1, 3].length) (baseStart_3763192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3763192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3763192 prefixEnd_3763192 := by exact prefixLift 3763192
  have htrace : WordTrace (prefixWord ++ tailWord_3763192) baseStart_3763192 baseEnd_3763192 := by
    simpa [prefixWord, tailWord_3763192, baseEnd_3763192] using wordTrace_append hprefix tailTrace_3763192
  have hstable : (prefixWord ++ tailWord_3763192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763192).length < 2 ^ (prefixWord ++ tailWord_3763192).sum := by decide
  have hdescent : baseEnd_3763192 < baseStart_3763192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763225 : List Nat := [1, 2, 1, 2, 1, 1, 6, 2, 1, 6]
def baseStart_3763225 : Nat := 118140960795 + 3763225 * 2 ^ 59
def prefixEnd_3763225 : Nat := 4983230072969 + 3 ^ 40 * 3763225 * 2
def baseEnd_3763225 : Nat := 644114412005381366193583

theorem tailTrace_3763225 : CollatzResearch.WordTrace tailWord_3763225 prefixEnd_3763225 644114412005381366193583 := by
  unfold tailWord_3763225
  simp only [CollatzResearch.WordTrace]
  refine ⟨137256091791486007506539129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91504061194324005004359419 137256091791486007506539129)
  ·
    refine ⟨102942068843614505629904347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137256091791486007506539129 102942068843614505629904347)
    ·
      refine ⟨154413103265421758444856521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102942068843614505629904347 154413103265421758444856521)
      ·
        refine ⟨115809827449066318833642391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154413103265421758444856521 115809827449066318833642391)
        ·
          refine ⟨173714741173599478250463587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115809827449066318833642391 173714741173599478250463587)
          ·
            refine ⟨260572111760399217375695381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173714741173599478250463587 260572111760399217375695381)
            ·
              refine ⟨12214317738768713314485721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 260572111760399217375695381 12214317738768713314485721)
              ·
                refine ⟨9160738304076534985864291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12214317738768713314485721 9160738304076534985864291)
                ·
                  refine ⟨13741107456114802478796437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9160738304076534985864291 13741107456114802478796437)
                  ·
                    refine ⟨644114412005381366193583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13741107456114802478796437 644114412005381366193583)
                    ·
                      rfl

theorem cell23_3763225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 6].length) (baseStart_3763225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3763225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3763225 prefixEnd_3763225 := by exact prefixLift 3763225
  have htrace : WordTrace (prefixWord ++ tailWord_3763225) baseStart_3763225 baseEnd_3763225 := by
    simpa [prefixWord, tailWord_3763225, baseEnd_3763225] using wordTrace_append hprefix tailTrace_3763225
  have hstable : (prefixWord ++ tailWord_3763225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763225).length < 2 ^ (prefixWord ++ tailWord_3763225).sum := by decide
  have hdescent : baseEnd_3763225 < baseStart_3763225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763226 : List Nat := [3, 1, 1, 3, 1, 2, 4, 3, 1, 1, 3]
def baseStart_3763226 : Nat := 118140960795 + 3763226 * 2 ^ 59
def prefixEnd_3763226 : Nat := 4983230072969 + 3 ^ 40 * 3763226 * 2
def baseEnd_3763226 : Nat := 1932343749496798594668245

theorem tailTrace_3763226 : CollatzResearch.WordTrace tailWord_3763226 prefixEnd_3763226 1932343749496798594668245 := by
  unfold tailWord_3763226
  simp only [CollatzResearch.WordTrace]
  refine ⟨34314032066120596169331383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91504085509654923118217021 34314032066120596169331383)
  ·
    refine ⟨51471048099180894253997075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34314032066120596169331383 51471048099180894253997075)
    ·
      refine ⟨77206572148771341380995613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51471048099180894253997075 77206572148771341380995613)
      ·
        refine ⟨28952464555789253017873355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77206572148771341380995613 28952464555789253017873355)
        ·
          refine ⟨43428696833683879526810033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28952464555789253017873355 43428696833683879526810033)
          ·
            refine ⟨32571522625262909645107525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43428696833683879526810033 32571522625262909645107525)
            ·
              refine ⟨6107160492236795558457661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32571522625262909645107525 6107160492236795558457661)
              ·
                refine ⟨2290185184588798334421623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6107160492236795558457661 2290185184588798334421623)
                ·
                  refine ⟨3435277776883197501632435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2290185184588798334421623 3435277776883197501632435)
                  ·
                    refine ⟨5152916665324796252448653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3435277776883197501632435 5152916665324796252448653)
                    ·
                      refine ⟨1932343749496798594668245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5152916665324796252448653 1932343749496798594668245)
                      ·
                        rfl

theorem cell23_3763226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_3763226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3763226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3763226 prefixEnd_3763226 := by exact prefixLift 3763226
  have htrace : WordTrace (prefixWord ++ tailWord_3763226) baseStart_3763226 baseEnd_3763226 := by
    simpa [prefixWord, tailWord_3763226, baseEnd_3763226] using wordTrace_append hprefix tailTrace_3763226
  have hstable : (prefixWord ++ tailWord_3763226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763226).length < 2 ^ (prefixWord ++ tailWord_3763226).sum := by decide
  have hdescent : baseEnd_3763226 < baseStart_3763226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763229 : List Nat := [1, 4, 2, 2, 3, 1, 1, 3, 1, 5]
def baseStart_3763229 : Nat := 118140960795 + 3763229 * 2 ^ 59
def prefixEnd_3763229 : Nat := 4983230072969 + 3 ^ 40 * 3763229 * 2
def baseEnd_3763229 : Nat := 644115096646254027643577

theorem tailTrace_3763229 : CollatzResearch.WordTrace tailWord_3763229 prefixEnd_3763229 644115096646254027643577 := by
  unfold tailWord_3763229
  simp only [CollatzResearch.WordTrace]
  refine ⟨137256237683471516189684741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91504158455647677459789827 137256237683471516189684741)
  ·
    refine ⟨25735544565650909285565889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137256237683471516189684741 25735544565650909285565889)
    ·
      refine ⟨19301658424238181964174417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25735544565650909285565889 19301658424238181964174417)
      ·
        refine ⟨14476243818178636473130813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19301658424238181964174417 14476243818178636473130813)
        ·
          refine ⟨5428591431816988677424055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14476243818178636473130813 5428591431816988677424055)
          ·
            refine ⟨8142887147725483016136083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5428591431816988677424055 8142887147725483016136083)
            ·
              refine ⟨12214330721588224524204125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8142887147725483016136083 12214330721588224524204125)
              ·
                refine ⟨4580374020595584196576547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12214330721588224524204125 4580374020595584196576547)
                ·
                  refine ⟨6870561030893376294864821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4580374020595584196576547 6870561030893376294864821)
                  ·
                    refine ⟨644115096646254027643577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6870561030893376294864821 644115096646254027643577)
                    ·
                      rfl

theorem cell23_3763229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_3763229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3763229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3763229 prefixEnd_3763229 := by exact prefixLift 3763229
  have htrace : WordTrace (prefixWord ++ tailWord_3763229) baseStart_3763229 baseEnd_3763229 := by
    simpa [prefixWord, tailWord_3763229, baseEnd_3763229] using wordTrace_append hprefix tailTrace_3763229
  have hstable : (prefixWord ++ tailWord_3763229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763229).length < 2 ^ (prefixWord ++ tailWord_3763229).sum := by decide
  have hdescent : baseEnd_3763229 < baseStart_3763229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763295 : List Nat := [1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 5]
def baseStart_3763295 : Nat := 118140960795 + 3763295 * 2 ^ 59
def prefixEnd_3763295 : Nat := 4983230072969 + 3 ^ 40 * 3763295 * 2
def baseEnd_3763295 : Nat := 1932379179661958824705427

theorem tailTrace_3763295 : CollatzResearch.WordTrace tailWord_3763295 prefixEnd_3763295 1932379179661958824705427 := by
  unfold tailWord_3763295
  simp only [CollatzResearch.WordTrace]
  refine ⟨137258644901232409461587339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91505763267488272974391559 137258644901232409461587339)
  ·
    refine ⟨205887967351848614192381009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137258644901232409461587339 205887967351848614192381009)
    ·
      refine ⟨154415975513886460644285757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205887967351848614192381009 154415975513886460644285757)
      ·
        refine ⟨57905990817707422741607159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154415975513886460644285757 57905990817707422741607159)
        ·
          refine ⟨86858986226561134112410739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57905990817707422741607159 86858986226561134112410739)
          ·
            refine ⟨130288479339841701168616109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86858986226561134112410739 130288479339841701168616109)
            ·
              refine ⟨48858179752440637938231041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130288479339841701168616109 48858179752440637938231041)
              ·
                refine ⟨36643634814330478453673281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48858179752440637938231041 36643634814330478453673281)
                ·
                  refine ⟨27482726110747858840254961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36643634814330478453673281 27482726110747858840254961)
                  ·
                    refine ⟨20612044583060894130191221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27482726110747858840254961 20612044583060894130191221)
                    ·
                      refine ⟨1932379179661958824705427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20612044583060894130191221 1932379179661958824705427)
                      ·
                        rfl

theorem cell23_3763295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_3763295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3763295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3763295 prefixEnd_3763295 := by exact prefixLift 3763295
  have htrace : WordTrace (prefixWord ++ tailWord_3763295) baseStart_3763295 baseEnd_3763295 := by
    simpa [prefixWord, tailWord_3763295, baseEnd_3763295] using wordTrace_append hprefix tailTrace_3763295
  have hstable : (prefixWord ++ tailWord_3763295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763295).length < 2 ^ (prefixWord ++ tailWord_3763295).sum := by decide
  have hdescent : baseEnd_3763295 < baseStart_3763295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763299 : List Nat := [1, 1, 1, 5, 1, 1, 1, 6, 2, 1, 3]
def baseStart_3763299 : Nat := 118140960795 + 3763299 * 2 ^ 59
def prefixEnd_3763299 : Nat := 4983230072969 + 3 ^ 40 * 3763299 * 2
def baseEnd_3763299 : Nat := 1932381233584576809055409

theorem tailTrace_3763299 : CollatzResearch.WordTrace tailWord_3763299 prefixEnd_3763299 1932381233584576809055409 := by
  unfold tailWord_3763299
  simp only [CollatzResearch.WordTrace]
  refine ⟨137258790793217918144732951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91505860528811945429821967 137258790793217918144732951)
  ·
    refine ⟨205888186189826877217099427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137258790793217918144732951 205888186189826877217099427)
    ·
      refine ⟨308832279284740315825649141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205888186189826877217099427 308832279284740315825649141)
      ·
        refine ⟨28953026182944404608654607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 308832279284740315825649141 28953026182944404608654607)
        ·
          refine ⟨43429539274416606912981911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28953026182944404608654607 43429539274416606912981911)
          ·
            refine ⟨65144308911624910369472867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43429539274416606912981911 65144308911624910369472867)
            ·
              refine ⟨97716463367437365554209301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65144308911624910369472867 97716463367437365554209301)
              ·
                refine ⟨4580459220348626510353561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 97716463367437365554209301 4580459220348626510353561)
                ·
                  refine ⟨3435344415261469882765171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4580459220348626510353561 3435344415261469882765171)
                  ·
                    refine ⟨5153016622892204824147757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3435344415261469882765171 5153016622892204824147757)
                    ·
                      refine ⟨1932381233584576809055409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5153016622892204824147757 1932381233584576809055409)
                      ·
                        rfl

theorem cell23_3763299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_3763299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3763299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3763299 prefixEnd_3763299 := by exact prefixLift 3763299
  have htrace : WordTrace (prefixWord ++ tailWord_3763299) baseStart_3763299 baseEnd_3763299 := by
    simpa [prefixWord, tailWord_3763299, baseEnd_3763299] using wordTrace_append hprefix tailTrace_3763299
  have hstable : (prefixWord ++ tailWord_3763299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763299).length < 2 ^ (prefixWord ++ tailWord_3763299).sum := by decide
  have hdescent : baseEnd_3763299 < baseStart_3763299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763339 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 6, 2, 2]
def baseStart_3763339 : Nat := 118140960795 + 3763339 * 2 ^ 59
def prefixEnd_3763339 : Nat := 4983230072969 + 3 ^ 40 * 3763339 * 2
def baseEnd_3763339 : Nat := 1932401772810756652555225

theorem tailTrace_3763339 : CollatzResearch.WordTrace tailWord_3763339 prefixEnd_3763339 1932401772810756652555225 := by
  unfold tailWord_3763339
  simp only [CollatzResearch.WordTrace]
  refine ⟨137260249713073004976189071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91506833142048669984126047 137260249713073004976189071)
  ·
    refine ⟨205890374569609507464283607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137260249713073004976189071 205890374569609507464283607)
    ·
      refine ⟨308835561854414261196425411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205890374569609507464283607 308835561854414261196425411)
      ·
        refine ⟨463253342781621391794638117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308835561854414261196425411 463253342781621391794638117)
        ·
          refine ⟨86860001771554010961494647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 463253342781621391794638117 86860001771554010961494647)
          ·
            refine ⟨130290002657331016442241971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86860001771554010961494647 130290002657331016442241971)
            ·
              refine ⟨195435003985996524663362957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130290002657331016442241971 195435003985996524663362957)
              ·
                refine ⟨73288126494748696748761109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195435003985996524663362957 73288126494748696748761109)
                ·
                  refine ⟨3435380929441345160098177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73288126494748696748761109 3435380929441345160098177)
                  ·
                    refine ⟨2576535697081008870073633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3435380929441345160098177 2576535697081008870073633)
                    ·
                      refine ⟨1932401772810756652555225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2576535697081008870073633 1932401772810756652555225)
                      ·
                        rfl

theorem cell23_3763339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 6, 2, 2].length) (baseStart_3763339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3763339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3763339 prefixEnd_3763339 := by exact prefixLift 3763339
  have htrace : WordTrace (prefixWord ++ tailWord_3763339) baseStart_3763339 baseEnd_3763339 := by
    simpa [prefixWord, tailWord_3763339, baseEnd_3763339] using wordTrace_append hprefix tailTrace_3763339
  have hstable : (prefixWord ++ tailWord_3763339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763339).length < 2 ^ (prefixWord ++ tailWord_3763339).sum := by decide
  have hdescent : baseEnd_3763339 < baseStart_3763339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763373 : List Nat := [1, 5, 2, 1, 3, 1, 2, 1, 1, 4, 2]
def baseStart_3763373 : Nat := 118140960795 + 3763373 * 2 ^ 59
def prefixEnd_3763373 : Nat := 4983230072969 + 3 ^ 40 * 3763373 * 2
def baseEnd_3763373 : Nat := 1932419231153009519530069

theorem tailTrace_3763373 : CollatzResearch.WordTrace tailWord_3763373 prefixEnd_3763373 1932419231153009519530069 := by
  unfold tailWord_3763373
  simp only [CollatzResearch.WordTrace]
  refine ⟨137261489794949828782926773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91507659863299885855284515 137261489794949828782926773)
  ·
    refine ⟨12868264668276546448399385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137261489794949828782926773 12868264668276546448399385)
    ·
      refine ⟨9651198501207409836299539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12868264668276546448399385 9651198501207409836299539)
      ·
        refine ⟨14476797751811114754449309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9651198501207409836299539 14476797751811114754449309)
        ·
          refine ⟨5428799156929168032918491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14476797751811114754449309 5428799156929168032918491)
          ·
            refine ⟨8143198735393752049377737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5428799156929168032918491 8143198735393752049377737)
            ·
              refine ⟨6107399051545314037033303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8143198735393752049377737 6107399051545314037033303)
              ·
                refine ⟨9161098577317971055549955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6107399051545314037033303 9161098577317971055549955)
                ·
                  refine ⟨13741647865976956583324933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9161098577317971055549955 13741647865976956583324933)
                  ·
                    refine ⟨2576558974870679359373425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13741647865976956583324933 2576558974870679359373425)
                    ·
                      refine ⟨1932419231153009519530069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2576558974870679359373425 1932419231153009519530069)
                      ·
                        rfl

theorem cell23_3763373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_3763373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3763373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3763373 prefixEnd_3763373 := by exact prefixLift 3763373
  have htrace : WordTrace (prefixWord ++ tailWord_3763373) baseStart_3763373 baseEnd_3763373 := by
    simpa [prefixWord, tailWord_3763373, baseEnd_3763373] using wordTrace_append hprefix tailTrace_3763373
  have hstable : (prefixWord ++ tailWord_3763373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763373).length < 2 ^ (prefixWord ++ tailWord_3763373).sum := by decide
  have hdescent : baseEnd_3763373 < baseStart_3763373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763394 : List Nat := [3, 5, 1, 1, 2, 2, 2, 1, 1, 3, 2]
def baseStart_3763394 : Nat := 118140960795 + 3763394 * 2 ^ 59
def prefixEnd_3763394 : Nat := 4983230072969 + 3 ^ 40 * 3763394 * 2
def baseEnd_3763394 : Nat := 1932430014246753937367473

theorem tailTrace_3763394 : CollatzResearch.WordTrace tailWord_3763394 prefixEnd_3763394 1932430014246753937367473 := by
  unfold tailWord_3763394
  simp only [CollatzResearch.WordTrace]
  refine ⟨34315563931968437342360309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91508170485249166246294157 34315563931968437342360309)
  ·
    refine ⟨3217084118622041000846279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34315563931968437342360309 3217084118622041000846279)
    ·
      refine ⟨4825626177933061501269419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3217084118622041000846279 4825626177933061501269419)
      ·
        refine ⟨7238439266899592251904129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4825626177933061501269419 7238439266899592251904129)
        ·
          refine ⟨5428829450174694188928097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7238439266899592251904129 5428829450174694188928097)
          ·
            refine ⟨4071622087631020641696073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5428829450174694188928097 4071622087631020641696073)
            ·
              refine ⟨3053716565723265481272055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4071622087631020641696073 3053716565723265481272055)
              ·
                refine ⟨4580574848584898221908083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3053716565723265481272055 4580574848584898221908083)
                ·
                  refine ⟨6870862272877347332862125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4580574848584898221908083 6870862272877347332862125)
                  ·
                    refine ⟨2576573352329005249823297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6870862272877347332862125 2576573352329005249823297)
                    ·
                      refine ⟨1932430014246753937367473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2576573352329005249823297 1932430014246753937367473)
                      ·
                        rfl

theorem cell23_3763394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_3763394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3763394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3763394 prefixEnd_3763394 := by exact prefixLift 3763394
  have htrace : WordTrace (prefixWord ++ tailWord_3763394) baseStart_3763394 baseEnd_3763394 := by
    simpa [prefixWord, tailWord_3763394, baseEnd_3763394] using wordTrace_append hprefix tailTrace_3763394
  have hstable : (prefixWord ++ tailWord_3763394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763394).length < 2 ^ (prefixWord ++ tailWord_3763394).sum := by decide
  have hdescent : baseEnd_3763394 < baseStart_3763394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763449 : List Nat := [1, 2, 1, 3, 1, 1, 4, 3, 2, 2, 3]
def baseStart_3763449 : Nat := 118140960795 + 3763449 * 2 ^ 59
def prefixEnd_3763449 : Nat := 4983230072969 + 3 ^ 40 * 3763449 * 2
def baseEnd_3763449 : Nat := 1932458255682751222179719

theorem tailTrace_3763449 : CollatzResearch.WordTrace tailWord_3763449 prefixEnd_3763449 1932458255682751222179719 := by
  unfold tailWord_3763449
  simp only [CollatzResearch.WordTrace]
  refine ⟨137264261742674493762693401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91509507828449662508462267 137264261742674493762693401)
  ·
    refine ⟨102948196307005870322020051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137264261742674493762693401 102948196307005870322020051)
    ·
      refine ⟨154422294460508805483030077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102948196307005870322020051 154422294460508805483030077)
      ·
        refine ⟨57908360422690802056136279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154422294460508805483030077 57908360422690802056136279)
        ·
          refine ⟨86862540634036203084204419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57908360422690802056136279 86862540634036203084204419)
          ·
            refine ⟨130293810951054304626306629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86862540634036203084204419 130293810951054304626306629)
            ·
              refine ⟨24430089553322682117432493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130293810951054304626306629 24430089553322682117432493)
              ·
                refine ⟨9161283582496005794037185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24430089553322682117432493 9161283582496005794037185)
                ·
                  refine ⟨6870962686872004345527889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9161283582496005794037185 6870962686872004345527889)
                  ·
                    refine ⟨5153222015154003259145917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6870962686872004345527889 5153222015154003259145917)
                    ·
                      refine ⟨1932458255682751222179719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5153222015154003259145917 1932458255682751222179719)
                      ·
                        rfl

theorem cell23_3763449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_3763449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3763449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3763449 prefixEnd_3763449 := by exact prefixLift 3763449
  have htrace : WordTrace (prefixWord ++ tailWord_3763449) baseStart_3763449 baseEnd_3763449 := by
    simpa [prefixWord, tailWord_3763449, baseEnd_3763449] using wordTrace_append hprefix tailTrace_3763449
  have hstable : (prefixWord ++ tailWord_3763449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763449).length < 2 ^ (prefixWord ++ tailWord_3763449).sum := by decide
  have hdescent : baseEnd_3763449 < baseStart_3763449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763473 : List Nat := [1, 2, 2, 1, 1, 4, 5, 2, 1, 4]
def baseStart_3763473 : Nat := 118140960795 + 3763473 * 2 ^ 59
def prefixEnd_3763473 : Nat := 4983230072969 + 3 ^ 40 * 3763473 * 2
def baseEnd_3763473 : Nat := 644156859739486376093203

theorem tailTrace_3763473 : CollatzResearch.WordTrace tailWord_3763473 prefixEnd_3763473 644156859739486376093203 := by
  unfold tailWord_3763473
  simp only [CollatzResearch.WordTrace]
  refine ⟨137265137094587545861567073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91510091396391697241044715 137265137094587545861567073)
  ·
    refine ⟨102948852820940659396175305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137265137094587545861567073 102948852820940659396175305)
    ·
      refine ⟨77211639615705494547131479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102948852820940659396175305 77211639615705494547131479)
      ·
        refine ⟨115817459423558241820697219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77211639615705494547131479 115817459423558241820697219)
        ·
          refine ⟨173726189135337362731045829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115817459423558241820697219 173726189135337362731045829)
          ·
            refine ⟨32573660462875755512071093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173726189135337362731045829 32573660462875755512071093)
            ·
              refine ⟨3053780668394602079256665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32573660462875755512071093 3053780668394602079256665)
              ·
                refine ⟨2290335501295951559442499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3053780668394602079256665 2290335501295951559442499)
                ·
                  refine ⟨3435503251943927339163749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2290335501295951559442499 3435503251943927339163749)
                  ·
                    refine ⟨644156859739486376093203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3435503251943927339163749 644156859739486376093203)
                    ·
                      rfl

theorem cell23_3763473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 2, 1, 4].length) (baseStart_3763473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3763473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3763473 prefixEnd_3763473 := by exact prefixLift 3763473
  have htrace : WordTrace (prefixWord ++ tailWord_3763473) baseStart_3763473 baseEnd_3763473 := by
    simpa [prefixWord, tailWord_3763473, baseEnd_3763473] using wordTrace_append hprefix tailTrace_3763473
  have hstable : (prefixWord ++ tailWord_3763473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763473).length < 2 ^ (prefixWord ++ tailWord_3763473).sum := by decide
  have hdescent : baseEnd_3763473 < baseStart_3763473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763529 : List Nat := [1, 2, 1, 1, 2, 3, 2, 3, 4, 4]
def baseStart_3763529 : Nat := 118140960795 + 3763529 * 2 ^ 59
def prefixEnd_3763529 : Nat := 4983230072969 + 3 ^ 40 * 3763529 * 2
def baseEnd_3763529 : Nat := 644166444711703636393117

theorem tailTrace_3763529 : CollatzResearch.WordTrace tailWord_3763529 prefixEnd_3763529 644166444711703636393117 := by
  unfold tailWord_3763529
  simp only [CollatzResearch.WordTrace]
  refine ⟨137267179582384667425605641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91511453054923111617070427 137267179582384667425605641)
  ·
    refine ⟨102950384686788500569204231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137267179582384667425605641 102950384686788500569204231)
    ·
      refine ⟨154425577030182750853806347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102950384686788500569204231 154425577030182750853806347)
      ·
        refine ⟨231638365545274126280709521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154425577030182750853806347 231638365545274126280709521)
        ·
          refine ⟨173728774158955594710532141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231638365545274126280709521 173728774158955594710532141)
          ·
            refine ⟨65148290309608348016449553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173728774158955594710532141 65148290309608348016449553)
            ·
              refine ⟨48861217732206261012337165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65148290309608348016449553 48861217732206261012337165)
              ·
                refine ⟨18322956649577347879626437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48861217732206261012337165 18322956649577347879626437)
                ·
                  refine ⟨3435554371795752727429957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18322956649577347879626437 3435554371795752727429957)
                  ·
                    refine ⟨644166444711703636393117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3435554371795752727429957 644166444711703636393117)
                    ·
                      rfl

theorem cell23_3763529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 4, 4].length) (baseStart_3763529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3763529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3763529 prefixEnd_3763529 := by exact prefixLift 3763529
  have htrace : WordTrace (prefixWord ++ tailWord_3763529) baseStart_3763529 baseEnd_3763529 := by
    simpa [prefixWord, tailWord_3763529, baseEnd_3763529] using wordTrace_append hprefix tailTrace_3763529
  have hstable : (prefixWord ++ tailWord_3763529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763529).length < 2 ^ (prefixWord ++ tailWord_3763529).sum := by decide
  have hdescent : baseEnd_3763529 < baseStart_3763529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763539 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 5, 2, 3]
def baseStart_3763539 : Nat := 118140960795 + 3763539 * 2 ^ 59
def prefixEnd_3763539 : Nat := 4983230072969 + 3 ^ 40 * 3763539 * 2
def baseEnd_3763539 : Nat := 1932504468941655870054305

theorem tailTrace_3763539 : CollatzResearch.WordTrace tailWord_3763539 prefixEnd_3763539 1932504468941655870054305 := by
  unfold tailWord_3763539
  simp only [CollatzResearch.WordTrace]
  refine ⟨137267544312348439133469671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91511696208232292755646447 137267544312348439133469671)
  ·
    refine ⟨205901316468522658700204507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137267544312348439133469671 205901316468522658700204507)
    ·
      refine ⟨308851974702783988050306761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205901316468522658700204507 308851974702783988050306761)
      ·
        refine ⟨231638981027087991037730071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308851974702783988050306761 231638981027087991037730071)
        ·
          refine ⟨347458471540631986556595107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231638981027087991037730071 347458471540631986556595107)
          ·
            refine ⟨521187707310947979834892661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347458471540631986556595107 521187707310947979834892661)
            ·
              refine ⟨48861347560401373109521187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 521187707310947979834892661 48861347560401373109521187)
              ·
                refine ⟨73292021340602059664281781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48861347560401373109521187 73292021340602059664281781)
                ·
                  refine ⟨6871127000681443093526417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73292021340602059664281781 6871127000681443093526417)
                  ·
                    refine ⟨5153345250511082320144813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6871127000681443093526417 5153345250511082320144813)
                    ·
                      refine ⟨1932504468941655870054305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5153345250511082320144813 1932504468941655870054305)
                      ·
                        rfl

theorem cell23_3763539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 2, 3].length) (baseStart_3763539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3763539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3763539 prefixEnd_3763539 := by exact prefixLift 3763539
  have htrace : WordTrace (prefixWord ++ tailWord_3763539) baseStart_3763539 baseEnd_3763539 := by
    simpa [prefixWord, tailWord_3763539, baseEnd_3763539] using wordTrace_append hprefix tailTrace_3763539
  have hstable : (prefixWord ++ tailWord_3763539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763539).length < 2 ^ (prefixWord ++ tailWord_3763539).sum := by decide
  have hdescent : baseEnd_3763539 < baseStart_3763539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763546 : List Nat := [3, 1, 1, 2, 1, 2, 4, 3, 2, 4]
def baseStart_3763546 : Nat := 118140960795 + 3763546 * 2 ^ 59
def prefixEnd_3763546 : Nat := 4983230072969 + 3 ^ 40 * 3763546 * 2
def baseEnd_3763546 : Nat := 644169354435412447555591

theorem tailTrace_3763546 : CollatzResearch.WordTrace tailWord_3763546 prefixEnd_3763546 644169354435412447555591 := by
  unfold tailWord_3763546
  simp only [CollatzResearch.WordTrace]
  refine ⟨34316949905830769832243623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91511866415548719552649661 34316949905830769832243623)
  ·
    refine ⟨51475424858746154748365435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34316949905830769832243623 51475424858746154748365435)
    ·
      refine ⟨77213137288119232122548153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51475424858746154748365435 77213137288119232122548153)
      ·
        refine ⟨57909852966089424091911115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77213137288119232122548153 57909852966089424091911115)
        ·
          refine ⟨86864779449134136137866673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57909852966089424091911115 86864779449134136137866673)
          ·
            refine ⟨65148584586850602103400005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86864779449134136137866673 65148584586850602103400005)
            ·
              refine ⟨12215359610034487894387501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65148584586850602103400005 12215359610034487894387501)
              ·
                refine ⟨4580759853762932960395313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12215359610034487894387501 4580759853762932960395313)
                ·
                  refine ⟨3435569890322199720296485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4580759853762932960395313 3435569890322199720296485)
                  ·
                    refine ⟨644169354435412447555591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3435569890322199720296485 644169354435412447555591)
                    ·
                      rfl

theorem cell23_3763546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 2, 4].length) (baseStart_3763546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3763546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3763546 prefixEnd_3763546 := by exact prefixLift 3763546
  have htrace : WordTrace (prefixWord ++ tailWord_3763546) baseStart_3763546 baseEnd_3763546 := by
    simpa [prefixWord, tailWord_3763546, baseEnd_3763546] using wordTrace_append hprefix tailTrace_3763546
  have hstable : (prefixWord ++ tailWord_3763546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763546).length < 2 ^ (prefixWord ++ tailWord_3763546).sum := by decide
  have hdescent : baseEnd_3763546 < baseStart_3763546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763556 : List Nat := [2, 3, 1, 1, 3, 2, 2, 1, 3, 2, 3]
def baseStart_3763556 : Nat := 118140960795 + 3763556 * 2 ^ 59
def prefixEnd_3763556 : Nat := 4983230072969 + 3 ^ 40 * 3763556 * 2
def baseEnd_3763556 : Nat := 1932513198112782303541727

theorem tailTrace_3763556 : CollatzResearch.WordTrace tailWord_3763556 prefixEnd_3763556 1932513198112782303541727 := by
  unfold tailWord_3763556
  simp only [CollatzResearch.WordTrace]
  refine ⟨68634082176643425518419261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91512109568857900691225681 68634082176643425518419261)
  ·
    refine ⟨25737780816241284569407223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68634082176643425518419261 25737780816241284569407223)
    ·
      refine ⟨38606671224361926854110835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25737780816241284569407223 38606671224361926854110835)
      ·
        refine ⟨57910006836542890281166253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38606671224361926854110835 57910006836542890281166253)
        ·
          refine ⟨21716252563703583855437345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57910006836542890281166253 21716252563703583855437345)
          ·
            refine ⟨16287189422777687891578009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21716252563703583855437345 16287189422777687891578009)
            ·
              refine ⟨12215392067083265918683507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16287189422777687891578009 12215392067083265918683507)
              ·
                refine ⟨18323088100624898878025261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12215392067083265918683507 18323088100624898878025261)
                ·
                  refine ⟨6871158037734337079259473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18323088100624898878025261 6871158037734337079259473)
                  ·
                    refine ⟨5153368528300752809444605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6871158037734337079259473 5153368528300752809444605)
                    ·
                      refine ⟨1932513198112782303541727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5153368528300752809444605 1932513198112782303541727)
                      ·
                        rfl

theorem cell23_3763556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_3763556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3763556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3763556 prefixEnd_3763556 := by exact prefixLift 3763556
  have htrace : WordTrace (prefixWord ++ tailWord_3763556) baseStart_3763556 baseEnd_3763556 := by
    simpa [prefixWord, tailWord_3763556, baseEnd_3763556] using wordTrace_append hprefix tailTrace_3763556
  have hstable : (prefixWord ++ tailWord_3763556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763556).length < 2 ^ (prefixWord ++ tailWord_3763556).sum := by decide
  have hdescent : baseEnd_3763556 < baseStart_3763556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763646 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3]
def baseStart_3763646 : Nat := 118140960795 + 3763646 * 2 ^ 59
def prefixEnd_3763646 : Nat := 4983230072969 + 3 ^ 40 * 3763646 * 2
def baseEnd_3763646 : Nat := 1932559411371686951416313

theorem tailTrace_3763646 : CollatzResearch.WordTrace tailWord_3763646 prefixEnd_3763646 1932559411371686951416313 := by
  unfold tailWord_3763646
  simp only [CollatzResearch.WordTrace]
  refine ⟨17158930865370099550951849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91514297948640530938409861 17158930865370099550951849)
  ·
    refine ⟨12869198149027574663213887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17158930865370099550951849 12869198149027574663213887)
    ·
      refine ⟨19303797223541361994820831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12869198149027574663213887 19303797223541361994820831)
      ·
        refine ⟨28955695835312042992231247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19303797223541361994820831 28955695835312042992231247)
        ·
          refine ⟨43433543752968064488346871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28955695835312042992231247 43433543752968064488346871)
          ·
            refine ⟨65150315629452096732520307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43433543752968064488346871 65150315629452096732520307)
            ·
              refine ⟨97725473444178145098780461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65150315629452096732520307 97725473444178145098780461)
              ·
                refine ⟨36647052541566804412042673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97725473444178145098780461 36647052541566804412042673)
                ·
                  refine ⟨27485289406175103309032005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36647052541566804412042673 27485289406175103309032005)
                  ·
                    refine ⟨5153491763657831870443501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27485289406175103309032005 5153491763657831870443501)
                    ·
                      refine ⟨1932559411371686951416313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5153491763657831870443501 1932559411371686951416313)
                      ·
                        rfl

theorem cell23_3763646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_3763646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3763646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3763646 prefixEnd_3763646 := by exact prefixLift 3763646
  have htrace : WordTrace (prefixWord ++ tailWord_3763646) baseStart_3763646 baseEnd_3763646 := by
    simpa [prefixWord, tailWord_3763646, baseEnd_3763646] using wordTrace_append hprefix tailTrace_3763646
  have hstable : (prefixWord ++ tailWord_3763646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763646).length < 2 ^ (prefixWord ++ tailWord_3763646).sum := by decide
  have hdescent : baseEnd_3763646 < baseStart_3763646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763696 : List Nat := [2, 1, 1, 1, 3, 4, 2, 2, 2, 5]
def baseStart_3763696 : Nat := 118140960795 + 3763696 * 2 ^ 59
def prefixEnd_3763696 : Nat := 4983230072969 + 3 ^ 40 * 3763696 * 2
def baseEnd_3763696 : Nat := 644195028468137251930361

theorem tailTrace_3763696 : CollatzResearch.WordTrace tailWord_3763696 prefixEnd_3763696 644195028468137251930361 := by
  unfold tailWord_3763696
  simp only [CollatzResearch.WordTrace]
  refine ⟨68636635286389827473467471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91515513715186436631289961 68636635286389827473467471)
  ·
    refine ⟨102954952929584741210201207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68636635286389827473467471 102954952929584741210201207)
    ·
      refine ⟨154432429394377111815301811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102954952929584741210201207 154432429394377111815301811)
      ·
        refine ⟨231648644091565667722952717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154432429394377111815301811 231648644091565667722952717)
        ·
          refine ⟨86868241534337125396107269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231648644091565667722952717 86868241534337125396107269)
          ·
            refine ⟨16287795287688211011770113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86868241534337125396107269 16287795287688211011770113)
            ·
              refine ⟨12215846465766158258827585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16287795287688211011770113 12215846465766158258827585)
              ·
                refine ⟨9161884849324618694120689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12215846465766158258827585 9161884849324618694120689)
                ·
                  refine ⟨6871413636993464020590517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9161884849324618694120689 6871413636993464020590517)
                  ·
                    refine ⟨644195028468137251930361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6871413636993464020590517 644195028468137251930361)
                    ·
                      rfl

theorem cell23_3763696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 2, 5].length) (baseStart_3763696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3763696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3763696 prefixEnd_3763696 := by exact prefixLift 3763696
  have htrace : WordTrace (prefixWord ++ tailWord_3763696) baseStart_3763696 baseEnd_3763696 := by
    simpa [prefixWord, tailWord_3763696, baseEnd_3763696] using wordTrace_append hprefix tailTrace_3763696
  have hstable : (prefixWord ++ tailWord_3763696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763696).length < 2 ^ (prefixWord ++ tailWord_3763696).sum := by decide
  have hdescent : baseEnd_3763696 < baseStart_3763696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763733 : List Nat := [1, 3, 2, 1, 3, 2, 3, 1, 2, 1, 4]
def baseStart_3763733 : Nat := 118140960795 + 3763733 * 2 ^ 59
def prefixEnd_3763733 : Nat := 4983230072969 + 3 ^ 40 * 3763733 * 2
def baseEnd_3763733 : Nat := 1932604084188628111028413

theorem tailTrace_3763733 : CollatzResearch.WordTrace tailWord_3763733 prefixEnd_3763733 1932604084188628111028413 := by
  unfold tailWord_3763733
  simp only [CollatzResearch.WordTrace]
  refine ⟨137274620073645610266031853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91516413382430406844021235 137274620073645610266031853)
  ·
    refine ⟨51477982527617103849761945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137274620073645610266031853 51477982527617103849761945)
    ·
      refine ⟨38608486895712827887321459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51477982527617103849761945 38608486895712827887321459)
      ·
        refine ⟨57912730343569241830982189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38608486895712827887321459 57912730343569241830982189)
        ·
          refine ⟨21717273878838465686618321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57912730343569241830982189 21717273878838465686618321)
          ·
            refine ⟨16287955409128849264963741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21717273878838465686618321 16287955409128849264963741)
            ·
              refine ⟨6107983278423318474361403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16287955409128849264963741 6107983278423318474361403)
              ·
                refine ⟨9161974917634977711542105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6107983278423318474361403 9161974917634977711542105)
                ·
                  refine ⟨6871481188226233283656579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9161974917634977711542105 6871481188226233283656579)
                  ·
                    refine ⟨10307221782339349925484869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6871481188226233283656579 10307221782339349925484869)
                    ·
                      refine ⟨1932604084188628111028413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10307221782339349925484869 1932604084188628111028413)
                      ·
                        rfl

theorem cell23_3763733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_3763733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3763733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3763733 prefixEnd_3763733 := by exact prefixLift 3763733
  have htrace : WordTrace (prefixWord ++ tailWord_3763733) baseStart_3763733 baseEnd_3763733 := by
    simpa [prefixWord, tailWord_3763733, baseEnd_3763733] using wordTrace_append hprefix tailTrace_3763733
  have hstable : (prefixWord ++ tailWord_3763733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763733).length < 2 ^ (prefixWord ++ tailWord_3763733).sum := by decide
  have hdescent : baseEnd_3763733 < baseStart_3763733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763746 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 2, 1, 6]
def baseStart_3763746 : Nat := 118140960795 + 3763746 * 2 ^ 59
def prefixEnd_3763746 : Nat := 4983230072969 + 3 ^ 40 * 3763746 * 2
def baseEnd_3763746 : Nat := 1932610759437136560165853

theorem tailTrace_3763746 : CollatzResearch.WordTrace tailWord_3763746 prefixEnd_3763746 1932610759437136560165853 := by
  unfold tailWord_3763746
  simp only [CollatzResearch.WordTrace]
  refine ⟨34318773555649628371563773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91516729481732342324170061 34318773555649628371563773)
  ·
    refine ⟨12869540083368610639336415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34318773555649628371563773 12869540083368610639336415)
    ·
      refine ⟨19304310125052915959004623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12869540083368610639336415 19304310125052915959004623)
      ·
        refine ⟨28956465187579373938506935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19304310125052915959004623 28956465187579373938506935)
        ·
          refine ⟨43434697781369060907760403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28956465187579373938506935 43434697781369060907760403)
          ·
            refine ⟨65152046672053591361640605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43434697781369060907760403 65152046672053591361640605)
            ·
              refine ⟨24432017502020096760615227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65152046672053591361640605 24432017502020096760615227)
              ·
                refine ⟨36648026253030145140922841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24432017502020096760615227 36648026253030145140922841)
                ·
                  refine ⟨27486019689772608855692131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36648026253030145140922841 27486019689772608855692131)
                  ·
                    refine ⟨41229029534658913283538197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27486019689772608855692131 41229029534658913283538197)
                    ·
                      refine ⟨1932610759437136560165853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41229029534658913283538197 1932610759437136560165853)
                      ·
                        rfl

theorem cell23_3763746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_3763746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3763746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3763746 prefixEnd_3763746 := by exact prefixLift 3763746
  have htrace : WordTrace (prefixWord ++ tailWord_3763746) baseStart_3763746 baseEnd_3763746 := by
    simpa [prefixWord, tailWord_3763746, baseEnd_3763746] using wordTrace_append hprefix tailTrace_3763746
  have hstable : (prefixWord ++ tailWord_3763746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763746).length < 2 ^ (prefixWord ++ tailWord_3763746).sum := by decide
  have hdescent : baseEnd_3763746 < baseStart_3763746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763793 : List Nat := [1, 2, 2, 1, 3, 2, 1, 3, 1, 5, 2]
def baseStart_3763793 : Nat := 118140960795 + 3763793 * 2 ^ 59
def prefixEnd_3763793 : Nat := 4983230072969 + 3 ^ 40 * 3763793 * 2
def baseEnd_3763793 : Nat := 1932634893027897876278137

theorem tailTrace_3763793 : CollatzResearch.WordTrace tailWord_3763793 prefixEnd_3763793 1932634893027897876278137 := by
  unfold tailWord_3763793
  simp only [CollatzResearch.WordTrace]
  refine ⟨137276808453428240513216033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91517872302285493675477355 137276808453428240513216033)
  ·
    refine ⟨102957606340071180384912025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137276808453428240513216033 102957606340071180384912025)
    ·
      refine ⟨77218204755053385288684019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102957606340071180384912025 77218204755053385288684019)
      ·
        refine ⟨115827307132580077933026029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77218204755053385288684019 115827307132580077933026029)
        ·
          refine ⟨43435240174717529224884761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115827307132580077933026029 43435240174717529224884761)
          ·
            refine ⟨32576430131038146918663571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43435240174717529224884761 32576430131038146918663571)
            ·
              refine ⟨48864645196557220377995357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32576430131038146918663571 48864645196557220377995357)
              ·
                refine ⟨18324241948708957641748259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48864645196557220377995357 18324241948708957641748259)
                ·
                  refine ⟨27486362923063436462622389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18324241948708957641748259 27486362923063436462622389)
                  ·
                    refine ⟨2576846524037197168370849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27486362923063436462622389 2576846524037197168370849)
                    ·
                      refine ⟨1932634893027897876278137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2576846524037197168370849 1932634893027897876278137)
                      ·
                        rfl

theorem cell23_3763793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 5, 2].length) (baseStart_3763793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3763793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3763793 prefixEnd_3763793 := by exact prefixLift 3763793
  have htrace : WordTrace (prefixWord ++ tailWord_3763793) baseStart_3763793 baseEnd_3763793 := by
    simpa [prefixWord, tailWord_3763793, baseEnd_3763793] using wordTrace_append hprefix tailTrace_3763793
  have hstable : (prefixWord ++ tailWord_3763793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763793).length < 2 ^ (prefixWord ++ tailWord_3763793).sum := by decide
  have hdescent : baseEnd_3763793 < baseStart_3763793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763840 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 5, 2, 2]
def baseStart_3763840 : Nat := 118140960795 + 3763840 * 2 ^ 59
def prefixEnd_3763840 : Nat := 4983230072969 + 3 ^ 40 * 3763840 * 2
def baseEnd_3763840 : Nat := 1932659026618659192390421

theorem tailTrace_3763840 : CollatzResearch.WordTrace tailWord_3763840 prefixEnd_3763840 1932659026618659192390421 := by
  unfold tailWord_3763840
  simp only [CollatzResearch.WordTrace]
  refine ⟨68639261342128983770088487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91519015122838645026784649 68639261342128983770088487)
  ·
    refine ⟨102958892013193475655132731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68639261342128983770088487 102958892013193475655132731)
    ·
      refine ⟨154438338019790213482699097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102958892013193475655132731 154438338019790213482699097)
      ·
        refine ⟨115828753514842660112024323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154438338019790213482699097 115828753514842660112024323)
        ·
          refine ⟨173743130272263990168036485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115828753514842660112024323 173743130272263990168036485)
          ·
            refine ⟨32576836926049498156506841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173743130272263990168036485 32576836926049498156506841)
            ·
              refine ⟨24432627694537123617380131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32576836926049498156506841 24432627694537123617380131)
              ·
                refine ⟨36648941541805685426070197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24432627694537123617380131 36648941541805685426070197)
                ·
                  refine ⟨3435838269544283008694081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36648941541805685426070197 3435838269544283008694081)
                  ·
                    refine ⟨2576878702158212256520561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3435838269544283008694081 2576878702158212256520561)
                    ·
                      refine ⟨1932659026618659192390421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2576878702158212256520561 1932659026618659192390421)
                      ·
                        rfl

theorem cell23_3763840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 5, 2, 2].length) (baseStart_3763840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3763840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3763840 prefixEnd_3763840 := by exact prefixLift 3763840
  have htrace : WordTrace (prefixWord ++ tailWord_3763840) baseStart_3763840 baseEnd_3763840 := by
    simpa [prefixWord, tailWord_3763840, baseEnd_3763840] using wordTrace_append hprefix tailTrace_3763840
  have hstable : (prefixWord ++ tailWord_3763840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763840).length < 2 ^ (prefixWord ++ tailWord_3763840).sum := by decide
  have hdescent : baseEnd_3763840 < baseStart_3763840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763868 : List Nat := [2, 2, 3, 2, 4, 1, 2, 2, 1, 1, 3]
def baseStart_3763868 : Nat := 118140960795 + 3763868 * 2 ^ 59
def prefixEnd_3763868 : Nat := 4983230072969 + 3 ^ 40 * 3763868 * 2
def baseEnd_3763868 : Nat := 1932673404076985082840293

theorem tailTrace_3763868 : CollatzResearch.WordTrace tailWord_3763868 prefixEnd_3763868 1932673404076985082840293 := by
  unfold tailWord_3763868
  simp only [CollatzResearch.WordTrace]
  refine ⟨68639771964078264161098129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91519695952104352214797505 68639771964078264161098129)
  ·
    refine ⟨51479828973058698120823597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68639771964078264161098129 51479828973058698120823597)
    ·
      refine ⟨19304935864897011795308849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51479828973058698120823597 19304935864897011795308849)
      ·
        refine ⟨14478701898672758846481637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19304935864897011795308849 14478701898672758846481637)
        ·
          refine ⟨2714756606001142283715307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14478701898672758846481637 2714756606001142283715307)
          ·
            refine ⟨4072134909001713425572961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2714756606001142283715307 4072134909001713425572961)
            ·
              refine ⟨3054101181751285069179721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4072134909001713425572961 3054101181751285069179721)
              ·
                refine ⟨2290575886313463801884791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3054101181751285069179721 2290575886313463801884791)
                ·
                  refine ⟨3435863829470195702827187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2290575886313463801884791 3435863829470195702827187)
                  ·
                    refine ⟨5153795744205293554240781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3435863829470195702827187 5153795744205293554240781)
                    ·
                      refine ⟨1932673404076985082840293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5153795744205293554240781 1932673404076985082840293)
                      ·
                        rfl

theorem cell23_3763868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_3763868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3763868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3763868 prefixEnd_3763868 := by exact prefixLift 3763868
  have htrace : WordTrace (prefixWord ++ tailWord_3763868) baseStart_3763868 baseEnd_3763868 := by
    simpa [prefixWord, tailWord_3763868, baseEnd_3763868] using wordTrace_append hprefix tailTrace_3763868
  have hstable : (prefixWord ++ tailWord_3763868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763868).length < 2 ^ (prefixWord ++ tailWord_3763868).sum := by decide
  have hdescent : baseEnd_3763868 < baseStart_3763868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763924 : List Nat := [2, 4, 1, 3, 1, 1, 3, 2, 2, 1, 3]
def baseStart_3763924 : Nat := 118140960795 + 3763924 * 2 ^ 59
def prefixEnd_3763924 : Nat := 4983230072969 + 3 ^ 40 * 3763924 * 2
def baseEnd_3763924 : Nat := 1932702158993636863740035

theorem tailTrace_3763924 : CollatzResearch.WordTrace tailWord_3763924 prefixEnd_3763924 1932702158993636863740035 := by
  unfold tailWord_3763924
  simp only [CollatzResearch.WordTrace]
  refine ⟨68640793207976824943117413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91521057610635766590823217 68640793207976824943117413)
  ·
    refine ⟨12870148726495654676834515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68640793207976824943117413 12870148726495654676834515)
    ·
      refine ⟨19305223089743482015251773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12870148726495654676834515 19305223089743482015251773)
      ·
        refine ⟨7239458658653805755719415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19305223089743482015251773 7239458658653805755719415)
        ·
          refine ⟨10859187987980708633579123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7239458658653805755719415 10859187987980708633579123)
          ·
            refine ⟨16288781981971062950368685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10859187987980708633579123 16288781981971062950368685)
            ·
              refine ⟨6108293243239148606388257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16288781981971062950368685 6108293243239148606388257)
              ·
                refine ⟨4581219932429361454791193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6108293243239148606388257 4581219932429361454791193)
                ·
                  refine ⟨3435914949322021091093395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4581219932429361454791193 3435914949322021091093395)
                  ·
                    refine ⟨5153872423983031636640093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3435914949322021091093395 5153872423983031636640093)
                    ·
                      refine ⟨1932702158993636863740035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5153872423983031636640093 1932702158993636863740035)
                      ·
                        rfl

theorem cell23_3763924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_3763924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3763924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3763924 prefixEnd_3763924 := by exact prefixLift 3763924
  have htrace : WordTrace (prefixWord ++ tailWord_3763924) baseStart_3763924 baseEnd_3763924 := by
    simpa [prefixWord, tailWord_3763924, baseEnd_3763924] using wordTrace_append hprefix tailTrace_3763924
  have hstable : (prefixWord ++ tailWord_3763924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763924).length < 2 ^ (prefixWord ++ tailWord_3763924).sum := by decide
  have hdescent : baseEnd_3763924 < baseStart_3763924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763947 : List Nat := [1, 1, 1, 1, 2, 4, 2, 5, 2, 2, 2]
def baseStart_3763947 : Nat := 118140960795 + 3763947 * 2 ^ 59
def prefixEnd_3763947 : Nat := 4983230072969 + 3 ^ 40 * 3763947 * 2
def baseEnd_3763947 : Nat := 1932713969048690273752429

theorem tailTrace_3763947 : CollatzResearch.WordTrace tailWord_3763947 prefixEnd_3763947 1932713969048690273752429 := by
  unfold tailWord_3763947
  simp only [CollatzResearch.WordTrace]
  refine ⟨137282425294870324814322095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91521616863246883209548063 137282425294870324814322095)
  ·
    refine ⟨205923637942305487221483143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137282425294870324814322095 205923637942305487221483143)
    ·
      refine ⟨308885456913458230832224715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205923637942305487221483143 308885456913458230832224715)
      ·
        refine ⟨463328185370187346248337073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308885456913458230832224715 463328185370187346248337073)
        ·
          refine ⟨347496139027640509686252805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463328185370187346248337073 347496139027640509686252805)
          ·
            refine ⟨65155526067682595566172401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 347496139027640509686252805 65155526067682595566172401)
            ·
              refine ⟨48866644550761946674629301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65155526067682595566172401 48866644550761946674629301)
              ·
                refine ⟨4581247926633932500746497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48866644550761946674629301 4581247926633932500746497)
                ·
                  refine ⟨3435935944975449375559873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4581247926633932500746497 3435935944975449375559873)
                  ·
                    refine ⟨2576951958731587031669905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3435935944975449375559873 2576951958731587031669905)
                    ·
                      refine ⟨1932713969048690273752429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2576951958731587031669905 1932713969048690273752429)
                      ·
                        rfl

theorem cell23_3763947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 2, 2, 2].length) (baseStart_3763947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3763947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3763947 prefixEnd_3763947 := by exact prefixLift 3763947
  have htrace : WordTrace (prefixWord ++ tailWord_3763947) baseStart_3763947 baseEnd_3763947 := by
    simpa [prefixWord, tailWord_3763947, baseEnd_3763947] using wordTrace_append hprefix tailTrace_3763947
  have hstable : (prefixWord ++ tailWord_3763947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763947).length < 2 ^ (prefixWord ++ tailWord_3763947).sum := by decide
  have hdescent : baseEnd_3763947 < baseStart_3763947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763953 : List Nat := [1, 2, 2, 2, 2, 3, 2, 2, 7]
def baseStart_3763953 : Nat := 118140960795 + 3763953 * 2 ^ 59
def prefixEnd_3763953 : Nat := 4983230072969 + 3 ^ 40 * 3763953 * 2
def baseEnd_3763953 : Nat := 214746338881401916697489

theorem tailTrace_3763953 : CollatzResearch.WordTrace tailWord_3763953 prefixEnd_3763953 214746338881401916697489 := by
  unfold tailWord_3763953
  simp only [CollatzResearch.WordTrace]
  refine ⟨137282644132848587839040513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91521762755232391892693675 137282644132848587839040513)
  ·
    refine ⟨102961983099636440879280385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137282644132848587839040513 102961983099636440879280385)
    ·
      refine ⟨77221487324727330659460289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102961983099636440879280385 77221487324727330659460289)
      ·
        refine ⟨57916115493545497994595217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77221487324727330659460289 57916115493545497994595217)
        ·
          refine ⟨43437086620159123495946413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57916115493545497994595217 43437086620159123495946413)
          ·
            refine ⟨16288907482559671310979905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43437086620159123495946413 16288907482559671310979905)
            ·
              refine ⟨12216680611919753483234929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16288907482559671310979905 12216680611919753483234929)
              ·
                refine ⟨9162510458939815112426197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12216680611919753483234929 9162510458939815112426197)
                ·
                  refine ⟨214746338881401916697489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9162510458939815112426197 214746338881401916697489)
                  ·
                    rfl

theorem cell23_3763953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 2, 7].length) (baseStart_3763953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3763953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3763953 prefixEnd_3763953 := by exact prefixLift 3763953
  have htrace : WordTrace (prefixWord ++ tailWord_3763953) baseStart_3763953 baseEnd_3763953 := by
    simpa [prefixWord, tailWord_3763953, baseEnd_3763953] using wordTrace_append hprefix tailTrace_3763953
  have hstable : (prefixWord ++ tailWord_3763953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763953).length < 2 ^ (prefixWord ++ tailWord_3763953).sum := by decide
  have hdescent : baseEnd_3763953 < baseStart_3763953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763963 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 4, 3, 3]
def baseStart_3763963 : Nat := 118140960795 + 3763963 * 2 ^ 59
def prefixEnd_3763963 : Nat := 4983230072969 + 3 ^ 40 * 3763963 * 2
def baseEnd_3763963 : Nat := 1932722184739162211152355

theorem tailTrace_3763963 : CollatzResearch.WordTrace tailWord_3763963 prefixEnd_3763963 1932722184739162211152355 := by
  unfold tailWord_3763963
  simp only [CollatzResearch.WordTrace]
  refine ⟨137283008862812359546904543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91522005908541573031269695 137283008862812359546904543)
  ·
    refine ⟨205924513294218539320356815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137283008862812359546904543 205924513294218539320356815)
    ·
      refine ⟨308886769941327808980535223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205924513294218539320356815 308886769941327808980535223)
      ·
        refine ⟨463330154911991713470802835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308886769941327808980535223 463330154911991713470802835)
        ·
          refine ⟨694995232367987570206204253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463330154911991713470802835 694995232367987570206204253)
          ·
            refine ⟨260623212137995338827326595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 694995232367987570206204253 260623212137995338827326595)
            ·
              refine ⟨390934818206993008240989893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260623212137995338827326595 390934818206993008240989893)
              ·
                refine ⟨73300278413811189045185605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 390934818206993008240989893 73300278413811189045185605)
                ·
                  refine ⟨13743802202589597945972301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73300278413811189045185605 13743802202589597945972301)
                  ·
                    refine ⟨5153925825971099229739613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13743802202589597945972301 5153925825971099229739613)
                    ·
                      refine ⟨1932722184739162211152355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5153925825971099229739613 1932722184739162211152355)
                      ·
                        rfl

theorem cell23_3763963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 3, 3].length) (baseStart_3763963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3763963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3763963 prefixEnd_3763963 := by exact prefixLift 3763963
  have htrace : WordTrace (prefixWord ++ tailWord_3763963) baseStart_3763963 baseEnd_3763963 := by
    simpa [prefixWord, tailWord_3763963, baseEnd_3763963] using wordTrace_append hprefix tailTrace_3763963
  have hstable : (prefixWord ++ tailWord_3763963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763963).length < 2 ^ (prefixWord ++ tailWord_3763963).sum := by decide
  have hdescent : baseEnd_3763963 < baseStart_3763963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764003 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 4]
def baseStart_3764003 : Nat := 118140960795 + 3764003 * 2 ^ 59
def prefixEnd_3764003 : Nat := 4983230072969 + 3 ^ 40 * 3764003 * 2
def baseEnd_3764003 : Nat := 1932742723965342054652171

theorem tailTrace_3764003 : CollatzResearch.WordTrace tailWord_3764003 prefixEnd_3764003 1932742723965342054652171 := by
  unfold tailWord_3764003
  simp only [CollatzResearch.WordTrace]
  refine ⟨137284467782667446378360663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91522978521778297585573775 137284467782667446378360663)
  ·
    refine ⟨205926701674001169567540995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137284467782667446378360663 205926701674001169567540995)
    ·
      refine ⟨308890052511001754351311493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205926701674001169567540995 308890052511001754351311493)
      ·
        refine ⟨57916884845812828940870905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 308890052511001754351311493 57916884845812828940870905)
        ·
          refine ⟨43437663634359621705653179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57916884845812828940870905 43437663634359621705653179)
          ·
            refine ⟨65156495451539432558479769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43437663634359621705653179 65156495451539432558479769)
            ·
              refine ⟨48867371588654574418859827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65156495451539432558479769 48867371588654574418859827)
              ·
                refine ⟨73301057382981861628289741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48867371588654574418859827 73301057382981861628289741)
                ·
                  refine ⟨27487896518618198110608653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73301057382981861628289741 27487896518618198110608653)
                  ·
                    refine ⟨10307961194481824291478245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27487896518618198110608653 10307961194481824291478245)
                    ·
                      refine ⟨1932742723965342054652171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10307961194481824291478245 1932742723965342054652171)
                      ·
                        rfl

theorem cell23_3764003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_3764003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764003 prefixEnd_3764003 := by exact prefixLift 3764003
  have htrace : WordTrace (prefixWord ++ tailWord_3764003) baseStart_3764003 baseEnd_3764003 := by
    simpa [prefixWord, tailWord_3764003, baseEnd_3764003] using wordTrace_append hprefix tailTrace_3764003
  have hstable : (prefixWord ++ tailWord_3764003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764003).length < 2 ^ (prefixWord ++ tailWord_3764003).sum := by decide
  have hdescent : baseEnd_3764003 < baseStart_3764003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764038 : List Nat := [6, 1, 1, 2, 1, 3, 2, 2, 5]
def baseStart_3764038 : Nat := 118140960795 + 3764038 * 2 ^ 59
def prefixEnd_3764038 : Nat := 4983230072969 + 3 ^ 40 * 3764038 * 2
def baseEnd_3764038 : Nat := 214751188420916601968279

theorem tailTrace_3764038 : CollatzResearch.WordTrace tailWord_3764038 prefixEnd_3764038 214751188420916601968279 := by
  unfold tailWord_3764038
  simp only [CollatzResearch.WordTrace]
  refine ⟨4290179510548145229871399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 91523829558360431570589845 4290179510548145229871399)
  ·
    refine ⟨6435269265822217844807099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4290179510548145229871399 6435269265822217844807099)
    ·
      refine ⟨9652903898733326767210649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6435269265822217844807099 9652903898733326767210649)
      ·
        refine ⟨7239677924049995075407987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9652903898733326767210649 7239677924049995075407987)
        ·
          refine ⟨10859516886074992613111981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7239677924049995075407987 10859516886074992613111981)
          ·
            refine ⟨4072318832278122229916993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10859516886074992613111981 4072318832278122229916993)
            ·
              refine ⟨3054239124208591672437745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4072318832278122229916993 3054239124208591672437745)
              ·
                refine ⟨2290679343156443754328309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3054239124208591672437745 2290679343156443754328309)
                ·
                  refine ⟨214751188420916601968279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2290679343156443754328309 214751188420916601968279)
                  ·
                    rfl

theorem cell23_3764038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_3764038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764038 prefixEnd_3764038 := by exact prefixLift 3764038
  have htrace : WordTrace (prefixWord ++ tailWord_3764038) baseStart_3764038 baseEnd_3764038 := by
    simpa [prefixWord, tailWord_3764038, baseEnd_3764038] using wordTrace_append hprefix tailTrace_3764038
  have hstable : (prefixWord ++ tailWord_3764038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764038).length < 2 ^ (prefixWord ++ tailWord_3764038).sum := by decide
  have hdescent : baseEnd_3764038 < baseStart_3764038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764074 : List Nat := [3, 1, 3, 4, 1, 1, 1, 1, 1, 4, 3]
def baseStart_3764074 : Nat := 118140960795 + 3764074 * 2 ^ 59
def prefixEnd_3764074 : Nat := 4983230072969 + 3 ^ 40 * 3764074 * 2
def baseEnd_3764074 : Nat := 1932779181091811276864345

theorem tailTrace_3764074 : CollatzResearch.WordTrace tailWord_3764074 prefixEnd_3764074 1932779181091811276864345 := by
  unfold tailWord_3764074
  simp only [CollatzResearch.WordTrace]
  refine ⟨34321764341352556376048819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91524704910273483669463517 34321764341352556376048819)
  ·
    refine ⟨51482646512028834564073229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34321764341352556376048819 51482646512028834564073229)
    ·
      refine ⟨19305992442010812961527461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51482646512028834564073229 19305992442010812961527461)
      ·
        refine ⟨3619873582877027430286399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19305992442010812961527461 3619873582877027430286399)
        ·
          refine ⟨5429810374315541145429599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3619873582877027430286399 5429810374315541145429599)
          ·
            refine ⟨8144715561473311718144399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5429810374315541145429599 8144715561473311718144399)
            ·
              refine ⟨12217073342209967577216599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8144715561473311718144399 12217073342209967577216599)
              ·
                refine ⟨18325610013314951365824899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12217073342209967577216599 18325610013314951365824899)
                ·
                  refine ⟨27488415019972427048737349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18325610013314951365824899 27488415019972427048737349)
                  ·
                    refine ⟨5154077816244830071638253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27488415019972427048737349 5154077816244830071638253)
                    ·
                      refine ⟨1932779181091811276864345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5154077816244830071638253 1932779181091811276864345)
                      ·
                        rfl

theorem cell23_3764074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_3764074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764074 prefixEnd_3764074 := by exact prefixLift 3764074
  have htrace : WordTrace (prefixWord ++ tailWord_3764074) baseStart_3764074 baseEnd_3764074 := by
    simpa [prefixWord, tailWord_3764074, baseEnd_3764074] using wordTrace_append hprefix tailTrace_3764074
  have hstable : (prefixWord ++ tailWord_3764074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764074).length < 2 ^ (prefixWord ++ tailWord_3764074).sum := by decide
  have hdescent : baseEnd_3764074 < baseStart_3764074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764083 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 5]
def baseStart_3764083 : Nat := 118140960795 + 3764083 * 2 ^ 59
def prefixEnd_3764083 : Nat := 4983230072969 + 3 ^ 40 * 3764083 * 2
def baseEnd_3764083 : Nat := 1932783802417701741651803

theorem tailTrace_3764083 : CollatzResearch.WordTrace tailWord_3764083 prefixEnd_3764083 1932783802417701741651803 := by
  unfold tailWord_3764083
  simp only [CollatzResearch.WordTrace]
  refine ⟨137287385622377620041272903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91524923748251746694181935 137287385622377620041272903)
  ·
    refine ⟨205931078433566430061909355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137287385622377620041272903 205931078433566430061909355)
    ·
      refine ⟨308896617650349645092864033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205931078433566430061909355 308896617650349645092864033)
      ·
        refine ⟨231672463237762233819648025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308896617650349645092864033 231672463237762233819648025)
        ·
          refine ⟨173754347428321675364736019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231672463237762233819648025 173754347428321675364736019)
          ·
            refine ⟨260631521142482513047104029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173754347428321675364736019 260631521142482513047104029)
            ·
              refine ⟨97736820428430942392664011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260631521142482513047104029 97736820428430942392664011)
              ·
                refine ⟨146605230642646413588996017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97736820428430942392664011 146605230642646413588996017)
                ·
                  refine ⟨109953922981984810191747013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146605230642646413588996017 109953922981984810191747013)
                  ·
                    refine ⟨20616360559122151910952565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109953922981984810191747013 20616360559122151910952565)
                    ·
                      refine ⟨1932783802417701741651803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20616360559122151910952565 1932783802417701741651803)
                      ·
                        rfl

theorem cell23_3764083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 5].length) (baseStart_3764083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764083 prefixEnd_3764083 := by exact prefixLift 3764083
  have htrace : WordTrace (prefixWord ++ tailWord_3764083) baseStart_3764083 baseEnd_3764083 := by
    simpa [prefixWord, tailWord_3764083, baseEnd_3764083] using wordTrace_append hprefix tailTrace_3764083
  have hstable : (prefixWord ++ tailWord_3764083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764083).length < 2 ^ (prefixWord ++ tailWord_3764083).sum := by decide
  have hdescent : baseEnd_3764083 < baseStart_3764083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764094 : List Nat := [4, 2, 3, 1, 1, 1, 3, 2, 6]
def baseStart_3764094 : Nat := 118140960795 + 3764094 * 2 ^ 59
def prefixEnd_3764094 : Nat := 4983230072969 + 3 ^ 40 * 3764094 * 2
def baseEnd_3764094 : Nat := 214754383411655688734917

theorem tailTrace_3764094 : CollatzResearch.WordTrace tailWord_3764094 prefixEnd_3764094 214754383411655688734917 := by
  unfold tailWord_3764094
  simp only [CollatzResearch.WordTrace]
  refine ⟨17160973353167221114990417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91525191216891845946615557 17160973353167221114990417)
  ·
    refine ⟨12870730014875415836242813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17160973353167221114990417 12870730014875415836242813)
    ·
      refine ⟨4826523755578280938591055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12870730014875415836242813 4826523755578280938591055)
      ·
        refine ⟨7239785633367421407886583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4826523755578280938591055 7239785633367421407886583)
        ·
          refine ⟨10859678450051132111829875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7239785633367421407886583 10859678450051132111829875)
          ·
            refine ⟨16289517675076698167744813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10859678450051132111829875 16289517675076698167744813)
            ·
              refine ⟨6108569128153761812904305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16289517675076698167744813 6108569128153761812904305)
              ·
                refine ⟨4581426846115321359678229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6108569128153761812904305 4581426846115321359678229)
                ·
                  refine ⟨214754383411655688734917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4581426846115321359678229 214754383411655688734917)
                  ·
                    rfl

theorem cell23_3764094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_3764094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764094 prefixEnd_3764094 := by exact prefixLift 3764094
  have htrace : WordTrace (prefixWord ++ tailWord_3764094) baseStart_3764094 baseEnd_3764094 := by
    simpa [prefixWord, tailWord_3764094, baseEnd_3764094] using wordTrace_append hprefix tailTrace_3764094
  have hstable : (prefixWord ++ tailWord_3764094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764094).length < 2 ^ (prefixWord ++ tailWord_3764094).sum := by decide
  have hdescent : baseEnd_3764094 < baseStart_3764094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764114 : List Nat := [3, 2, 3, 2, 1, 1, 1, 2, 1, 5, 2]
def baseStart_3764114 : Nat := 118140960795 + 3764114 * 2 ^ 59
def prefixEnd_3764114 : Nat := 4983230072969 + 3 ^ 40 * 3764114 * 2
def baseEnd_3764114 : Nat := 1932799720317991120364161

theorem tailTrace_3764114 : CollatzResearch.WordTrace tailWord_3764114 prefixEnd_3764114 1932799720317991120364161 := by
  unfold tailWord_3764114
  simp only [CollatzResearch.WordTrace]
  refine ⟨34322129071316328083912849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91525677523510208223767597 34322129071316328083912849)
  ·
    refine ⟨25741596803487246062934637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34322129071316328083912849 25741596803487246062934637)
    ·
      refine ⟨9653098801307717273600489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25741596803487246062934637 9653098801307717273600489)
      ·
        refine ⟨7239824100980787955200367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9653098801307717273600489 7239824100980787955200367)
        ·
          refine ⟨10859736151471181932800551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7239824100980787955200367 10859736151471181932800551)
          ·
            refine ⟨16289604227206772899200827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10859736151471181932800551 16289604227206772899200827)
            ·
              refine ⟨24434406340810159348801241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16289604227206772899200827 24434406340810159348801241)
              ·
                refine ⟨18325804755607619511600931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24434406340810159348801241 18325804755607619511600931)
                ·
                  refine ⟨27488707133411429267401397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18325804755607619511600931 27488707133411429267401397)
                  ·
                    refine ⟨2577066293757321493818881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27488707133411429267401397 2577066293757321493818881)
                    ·
                      refine ⟨1932799720317991120364161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2577066293757321493818881 1932799720317991120364161)
                      ·
                        rfl

theorem cell23_3764114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_3764114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764114 prefixEnd_3764114 := by exact prefixLift 3764114
  have htrace : WordTrace (prefixWord ++ tailWord_3764114) baseStart_3764114 baseEnd_3764114 := by
    simpa [prefixWord, tailWord_3764114, baseEnd_3764114] using wordTrace_append hprefix tailTrace_3764114
  have hstable : (prefixWord ++ tailWord_3764114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764114).length < 2 ^ (prefixWord ++ tailWord_3764114).sum := by decide
  have hdescent : baseEnd_3764114 < baseStart_3764114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764124 : List Nat := [2, 2, 3, 3, 1, 2, 2, 2, 1, 5]
def baseStart_3764124 : Nat := 118140960795 + 3764124 * 2 ^ 59
def prefixEnd_3764124 : Nat := 4983230072969 + 3 ^ 40 * 3764124 * 2
def baseEnd_3764124 : Nat := 644268285041512027079705

theorem tailTrace_3764124 : CollatzResearch.WordTrace tailWord_3764124 prefixEnd_3764124 644268285041512027079705 := by
  unfold tailWord_3764124
  simp only [CollatzResearch.WordTrace]
  refine ⟨68644440507614542021757713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91525920676819389362343617 68644440507614542021757713)
  ·
    refine ⟨51483330380710906516318285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68644440507614542021757713 51483330380710906516318285)
    ·
      refine ⟨19306248892766589943619357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51483330380710906516318285 19306248892766589943619357)
      ·
        refine ⟨7239843334787471228857259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19306248892766589943619357 7239843334787471228857259)
        ·
          refine ⟨10859765002181206843285889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7239843334787471228857259 10859765002181206843285889)
          ·
            refine ⟨8144823751635905132464417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10859765002181206843285889 8144823751635905132464417)
            ·
              refine ⟨6108617813726928849348313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8144823751635905132464417 6108617813726928849348313)
              ·
                refine ⟨4581463360295196637011235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6108617813726928849348313 4581463360295196637011235)
                ·
                  refine ⟨6872195040442794955516853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4581463360295196637011235 6872195040442794955516853)
                  ·
                    refine ⟨644268285041512027079705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6872195040442794955516853 644268285041512027079705)
                    ·
                      rfl

theorem cell23_3764124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_3764124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764124 prefixEnd_3764124 := by exact prefixLift 3764124
  have htrace : WordTrace (prefixWord ++ tailWord_3764124) baseStart_3764124 baseEnd_3764124 := by
    simpa [prefixWord, tailWord_3764124, baseEnd_3764124] using wordTrace_append hprefix tailTrace_3764124
  have hstable : (prefixWord ++ tailWord_3764124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764124).length < 2 ^ (prefixWord ++ tailWord_3764124).sum := by decide
  have hdescent : baseEnd_3764124 < baseStart_3764124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764147 : List Nat := [1, 1, 1, 2, 3, 1, 3, 5, 1, 2, 3]
def baseStart_3764147 : Nat := 118140960795 + 3764147 * 2 ^ 59
def prefixEnd_3764147 : Nat := 4983230072969 + 3 ^ 40 * 3764147 * 2
def baseEnd_3764147 : Nat := 1932816665179589491251509

theorem tailTrace_3764147 : CollatzResearch.WordTrace tailWord_3764147 prefixEnd_3764147 1932816665179589491251509 := by
  unfold tailWord_3764147
  simp only [CollatzResearch.WordTrace]
  refine ⟨137289719894145758971602695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91526479929430505981068463 137289719894145758971602695)
  ·
    refine ⟨205934579841218638457404043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137289719894145758971602695 205934579841218638457404043)
    ·
      refine ⟨308901869761827957686106065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205934579841218638457404043 308901869761827957686106065)
      ·
        refine ⟨231676402321370968264579549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308901869761827957686106065 231676402321370968264579549)
        ·
          refine ⟨86878650870514113099217331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231676402321370968264579549 86878650870514113099217331)
          ·
            refine ⟨130317976305771169648825997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86878650870514113099217331 130317976305771169648825997)
            ·
              refine ⟨48869241114664188618309749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130317976305771169648825997 48869241114664188618309749)
              ·
                refine ⟨4581491354499767682966539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48869241114664188618309749 4581491354499767682966539)
                ·
                  refine ⟨6872237031749651524449809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4581491354499767682966539 6872237031749651524449809)
                  ·
                    refine ⟨5154177773812238643337357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6872237031749651524449809 5154177773812238643337357)
                    ·
                      refine ⟨1932816665179589491251509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5154177773812238643337357 1932816665179589491251509)
                      ·
                        rfl

theorem cell23_3764147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 2, 3].length) (baseStart_3764147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764147 prefixEnd_3764147 := by exact prefixLift 3764147
  have htrace : WordTrace (prefixWord ++ tailWord_3764147) baseStart_3764147 baseEnd_3764147 := by
    simpa [prefixWord, tailWord_3764147, baseEnd_3764147] using wordTrace_append hprefix tailTrace_3764147
  have hstable : (prefixWord ++ tailWord_3764147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764147).length < 2 ^ (prefixWord ++ tailWord_3764147).sum := by decide
  have hdescent : baseEnd_3764147 < baseStart_3764147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764148 : List Nat := [2, 5, 2, 1, 2, 1, 1, 2, 2, 3, 2]
def baseStart_3764148 : Nat := 118140960795 + 3764148 * 2 ^ 59
def prefixEnd_3764148 : Nat := 4983230072969 + 3 ^ 40 * 3764148 * 2
def baseEnd_3764148 : Nat := 1932817178660243987339005

theorem tailTrace_3764148 : CollatzResearch.WordTrace tailWord_3764148 prefixEnd_3764148 1932817178660243987339005 := by
  unfold tailWord_3764148
  simp only [CollatzResearch.WordTrace]
  refine ⟨68644878183571068071194549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91526504244761424094926065 68644878183571068071194549)
  ·
    refine ⟨6435457329709787631674489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68644878183571068071194549 6435457329709787631674489)
    ·
      refine ⟨4826592997282340723755867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6435457329709787631674489 4826592997282340723755867)
      ·
        refine ⟨7239889495923511085633801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4826592997282340723755867 7239889495923511085633801)
        ·
          refine ⟨5429917121942633314225351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7239889495923511085633801 5429917121942633314225351)
          ·
            refine ⟨8144875682913949971338027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5429917121942633314225351 8144875682913949971338027)
            ·
              refine ⟨12217313524370924957007041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8144875682913949971338027 12217313524370924957007041)
              ·
                refine ⟨9162985143278193717755281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12217313524370924957007041 9162985143278193717755281)
                ·
                  refine ⟨6872238857458645288316461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9162985143278193717755281 6872238857458645288316461)
                  ·
                    refine ⟨2577089571546991983118673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6872238857458645288316461 2577089571546991983118673)
                    ·
                      refine ⟨1932817178660243987339005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2577089571546991983118673 1932817178660243987339005)
                      ·
                        rfl

theorem cell23_3764148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_3764148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764148 prefixEnd_3764148 := by exact prefixLift 3764148
  have htrace : WordTrace (prefixWord ++ tailWord_3764148) baseStart_3764148 baseEnd_3764148 := by
    simpa [prefixWord, tailWord_3764148, baseEnd_3764148] using wordTrace_append hprefix tailTrace_3764148
  have hstable : (prefixWord ++ tailWord_3764148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764148).length < 2 ^ (prefixWord ++ tailWord_3764148).sum := by decide
  have hdescent : baseEnd_3764148 < baseStart_3764148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764177 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 6, 1, 3]
def baseStart_3764177 : Nat := 118140960795 + 3764177 * 2 ^ 59
def prefixEnd_3764177 : Nat := 4983230072969 + 3 ^ 40 * 3764177 * 2
def baseEnd_3764177 : Nat := 1932832069599224373876371

theorem tailTrace_3764177 : CollatzResearch.WordTrace tailWord_3764177 prefixEnd_3764177 1932832069599224373876371 := by
  unfold tailWord_3764177
  simp only [CollatzResearch.WordTrace]
  refine ⟨137290814084037074095194785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91527209389358049396796523 137290814084037074095194785)
  ·
    refine ⟨102968110563027805571396089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137290814084037074095194785 102968110563027805571396089)
    ·
      refine ⟨77226082922270854178547067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102968110563027805571396089 77226082922270854178547067)
      ·
        refine ⟨115839124383406281267820601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77226082922270854178547067 115839124383406281267820601)
        ·
          refine ⟨86879343287554710950865451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115839124383406281267820601 86879343287554710950865451)
          ·
            refine ⟨130319014931332066426298177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86879343287554710950865451 130319014931332066426298177)
            ·
              refine ⟨97739261198499049819723633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130319014931332066426298177 97739261198499049819723633)
              ·
                refine ⟨73304445898874287364792725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97739261198499049819723633 73304445898874287364792725)
                ·
                  refine ⟨3436145901509732220224659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73304445898874287364792725 3436145901509732220224659)
                  ·
                    refine ⟨5154218852264598330336989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3436145901509732220224659 5154218852264598330336989)
                    ·
                      refine ⟨1932832069599224373876371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5154218852264598330336989 1932832069599224373876371)
                      ·
                        rfl

theorem cell23_3764177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 6, 1, 3].length) (baseStart_3764177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764177 prefixEnd_3764177 := by exact prefixLift 3764177
  have htrace : WordTrace (prefixWord ++ tailWord_3764177) baseStart_3764177 baseEnd_3764177 := by
    simpa [prefixWord, tailWord_3764177, baseEnd_3764177] using wordTrace_append hprefix tailTrace_3764177
  have hstable : (prefixWord ++ tailWord_3764177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764177).length < 2 ^ (prefixWord ++ tailWord_3764177).sum := by decide
  have hdescent : baseEnd_3764177 < baseStart_3764177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764178 : List Nat := [3, 2, 2, 3, 3, 1, 1, 2, 1, 1, 4]
def baseStart_3764178 : Nat := 118140960795 + 3764178 * 2 ^ 59
def prefixEnd_3764178 : Nat := 4983230072969 + 3 ^ 40 * 3764178 * 2
def baseEnd_3764178 : Nat := 1932832583079878869963867

theorem tailTrace_3764178 : CollatzResearch.WordTrace tailWord_3764178 prefixEnd_3764178 1932832583079878869963867 := by
  unfold tailWord_3764178
  simp only [CollatzResearch.WordTrace]
  refine ⟨34322712639258362816495297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91527233704688967510654125 34322712639258362816495297)
  ·
    refine ⟨25742034479443772112371473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34322712639258362816495297 25742034479443772112371473)
    ·
      refine ⟨19306525859582829084278605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25742034479443772112371473 19306525859582829084278605)
      ·
        refine ⟨7239947197343560906604477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19306525859582829084278605 7239947197343560906604477)
        ·
          refine ⟨2714980199003835339976679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7239947197343560906604477 2714980199003835339976679)
          ·
            refine ⟨4072470298505753009965019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2714980199003835339976679 4072470298505753009965019)
            ·
              refine ⟨6108705447758629514947529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4072470298505753009965019 6108705447758629514947529)
              ·
                refine ⟨4581529085818972136210647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6108705447758629514947529 4581529085818972136210647)
                ·
                  refine ⟨6872293628728458204315971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4581529085818972136210647 6872293628728458204315971)
                  ·
                    refine ⟨10308440443092687306473957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6872293628728458204315971 10308440443092687306473957)
                    ·
                      refine ⟨1932832583079878869963867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10308440443092687306473957 1932832583079878869963867)
                      ·
                        rfl

theorem cell23_3764178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_3764178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764178 prefixEnd_3764178 := by exact prefixLift 3764178
  have htrace : WordTrace (prefixWord ++ tailWord_3764178) baseStart_3764178 baseEnd_3764178 := by
    simpa [prefixWord, tailWord_3764178, baseEnd_3764178] using wordTrace_append hprefix tailTrace_3764178
  have hstable : (prefixWord ++ tailWord_3764178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764178).length < 2 ^ (prefixWord ++ tailWord_3764178).sum := by decide
  have hdescent : baseEnd_3764178 < baseStart_3764178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764181 : List Nat := [1, 3, 2, 3, 2, 3, 1, 2, 1, 2, 3]
def baseStart_3764181 : Nat := 118140960795 + 3764181 * 2 ^ 59
def prefixEnd_3764181 : Nat := 4983230072969 + 3 ^ 40 * 3764181 * 2
def baseEnd_3764181 : Nat := 1932834123521842358226353

theorem tailTrace_3764181 : CollatzResearch.WordTrace tailWord_3764181 prefixEnd_3764181 1932834123521842358226353 := by
  unfold tailWord_3764181
  simp only [CollatzResearch.WordTrace]
  refine ⟨137290959976022582778340397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91527306650681721852226931 137290959976022582778340397)
  ·
    refine ⟨51484109991008468541877649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137290959976022582778340397 51484109991008468541877649)
    ·
      refine ⟨38613082493256351406408237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51484109991008468541877649 38613082493256351406408237)
      ·
        refine ⟨14479905934971131777403089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38613082493256351406408237 14479905934971131777403089)
        ·
          refine ⟨10859929451228348833052317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14479905934971131777403089 10859929451228348833052317)
          ·
            refine ⟨4072473544210630812394619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10859929451228348833052317 4072473544210630812394619)
            ·
              refine ⟨6108710316315946218591929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4072473544210630812394619 6108710316315946218591929)
              ·
                refine ⟨4581532737236959663943947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6108710316315946218591929 4581532737236959663943947)
                ·
                  refine ⟨6872299105855439495915921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4581532737236959663943947 6872299105855439495915921)
                  ·
                    refine ⟨5154224329391579621936941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6872299105855439495915921 5154224329391579621936941)
                    ·
                      refine ⟨1932834123521842358226353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5154224329391579621936941 1932834123521842358226353)
                      ·
                        rfl

theorem cell23_3764181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_3764181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764181 prefixEnd_3764181 := by exact prefixLift 3764181
  have htrace : WordTrace (prefixWord ++ tailWord_3764181) baseStart_3764181 baseEnd_3764181 := by
    simpa [prefixWord, tailWord_3764181, baseEnd_3764181] using wordTrace_append hprefix tailTrace_3764181
  have hstable : (prefixWord ++ tailWord_3764181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764181).length < 2 ^ (prefixWord ++ tailWord_3764181).sum := by decide
  have hdescent : baseEnd_3764181 < baseStart_3764181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764204 : List Nat := [2, 2, 1, 1, 2, 1, 1, 7, 1, 3, 2]
def baseStart_3764204 : Nat := 118140960795 + 3764204 * 2 ^ 59
def prefixEnd_3764204 : Nat := 4983230072969 + 3 ^ 40 * 3764204 * 2
def baseEnd_3764204 : Nat := 1932845933576895768238747

theorem tailTrace_3764204 : CollatzResearch.WordTrace tailWord_3764204 prefixEnd_3764204 1932845933576895768238747 := by
  unfold tailWord_3764204
  simp only [CollatzResearch.WordTrace]
  refine ⟨68645899427469628853213833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91527865903292838470951777 68645899427469628853213833)
  ·
    refine ⟨51484424570602221639910375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68645899427469628853213833 51484424570602221639910375)
    ·
      refine ⟨77226636855903332459865563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51484424570602221639910375 77226636855903332459865563)
      ·
        refine ⟨115839955283854998689798345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77226636855903332459865563 115839955283854998689798345)
        ·
          refine ⟨86879966462891249017348759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115839955283854998689798345 86879966462891249017348759)
          ·
            refine ⟨130319949694336873526023139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86879966462891249017348759 130319949694336873526023139)
            ·
              refine ⟨195479924541505310289034709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130319949694336873526023139 195479924541505310289034709)
              ·
                refine ⟨4581560731441530709899251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 195479924541505310289034709 4581560731441530709899251)
                ·
                  refine ⟨6872341097162296064848877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4581560731441530709899251 6872341097162296064848877)
                  ·
                    refine ⟨2577127911435861024318329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6872341097162296064848877 2577127911435861024318329)
                    ·
                      refine ⟨1932845933576895768238747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2577127911435861024318329 1932845933576895768238747)
                      ·
                        rfl

theorem cell23_3764204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 3, 2].length) (baseStart_3764204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764204 prefixEnd_3764204 := by exact prefixLift 3764204
  have htrace : WordTrace (prefixWord ++ tailWord_3764204) baseStart_3764204 baseEnd_3764204 := by
    simpa [prefixWord, tailWord_3764204, baseEnd_3764204] using wordTrace_append hprefix tailTrace_3764204
  have hstable : (prefixWord ++ tailWord_3764204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764204).length < 2 ^ (prefixWord ++ tailWord_3764204).sum := by decide
  have hdescent : baseEnd_3764204 < baseStart_3764204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764240 : List Nat := [2, 1, 1, 1, 1, 1, 1, 8, 7]
def baseStart_3764240 : Nat := 118140960795 + 3764240 * 2 ^ 59
def prefixEnd_3764240 : Nat := 4983230072969 + 3 ^ 40 * 3764240 * 2
def baseEnd_3764240 : Nat := 214762713208939736376509

theorem tailTrace_3764240 : CollatzResearch.WordTrace tailWord_3764240 prefixEnd_3764240 214762713208939736376509 := by
  unfold tailWord_3764240
  simp only [CollatzResearch.WordTrace]
  refine ⟨68646555941404417927369087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91528741255205890569825449 68646555941404417927369087)
  ·
    refine ⟨102969833912106626891053631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68646555941404417927369087 102969833912106626891053631)
    ·
      refine ⟨154454750868159940336580447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102969833912106626891053631 154454750868159940336580447)
      ·
        refine ⟨231682126302239910504870671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154454750868159940336580447 231682126302239910504870671)
        ·
          refine ⟨347523189453359865757306007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231682126302239910504870671 347523189453359865757306007)
          ·
            refine ⟨521284784180039798635959011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347523189453359865757306007 521284784180039798635959011)
            ·
              refine ⟨781927176270059697953938517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521284784180039798635959011 781927176270059697953938517)
              ·
                refine ⟨9163209096914762085397717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 781927176270059697953938517 9163209096914762085397717)
                ·
                  refine ⟨214762713208939736376509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9163209096914762085397717 214762713208939736376509)
                  ·
                    rfl

theorem cell23_3764240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 8, 7].length) (baseStart_3764240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764240 prefixEnd_3764240 := by exact prefixLift 3764240
  have htrace : WordTrace (prefixWord ++ tailWord_3764240) baseStart_3764240 baseEnd_3764240 := by
    simpa [prefixWord, tailWord_3764240, baseEnd_3764240] using wordTrace_append hprefix tailTrace_3764240
  have hstable : (prefixWord ++ tailWord_3764240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764240).length < 2 ^ (prefixWord ++ tailWord_3764240).sum := by decide
  have hdescent : baseEnd_3764240 < baseStart_3764240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764274 : List Nat := [3, 2, 1, 1, 2, 3, 2, 4, 5]
def baseStart_3764274 : Nat := 118140960795 + 3764274 * 2 ^ 59
def prefixEnd_3764274 : Nat := 4983230072969 + 3 ^ 40 * 3764274 * 2
def baseEnd_3764274 : Nat := 214764653024745610484825

theorem tailTrace_3764274 : CollatzResearch.WordTrace tailWord_3764274 prefixEnd_3764274 214764653024745610484825 := by
  unfold tailWord_3764274
  simp only [CollatzResearch.WordTrace]
  refine ⟨34323587991171414915368969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91529567976457106440983917 34323587991171414915368969)
  ·
    refine ⟨25742690993378561186526727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34323587991171414915368969 25742690993378561186526727)
    ·
      refine ⟨38614036490067841779790091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25742690993378561186526727 38614036490067841779790091)
      ·
        refine ⟨57921054735101762669685137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38614036490067841779790091 57921054735101762669685137)
        ·
          refine ⟨43440791051326322002263853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57921054735101762669685137 43440791051326322002263853)
          ·
            refine ⟨16290296644247370750848945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43440791051326322002263853 16290296644247370750848945)
            ·
              refine ⟨12217722483185528063136709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16290296644247370750848945 12217722483185528063136709)
              ·
                refine ⟨2290822965597286511838133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12217722483185528063136709 2290822965597286511838133)
                ·
                  refine ⟨214764653024745610484825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2290822965597286511838133 214764653024745610484825)
                  ·
                    rfl

theorem cell23_3764274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 4, 5].length) (baseStart_3764274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764274 prefixEnd_3764274 := by exact prefixLift 3764274
  have htrace : WordTrace (prefixWord ++ tailWord_3764274) baseStart_3764274 baseEnd_3764274 := by
    simpa [prefixWord, tailWord_3764274, baseEnd_3764274] using wordTrace_append hprefix tailTrace_3764274
  have hstable : (prefixWord ++ tailWord_3764274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764274).length < 2 ^ (prefixWord ++ tailWord_3764274).sum := by decide
  have hdescent : baseEnd_3764274 < baseStart_3764274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764324 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 4, 4, 2]
def baseStart_3764324 : Nat := 118140960795 + 3764324 * 2 ^ 59
def prefixEnd_3764324 : Nat := 4983230072969 + 3 ^ 40 * 3764324 * 2
def baseEnd_3764324 : Nat := 1932907551255435298738195

theorem tailTrace_3764324 : CollatzResearch.WordTrace tailWord_3764324 prefixEnd_3764324 1932907551255435298738195 := by
  unfold tailWord_3764324
  simp only [CollatzResearch.WordTrace]
  refine ⟨68648087807252259100398013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91530783743003012133864017 68648087807252259100398013)
  ·
    refine ⟨25743032927719597162649255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68648087807252259100398013 25743032927719597162649255)
    ·
      refine ⟨38614549391579395743973883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25743032927719597162649255 38614549391579395743973883)
      ·
        refine ⟨57921824087369093615960825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38614549391579395743973883 57921824087369093615960825)
        ·
          refine ⟨43441368065526820211970619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57921824087369093615960825 43441368065526820211970619)
          ·
            refine ⟨65162052098290230317955929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43441368065526820211970619 65162052098290230317955929)
            ·
              refine ⟨48871539073717672738466947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65162052098290230317955929 48871539073717672738466947)
              ·
                refine ⟨73307308610576509107700421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48871539073717672738466947 73307308610576509107700421)
                ·
                  refine ⟨13745120364483095457693829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73307308610576509107700421 13745120364483095457693829)
                  ·
                    refine ⟨2577210068340580398317593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13745120364483095457693829 2577210068340580398317593)
                    ·
                      refine ⟨1932907551255435298738195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2577210068340580398317593 1932907551255435298738195)
                      ·
                        rfl

theorem cell23_3764324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 4, 4, 2].length) (baseStart_3764324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764324 prefixEnd_3764324 := by exact prefixLift 3764324
  have htrace : WordTrace (prefixWord ++ tailWord_3764324) baseStart_3764324 baseEnd_3764324 := by
    simpa [prefixWord, tailWord_3764324, baseEnd_3764324] using wordTrace_append hprefix tailTrace_3764324
  have hstable : (prefixWord ++ tailWord_3764324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764324).length < 2 ^ (prefixWord ++ tailWord_3764324).sum := by decide
  have hdescent : baseEnd_3764324 < baseStart_3764324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764385 : List Nat := [1, 2, 3, 3, 1, 4, 2, 2, 1, 4]
def baseStart_3764385 : Nat := 118140960795 + 3764385 * 2 ^ 59
def prefixEnd_3764385 : Nat := 4983230072969 + 3 ^ 40 * 3764385 * 2
def baseEnd_3764385 : Nat := 644312957858453186691805

theorem tailTrace_3764385 : CollatzResearch.WordTrace tailWord_3764385 prefixEnd_3764385 644312957858453186691805 := by
  unfold tailWord_3764385
  simp only [CollatzResearch.WordTrace]
  refine ⟨137298400467283525618766609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91532266978189017079177739 137298400467283525618766609)
  ·
    refine ⟨102973800350462644214074957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137298400467283525618766609 102973800350462644214074957)
    ·
      refine ⟨38615175131423491580278109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102973800350462644214074957 38615175131423491580278109)
      ·
        refine ⟨14480690674283809342604291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38615175131423491580278109 14480690674283809342604291)
        ·
          refine ⟨21721036011425714013906437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14480690674283809342604291 21721036011425714013906437)
          ·
            refine ⟨4072694252142321377607457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21721036011425714013906437 4072694252142321377607457)
            ·
              refine ⟨3054520689106741033205593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4072694252142321377607457 3054520689106741033205593)
              ·
                refine ⟨2290890516830055774904195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3054520689106741033205593 2290890516830055774904195)
                ·
                  refine ⟨3436335775245083662356293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2290890516830055774904195 3436335775245083662356293)
                  ·
                    refine ⟨644312957858453186691805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3436335775245083662356293 644312957858453186691805)
                    ·
                      rfl

theorem cell23_3764385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 2, 1, 4].length) (baseStart_3764385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764385 prefixEnd_3764385 := by exact prefixLift 3764385
  have htrace : WordTrace (prefixWord ++ tailWord_3764385) baseStart_3764385 baseEnd_3764385 := by
    simpa [prefixWord, tailWord_3764385, baseEnd_3764385] using wordTrace_append hprefix tailTrace_3764385
  have hstable : (prefixWord ++ tailWord_3764385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764385).length < 2 ^ (prefixWord ++ tailWord_3764385).sum := by decide
  have hdescent : baseEnd_3764385 < baseStart_3764385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764424 : List Nat := [2, 1, 3, 1, 2, 1, 1, 4, 4, 4]
def baseStart_3764424 : Nat := 118140960795 + 3764424 * 2 ^ 59
def prefixEnd_3764424 : Nat := 4983230072969 + 3 ^ 40 * 3764424 * 2
def baseEnd_3764424 : Nat := 644319633106961635829245

theorem tailTrace_3764424 : CollatzResearch.WordTrace tailWord_3764424 prefixEnd_3764424 644319633106961635829245 := by
  unfold tailWord_3764424
  simp only [CollatzResearch.WordTrace]
  refine ⟨68649911457071117639718163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91533215276094823519624217 68649911457071117639718163)
  ·
    refine ⟨102974867185606676459577245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68649911457071117639718163 102974867185606676459577245)
    ·
      refine ⟨38615575194602503672341467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102974867185606676459577245 38615575194602503672341467)
      ·
        refine ⟨57923362791903755508512201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38615575194602503672341467 57923362791903755508512201)
        ·
          refine ⟨43442522093927816631384151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57923362791903755508512201 43442522093927816631384151)
          ·
            refine ⟨65163783140891724947076227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43442522093927816631384151 65163783140891724947076227)
            ·
              refine ⟨97745674711337587420614341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65163783140891724947076227 97745674711337587420614341)
              ·
                refine ⟨18327314008375797641365189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97745674711337587420614341 18327314008375797641365189)
                ·
                  refine ⟨3436371376570462057755973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18327314008375797641365189 3436371376570462057755973)
                  ·
                    refine ⟨644319633106961635829245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3436371376570462057755973 644319633106961635829245)
                    ·
                      rfl

theorem cell23_3764424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_3764424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764424 prefixEnd_3764424 := by exact prefixLift 3764424
  have htrace : WordTrace (prefixWord ++ tailWord_3764424) baseStart_3764424 baseEnd_3764424 := by
    simpa [prefixWord, tailWord_3764424, baseEnd_3764424] using wordTrace_append hprefix tailTrace_3764424
  have hstable : (prefixWord ++ tailWord_3764424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764424).length < 2 ^ (prefixWord ++ tailWord_3764424).sum := by decide
  have hdescent : baseEnd_3764424 < baseStart_3764424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764428 : List Nat := [2, 2, 1, 6, 1, 1, 1, 3, 1, 5]
def baseStart_3764428 : Nat := 118140960795 + 3764428 * 2 ^ 59
def prefixEnd_3764428 : Nat := 4983230072969 + 3 ^ 40 * 3764428 * 2
def baseEnd_3764428 : Nat := 644320317747834297279239

theorem tailTrace_3764428 : CollatzResearch.WordTrace tailWord_3764428 prefixEnd_3764428 644320317747834297279239 := by
  unfold tailWord_3764428
  simp only [CollatzResearch.WordTrace]
  refine ⟨68649984403063871981290969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91533312537418495975054625 68649984403063871981290969)
  ·
    refine ⟨51487488302297903985968227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68649984403063871981290969 51487488302297903985968227)
    ·
      refine ⟨77231232453446855978952341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51487488302297903985968227 77231232453446855978952341)
      ·
        refine ⟨3620214021255321374013391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 77231232453446855978952341 3620214021255321374013391)
        ·
          refine ⟨5430321031882982061020087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3620214021255321374013391 5430321031882982061020087)
          ·
            refine ⟨8145481547824473091530131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5430321031882982061020087 8145481547824473091530131)
            ·
              refine ⟨12218222321736709637295197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8145481547824473091530131 12218222321736709637295197)
              ·
                refine ⟨4581833370651266113985699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12218222321736709637295197 4581833370651266113985699)
                ·
                  refine ⟨6872750055976899170978549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4581833370651266113985699 6872750055976899170978549)
                  ·
                    refine ⟨644320317747834297279239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6872750055976899170978549 644320317747834297279239)
                    ·
                      rfl

theorem cell23_3764428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 1, 5].length) (baseStart_3764428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764428 prefixEnd_3764428 := by exact prefixLift 3764428
  have htrace : WordTrace (prefixWord ++ tailWord_3764428) baseStart_3764428 baseEnd_3764428 := by
    simpa [prefixWord, tailWord_3764428, baseEnd_3764428] using wordTrace_append hprefix tailTrace_3764428
  have hstable : (prefixWord ++ tailWord_3764428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764428).length < 2 ^ (prefixWord ++ tailWord_3764428).sum := by decide
  have hdescent : baseEnd_3764428 < baseStart_3764428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764431 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 5, 2, 2]
def baseStart_3764431 : Nat := 118140960795 + 3764431 * 2 ^ 59
def prefixEnd_3764431 : Nat := 4983230072969 + 3 ^ 40 * 3764431 * 2
def baseEnd_3764431 : Nat := 1932962493685466380100203

theorem tailTrace_3764431 : CollatzResearch.WordTrace tailWord_3764431 prefixEnd_3764431 1932962493685466380100203 := by
  unfold tailWord_3764431
  simp only [CollatzResearch.WordTrace]
  refine ⟨137300078225116875474941147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91533385483411250316627431 137300078225116875474941147)
  ·
    refine ⟨205950117337675313212411721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137300078225116875474941147 205950117337675313212411721)
    ·
      refine ⟨154462588003256484909308791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205950117337675313212411721 154462588003256484909308791)
      ·
        refine ⟨231693882004884727363963187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154462588003256484909308791 231693882004884727363963187)
        ·
          refine ⟨347540823007327091045944781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231693882004884727363963187 347540823007327091045944781)
          ·
            refine ⟨130327808627747659142229293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 347540823007327091045944781 130327808627747659142229293)
            ·
              refine ⟨48872928235405372178335985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130327808627747659142229293 48872928235405372178335985)
              ·
                refine ⟨36654696176554029133751989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48872928235405372178335985 36654696176554029133751989)
                ·
                  refine ⟨3436377766551940231289249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36654696176554029133751989 3436377766551940231289249)
                  ·
                    refine ⟨2577283324913955173466937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3436377766551940231289249 2577283324913955173466937)
                    ·
                      refine ⟨1932962493685466380100203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2577283324913955173466937 1932962493685466380100203)
                      ·
                        rfl

theorem cell23_3764431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 5, 2, 2].length) (baseStart_3764431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764431 prefixEnd_3764431 := by exact prefixLift 3764431
  have htrace : WordTrace (prefixWord ++ tailWord_3764431) baseStart_3764431 baseEnd_3764431 := by
    simpa [prefixWord, tailWord_3764431, baseEnd_3764431] using wordTrace_append hprefix tailTrace_3764431
  have hstable : (prefixWord ++ tailWord_3764431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764431).length < 2 ^ (prefixWord ++ tailWord_3764431).sum := by decide
  have hdescent : baseEnd_3764431 < baseStart_3764431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764441 : List Nat := [1, 2, 1, 2, 3, 1, 5, 2, 2, 4]
def baseStart_3764441 : Nat := 118140960795 + 3764441 * 2 ^ 59
def prefixEnd_3764441 : Nat := 4983230072969 + 3 ^ 40 * 3764441 * 2
def baseEnd_3764441 : Nat := 644322542830670446991719

theorem tailTrace_3764441 : CollatzResearch.WordTrace tailWord_3764441 prefixEnd_3764441 644322542830670446991719 := by
  unfold tailWord_3764441
  simp only [CollatzResearch.WordTrace]
  refine ⟨137300442955080647182805177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91533628636720431455203451 137300442955080647182805177)
  ·
    refine ⟨102975332216310485387103883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137300442955080647182805177 102975332216310485387103883)
    ·
      refine ⟨154462998324465728080655825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102975332216310485387103883 154462998324465728080655825)
      ·
        refine ⟨115847248743349296060491869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154462998324465728080655825 115847248743349296060491869)
        ·
          refine ⟨43442718278755986022684451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115847248743349296060491869 43442718278755986022684451)
          ·
            refine ⟨65164077418133979034026677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43442718278755986022684451 65164077418133979034026677)
            ·
              refine ⟨6109132257950060534440001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65164077418133979034026677 6109132257950060534440001)
              ·
                refine ⟨4581849193462545400830001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6109132257950060534440001 4581849193462545400830001)
                ·
                  refine ⟨3436386895096909050622501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4581849193462545400830001 3436386895096909050622501)
                  ·
                    refine ⟨644322542830670446991719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3436386895096909050622501 644322542830670446991719)
                    ·
                      rfl

theorem cell23_3764441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 2, 2, 4].length) (baseStart_3764441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764441 prefixEnd_3764441 := by exact prefixLift 3764441
  have htrace : WordTrace (prefixWord ++ tailWord_3764441) baseStart_3764441 baseEnd_3764441 := by
    simpa [prefixWord, tailWord_3764441, baseEnd_3764441] using wordTrace_append hprefix tailTrace_3764441
  have hstable : (prefixWord ++ tailWord_3764441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764441).length < 2 ^ (prefixWord ++ tailWord_3764441).sum := by decide
  have hdescent : baseEnd_3764441 < baseStart_3764441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764447 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 7]
def baseStart_3764447 : Nat := 118140960795 + 3764447 * 2 ^ 59
def prefixEnd_3764447 : Nat := 4983230072969 + 3 ^ 40 * 3764447 * 2
def baseEnd_3764447 : Nat := 1932970709375938317500129

theorem tailTrace_3764447 : CollatzResearch.WordTrace tailWord_3764447 prefixEnd_3764447 1932970709375938317500129 := by
  unfold tailWord_3764447
  simp only [CollatzResearch.WordTrace]
  refine ⟨137300661793058910207523595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91533774528705940138349063 137300661793058910207523595)
  ·
    refine ⟨205950992689588365311285393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137300661793058910207523595 205950992689588365311285393)
    ·
      refine ⟨154463244517191273983464045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205950992689588365311285393 154463244517191273983464045)
      ·
        refine ⟨57923716693946727743799017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154463244517191273983464045 57923716693946727743799017)
        ·
          refine ⟨43442787520460045807849263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57923716693946727743799017 43442787520460045807849263)
          ·
            refine ⟨65164181280690068711773895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43442787520460045807849263 65164181280690068711773895)
            ·
              refine ⟨97746271921035103067660843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65164181280690068711773895 97746271921035103067660843)
              ·
                refine ⟨146619407881552654601491265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97746271921035103067660843 146619407881552654601491265)
                ·
                  refine ⟨109964555911164490951118449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146619407881552654601491265 109964555911164490951118449)
                  ·
                    refine ⟨82473416933373368213338837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 109964555911164490951118449 82473416933373368213338837)
                    ·
                      refine ⟨1932970709375938317500129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 82473416933373368213338837 1932970709375938317500129)
                      ·
                        rfl

theorem cell23_3764447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_3764447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764447 prefixEnd_3764447 := by exact prefixLift 3764447
  have htrace : WordTrace (prefixWord ++ tailWord_3764447) baseStart_3764447 baseEnd_3764447 := by
    simpa [prefixWord, tailWord_3764447, baseEnd_3764447] using wordTrace_append hprefix tailTrace_3764447
  have hstable : (prefixWord ++ tailWord_3764447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764447).length < 2 ^ (prefixWord ++ tailWord_3764447).sum := by decide
  have hdescent : baseEnd_3764447 < baseStart_3764447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764448 : List Nat := [2, 1, 1, 3, 1, 3, 4, 1, 3, 2, 2]
def baseStart_3764448 : Nat := 118140960795 + 3764448 * 2 ^ 59
def prefixEnd_3764448 : Nat := 4983230072969 + 3 ^ 40 * 3764448 * 2
def baseEnd_3764448 : Nat := 1932971222856592813587625

theorem tailTrace_3764448 : CollatzResearch.WordTrace tailWord_3764448 prefixEnd_3764448 1932971222856592813587625 := by
  unfold tailWord_3764448
  simp only [CollatzResearch.WordTrace]
  refine ⟨68650349133027643689154999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91533798844036858252206665 68650349133027643689154999)
  ·
    refine ⟨102975523699541465533732499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68650349133027643689154999 102975523699541465533732499)
    ·
      refine ⟨154463285549312198300598749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102975523699541465533732499 154463285549312198300598749)
      ·
        refine ⟨57923732080992074362724531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154463285549312198300598749 57923732080992074362724531)
        ·
          refine ⟨86885598121488111544086797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57923732080992074362724531 86885598121488111544086797)
          ·
            refine ⟨32582099295558041829032549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86885598121488111544086797 32582099295558041829032549)
            ·
              refine ⟨6109143617917132842943603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32582099295558041829032549 6109143617917132842943603)
              ·
                refine ⟨9163715426875699264415405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6109143617917132842943603 9163715426875699264415405)
                ·
                  refine ⟨3436393285078387224155777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9163715426875699264415405 3436393285078387224155777)
                  ·
                    refine ⟨2577294963808790418116833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3436393285078387224155777 2577294963808790418116833)
                    ·
                      refine ⟨1932971222856592813587625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2577294963808790418116833 1932971222856592813587625)
                      ·
                        rfl

theorem cell23_3764448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 3, 2, 2].length) (baseStart_3764448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764448 prefixEnd_3764448 := by exact prefixLift 3764448
  have htrace : WordTrace (prefixWord ++ tailWord_3764448) baseStart_3764448 baseEnd_3764448 := by
    simpa [prefixWord, tailWord_3764448, baseEnd_3764448] using wordTrace_append hprefix tailTrace_3764448
  have hstable : (prefixWord ++ tailWord_3764448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764448).length < 2 ^ (prefixWord ++ tailWord_3764448).sum := by decide
  have hdescent : baseEnd_3764448 < baseStart_3764448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764457 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 2, 2, 6]
def baseStart_3764457 : Nat := 118140960795 + 3764457 * 2 ^ 59
def prefixEnd_3764457 : Nat := 4983230072969 + 3 ^ 40 * 3764457 * 2
def baseEnd_3764457 : Nat := 1932975844182483278375083

theorem tailTrace_3764457 : CollatzResearch.WordTrace tailWord_3764457 prefixEnd_3764457 1932975844182483278375083 := by
  unfold tailWord_3764457
  simp only [CollatzResearch.WordTrace]
  refine ⟨137301026523022681915387625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91534017682015121276925083 137301026523022681915387625)
  ·
    refine ⟨102975769892267011436540719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137301026523022681915387625 102975769892267011436540719)
    ·
      refine ⟨154463654838400517154811079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102975769892267011436540719 154463654838400517154811079)
      ·
        refine ⟨231695482257600775732216619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154463654838400517154811079 231695482257600775732216619)
        ·
          refine ⟨347543223386401163598324929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231695482257600775732216619 347543223386401163598324929)
          ·
            refine ⟨260657417539800872698743697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347543223386401163598324929 260657417539800872698743697)
            ·
              refine ⟨195493063154850654524057773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260657417539800872698743697 195493063154850654524057773)
              ·
                refine ⟨73309898683068995446521665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195493063154850654524057773 73309898683068995446521665)
                ·
                  refine ⟨54982424012301746584891249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73309898683068995446521665 54982424012301746584891249)
                  ·
                    refine ⟨41236818009226309938668437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54982424012301746584891249 41236818009226309938668437)
                    ·
                      refine ⟨1932975844182483278375083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41236818009226309938668437 1932975844182483278375083)
                      ·
                        rfl

theorem cell23_3764457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 2, 6].length) (baseStart_3764457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764457 prefixEnd_3764457 := by exact prefixLift 3764457
  have htrace : WordTrace (prefixWord ++ tailWord_3764457) baseStart_3764457 baseEnd_3764457 := by
    simpa [prefixWord, tailWord_3764457, baseEnd_3764457] using wordTrace_append hprefix tailTrace_3764457
  have hstable : (prefixWord ++ tailWord_3764457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764457).length < 2 ^ (prefixWord ++ tailWord_3764457).sum := by decide
  have hdescent : baseEnd_3764457 < baseStart_3764457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764458 : List Nat := [3, 1, 3, 1, 1, 2, 5, 1, 2, 4]
def baseStart_3764458 : Nat := 118140960795 + 3764458 * 2 ^ 59
def prefixEnd_3764458 : Nat := 4983230072969 + 3 ^ 40 * 3764458 * 2
def baseEnd_3764458 : Nat := 644325452554379258154193

theorem tailTrace_3764458 : CollatzResearch.WordTrace tailWord_3764458 prefixEnd_3764458 644325452554379258154193 := by
  unfold tailWord_3764458
  simp only [CollatzResearch.WordTrace]
  refine ⟨34325265749004764771543507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91534041997346039390782685 34325265749004764771543507)
  ·
    refine ⟨51487898623507147157315261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34325265749004764771543507 51487898623507147157315261)
    ·
      refine ⟨19307961983815180183993223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51487898623507147157315261 19307961983815180183993223)
      ·
        refine ⟨28961942975722770275989835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19307961983815180183993223 28961942975722770275989835)
        ·
          refine ⟨43442914463584155413984753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28961942975722770275989835 43442914463584155413984753)
          ·
            refine ⟨32582185847688116560488565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43442914463584155413984753 32582185847688116560488565)
            ·
              refine ⟨3054579923220760927545803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32582185847688116560488565 3054579923220760927545803)
              ·
                refine ⟨4581869884831141391318705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3054579923220760927545803 4581869884831141391318705)
                ·
                  refine ⟨3436402413623356043489029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4581869884831141391318705 3436402413623356043489029)
                  ·
                    refine ⟨644325452554379258154193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3436402413623356043489029 644325452554379258154193)
                    ·
                      rfl

theorem cell23_3764458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_3764458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764458 prefixEnd_3764458 := by exact prefixLift 3764458
  have htrace : WordTrace (prefixWord ++ tailWord_3764458) baseStart_3764458 baseEnd_3764458 := by
    simpa [prefixWord, tailWord_3764458, baseEnd_3764458] using wordTrace_append hprefix tailTrace_3764458
  have hstable : (prefixWord ++ tailWord_3764458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764458).length < 2 ^ (prefixWord ++ tailWord_3764458).sum := by decide
  have hdescent : baseEnd_3764458 < baseStart_3764458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764461 : List Nat := [1, 5, 1, 2, 3, 1, 1, 1, 1, 1, 6]
def baseStart_3764461 : Nat := 118140960795 + 3764461 * 2 ^ 59
def prefixEnd_3764461 : Nat := 4983230072969 + 3 ^ 40 * 3764461 * 2
def baseEnd_3764461 : Nat := 1932977898105101262725065

theorem tailTrace_3764461 : CollatzResearch.WordTrace tailWord_3764461 prefixEnd_3764461 1932977898105101262725065 := by
  unfold tailWord_3764461
  simp only [CollatzResearch.WordTrace]
  refine ⟨137301172415008190598533237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91534114943338793732355491 137301172415008190598533237)
  ·
    refine ⟨12871984913907017868612491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137301172415008190598533237 12871984913907017868612491)
    ·
      refine ⟨19307977370860526802918737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12871984913907017868612491 19307977370860526802918737)
      ·
        refine ⟨14480983028145395102189053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19307977370860526802918737 14480983028145395102189053)
        ·
          refine ⟨5430368635554523163320895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14480983028145395102189053 5430368635554523163320895)
          ·
            refine ⟨8145552953331784744981343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5430368635554523163320895 8145552953331784744981343)
            ·
              refine ⟨12218329429997677117472015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8145552953331784744981343 12218329429997677117472015)
              ·
                refine ⟨18327494144996515676208023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12218329429997677117472015 18327494144996515676208023)
                ·
                  refine ⟨27491241217494773514312035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18327494144996515676208023 27491241217494773514312035)
                  ·
                    refine ⟨41236861826242160271468053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27491241217494773514312035 41236861826242160271468053)
                    ·
                      refine ⟨1932977898105101262725065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41236861826242160271468053 1932977898105101262725065)
                      ·
                        rfl

theorem cell23_3764461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_3764461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764461 prefixEnd_3764461 := by exact prefixLift 3764461
  have htrace : WordTrace (prefixWord ++ tailWord_3764461) baseStart_3764461 baseEnd_3764461 := by
    simpa [prefixWord, tailWord_3764461, baseEnd_3764461] using wordTrace_append hprefix tailTrace_3764461
  have hstable : (prefixWord ++ tailWord_3764461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764461).length < 2 ^ (prefixWord ++ tailWord_3764461).sum := by decide
  have hdescent : baseEnd_3764461 < baseStart_3764461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764481 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 6, 1, 3]
def baseStart_3764481 : Nat := 118140960795 + 3764481 * 2 ^ 59
def prefixEnd_3764481 : Nat := 4983230072969 + 3 ^ 40 * 3764481 * 2
def baseEnd_3764481 : Nat := 1932988167718191184474973

theorem tailTrace_3764481 : CollatzResearch.WordTrace tailWord_3764481 prefixEnd_3764481 1932988167718191184474973 := by
  unfold tailWord_3764481
  simp only [CollatzResearch.WordTrace]
  refine ⟨137301901874935734014261297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91534601249957156009507531 137301901874935734014261297)
  ·
    refine ⟨102976426406201800510695973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137301901874935734014261297 102976426406201800510695973)
    ·
      refine ⟨19308079951162837595755495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102976426406201800510695973 19308079951162837595755495)
      ·
        refine ⟨28962119926744256393633243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19308079951162837595755495 28962119926744256393633243)
        ·
          refine ⟨43443179890116384590449865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28962119926744256393633243 43443179890116384590449865)
          ·
            refine ⟨32582384917587288442837399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43443179890116384590449865 32582384917587288442837399)
            ·
              refine ⟨48873577376380932664256099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32582384917587288442837399 48873577376380932664256099)
              ·
                refine ⟨73310366064571398996384149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48873577376380932664256099 73310366064571398996384149)
                ·
                  refine ⟨3436423409276784327955507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73310366064571398996384149 3436423409276784327955507)
                  ·
                    refine ⟨5154635113915176491933261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3436423409276784327955507 5154635113915176491933261)
                    ·
                      refine ⟨1932988167718191184474973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5154635113915176491933261 1932988167718191184474973)
                      ·
                        rfl

theorem cell23_3764481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_3764481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764481 prefixEnd_3764481 := by exact prefixLift 3764481
  have htrace : WordTrace (prefixWord ++ tailWord_3764481) baseStart_3764481 baseEnd_3764481 := by
    simpa [prefixWord, tailWord_3764481, baseEnd_3764481] using wordTrace_append hprefix tailTrace_3764481
  have hstable : (prefixWord ++ tailWord_3764481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764481).length < 2 ^ (prefixWord ++ tailWord_3764481).sum := by decide
  have hdescent : baseEnd_3764481 < baseStart_3764481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764494 : List Nat := [4, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5]
def baseStart_3764494 : Nat := 118140960795 + 3764494 * 2 ^ 59
def prefixEnd_3764494 : Nat := 4983230072969 + 3 ^ 40 * 3764494 * 2
def baseEnd_3764494 : Nat := 1932994842966699633612413

theorem tailTrace_3764494 : CollatzResearch.WordTrace tailWord_3764494 prefixEnd_3764494 1932994842966699633612413 := by
  unfold tailWord_3764494
  simp only [CollatzResearch.WordTrace]
  refine ⟨17162797002986079654310567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91534917349259091489656357 17162797002986079654310567)
  ·
    refine ⟨25744195504479119481465851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17162797002986079654310567 25744195504479119481465851)
    ·
      refine ⟨38616293256718679222198777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25744195504479119481465851 38616293256718679222198777)
      ·
        refine ⟨28962219942539009416649083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38616293256718679222198777 28962219942539009416649083)
        ·
          refine ⟨43443329913808514124973625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28962219942539009416649083 43443329913808514124973625)
          ·
            refine ⟨32582497435356385593730219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43443329913808514124973625 32582497435356385593730219)
            ·
              refine ⟨48873746153034578390595329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32582497435356385593730219 48873746153034578390595329)
              ·
                refine ⟨36655309614775933792946497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48873746153034578390595329 36655309614775933792946497)
                ·
                  refine ⟨27491482211081950344709873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36655309614775933792946497 27491482211081950344709873)
                  ·
                    refine ⟨20618611658311462758532405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27491482211081950344709873 20618611658311462758532405)
                    ·
                      refine ⟨1932994842966699633612413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20618611658311462758532405 1932994842966699633612413)
                      ·
                        rfl

theorem cell23_3764494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_3764494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764494 prefixEnd_3764494 := by exact prefixLift 3764494
  have htrace : WordTrace (prefixWord ++ tailWord_3764494) baseStart_3764494 baseEnd_3764494 := by
    simpa [prefixWord, tailWord_3764494, baseEnd_3764494] using wordTrace_append hprefix tailTrace_3764494
  have hstable : (prefixWord ++ tailWord_3764494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764494).length < 2 ^ (prefixWord ++ tailWord_3764494).sum := by decide
  have hdescent : baseEnd_3764494 < baseStart_3764494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764504 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 2, 3, 4]
def baseStart_3764504 : Nat := 118140960795 + 3764504 * 2 ^ 59
def prefixEnd_3764504 : Nat := 4983230072969 + 3 ^ 40 * 3764504 * 2
def baseEnd_3764504 : Nat := 1932999977773244594487367

theorem tailTrace_3764504 : CollatzResearch.WordTrace tailWord_3764504 prefixEnd_3764504 1932999977773244594487367 := by
  unfold tailWord_3764504
  simp only [CollatzResearch.WordTrace]
  refine ⟨68651370376926204471174283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91535160502568272628232377 68651370376926204471174283)
  ·
    refine ⟨102977055565389306706761425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68651370376926204471174283 102977055565389306706761425)
    ·
      refine ⟨77232791674041980030071069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102977055565389306706761425 77232791674041980030071069)
      ·
        refine ⟨28962296877765742511276651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77232791674041980030071069 28962296877765742511276651)
        ·
          refine ⟨43443445316648613766914977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28962296877765742511276651 43443445316648613766914977)
          ·
            refine ⟨32582583987486460325186233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43443445316648613766914977 32582583987486460325186233)
            ·
              refine ⟨24436937990614845243889675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32582583987486460325186233 24436937990614845243889675)
              ·
                refine ⟨36655406985922267865834513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24436937990614845243889675 36655406985922267865834513)
                ·
                  refine ⟨27491555239441700899375885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36655406985922267865834513 27491555239441700899375885)
                  ·
                    refine ⟨10309333214790637837265957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27491555239441700899375885 10309333214790637837265957)
                    ·
                      refine ⟨1932999977773244594487367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10309333214790637837265957 1932999977773244594487367)
                      ·
                        rfl

theorem cell23_3764504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_3764504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764504 prefixEnd_3764504 := by exact prefixLift 3764504
  have htrace : WordTrace (prefixWord ++ tailWord_3764504) baseStart_3764504 baseEnd_3764504 := by
    simpa [prefixWord, tailWord_3764504, baseEnd_3764504] using wordTrace_append hprefix tailTrace_3764504
  have hstable : (prefixWord ++ tailWord_3764504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764504).length < 2 ^ (prefixWord ++ tailWord_3764504).sum := by decide
  have hdescent : baseEnd_3764504 < baseStart_3764504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764519 : List Nat := [1, 1, 8, 1, 1, 2, 1, 2, 1, 2, 3]
def baseStart_3764519 : Nat := 118140960795 + 3764519 * 2 ^ 59
def prefixEnd_3764519 : Nat := 4983230072969 + 3 ^ 40 * 3764519 * 2
def baseEnd_3764519 : Nat := 1933007679983062035799799

theorem tailTrace_3764519 : CollatzResearch.WordTrace tailWord_3764519 prefixEnd_3764519 1933007679983062035799799 := by
  unfold tailWord_3764519
  simp only [CollatzResearch.WordTrace]
  refine ⟨137303287848798066504144611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91535525232532044336096407 137303287848798066504144611)
  ·
    refine ⟨205954931773197099756216917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137303287848798066504144611 205954931773197099756216917)
    ·
      refine ⟨2413534356717153512768167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 205954931773197099756216917 2413534356717153512768167)
      ·
        refine ⟨3620301535075730269152251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2413534356717153512768167 3620301535075730269152251)
        ·
          refine ⟨5430452302613595403728377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3620301535075730269152251 5430452302613595403728377)
          ·
            refine ⟨4072839226960196552796283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5430452302613595403728377 4072839226960196552796283)
            ·
              refine ⟨6109258840440294829194425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4072839226960196552796283 6109258840440294829194425)
              ·
                refine ⟨4581944130330221121895819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6109258840440294829194425 4581944130330221121895819)
                ·
                  refine ⟨6872916195495331682843729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4581944130330221121895819 6872916195495331682843729)
                  ·
                    refine ⟨5154687146621498762132797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6872916195495331682843729 5154687146621498762132797)
                    ·
                      refine ⟨1933007679983062035799799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5154687146621498762132797 1933007679983062035799799)
                      ·
                        rfl

theorem cell23_3764519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_3764519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764519 prefixEnd_3764519 := by exact prefixLift 3764519
  have htrace : WordTrace (prefixWord ++ tailWord_3764519) baseStart_3764519 baseEnd_3764519 := by
    simpa [prefixWord, tailWord_3764519, baseEnd_3764519] using wordTrace_append hprefix tailTrace_3764519
  have hstable : (prefixWord ++ tailWord_3764519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764519).length < 2 ^ (prefixWord ++ tailWord_3764519).sum := by decide
  have hdescent : baseEnd_3764519 < baseStart_3764519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764524 : List Nat := [2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 5]
def baseStart_3764524 : Nat := 118140960795 + 3764524 * 2 ^ 59
def prefixEnd_3764524 : Nat := 4983230072969 + 3 ^ 40 * 3764524 * 2
def baseEnd_3764524 : Nat := 1933010247386334516237275

theorem tailTrace_3764524 : CollatzResearch.WordTrace tailWord_3764524 prefixEnd_3764524 1933010247386334516237275 := by
  unfold tailWord_3764524
  simp only [CollatzResearch.WordTrace]
  refine ⟨68651735106889976179038313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91535646809186634905384417 68651735106889976179038313)
  ·
    refine ⟨51488801330167482134278735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68651735106889976179038313 51488801330167482134278735)
    ·
      refine ⟨77233201995251223201418103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51488801330167482134278735 77233201995251223201418103)
      ·
        refine ⟨115849802992876834802127155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77233201995251223201418103 115849802992876834802127155)
        ·
          refine ⟨173774704489315252203190733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115849802992876834802127155 173774704489315252203190733)
          ·
            refine ⟨65165514183493219576196525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173774704489315252203190733 65165514183493219576196525)
            ·
              refine ⟨24437067818809957341073697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65165514183493219576196525 24437067818809957341073697)
              ·
                refine ⟨18327800864107468005805273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24437067818809957341073697 18327800864107468005805273)
                ·
                  refine ⟨13745850648080601004353955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18327800864107468005805273 13745850648080601004353955)
                  ·
                    refine ⟨20618775972120901506530933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13745850648080601004353955 20618775972120901506530933)
                    ·
                      refine ⟨1933010247386334516237275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20618775972120901506530933 1933010247386334516237275)
                      ·
                        rfl

theorem cell23_3764524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_3764524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764524 prefixEnd_3764524 := by exact prefixLift 3764524
  have htrace : WordTrace (prefixWord ++ tailWord_3764524) baseStart_3764524 baseEnd_3764524 := by
    simpa [prefixWord, tailWord_3764524, baseEnd_3764524] using wordTrace_append hprefix tailTrace_3764524
  have hstable : (prefixWord ++ tailWord_3764524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764524).length < 2 ^ (prefixWord ++ tailWord_3764524).sum := by decide
  have hdescent : baseEnd_3764524 < baseStart_3764524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764538 : List Nat := [3, 1, 1, 1, 4, 3, 1, 2, 1, 4, 2]
def baseStart_3764538 : Nat := 118140960795 + 3764538 * 2 ^ 59
def prefixEnd_3764538 : Nat := 4983230072969 + 3 ^ 40 * 3764538 * 2
def baseEnd_3764538 : Nat := 1933017436115497461462211

theorem tailTrace_3764538 : CollatzResearch.WordTrace tailWord_3764538 prefixEnd_3764538 1933017436115497461462211 := by
  unfold tailWord_3764538
  simp only [CollatzResearch.WordTrace]
  refine ⟨34325995208932308187271567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91535987223819488499390845 34325995208932308187271567)
  ·
    refine ⟨51488992813398462280907351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34325995208932308187271567 51488992813398462280907351)
    ·
      refine ⟨77233489220097693421361027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51488992813398462280907351 77233489220097693421361027)
      ·
        refine ⟨115850233830146540132041541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77233489220097693421361027 115850233830146540132041541)
        ·
          refine ⟨21721918843152476274757789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115850233830146540132041541 21721918843152476274757789)
          ·
            refine ⟨8145719566182178603034171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21721918843152476274757789 8145719566182178603034171)
            ·
              refine ⟨12218579349273267904551257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8145719566182178603034171 12218579349273267904551257)
              ·
                refine ⟨9163934511954950928413443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12218579349273267904551257 9163934511954950928413443)
                ·
                  refine ⟨13745901767932426392620165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9163934511954950928413443 13745901767932426392620165)
                  ·
                    refine ⟨2577356581487329948616281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13745901767932426392620165 2577356581487329948616281)
                    ·
                      refine ⟨1933017436115497461462211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2577356581487329948616281 1933017436115497461462211)
                      ·
                        rfl

theorem cell23_3764538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 1, 4, 2].length) (baseStart_3764538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764538 prefixEnd_3764538 := by exact prefixLift 3764538
  have htrace : WordTrace (prefixWord ++ tailWord_3764538) baseStart_3764538 baseEnd_3764538 := by
    simpa [prefixWord, tailWord_3764538, baseEnd_3764538] using wordTrace_append hprefix tailTrace_3764538
  have hstable : (prefixWord ++ tailWord_3764538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764538).length < 2 ^ (prefixWord ++ tailWord_3764538).sum := by decide
  have hdescent : baseEnd_3764538 < baseStart_3764538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764542 : List Nat := [4, 2, 1, 2, 1, 3, 3, 1, 1, 3, 2]
def baseStart_3764542 : Nat := 118140960795 + 3764542 * 2 ^ 59
def prefixEnd_3764542 : Nat := 4983230072969 + 3 ^ 40 * 3764542 * 2
def baseEnd_3764542 : Nat := 1933019490038115445812193

theorem tailTrace_3764542 : CollatzResearch.WordTrace tailWord_3764542 prefixEnd_3764542 1933019490038115445812193 := by
  unfold tailWord_3764542
  simp only [CollatzResearch.WordTrace]
  refine ⟨17163015840964342679028985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91536084485143160954821253 17163015840964342679028985)
  ·
    refine ⟨12872261880723257009271739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17163015840964342679028985 12872261880723257009271739)
    ·
      refine ⟨19308392821084885513907609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12872261880723257009271739 19308392821084885513907609)
      ·
        refine ⟨14481294615813664135430707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19308392821084885513907609 14481294615813664135430707)
        ·
          refine ⟨21721941923720496203146061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14481294615813664135430707 21721941923720496203146061)
          ·
            refine ⟨8145728221395186076179773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21721941923720496203146061 8145728221395186076179773)
            ·
              refine ⟨3054648083023194778567415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8145728221395186076179773 3054648083023194778567415)
              ·
                refine ⟨4581972124534792167851123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3054648083023194778567415 4581972124534792167851123)
                ·
                  refine ⟨6872958186802188251776685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4581972124534792167851123 6872958186802188251776685)
                  ·
                    refine ⟨2577359320050820594416257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6872958186802188251776685 2577359320050820594416257)
                    ·
                      refine ⟨1933019490038115445812193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2577359320050820594416257 1933019490038115445812193)
                      ·
                        rfl

theorem cell23_3764542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_3764542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764542 prefixEnd_3764542 := by exact prefixLift 3764542
  have htrace : WordTrace (prefixWord ++ tailWord_3764542) baseStart_3764542 baseEnd_3764542 := by
    simpa [prefixWord, tailWord_3764542, baseEnd_3764542] using wordTrace_append hprefix tailTrace_3764542
  have hstable : (prefixWord ++ tailWord_3764542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764542).length < 2 ^ (prefixWord ++ tailWord_3764542).sum := by decide
  have hdescent : baseEnd_3764542 < baseStart_3764542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764572 : List Nat := [2, 2, 4, 3, 1, 1, 2, 1, 1, 4, 2]
def baseStart_3764572 : Nat := 118140960795 + 3764572 * 2 ^ 59
def prefixEnd_3764572 : Nat := 4983230072969 + 3 ^ 40 * 3764572 * 2
def baseEnd_3764572 : Nat := 1933034894457750328437055

theorem tailTrace_3764572 : CollatzResearch.WordTrace tailWord_3764572 prefixEnd_3764572 1933034894457750328437055 := by
  unfold tailWord_3764572
  simp only [CollatzResearch.WordTrace]
  refine ⟨68652610458803028277911985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91536813945070704370549313 68652610458803028277911985)
  ·
    refine ⟨51489457844102271208433989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68652610458803028277911985 51489457844102271208433989)
    ·
      refine ⟨9654273345769175851581373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51489457844102271208433989 9654273345769175851581373)
      ·
        refine ⟨3620352504663440944343015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9654273345769175851581373 3620352504663440944343015)
        ·
          refine ⟨5430528756995161416514523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3620352504663440944343015 5430528756995161416514523)
          ·
            refine ⟨8145793135492742124771785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5430528756995161416514523 8145793135492742124771785)
            ·
              refine ⟨6109344851619556593578839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8145793135492742124771785 6109344851619556593578839)
              ·
                refine ⟨9164017277429334890368259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6109344851619556593578839 9164017277429334890368259)
                ·
                  refine ⟨13746025916144002335552389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9164017277429334890368259 13746025916144002335552389)
                  ·
                    refine ⟨2577379859277000437916073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13746025916144002335552389 2577379859277000437916073)
                    ·
                      refine ⟨1933034894457750328437055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2577379859277000437916073 1933034894457750328437055)
                      ·
                        rfl

theorem cell23_3764572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_3764572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764572 prefixEnd_3764572 := by exact prefixLift 3764572
  have htrace : WordTrace (prefixWord ++ tailWord_3764572) baseStart_3764572 baseEnd_3764572 := by
    simpa [prefixWord, tailWord_3764572, baseEnd_3764572] using wordTrace_append hprefix tailTrace_3764572
  have hstable : (prefixWord ++ tailWord_3764572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764572).length < 2 ^ (prefixWord ++ tailWord_3764572).sum := by decide
  have hdescent : baseEnd_3764572 < baseStart_3764572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764631 : List Nat := [1, 1, 3, 3, 1, 1, 3, 2, 1, 4, 3]
def baseStart_3764631 : Nat := 118140960795 + 3764631 * 2 ^ 59
def prefixEnd_3764631 : Nat := 4983230072969 + 3 ^ 40 * 3764631 * 2
def baseEnd_3764631 : Nat := 1933065189816365597599283

theorem tailTrace_3764631 : CollatzResearch.WordTrace tailWord_3764631 prefixEnd_3764631 1933065189816365597599283 := by
  unfold tailWord_3764631
  simp only [CollatzResearch.WordTrace]
  refine ⟨137307372824392309632221747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91538248549594873088147831 137307372824392309632221747)
  ·
    refine ⟨205961059236588464448332621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137307372824392309632221747 205961059236588464448332621)
    ·
      refine ⟨77235397213720674168124733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205961059236588464448332621 77235397213720674168124733)
      ·
        refine ⟨28963273955145252813046775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77235397213720674168124733 28963273955145252813046775)
        ·
          refine ⟨43444910932717879219570163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28963273955145252813046775 43444910932717879219570163)
          ·
            refine ⟨65167366399076818829355245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43444910932717879219570163 65167366399076818829355245)
            ·
              refine ⟨24437762399653807061008217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65167366399076818829355245 24437762399653807061008217)
              ·
                refine ⟨18328321799740355295756163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24437762399653807061008217 18328321799740355295756163)
                ·
                  refine ⟨27492482699610532943634245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18328321799740355295756163 27492482699610532943634245)
                  ·
                    refine ⟨5154840506176974926931421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27492482699610532943634245 5154840506176974926931421)
                    ·
                      refine ⟨1933065189816365597599283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5154840506176974926931421 1933065189816365597599283)
                      ·
                        rfl

theorem cell23_3764631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_3764631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764631 prefixEnd_3764631 := by exact prefixLift 3764631
  have htrace : WordTrace (prefixWord ++ tailWord_3764631) baseStart_3764631 baseEnd_3764631 := by
    simpa [prefixWord, tailWord_3764631, baseEnd_3764631] using wordTrace_append hprefix tailTrace_3764631
  have hstable : (prefixWord ++ tailWord_3764631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764631).length < 2 ^ (prefixWord ++ tailWord_3764631).sum := by decide
  have hdescent : baseEnd_3764631 < baseStart_3764631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764705 : List Nat := [1, 2, 3, 1, 2, 2, 4, 1, 2, 3, 2]
def baseStart_3764705 : Nat := 118140960795 + 3764705 * 2 ^ 59
def prefixEnd_3764705 : Nat := 4983230072969 + 3 ^ 40 * 3764705 * 2
def baseEnd_3764705 : Nat := 1933103187384798308073943

theorem tailTrace_3764705 : CollatzResearch.WordTrace tailWord_3764705 prefixEnd_3764705 1933103187384798308073943 := by
  unfold tailWord_3764705
  simp only [CollatzResearch.WordTrace]
  refine ⟨137310071826124220270415569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91540047884082813513610379 137310071826124220270415569)
  ·
    refine ⟨102982553869593165202811677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137310071826124220270415569 102982553869593165202811677)
    ·
      refine ⟨38618457701097436951054379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102982553869593165202811677 38618457701097436951054379)
      ·
        refine ⟨57927686551646155426581569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38618457701097436951054379 57927686551646155426581569)
        ·
          refine ⟨43445764913734616569936177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57927686551646155426581569 43445764913734616569936177)
          ·
            refine ⟨32584323685300962427452133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43445764913734616569936177 32584323685300962427452133)
            ·
              refine ⟨6109560690993930455147275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32584323685300962427452133 6109560690993930455147275)
              ·
                refine ⟨9164341036490895682720913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6109560690993930455147275 9164341036490895682720913)
                ·
                  refine ⟨6873255777368171762040685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9164341036490895682720913 6873255777368171762040685)
                  ·
                    refine ⟨2577470916513064410765257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6873255777368171762040685 2577470916513064410765257)
                    ·
                      refine ⟨1933103187384798308073943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2577470916513064410765257 1933103187384798308073943)
                      ·
                        rfl

theorem cell23_3764705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 3, 2].length) (baseStart_3764705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764705 prefixEnd_3764705 := by exact prefixLift 3764705
  have htrace : WordTrace (prefixWord ++ tailWord_3764705) baseStart_3764705 baseEnd_3764705 := by
    simpa [prefixWord, tailWord_3764705, baseEnd_3764705] using wordTrace_append hprefix tailTrace_3764705
  have hstable : (prefixWord ++ tailWord_3764705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764705).length < 2 ^ (prefixWord ++ tailWord_3764705).sum := by decide
  have hdescent : baseEnd_3764705 < baseStart_3764705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764735 : List Nat := [1, 1, 2, 2, 1, 2, 4, 3, 3, 2, 2]
def baseStart_3764735 : Nat := 118140960795 + 3764735 * 2 ^ 59
def prefixEnd_3764735 : Nat := 4983230072969 + 3 ^ 40 * 3764735 * 2
def baseEnd_3764735 : Nat := 1933118591804433190698805

theorem tailTrace_3764735 : CollatzResearch.WordTrace tailWord_3764735 prefixEnd_3764735 1933118591804433190698805 := by
  unfold tailWord_3764735
  simp only [CollatzResearch.WordTrace]
  refine ⟨137311166016015535394007659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91540777344010356929338439 137311166016015535394007659)
  ·
    refine ⟨205966749024023303091011489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137311166016015535394007659 205966749024023303091011489)
    ·
      refine ⟨154475061768017477318258617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205966749024023303091011489 154475061768017477318258617)
      ·
        refine ⟨115856296326013107988693963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154475061768017477318258617 115856296326013107988693963)
        ·
          refine ⟨173784444489019661983040945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115856296326013107988693963 173784444489019661983040945)
          ·
            refine ⟨130338333366764746487280709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173784444489019661983040945 130338333366764746487280709)
            ·
              refine ⟨24438437506268389966365133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130338333366764746487280709 24438437506268389966365133)
              ·
                refine ⟨9164414064850646237386925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24438437506268389966365133 9164414064850646237386925)
                ·
                  refine ⟨3436655274318992339020097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9164414064850646237386925 3436655274318992339020097)
                  ·
                    refine ⟨2577491455739244254265073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3436655274318992339020097 2577491455739244254265073)
                    ·
                      refine ⟨1933118591804433190698805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2577491455739244254265073 1933118591804433190698805)
                      ·
                        rfl

theorem cell23_3764735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 3, 3, 2, 2].length) (baseStart_3764735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764735 prefixEnd_3764735 := by exact prefixLift 3764735
  have htrace : WordTrace (prefixWord ++ tailWord_3764735) baseStart_3764735 baseEnd_3764735 := by
    simpa [prefixWord, tailWord_3764735, baseEnd_3764735] using wordTrace_append hprefix tailTrace_3764735
  have hstable : (prefixWord ++ tailWord_3764735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764735).length < 2 ^ (prefixWord ++ tailWord_3764735).sum := by decide
  have hdescent : baseEnd_3764735 < baseStart_3764735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764741 : List Nat := [1, 3, 1, 1, 2, 2, 5, 8]
def baseStart_3764741 : Nat := 118140960795 + 3764741 * 2 ^ 59
def prefixEnd_3764741 : Nat := 4983230072969 + 3 ^ 40 * 3764741 * 2
def baseEnd_3764741 : Nat := 71597098988457783971251

theorem tailTrace_3764741 : CollatzResearch.WordTrace tailWord_3764741 prefixEnd_3764741 71597098988457783971251 := by
  unfold tailWord_3764741
  simp only [CollatzResearch.WordTrace]
  refine ⟨137311384853993798418726077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91540923235995865612484051 137311384853993798418726077)
  ·
    refine ⟨51491769320247674407022279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137311384853993798418726077 51491769320247674407022279)
    ·
      refine ⟨77237653980371511610533419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51491769320247674407022279 77237653980371511610533419)
      ·
        refine ⟨115856480970557267415800129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77237653980371511610533419 115856480970557267415800129)
        ·
          refine ⟨86892360727917950561850097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115856480970557267415800129 86892360727917950561850097)
          ·
            refine ⟨65169270545938462921387573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86892360727917950561850097 65169270545938462921387573)
            ·
              refine ⟨6109619113681730898880085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65169270545938462921387573 6109619113681730898880085)
              ·
                refine ⟨71597098988457783971251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6109619113681730898880085 71597098988457783971251)
                ·
                  rfl

theorem cell23_3764741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 8].length) (baseStart_3764741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764741 prefixEnd_3764741 := by exact prefixLift 3764741
  have htrace : WordTrace (prefixWord ++ tailWord_3764741) baseStart_3764741 baseEnd_3764741 := by
    simpa [prefixWord, tailWord_3764741, baseEnd_3764741] using wordTrace_append hprefix tailTrace_3764741
  have hstable : (prefixWord ++ tailWord_3764741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764741).length < 2 ^ (prefixWord ++ tailWord_3764741).sum := by decide
  have hdescent : baseEnd_3764741 < baseStart_3764741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764748 : List Nat := [2, 2, 1, 2, 4, 1, 1, 3, 1, 2, 4]
def baseStart_3764748 : Nat := 118140960795 + 3764748 * 2 ^ 59
def prefixEnd_3764748 : Nat := 4983230072969 + 3 ^ 40 * 3764748 * 2
def baseEnd_3764748 : Nat := 1933125267052941639836245

theorem tailTrace_3764748 : CollatzResearch.WordTrace tailWord_3764748 prefixEnd_3764748 1933125267052941639836245 := by
  unfold tailWord_3764748
  simp only [CollatzResearch.WordTrace]
  refine ⟨68655820082484219307115449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91541093443312292409487265 68655820082484219307115449)
  ·
    refine ⟨51491865061863164480336587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68655820082484219307115449 51491865061863164480336587)
    ·
      refine ⟨77237797592794746720504881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51491865061863164480336587 77237797592794746720504881)
      ·
        refine ⟨57928348194596060040378661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77237797592794746720504881 57928348194596060040378661)
        ·
          refine ⟨10861565286486761257570999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57928348194596060040378661 10861565286486761257570999)
          ·
            refine ⟨16292347929730141886356499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10861565286486761257570999 16292347929730141886356499)
            ·
              refine ⟨24438521894595212829534749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16292347929730141886356499 24438521894595212829534749)
              ·
                refine ⟨9164445710473204811075531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24438521894595212829534749 9164445710473204811075531)
                ·
                  refine ⟨13746668565709807216613297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9164445710473204811075531 13746668565709807216613297)
                  ·
                    refine ⟨10310001424282355412459973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13746668565709807216613297 10310001424282355412459973)
                    ·
                      refine ⟨1933125267052941639836245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10310001424282355412459973 1933125267052941639836245)
                      ·
                        rfl

theorem cell23_3764748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_3764748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764748 prefixEnd_3764748 := by exact prefixLift 3764748
  have htrace : WordTrace (prefixWord ++ tailWord_3764748) baseStart_3764748 baseEnd_3764748 := by
    simpa [prefixWord, tailWord_3764748, baseEnd_3764748] using wordTrace_append hprefix tailTrace_3764748
  have hstable : (prefixWord ++ tailWord_3764748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764748).length < 2 ^ (prefixWord ++ tailWord_3764748).sum := by decide
  have hdescent : baseEnd_3764748 < baseStart_3764748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764769 : List Nat := [1, 2, 3, 2, 2, 1, 4, 3, 1, 2, 2]
def baseStart_3764769 : Nat := 118140960795 + 3764769 * 2 ^ 59
def prefixEnd_3764769 : Nat := 4983230072969 + 3 ^ 40 * 3764769 * 2
def baseEnd_3764769 : Nat := 1933136050146686057673649

theorem tailTrace_3764769 : CollatzResearch.WordTrace tailWord_3764769 prefixEnd_3764769 1933136050146686057673649 := by
  unfold tailWord_3764769
  simp only [CollatzResearch.WordTrace]
  refine ⟨137312406097892359200745361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91541604065261572800496907 137312406097892359200745361)
  ·
    refine ⟨102984304573419269400559021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137312406097892359200745361 102984304573419269400559021)
    ·
      refine ⟨38619114215032226025209633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102984304573419269400559021 38619114215032226025209633)
      ·
        refine ⟨28964335661274169518907225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38619114215032226025209633 28964335661274169518907225)
        ·
          refine ⟨21723251745955627139180419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28964335661274169518907225 21723251745955627139180419)
          ·
            refine ⟨32584877618933440708770629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21723251745955627139180419 32584877618933440708770629)
            ·
              refine ⟨6109664553550020132894493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32584877618933440708770629 6109664553550020132894493)
              ·
                refine ⟨2291124207581257549835435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6109664553550020132894493 2291124207581257549835435)
                ·
                  refine ⟨3436686311371886324753153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2291124207581257549835435 3436686311371886324753153)
                  ·
                    refine ⟨2577514733528914743564865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3436686311371886324753153 2577514733528914743564865)
                    ·
                      refine ⟨1933136050146686057673649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2577514733528914743564865 1933136050146686057673649)
                      ·
                        rfl

theorem cell23_3764769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_3764769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764769 prefixEnd_3764769 := by exact prefixLift 3764769
  have htrace : WordTrace (prefixWord ++ tailWord_3764769) baseStart_3764769 baseEnd_3764769 := by
    simpa [prefixWord, tailWord_3764769, baseEnd_3764769] using wordTrace_append hprefix tailTrace_3764769
  have hstable : (prefixWord ++ tailWord_3764769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764769).length < 2 ^ (prefixWord ++ tailWord_3764769).sum := by decide
  have hdescent : baseEnd_3764769 < baseStart_3764769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764775 : List Nat := [1, 1, 7, 2, 1, 1, 10]
def baseStart_3764775 : Nat := 118140960795 + 3764775 * 2 ^ 59
def prefixEnd_3764775 : Nat := 4983230072969 + 3 ^ 40 * 3764775 * 2
def baseEnd_3764775 : Nat := 23865915197908802891341

theorem tailTrace_3764775 : CollatzResearch.WordTrace tailWord_3764775 prefixEnd_3764775 23865915197908802891341 := by
  unfold tailWord_3764775
  simp only [CollatzResearch.WordTrace]
  refine ⟨137312624935870622225463779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91541749957247081483642519 137312624935870622225463779)
  ·
    refine ⟨205968937403805933338195669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137312624935870622225463779 205968937403805933338195669)
    ·
      refine ⟨4827396970401701562613961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 205968937403805933338195669 4827396970401701562613961)
      ·
        refine ⟨3620547727801276171960471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4827396970401701562613961 3620547727801276171960471)
        ·
          refine ⟨5430821591701914257940707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3620547727801276171960471 5430821591701914257940707)
          ·
            refine ⟨8146232387552871386911061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5430821591701914257940707 8146232387552871386911061)
            ·
              refine ⟨23865915197908802891341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8146232387552871386911061 23865915197908802891341)
              ·
                rfl

theorem cell23_3764775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 10].length) (baseStart_3764775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764775 prefixEnd_3764775 := by exact prefixLift 3764775
  have htrace : WordTrace (prefixWord ++ tailWord_3764775) baseStart_3764775 baseEnd_3764775 := by
    simpa [prefixWord, tailWord_3764775, baseEnd_3764775] using wordTrace_append hprefix tailTrace_3764775
  have hstable : (prefixWord ++ tailWord_3764775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764775).length < 2 ^ (prefixWord ++ tailWord_3764775).sum := by decide
  have hdescent : baseEnd_3764775 < baseStart_3764775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764812 : List Nat := [2, 2, 1, 3, 1, 2, 4, 2, 1, 3, 2]
def baseStart_3764812 : Nat := 118140960795 + 3764812 * 2 ^ 59
def prefixEnd_3764812 : Nat := 4983230072969 + 3 ^ 40 * 3764812 * 2
def baseEnd_3764812 : Nat := 1933158129814829389435951

theorem tailTrace_3764812 : CollatzResearch.WordTrace tailWord_3764812 prefixEnd_3764812 1933158129814829389435951 := by
  unfold tailWord_3764812
  simp only [CollatzResearch.WordTrace]
  refine ⟨68656987218368288772280345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91542649624491051696373793 68656987218368288772280345)
  ·
    refine ⟨51492740413776216579210259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68656987218368288772280345 51492740413776216579210259)
    ·
      refine ⟨77239110620664324868815389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51492740413776216579210259 77239110620664324868815389)
      ·
        refine ⟨28964666482749121825805771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77239110620664324868815389 28964666482749121825805771)
        ·
          refine ⟨43446999724123682738708657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28964666482749121825805771 43446999724123682738708657)
          ·
            refine ⟨32585249793092762054031493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43446999724123682738708657 32585249793092762054031493)
            ·
              refine ⟨6109734336204892885130905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32585249793092762054031493 6109734336204892885130905)
              ·
                refine ⟨4582300752153669663848179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6109734336204892885130905 4582300752153669663848179)
                ·
                  refine ⟨6873451128230504495772269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4582300752153669663848179 6873451128230504495772269)
                  ·
                    refine ⟨2577544173086439185914601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6873451128230504495772269 2577544173086439185914601)
                    ·
                      refine ⟨1933158129814829389435951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2577544173086439185914601 1933158129814829389435951)
                      ·
                        rfl

theorem cell23_3764812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_3764812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764812 prefixEnd_3764812 := by exact prefixLift 3764812
  have htrace : WordTrace (prefixWord ++ tailWord_3764812) baseStart_3764812 baseEnd_3764812 := by
    simpa [prefixWord, tailWord_3764812, baseEnd_3764812] using wordTrace_append hprefix tailTrace_3764812
  have hstable : (prefixWord ++ tailWord_3764812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764812).length < 2 ^ (prefixWord ++ tailWord_3764812).sum := by decide
  have hdescent : baseEnd_3764812 < baseStart_3764812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764831 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 9]
def baseStart_3764831 : Nat := 118140960795 + 3764831 * 2 ^ 59
def prefixEnd_3764831 : Nat := 4983230072969 + 3 ^ 40 * 3764831 * 2
def baseEnd_3764831 : Nat := 214796431771918312788707

theorem tailTrace_3764831 : CollatzResearch.WordTrace tailWord_3764831 prefixEnd_3764831 214796431771918312788707 := by
  unfold tailWord_3764831
  simp only [CollatzResearch.WordTrace]
  refine ⟨137314667423667743789502347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91543111615778495859668231 137314667423667743789502347)
  ·
    refine ⟨205972001135501615684253521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137314667423667743789502347 205972001135501615684253521)
    ·
      refine ⟨154479000851626211763190141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205972001135501615684253521 154479000851626211763190141)
      ·
        refine ⟨57929625319359829411196303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154479000851626211763190141 57929625319359829411196303)
        ·
          refine ⟨86894437979039744116794455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57929625319359829411196303 86894437979039744116794455)
          ·
            refine ⟨130341656968559616175191683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86894437979039744116794455 130341656968559616175191683)
            ·
              refine ⟨195512485452839424262787525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130341656968559616175191683 195512485452839424262787525)
              ·
                refine ⟨36658591022407392049272661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195512485452839424262787525 36658591022407392049272661)
                ·
                  refine ⟨214796431771918312788707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 36658591022407392049272661 214796431771918312788707)
                  ·
                    rfl

theorem cell23_3764831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 9].length) (baseStart_3764831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764831 prefixEnd_3764831 := by exact prefixLift 3764831
  have htrace : WordTrace (prefixWord ++ tailWord_3764831) baseStart_3764831 baseEnd_3764831 := by
    simpa [prefixWord, tailWord_3764831, baseEnd_3764831] using wordTrace_append hprefix tailTrace_3764831
  have hstable : (prefixWord ++ tailWord_3764831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764831).length < 2 ^ (prefixWord ++ tailWord_3764831).sum := by decide
  have hdescent : baseEnd_3764831 < baseStart_3764831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764841 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 9]
def baseStart_3764841 : Nat := 118140960795 + 3764841 * 2 ^ 59
def prefixEnd_3764841 : Nat := 4983230072969 + 3 ^ 40 * 3764841 * 2
def baseEnd_3764841 : Nat := 1933173020753809775973317

theorem tailTrace_3764841 : CollatzResearch.WordTrace tailWord_3764841 prefixEnd_3764841 1933173020753809775973317 := by
  unfold tailWord_3764841
  simp only [CollatzResearch.WordTrace]
  refine ⟨137315032153631515497366377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91543354769087676998244251 137315032153631515497366377)
  ·
    refine ⟨102986274115223636623024783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137315032153631515497366377 102986274115223636623024783)
    ·
      refine ⟨154479411172835454934537175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102986274115223636623024783 154479411172835454934537175)
      ·
        refine ⟨231719116759253182401805763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154479411172835454934537175 231719116759253182401805763)
        ·
          refine ⟨347578675138879773602708645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231719116759253182401805763 347578675138879773602708645)
          ·
            refine ⟨65171001588539957550507871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 347578675138879773602708645 65171001588539957550507871)
            ·
              refine ⟨97756502382809936325761807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65171001588539957550507871 97756502382809936325761807)
              ·
                refine ⟨146634753574214904488642711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97756502382809936325761807 146634753574214904488642711)
                ·
                  refine ⟨219952130361322356732964067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146634753574214904488642711 219952130361322356732964067)
                  ·
                    refine ⟨329928195541983535099446101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 219952130361322356732964067 329928195541983535099446101)
                    ·
                      refine ⟨1933173020753809775973317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 329928195541983535099446101 1933173020753809775973317)
                      ·
                        rfl

theorem cell23_3764841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 9].length) (baseStart_3764841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764841 prefixEnd_3764841 := by exact prefixLift 3764841
  have htrace : WordTrace (prefixWord ++ tailWord_3764841) baseStart_3764841 baseEnd_3764841 := by
    simpa [prefixWord, tailWord_3764841, baseEnd_3764841] using wordTrace_append hprefix tailTrace_3764841
  have hstable : (prefixWord ++ tailWord_3764841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764841).length < 2 ^ (prefixWord ++ tailWord_3764841).sum := by decide
  have hdescent : baseEnd_3764841 < baseStart_3764841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764842 : List Nat := [3, 1, 3, 2, 1, 1, 1, 3, 4, 2, 2]
def baseStart_3764842 : Nat := 118140960795 + 3764842 * 2 ^ 59
def prefixEnd_3764842 : Nat := 4983230072969 + 3 ^ 40 * 3764842 * 2
def baseEnd_3764842 : Nat := 1933173534234464272060813

theorem tailTrace_3764842 : CollatzResearch.WordTrace tailWord_3764842 prefixEnd_3764842 1933173534234464272060813 := by
  unfold tailWord_3764842
  simp only [CollatzResearch.WordTrace]
  refine ⟨34328767156656973167038195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91543379084418595112101853 34328767156656973167038195)
  ·
    refine ⟨51493150734985459750557293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34328767156656973167038195 51493150734985459750557293)
    ·
      refine ⟨19309931525619547406458985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51493150734985459750557293 19309931525619547406458985)
      ·
        refine ⟨14482448644214660554844239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19309931525619547406458985 14482448644214660554844239)
        ·
          refine ⟨21723672966321990832266359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14482448644214660554844239 21723672966321990832266359)
          ·
            refine ⟨32585509449482986248399539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21723672966321990832266359 32585509449482986248399539)
            ·
              refine ⟨48878264174224479372599309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32585509449482986248399539 48878264174224479372599309)
              ·
                refine ⟨18329349065334179764724741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48878264174224479372599309 18329349065334179764724741)
                ·
                  refine ⟨3436752949750158705885889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18329349065334179764724741 3436752949750158705885889)
                  ·
                    refine ⟨2577564712312619029414417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3436752949750158705885889 2577564712312619029414417)
                    ·
                      refine ⟨1933173534234464272060813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2577564712312619029414417 1933173534234464272060813)
                      ·
                        rfl

theorem cell23_3764842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_3764842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764842 prefixEnd_3764842 := by exact prefixLift 3764842
  have htrace : WordTrace (prefixWord ++ tailWord_3764842) baseStart_3764842 baseEnd_3764842 := by
    simpa [prefixWord, tailWord_3764842, baseEnd_3764842] using wordTrace_append hprefix tailTrace_3764842
  have hstable : (prefixWord ++ tailWord_3764842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764842).length < 2 ^ (prefixWord ++ tailWord_3764842).sum := by decide
  have hdescent : baseEnd_3764842 < baseStart_3764842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764851 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 8]
def baseStart_3764851 : Nat := 118140960795 + 3764851 * 2 ^ 59
def prefixEnd_3764851 : Nat := 4983230072969 + 3 ^ 40 * 3764851 * 2
def baseEnd_3764851 : Nat := 1933178155560354736848271

theorem tailTrace_3764851 : CollatzResearch.WordTrace tailWord_3764851 prefixEnd_3764851 1933178155560354736848271 := by
  unfold tailWord_3764851
  simp only [CollatzResearch.WordTrace]
  refine ⟨137315396883595287205230407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91543597922396858136820271 137315396883595287205230407)
  ·
    refine ⟨205973095325392930807845611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137315396883595287205230407 205973095325392930807845611)
    ·
      refine ⟨308959642988089396211768417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205973095325392930807845611 308959642988089396211768417)
      ·
        refine ⟨231719732241067047158826313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308959642988089396211768417 231719732241067047158826313)
        ·
          refine ⟨173789799180800285369119735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231719732241067047158826313 173789799180800285369119735)
          ·
            refine ⟨260684698771200428053679603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173789799180800285369119735 260684698771200428053679603)
            ·
              refine ⟨391027048156800642080519405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260684698771200428053679603 391027048156800642080519405)
              ·
                refine ⟨146635143058800240780194777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 391027048156800642080519405 146635143058800240780194777)
                ·
                  refine ⟨109976357294100180585146083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146635143058800240780194777 109976357294100180585146083)
                  ·
                    refine ⟨164964535941150270877719125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109976357294100180585146083 164964535941150270877719125)
                    ·
                      refine ⟨1933178155560354736848271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 164964535941150270877719125 1933178155560354736848271)
                      ·
                        rfl

theorem cell23_3764851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 8].length) (baseStart_3764851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764851 prefixEnd_3764851 := by exact prefixLift 3764851
  have htrace : WordTrace (prefixWord ++ tailWord_3764851) baseStart_3764851 baseEnd_3764851 := by
    simpa [prefixWord, tailWord_3764851, baseEnd_3764851] using wordTrace_append hprefix tailTrace_3764851
  have hstable : (prefixWord ++ tailWord_3764851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764851).length < 2 ^ (prefixWord ++ tailWord_3764851).sum := by decide
  have hdescent : baseEnd_3764851 < baseStart_3764851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764853 : List Nat := [1, 3, 4, 2, 3, 1, 2, 1, 2, 1, 3]
def baseStart_3764853 : Nat := 118140960795 + 3764853 * 2 ^ 59
def prefixEnd_3764853 : Nat := 4983230072969 + 3 ^ 40 * 3764853 * 2
def baseEnd_3764853 : Nat := 1933179182521663729023263

theorem tailTrace_3764853 : CollatzResearch.WordTrace tailWord_3764853 prefixEnd_3764853 1933179182521663729023263 := by
  unfold tailWord_3764853
  simp only [CollatzResearch.WordTrace]
  refine ⟨137315469829588041546803213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91543646553058694364535475 137315469829588041546803213)
  ·
    refine ⟨51493301186095515580051205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137315469829588041546803213 51493301186095515580051205)
    ·
      refine ⟨9654993972392909171259601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51493301186095515580051205 9654993972392909171259601)
      ·
        refine ⟨7241245479294681878444701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9654993972392909171259601 7241245479294681878444701)
        ·
          refine ⟨2715467054735505704416763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7241245479294681878444701 2715467054735505704416763)
          ·
            refine ⟨4073200582103258556625145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2715467054735505704416763 4073200582103258556625145)
            ·
              refine ⟨3054900436577443917468859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4073200582103258556625145 3054900436577443917468859)
              ·
                refine ⟨4582350654866165876203289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3054900436577443917468859 4582350654866165876203289)
                ·
                  refine ⟨3436762991149624407152467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4582350654866165876203289 3436762991149624407152467)
                  ·
                    refine ⟨5155144486724436610728701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3436762991149624407152467 5155144486724436610728701)
                    ·
                      refine ⟨1933179182521663729023263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5155144486724436610728701 1933179182521663729023263)
                      ·
                        rfl

theorem cell23_3764853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_3764853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764853 prefixEnd_3764853 := by exact prefixLift 3764853
  have htrace : WordTrace (prefixWord ++ tailWord_3764853) baseStart_3764853 baseEnd_3764853 := by
    simpa [prefixWord, tailWord_3764853, baseEnd_3764853] using wordTrace_append hprefix tailTrace_3764853
  have hstable : (prefixWord ++ tailWord_3764853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764853).length < 2 ^ (prefixWord ++ tailWord_3764853).sum := by decide
  have hdescent : baseEnd_3764853 < baseStart_3764853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764858 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 6, 3, 3]
def baseStart_3764858 : Nat := 118140960795 + 3764858 * 2 ^ 59
def prefixEnd_3764858 : Nat := 4983230072969 + 3 ^ 40 * 3764858 * 2
def baseEnd_3764858 : Nat := 1933181749924936209460739

theorem tailTrace_3764858 : CollatzResearch.WordTrace tailWord_3764858 prefixEnd_3764858 1933181749924936209460739 := by
  unfold tailWord_3764858
  simp only [CollatzResearch.WordTrace]
  refine ⟨34328913048642481850183807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91543768129713284933823485 34328913048642481850183807)
  ·
    refine ⟨51493369572963722775275711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34328913048642481850183807 51493369572963722775275711)
    ·
      refine ⟨77240054359445584162913567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51493369572963722775275711 77240054359445584162913567)
      ·
        refine ⟨115860081539168376244370351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77240054359445584162913567 115860081539168376244370351)
        ·
          refine ⟨173790122308752564366555527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115860081539168376244370351 173790122308752564366555527)
          ·
            refine ⟨260685183463128846549833291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173790122308752564366555527 260685183463128846549833291)
            ·
              refine ⟨391027775194693269824749937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260685183463128846549833291 391027775194693269824749937)
              ·
                refine ⟨293270831396019952368562453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 391027775194693269824749937 293270831396019952368562453)
                ·
                  refine ⟨13747070221688435267276365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 293270831396019952368562453 13747070221688435267276365)
                  ·
                    refine ⟨5155151333133163225228637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13747070221688435267276365 5155151333133163225228637)
                    ·
                      refine ⟨1933181749924936209460739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5155151333133163225228637 1933181749924936209460739)
                      ·
                        rfl

theorem cell23_3764858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 6, 3, 3].length) (baseStart_3764858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764858 prefixEnd_3764858 := by exact prefixLift 3764858
  have htrace : WordTrace (prefixWord ++ tailWord_3764858) baseStart_3764858 baseEnd_3764858 := by
    simpa [prefixWord, tailWord_3764858, baseEnd_3764858] using wordTrace_append hprefix tailTrace_3764858
  have hstable : (prefixWord ++ tailWord_3764858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764858).length < 2 ^ (prefixWord ++ tailWord_3764858).sum := by decide
  have hdescent : baseEnd_3764858 < baseStart_3764858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764888 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 3, 2, 5]
def baseStart_3764888 : Nat := 118140960795 + 3764888 * 2 ^ 59
def prefixEnd_3764888 : Nat := 4983230072969 + 3 ^ 40 * 3764888 * 2
def baseEnd_3764888 : Nat := 1933197154344571092085601

theorem tailTrace_3764888 : CollatzResearch.WordTrace tailWord_3764888 prefixEnd_3764888 1933197154344571092085601 := by
  unfold tailWord_3764888
  simp only [CollatzResearch.WordTrace]
  refine ⟨68658373192230621262163659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91544497589640828349551545 68658373192230621262163659)
  ·
    refine ⟨102987559788345931893245489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68658373192230621262163659 102987559788345931893245489)
    ·
      refine ⟨77240669841259448919934117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102987559788345931893245489 77240669841259448919934117)
      ·
        refine ⟨14482625595236146672487647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77240669841259448919934117 14482625595236146672487647)
        ·
          refine ⟨21723938392854220008731471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14482625595236146672487647 21723938392854220008731471)
          ·
            refine ⟨32585907589281330013097207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21723938392854220008731471 32585907589281330013097207)
            ·
              refine ⟨48878861383921995019645811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32585907589281330013097207 48878861383921995019645811)
              ·
                refine ⟨73318292075882992529468717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48878861383921995019645811 73318292075882992529468717)
                ·
                  refine ⟨27494359528456122198550769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73318292075882992529468717 27494359528456122198550769)
                  ·
                    refine ⟨20620769646342091648913077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27494359528456122198550769 20620769646342091648913077)
                    ·
                      refine ⟨1933197154344571092085601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20620769646342091648913077 1933197154344571092085601)
                      ·
                        rfl

theorem cell23_3764888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_3764888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764888 prefixEnd_3764888 := by exact prefixLift 3764888
  have htrace : WordTrace (prefixWord ++ tailWord_3764888) baseStart_3764888 baseEnd_3764888 := by
    simpa [prefixWord, tailWord_3764888, baseEnd_3764888] using wordTrace_append hprefix tailTrace_3764888
  have hstable : (prefixWord ++ tailWord_3764888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764888).length < 2 ^ (prefixWord ++ tailWord_3764888).sum := by decide
  have hdescent : baseEnd_3764888 < baseStart_3764888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764915 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 1, 6, 2]
def baseStart_3764915 : Nat := 118140960795 + 3764915 * 2 ^ 59
def prefixEnd_3764915 : Nat := 4983230072969 + 3 ^ 40 * 3764915 * 2
def baseEnd_3764915 : Nat := 1933211018322242486447977

theorem tailTrace_3764915 : CollatzResearch.WordTrace tailWord_3764915 prefixEnd_3764915 1933211018322242486447977 := by
  unfold tailWord_3764915
  simp only [CollatzResearch.WordTrace]
  refine ⟨137317731155363426135560199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91545154103575617423706799 137317731155363426135560199)
  ·
    refine ⟨205976596733045139203340299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137317731155363426135560199 205976596733045139203340299)
    ·
      refine ⟨308964895099567708805010449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205976596733045139203340299 308964895099567708805010449)
      ·
        refine ⟨231723671324675781603757837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308964895099567708805010449 231723671324675781603757837)
        ·
          refine ⟨86896376746753418101409189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231723671324675781603757837 86896376746753418101409189)
          ·
            refine ⟨16293070640016265894014223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86896376746753418101409189 16293070640016265894014223)
            ·
              refine ⟨24439605960024398841021335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16293070640016265894014223 24439605960024398841021335)
              ·
                refine ⟨36659408940036598261532003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24439605960024398841021335 36659408940036598261532003)
                ·
                  refine ⟨54989113410054897392298005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36659408940036598261532003 54989113410054897392298005)
                  ·
                    refine ⟨2577614691096323315263969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 54989113410054897392298005 2577614691096323315263969)
                    ·
                      refine ⟨1933211018322242486447977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2577614691096323315263969 1933211018322242486447977)
                      ·
                        rfl

theorem cell23_3764915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 6, 2].length) (baseStart_3764915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764915 prefixEnd_3764915 := by exact prefixLift 3764915
  have htrace : WordTrace (prefixWord ++ tailWord_3764915) baseStart_3764915 baseEnd_3764915 := by
    simpa [prefixWord, tailWord_3764915, baseEnd_3764915] using wordTrace_append hprefix tailTrace_3764915
  have hstable : (prefixWord ++ tailWord_3764915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764915).length < 2 ^ (prefixWord ++ tailWord_3764915).sum := by decide
  have hdescent : baseEnd_3764915 < baseStart_3764915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764925 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 5, 4]
def baseStart_3764925 : Nat := 118140960795 + 3764925 * 2 ^ 59
def prefixEnd_3764925 : Nat := 4983230072969 + 3 ^ 40 * 3764925 * 2
def baseEnd_3764925 : Nat := 644405384376262482440977

theorem tailTrace_3764925 : CollatzResearch.WordTrace tailWord_3764925 prefixEnd_3764925 644405384376262482440977 := by
  unfold tailWord_3764925
  simp only [CollatzResearch.WordTrace]
  refine ⟨137318095885327197843424229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91545397256884798562282819 137318095885327197843424229)
  ·
    refine ⟨25747142978498849595642043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137318095885327197843424229 25747142978498849595642043)
    ·
      refine ⟨38620714467748274393463065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25747142978498849595642043 38620714467748274393463065)
      ·
        refine ⟨28965535850811205795097299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38620714467748274393463065 28965535850811205795097299)
        ·
          refine ⟨43448303776216808692645949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28965535850811205795097299 43448303776216808692645949)
          ·
            refine ⟨16293113916081303259742231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43448303776216808692645949 16293113916081303259742231)
            ·
              refine ⟨24439670874121954889613347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16293113916081303259742231 24439670874121954889613347)
              ·
                refine ⟨36659506311182932334420021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24439670874121954889613347 36659506311182932334420021)
                ·
                  refine ⟨3436828716673399906351877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36659506311182932334420021 3436828716673399906351877)
                  ·
                    refine ⟨644405384376262482440977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3436828716673399906351877 644405384376262482440977)
                    ·
                      rfl

theorem cell23_3764925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_3764925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764925 prefixEnd_3764925 := by exact prefixLift 3764925
  have htrace : WordTrace (prefixWord ++ tailWord_3764925) baseStart_3764925 baseEnd_3764925 := by
    simpa [prefixWord, tailWord_3764925, baseEnd_3764925] using wordTrace_append hprefix tailTrace_3764925
  have hstable : (prefixWord ++ tailWord_3764925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764925).length < 2 ^ (prefixWord ++ tailWord_3764925).sum := by decide
  have hdescent : baseEnd_3764925 < baseStart_3764925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764932 : List Nat := [2, 3, 3, 1, 1, 2, 3, 1, 2, 1, 4]
def baseStart_3764932 : Nat := 118140960795 + 3764932 * 2 ^ 59
def prefixEnd_3764932 : Nat := 4983230072969 + 3 ^ 40 * 3764932 * 2
def baseEnd_3764932 : Nat := 1933219747493368919935399

theorem tailTrace_3764932 : CollatzResearch.WordTrace tailWord_3764932 prefixEnd_3764932 1933219747493368919935399 := by
  unfold tailWord_3764932
  simp only [CollatzResearch.WordTrace]
  refine ⟨68659175598150919019464525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91545567464201225359286033 68659175598150919019464525)
  ·
    refine ⟨25747190849306594632299197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68659175598150919019464525 25747190849306594632299197)
    ·
      refine ⟨9655196568489972987112199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25747190849306594632299197 9655196568489972987112199)
      ·
        refine ⟨14482794852734959480668299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9655196568489972987112199 14482794852734959480668299)
        ·
          refine ⟨21724192279102439221002449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14482794852734959480668299 21724192279102439221002449)
          ·
            refine ⟨16293144209326829415751837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21724192279102439221002449 16293144209326829415751837)
            ·
              refine ⟨6109929078497561030906939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16293144209326829415751837 6109929078497561030906939)
              ·
                refine ⟨9164893617746341546360409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6109929078497561030906939 9164893617746341546360409)
                ·
                  refine ⟨6873670213309756159770307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9164893617746341546360409 6873670213309756159770307)
                  ·
                    refine ⟨10310505319964634239655461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6873670213309756159770307 10310505319964634239655461)
                    ·
                      refine ⟨1933219747493368919935399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10310505319964634239655461 1933219747493368919935399)
                      ·
                        rfl

theorem cell23_3764932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_3764932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764932 prefixEnd_3764932 := by exact prefixLift 3764932
  have htrace : WordTrace (prefixWord ++ tailWord_3764932) baseStart_3764932 baseEnd_3764932 := by
    simpa [prefixWord, tailWord_3764932, baseEnd_3764932] using wordTrace_append hprefix tailTrace_3764932
  have hstable : (prefixWord ++ tailWord_3764932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764932).length < 2 ^ (prefixWord ++ tailWord_3764932).sum := by decide
  have hdescent : baseEnd_3764932 < baseStart_3764932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764935 : List Nat := [1, 1, 4, 1, 1, 1, 2, 5, 2, 2, 3]
def baseStart_3764935 : Nat := 118140960795 + 3764935 * 2 ^ 59
def prefixEnd_3764935 : Nat := 4983230072969 + 3 ^ 40 * 3764935 * 2
def baseEnd_3764935 : Nat := 1933221287935332408197885

theorem tailTrace_3764935 : CollatzResearch.WordTrace tailWord_3764935 prefixEnd_3764935 1933221287935332408197885 := by
  unfold tailWord_3764935
  simp only [CollatzResearch.WordTrace]
  refine ⟨137318460615290969551288259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91545640410193979700858839 137318460615290969551288259)
  ·
    refine ⟨205977690922936454326932389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137318460615290969551288259 205977690922936454326932389)
    ·
      refine ⟨38620817048050585186299823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205977690922936454326932389 38620817048050585186299823)
      ·
        refine ⟨57931225572075877779449735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38620817048050585186299823 57931225572075877779449735)
        ·
          refine ⟨86896838358113816669174603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57931225572075877779449735 86896838358113816669174603)
          ·
            refine ⟨130345257537170725003761905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86896838358113816669174603 130345257537170725003761905)
            ·
              refine ⟨97758943152878043752821429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130345257537170725003761905 97758943152878043752821429)
              ·
                refine ⟨9164900920582316601827009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97758943152878043752821429 9164900920582316601827009)
                ·
                  refine ⟨6873675690436737451370257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9164900920582316601827009 6873675690436737451370257)
                  ·
                    refine ⟨5155256767827553088527693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6873675690436737451370257 5155256767827553088527693)
                    ·
                      refine ⟨1933221287935332408197885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5155256767827553088527693 1933221287935332408197885)
                      ·
                        rfl

theorem cell23_3764935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_3764935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3764935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3764935 prefixEnd_3764935 := by exact prefixLift 3764935
  have htrace : WordTrace (prefixWord ++ tailWord_3764935) baseStart_3764935 baseEnd_3764935 := by
    simpa [prefixWord, tailWord_3764935, baseEnd_3764935] using wordTrace_append hprefix tailTrace_3764935
  have hstable : (prefixWord ++ tailWord_3764935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764935).length < 2 ^ (prefixWord ++ tailWord_3764935).sum := by decide
  have hdescent : baseEnd_3764935 < baseStart_3764935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765025 : List Nat := [1, 2, 3, 2, 1, 2, 1, 4, 1, 1, 5]
def baseStart_3765025 : Nat := 118140960795 + 3765025 * 2 ^ 59
def prefixEnd_3765025 : Nat := 4983230072969 + 3 ^ 40 * 3765025 * 2
def baseEnd_3765025 : Nat := 1933267501194237056072471

theorem tailTrace_3765025 : CollatzResearch.WordTrace tailWord_3765025 prefixEnd_3765025 1933267501194237056072471 := by
  unfold tailWord_3765025
  simp only [CollatzResearch.WordTrace]
  refine ⟨137321743184964914922064529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91547828789976609948043019 137321743184964914922064529)
  ·
    refine ⟨102991307388723686191548397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137321743184964914922064529 102991307388723686191548397)
    ·
      refine ⟨38621740270771382321830649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102991307388723686191548397 38621740270771382321830649)
      ·
        refine ⟨28966305203078536741372987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38621740270771382321830649 28966305203078536741372987)
        ·
          refine ⟨43449457804617805112059481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28966305203078536741372987 43449457804617805112059481)
          ·
            refine ⟨32587093353463353834044611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43449457804617805112059481 32587093353463353834044611)
            ·
              refine ⟨48880640030195030751066917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32587093353463353834044611 48880640030195030751066917)
              ·
                refine ⟨9165120005661568265825047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48880640030195030751066917 9165120005661568265825047)
                ·
                  refine ⟨13747680008492352398737571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9165120005661568265825047 13747680008492352398737571)
                  ·
                    refine ⟨20621520012738528598106357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13747680008492352398737571 20621520012738528598106357)
                    ·
                      refine ⟨1933267501194237056072471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20621520012738528598106357 1933267501194237056072471)
                      ·
                        rfl

theorem cell23_3765025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_3765025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765025 prefixEnd_3765025 := by exact prefixLift 3765025
  have htrace : WordTrace (prefixWord ++ tailWord_3765025) baseStart_3765025 baseEnd_3765025 := by
    simpa [prefixWord, tailWord_3765025, baseEnd_3765025] using wordTrace_append hprefix tailTrace_3765025
  have hstable : (prefixWord ++ tailWord_3765025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765025).length < 2 ^ (prefixWord ++ tailWord_3765025).sum := by decide
  have hdescent : baseEnd_3765025 < baseStart_3765025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765042 : List Nat := [3, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3]
def baseStart_3765042 : Nat := 118140960795 + 3765042 * 2 ^ 59
def prefixEnd_3765042 : Nat := 4983230072969 + 3 ^ 40 * 3765042 * 2
def baseEnd_3765042 : Nat := 1933276230365363489559893

theorem tailTrace_3765042 : CollatzResearch.WordTrace tailWord_3765042 prefixEnd_3765042 1933276230365363489559893 := by
  unfold tailWord_3765042
  simp only [CollatzResearch.WordTrace]
  refine ⟨34330590806475831706358345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91548242150602217883622253 34330590806475831706358345)
  ·
    refine ⟨25747943104856873779768759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34330590806475831706358345 25747943104856873779768759)
    ·
      refine ⟨38621914657285310669653139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25747943104856873779768759 38621914657285310669653139)
      ·
        refine ⟨57932871985927966004479709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38621914657285310669653139 57932871985927966004479709)
        ·
          refine ⟨21724826994722987251679891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57932871985927966004479709 21724826994722987251679891)
          ·
            refine ⟨32587240492084480877519837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21724826994722987251679891 32587240492084480877519837)
            ·
              refine ⟨12220215184531680329069939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32587240492084480877519837 12220215184531680329069939)
              ·
                refine ⟨18330322776797520493604909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12220215184531680329069939 18330322776797520493604909)
                ·
                  refine ⟨6873871041299070185101841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18330322776797520493604909 6873871041299070185101841)
                  ·
                    refine ⟨5155403280974302638826381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6873871041299070185101841 5155403280974302638826381)
                    ·
                      refine ⟨1933276230365363489559893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5155403280974302638826381 1933276230365363489559893)
                      ·
                        rfl

theorem cell23_3765042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_3765042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765042 prefixEnd_3765042 := by exact prefixLift 3765042
  have htrace : WordTrace (prefixWord ++ tailWord_3765042) baseStart_3765042 baseEnd_3765042 := by
    simpa [prefixWord, tailWord_3765042, baseEnd_3765042] using wordTrace_append hprefix tailTrace_3765042
  have hstable : (prefixWord ++ tailWord_3765042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765042).length < 2 ^ (prefixWord ++ tailWord_3765042).sum := by decide
  have hdescent : baseEnd_3765042 < baseStart_3765042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765045 : List Nat := [1, 3, 3, 1, 3, 1, 2, 9]
def baseStart_3765045 : Nat := 118140960795 + 3765045 * 2 ^ 59
def prefixEnd_3765045 : Nat := 4983230072969 + 3 ^ 40 * 3765045 * 2
def baseEnd_3765045 : Nat := 71602880400271369548977

theorem tailTrace_3765045 : CollatzResearch.WordTrace tailWord_3765045 prefixEnd_3765045 71602880400271369548977 := by
  unfold tailWord_3765045
  simp only [CollatzResearch.WordTrace]
  refine ⟨137322472644892458337792589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91548315096594972225195059 137322472644892458337792589)
  ·
    refine ⟨51495927241834671876672221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137322472644892458337792589 51495927241834671876672221)
    ·
      refine ⟨19310972715688001953752083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51495927241834671876672221 19310972715688001953752083)
      ·
        refine ⟨28966459073532002930628125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19310972715688001953752083 28966459073532002930628125)
        ·
          refine ⟨10862422152574501098985547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28966459073532002930628125 10862422152574501098985547)
          ·
            refine ⟨16293633228861751648478321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10862422152574501098985547 16293633228861751648478321)
            ·
              refine ⟨12220224921646313736358741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16293633228861751648478321 12220224921646313736358741)
              ·
                refine ⟨71602880400271369548977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12220224921646313736358741 71602880400271369548977)
                ·
                  rfl

theorem cell23_3765045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 9].length) (baseStart_3765045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765045 prefixEnd_3765045 := by exact prefixLift 3765045
  have htrace : WordTrace (prefixWord ++ tailWord_3765045) baseStart_3765045 baseEnd_3765045 := by
    simpa [prefixWord, tailWord_3765045, baseEnd_3765045] using wordTrace_append hprefix tailTrace_3765045
  have hstable : (prefixWord ++ tailWord_3765045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765045).length < 2 ^ (prefixWord ++ tailWord_3765045).sum := by decide
  have hdescent : baseEnd_3765045 < baseStart_3765045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765059 : List Nat := [1, 1, 1, 3, 1, 4, 5, 1, 1, 2, 3]
def baseStart_3765059 : Nat := 118140960795 + 3765059 * 2 ^ 59
def prefixEnd_3765059 : Nat := 4983230072969 + 3 ^ 40 * 3765059 * 2
def baseEnd_3765059 : Nat := 1933284959536489923047315

theorem tailTrace_3765059 : CollatzResearch.WordTrace tailWord_3765059 prefixEnd_3765059 1933284959536489923047315 := by
  unfold tailWord_3765059
  simp only [CollatzResearch.WordTrace]
  refine ⟨137322983266841738728802231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91548655511227825819201487 137322983266841738728802231)
  ·
    refine ⟨205984474900262608093203347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137322983266841738728802231 205984474900262608093203347)
    ·
      refine ⟨308976712350393912139805021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205984474900262608093203347 308976712350393912139805021)
      ·
        refine ⟨115866267131397717052426883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308976712350393912139805021 115866267131397717052426883)
        ·
          refine ⟨173799400697096575578640325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115866267131397717052426883 173799400697096575578640325)
          ·
            refine ⟨32587387630705607920995061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173799400697096575578640325 32587387630705607920995061)
            ·
              refine ⟨3055067590378650742593287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32587387630705607920995061 3055067590378650742593287)
              ·
                refine ⟨4582601385567976113889931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3055067590378650742593287 4582601385567976113889931)
                ·
                  refine ⟨6873902078351964170834897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4582601385567976113889931 6873902078351964170834897)
                  ·
                    refine ⟨5155426558763973128126173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6873902078351964170834897 5155426558763973128126173)
                    ·
                      refine ⟨1933284959536489923047315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5155426558763973128126173 1933284959536489923047315)
                      ·
                        rfl

theorem cell23_3765059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 1, 2, 3].length) (baseStart_3765059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765059 prefixEnd_3765059 := by exact prefixLift 3765059
  have htrace : WordTrace (prefixWord ++ tailWord_3765059) baseStart_3765059 baseEnd_3765059 := by
    simpa [prefixWord, tailWord_3765059, baseEnd_3765059] using wordTrace_append hprefix tailTrace_3765059
  have hstable : (prefixWord ++ tailWord_3765059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765059).length < 2 ^ (prefixWord ++ tailWord_3765059).sum := by decide
  have hdescent : baseEnd_3765059 < baseStart_3765059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765062 : List Nat := [6, 1, 1, 2, 13]
def baseStart_3765062 : Nat := 118140960795 + 3765062 * 2 ^ 59
def prefixEnd_3765062 : Nat := 4983230072969 + 3 ^ 40 * 3765062 * 2
def baseEnd_3765062 : Nat := 2651970507515025255569

theorem tailTrace_3765062 : CollatzResearch.WordTrace tailWord_3765062 prefixEnd_3765062 2651970507515025255569 := by
  unfold tailWord_3765062
  simp only [CollatzResearch.WordTrace]
  refine ⟨4291346646432214695036295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 91548728457220580160774293 4291346646432214695036295)
  ·
    refine ⟨6437019969648322042554443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4291346646432214695036295 6437019969648322042554443)
    ·
      refine ⟨9655529954472483063831665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6437019969648322042554443 9655529954472483063831665)
      ·
        refine ⟨7241647465854362297873749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9655529954472483063831665 7241647465854362297873749)
        ·
          refine ⟨2651970507515025255569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 7241647465854362297873749 2651970507515025255569)
          ·
            rfl

theorem cell23_3765062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 13].length) (baseStart_3765062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765062 prefixEnd_3765062 := by exact prefixLift 3765062
  have htrace : WordTrace (prefixWord ++ tailWord_3765062) baseStart_3765062 baseEnd_3765062 := by
    simpa [prefixWord, tailWord_3765062, baseEnd_3765062] using wordTrace_append hprefix tailTrace_3765062
  have hstable : (prefixWord ++ tailWord_3765062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765062).length < 2 ^ (prefixWord ++ tailWord_3765062).sum := by decide
  have hdescent : baseEnd_3765062 < baseStart_3765062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765072 : List Nat := [2, 1, 1, 1, 1, 4, 2, 3, 4, 1, 3]
def baseStart_3765072 : Nat := 118140960795 + 3765072 * 2 ^ 59
def prefixEnd_3765072 : Nat := 4983230072969 + 3 ^ 40 * 3765072 * 2
def baseEnd_3765072 : Nat := 1933291634784998372184755

theorem tailTrace_3765072 : CollatzResearch.WordTrace tailWord_3765072 prefixEnd_3765072 1933291634784998372184755 := by
  unfold tailWord_3765072
  simp only [CollatzResearch.WordTrace]
  refine ⟨68661728707897320974512735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91548971610529761299350313 68661728707897320974512735)
  ·
    refine ⟨102992593061845981461769103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68661728707897320974512735 102992593061845981461769103)
    ·
      refine ⟨154488889592768972192653655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102992593061845981461769103 154488889592768972192653655)
      ·
        refine ⟨231733334389153458288980483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154488889592768972192653655 231733334389153458288980483)
        ·
          refine ⟨347600001583730187433470725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231733334389153458288980483 347600001583730187433470725)
          ·
            refine ⟨65175000296949410143775761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 347600001583730187433470725 65175000296949410143775761)
            ·
              refine ⟨48881250222712057607831821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65175000296949410143775761 48881250222712057607831821)
              ·
                refine ⟨18330468833517021602936933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48881250222712057607831821 18330468833517021602936933)
                ·
                  refine ⟨3436962906284441550550675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18330468833517021602936933 3436962906284441550550675)
                  ·
                    refine ⟨5155444359426662325826013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3436962906284441550550675 5155444359426662325826013)
                    ·
                      refine ⟨1933291634784998372184755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5155444359426662325826013 1933291634784998372184755)
                      ·
                        rfl

theorem cell23_3765072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 4, 1, 3].length) (baseStart_3765072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765072 prefixEnd_3765072 := by exact prefixLift 3765072
  have htrace : WordTrace (prefixWord ++ tailWord_3765072) baseStart_3765072 baseEnd_3765072 := by
    simpa [prefixWord, tailWord_3765072, baseEnd_3765072] using wordTrace_append hprefix tailTrace_3765072
  have hstable : (prefixWord ++ tailWord_3765072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765072).length < 2 ^ (prefixWord ++ tailWord_3765072).sum := by decide
  have hdescent : baseEnd_3765072 < baseStart_3765072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765073 : List Nat := [1, 2, 2, 1, 6, 1, 1, 4, 1, 2, 2]
def baseStart_3765073 : Nat := 118140960795 + 3765073 * 2 ^ 59
def prefixEnd_3765073 : Nat := 4983230072969 + 3 ^ 40 * 3765073 * 2
def baseEnd_3765073 : Nat := 1933292148265652868272251

theorem tailTrace_3765073 : CollatzResearch.WordTrace tailWord_3765073 prefixEnd_3765073 1933292148265652868272251 := by
  unfold tailWord_3765073
  simp only [CollatzResearch.WordTrace]
  refine ⟨137323493888791019119811873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91548995925860679413207915 137323493888791019119811873)
  ·
    refine ⟨102992620416593264339858905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137323493888791019119811873 102992620416593264339858905)
    ·
      refine ⟨77244465312444948254894179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102992620416593264339858905 77244465312444948254894179)
      ·
        refine ⟨115866697968667422382341269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77244465312444948254894179 115866697968667422382341269)
        ·
          refine ⟨5431251467281285424172247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 115866697968667422382341269 5431251467281285424172247)
          ·
            refine ⟨8146877200921928136258371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5431251467281285424172247 8146877200921928136258371)
            ·
              refine ⟨12220315801382892204387557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8146877200921928136258371 12220315801382892204387557)
              ·
                refine ⟨2291309212759292288322667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12220315801382892204387557 2291309212759292288322667)
                ·
                  refine ⟨3436963819138938432484001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2291309212759292288322667 3436963819138938432484001)
                  ·
                    refine ⟨2577722864354203824363001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3436963819138938432484001 2577722864354203824363001)
                    ·
                      refine ⟨1933292148265652868272251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2577722864354203824363001 1933292148265652868272251)
                      ·
                        rfl

theorem cell23_3765073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 4, 1, 2, 2].length) (baseStart_3765073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765073 prefixEnd_3765073 := by exact prefixLift 3765073
  have htrace : WordTrace (prefixWord ++ tailWord_3765073) baseStart_3765073 baseEnd_3765073 := by
    simpa [prefixWord, tailWord_3765073, baseEnd_3765073] using wordTrace_append hprefix tailTrace_3765073
  have hstable : (prefixWord ++ tailWord_3765073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765073).length < 2 ^ (prefixWord ++ tailWord_3765073).sum := by decide
  have hdescent : baseEnd_3765073 < baseStart_3765073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765112 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 3, 4, 2]
def baseStart_3765112 : Nat := 118140960795 + 3765112 * 2 ^ 59
def prefixEnd_3765112 : Nat := 4983230072969 + 3 ^ 40 * 3765112 * 2
def baseEnd_3765112 : Nat := 1933312174011178215684571

theorem tailTrace_3765112 : CollatzResearch.WordTrace tailWord_3765112 prefixEnd_3765112 1933312174011178215684571 := by
  unfold tailWord_3765112
  simp only [CollatzResearch.WordTrace]
  refine ⟨68662458167824864390240795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91549944223766485853654393 68662458167824864390240795)
  ·
    refine ⟨102993687251737296585361193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68662458167824864390240795 102993687251737296585361193)
    ·
      refine ⟨77245265438802972439020895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102993687251737296585361193 77245265438802972439020895)
      ·
        refine ⟨115867898158204458658531343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77245265438802972439020895 115867898158204458658531343)
        ·
          refine ⟨173801847237306687987797015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115867898158204458658531343 173801847237306687987797015)
          ·
            refine ⟨260702770855960031981695523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173801847237306687987797015 260702770855960031981695523)
            ·
              refine ⟨391054156283940047972543285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260702770855960031981695523 391054156283940047972543285)
              ·
                refine ⟨36661327151619379497425933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 391054156283940047972543285 36661327151619379497425933)
                ·
                  refine ⟨13747997681857267311534725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36661327151619379497425933 13747997681857267311534725)
                  ·
                    refine ⟨2577749565348237620912761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13747997681857267311534725 2577749565348237620912761)
                    ·
                      refine ⟨1933312174011178215684571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2577749565348237620912761 1933312174011178215684571)
                      ·
                        rfl

theorem cell23_3765112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 3, 4, 2].length) (baseStart_3765112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765112 prefixEnd_3765112 := by exact prefixLift 3765112
  have htrace : WordTrace (prefixWord ++ tailWord_3765112) baseStart_3765112 baseEnd_3765112 := by
    simpa [prefixWord, tailWord_3765112, baseEnd_3765112] using wordTrace_append hprefix tailTrace_3765112
  have hstable : (prefixWord ++ tailWord_3765112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765112).length < 2 ^ (prefixWord ++ tailWord_3765112).sum := by decide
  have hdescent : baseEnd_3765112 < baseStart_3765112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765115 : List Nat := [1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 5]
def baseStart_3765115 : Nat := 118140960795 + 3765115 * 2 ^ 59
def prefixEnd_3765115 : Nat := 4983230072969 + 3 ^ 40 * 3765115 * 2
def baseEnd_3765115 : Nat := 1933313714453141703947057

theorem tailTrace_3765115 : CollatzResearch.WordTrace tailWord_3765115 prefixEnd_3765115 1933313714453141703947057 := by
  unfold tailWord_3765115
  simp only [CollatzResearch.WordTrace]
  refine ⟨137325025754638860292840799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91550017169759240195227199 137325025754638860292840799)
  ·
    refine ⟨205987538631958290439261199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137325025754638860292840799 205987538631958290439261199)
    ·
      refine ⟨308981307947937435658891799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205987538631958290439261199 308981307947937435658891799)
      ·
        refine ⟨463471961921906153488337699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308981307947937435658891799 463471961921906153488337699)
        ·
          refine ⟨695207942882859230232506549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463471961921906153488337699 695207942882859230232506549)
          ·
            refine ⟨65175744645268052834297489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 695207942882859230232506549 65175744645268052834297489)
            ·
              refine ⟨48881808483951039625723117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65175744645268052834297489 48881808483951039625723117)
              ·
                refine ⟨18330678181481639859646169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48881808483951039625723117 18330678181481639859646169)
                ·
                  refine ⟨13748008636111229894734627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18330678181481639859646169 13748008636111229894734627)
                  ·
                    refine ⟨20622012954166844842101941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13748008636111229894734627 20622012954166844842101941)
                    ·
                      refine ⟨1933313714453141703947057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20622012954166844842101941 1933313714453141703947057)
                      ·
                        rfl

theorem cell23_3765115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 5].length) (baseStart_3765115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765115 prefixEnd_3765115 := by exact prefixLift 3765115
  have htrace : WordTrace (prefixWord ++ tailWord_3765115) baseStart_3765115 baseEnd_3765115 := by
    simpa [prefixWord, tailWord_3765115, baseEnd_3765115] using wordTrace_append hprefix tailTrace_3765115
  have hstable : (prefixWord ++ tailWord_3765115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765115).length < 2 ^ (prefixWord ++ tailWord_3765115).sum := by decide
  have hdescent : baseEnd_3765115 < baseStart_3765115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765219 : List Nat := [1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 4]
def baseStart_3765219 : Nat := 118140960795 + 3765219 * 2 ^ 59
def prefixEnd_3765219 : Nat := 4983230072969 + 3 ^ 40 * 3765219 * 2
def baseEnd_3765219 : Nat := 1933367116441209297046579

theorem tailTrace_3765219 : CollatzResearch.WordTrace tailWord_3765219 prefixEnd_3765219 1933367116441209297046579 := by
  unfold tailWord_3765219
  simp only [CollatzResearch.WordTrace]
  refine ⟨137328818946262086054626711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91552545964174724036417807 137328818946262086054626711)
  ·
    refine ⟨205993228419393129081940067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137328818946262086054626711 205993228419393129081940067)
    ·
      refine ⟨308989842629089693622910101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205993228419393129081940067 308989842629089693622910101)
      ·
        refine ⟨14483898873238579388573911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 308989842629089693622910101 14483898873238579388573911)
        ·
          refine ⟨21725848309857869082860867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14483898873238579388573911 21725848309857869082860867)
          ·
            refine ⟨32588772464786803624291301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21725848309857869082860867 32588772464786803624291301)
            ·
              refine ⟨6110394837147525679554619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32588772464786803624291301 6110394837147525679554619)
              ·
                refine ⟨9165592255721288519331929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6110394837147525679554619 9165592255721288519331929)
                ·
                  refine ⟨6874194191790966389498947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9165592255721288519331929 6874194191790966389498947)
                  ·
                    refine ⟨10311291287686449584248421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6874194191790966389498947 10311291287686449584248421)
                    ·
                      refine ⟨1933367116441209297046579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10311291287686449584248421 1933367116441209297046579)
                      ·
                        rfl

theorem cell23_3765219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_3765219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765219 prefixEnd_3765219 := by exact prefixLift 3765219
  have htrace : WordTrace (prefixWord ++ tailWord_3765219) baseStart_3765219 baseEnd_3765219 := by
    simpa [prefixWord, tailWord_3765219, baseEnd_3765219] using wordTrace_append hprefix tailTrace_3765219
  have hstable : (prefixWord ++ tailWord_3765219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765219).length < 2 ^ (prefixWord ++ tailWord_3765219).sum := by decide
  have hdescent : baseEnd_3765219 < baseStart_3765219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765237 : List Nat := [1, 3, 5, 2, 2, 1, 2, 2, 5]
def baseStart_3765237 : Nat := 118140960795 + 3765237 * 2 ^ 59
def prefixEnd_3765237 : Nat := 4983230072969 + 3 ^ 40 * 3765237 * 2
def baseEnd_3765237 : Nat := 214819595454776691846833

theorem tailTrace_3765237 : CollatzResearch.WordTrace tailWord_3765237 prefixEnd_3765237 214819595454776691846833 := by
  unfold tailWord_3765237
  simp only [CollatzResearch.WordTrace]
  refine ⟨137329475460196875128781965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91552983640131250085854643 137329475460196875128781965)
  ·
    refine ⟨51498553297573828173293237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137329475460196875128781965 51498553297573828173293237)
    ·
      refine ⟨4827989371647546391246241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51498553297573828173293237 4827989371647546391246241)
      ·
        refine ⟨3620992028735659793434681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4827989371647546391246241 3620992028735659793434681)
        ·
          refine ⟨2715744021551744845076011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3620992028735659793434681 2715744021551744845076011)
          ·
            refine ⟨4073616032327617267614017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2715744021551744845076011 4073616032327617267614017)
            ·
              refine ⟨3055212024245712950710513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4073616032327617267614017 3055212024245712950710513)
              ·
                refine ⟨2291409018184284713032885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3055212024245712950710513 2291409018184284713032885)
                ·
                  refine ⟨214819595454776691846833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2291409018184284713032885 214819595454776691846833)
                  ·
                    rfl

theorem cell23_3765237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 2, 5].length) (baseStart_3765237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765237 prefixEnd_3765237 := by exact prefixLift 3765237
  have htrace : WordTrace (prefixWord ++ tailWord_3765237) baseStart_3765237 baseEnd_3765237 := by
    simpa [prefixWord, tailWord_3765237, baseEnd_3765237] using wordTrace_append hprefix tailTrace_3765237
  have hstable : (prefixWord ++ tailWord_3765237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765237).length < 2 ^ (prefixWord ++ tailWord_3765237).sum := by decide
  have hdescent : baseEnd_3765237 < baseStart_3765237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765280 : List Nat := [2, 1, 1, 7, 1, 1, 2, 3, 1, 4]
def baseStart_3765280 : Nat := 118140960795 + 3765280 * 2 ^ 59
def prefixEnd_3765280 : Nat := 4983230072969 + 3 ^ 40 * 3765280 * 2
def baseEnd_3765280 : Nat := 644466146253711186127933

theorem tailTrace_3765280 : CollatzResearch.WordTrace tailWord_3765280 prefixEnd_3765280 644466146253711186127933 := by
  unfold tailWord_3765280
  simp only [CollatzResearch.WordTrace]
  refine ⟨68665521899520546736298647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91554029199360728981731529 68665521899520546736298647)
  ·
    refine ⟨102998282849280820104447971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68665521899520546736298647 102998282849280820104447971)
    ·
      refine ⟨154497424273921230156671957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102998282849280820104447971 154497424273921230156671957)
      ·
        refine ⟨3621033381420028831796999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 154497424273921230156671957 3621033381420028831796999)
        ·
          refine ⟨5431550072130043247695499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3621033381420028831796999 5431550072130043247695499)
          ·
            refine ⟨8147325108195064871543249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5431550072130043247695499 8147325108195064871543249)
            ·
              refine ⟨6110493831146298653657437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8147325108195064871543249 6110493831146298653657437)
              ·
                refine ⟨2291435186679861995121539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6110493831146298653657437 2291435186679861995121539)
                ·
                  refine ⟨3437152780019792992682309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2291435186679861995121539 3437152780019792992682309)
                  ·
                    refine ⟨644466146253711186127933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3437152780019792992682309 644466146253711186127933)
                    ·
                      rfl

theorem cell23_3765280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 3, 1, 4].length) (baseStart_3765280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765280 prefixEnd_3765280 := by exact prefixLift 3765280
  have htrace : WordTrace (prefixWord ++ tailWord_3765280) baseStart_3765280 baseEnd_3765280 := by
    simpa [prefixWord, tailWord_3765280, baseEnd_3765280] using wordTrace_append hprefix tailTrace_3765280
  have hstable : (prefixWord ++ tailWord_3765280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765280).length < 2 ^ (prefixWord ++ tailWord_3765280).sum := by decide
  have hdescent : baseEnd_3765280 < baseStart_3765280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765319 : List Nat := [1, 1, 4, 1, 3, 2, 3, 1, 1, 6]
def baseStart_3765319 : Nat := 118140960795 + 3765319 * 2 ^ 59
def prefixEnd_3765319 : Nat := 4983230072969 + 3 ^ 40 * 3765319 * 2
def baseEnd_3765319 : Nat := 644472821502219635265373

theorem tailTrace_3765319 : CollatzResearch.WordTrace tailWord_3765319 prefixEnd_3765319 644472821502219635265373 := by
  unfold tailWord_3765319
  simp only [CollatzResearch.WordTrace]
  refine ⟨137332466245899803133267011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91554977497266535422178007 137332466245899803133267011)
  ·
    refine ⟨205998699368849704699900517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137332466245899803133267011 205998699368849704699900517)
    ·
      refine ⟨38624756131659319631231347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205998699368849704699900517 38624756131659319631231347)
      ·
        refine ⟨57937134197488979446847021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38624756131659319631231347 57937134197488979446847021)
        ·
          refine ⟨21726425324058367292567633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57937134197488979446847021 21726425324058367292567633)
          ·
            refine ⟨16294818993043775469425725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21726425324058367292567633 16294818993043775469425725)
            ·
              refine ⟨6110557122391415801034647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16294818993043775469425725 6110557122391415801034647)
              ·
                refine ⟨9165835683587123701551971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6110557122391415801034647 9165835683587123701551971)
                ·
                  refine ⟨13748753525380685552327957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9165835683587123701551971 13748753525380685552327957)
                  ·
                    refine ⟨644472821502219635265373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13748753525380685552327957 644472821502219635265373)
                    ·
                      rfl

theorem cell23_3765319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_3765319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765319 prefixEnd_3765319 := by exact prefixLift 3765319
  have htrace : WordTrace (prefixWord ++ tailWord_3765319) baseStart_3765319 baseEnd_3765319 := by
    simpa [prefixWord, tailWord_3765319, baseEnd_3765319] using wordTrace_append hprefix tailTrace_3765319
  have hstable : (prefixWord ++ tailWord_3765319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765319).length < 2 ^ (prefixWord ++ tailWord_3765319).sum := by decide
  have hdescent : baseEnd_3765319 < baseStart_3765319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765326 : List Nat := [4, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4]
def baseStart_3765326 : Nat := 118140960795 + 3765326 * 2 ^ 59
def prefixEnd_3765326 : Nat := 4983230072969 + 3 ^ 40 * 3765326 * 2
def baseEnd_3765326 : Nat := 1933422058871240378408587

theorem tailTrace_3765326 : CollatzResearch.WordTrace tailWord_3765326 prefixEnd_3765326 1933422058871240378408587 := by
  unfold tailWord_3765326
  simp only [CollatzResearch.WordTrace]
  refine ⟨17166590194609305416096479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91555147704582962219181221 17166590194609305416096479)
  ·
    refine ⟨25749885291913958124144719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17166590194609305416096479 25749885291913958124144719)
    ·
      refine ⟨38624827937870937186217079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25749885291913958124144719 38624827937870937186217079)
      ·
        refine ⟨57937241906806405779325619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38624827937870937186217079 57937241906806405779325619)
        ·
          refine ⟨86905862860209608668988429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57937241906806405779325619 86905862860209608668988429)
          ·
            refine ⟨32589698572578603250870661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86905862860209608668988429 32589698572578603250870661)
            ·
              refine ⟨6110568482358488109538249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32589698572578603250870661 6110568482358488109538249)
              ·
                refine ⟨4582926361768866082153687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6110568482358488109538249 4582926361768866082153687)
                ·
                  refine ⟨6874389542653299123230531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4582926361768866082153687 6874389542653299123230531)
                  ·
                    refine ⟨10311584313979948684845797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6874389542653299123230531 10311584313979948684845797)
                    ·
                      refine ⟨1933422058871240378408587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10311584313979948684845797 1933422058871240378408587)
                      ·
                        rfl

theorem cell23_3765326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_3765326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765326 prefixEnd_3765326 := by exact prefixLift 3765326
  have htrace : WordTrace (prefixWord ++ tailWord_3765326) baseStart_3765326 baseEnd_3765326 := by
    simpa [prefixWord, tailWord_3765326, baseEnd_3765326] using wordTrace_append hprefix tailTrace_3765326
  have hstable : (prefixWord ++ tailWord_3765326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765326).length < 2 ^ (prefixWord ++ tailWord_3765326).sum := by decide
  have hdescent : baseEnd_3765326 < baseStart_3765326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765329 : List Nat := [1, 2, 2, 1, 3, 1, 2, 3, 3, 2, 3]
def baseStart_3765329 : Nat := 118140960795 + 3765329 * 2 ^ 59
def prefixEnd_3765329 : Nat := 4983230072969 + 3 ^ 40 * 3765329 * 2
def baseEnd_3765329 : Nat := 1933423599313203866671073

theorem tailTrace_3765329 : CollatzResearch.WordTrace tailWord_3765329 prefixEnd_3765329 1933423599313203866671073 := by
  unfold tailWord_3765329
  simp only [CollatzResearch.WordTrace]
  refine ⟨137332830975863574841131041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91555220650575716560754027 137332830975863574841131041)
  ·
    refine ⟨102999623231897681130848281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137332830975863574841131041 102999623231897681130848281)
    ·
      refine ⟨77249717423923260848136211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102999623231897681130848281 77249717423923260848136211)
      ·
        refine ⟨115874576135884891272204317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77249717423923260848136211 115874576135884891272204317)
        ·
          refine ⟨43452966050956834227076619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115874576135884891272204317 43452966050956834227076619)
          ·
            refine ⟨65179449076435251340614929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43452966050956834227076619 65179449076435251340614929)
            ·
              refine ⟨48884586807326438505461197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65179449076435251340614929 48884586807326438505461197)
              ·
                refine ⟨18331720052747414439547949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48884586807326438505461197 18331720052747414439547949)
                ·
                  refine ⟨6874395019780280414830481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18331720052747414439547949 6874395019780280414830481)
                  ·
                    refine ⟨5155796264835210311122861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6874395019780280414830481 5155796264835210311122861)
                    ·
                      refine ⟨1933423599313203866671073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5155796264835210311122861 1933423599313203866671073)
                      ·
                        rfl

theorem cell23_3765329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 2, 3].length) (baseStart_3765329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765329 prefixEnd_3765329 := by exact prefixLift 3765329
  have htrace : WordTrace (prefixWord ++ tailWord_3765329) baseStart_3765329 baseEnd_3765329 := by
    simpa [prefixWord, tailWord_3765329, baseEnd_3765329] using wordTrace_append hprefix tailTrace_3765329
  have hstable : (prefixWord ++ tailWord_3765329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765329).length < 2 ^ (prefixWord ++ tailWord_3765329).sum := by decide
  have hdescent : baseEnd_3765329 < baseStart_3765329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765346 : List Nat := [3, 3, 2, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_3765346 : Nat := 118140960795 + 3765346 * 2 ^ 59
def prefixEnd_3765346 : Nat := 4983230072969 + 3 ^ 40 * 3765346 * 2
def baseEnd_3765346 : Nat := 1933432328484330300158495

theorem tailTrace_3765346 : CollatzResearch.WordTrace tailWord_3765346 prefixEnd_3765346 1933432328484330300158495 := by
  unfold tailWord_3765346
  simp only [CollatzResearch.WordTrace]
  refine ⟨34333362754200496686124973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91555634011201324496333261 34333362754200496686124973)
  ·
    refine ⟨12875011032825186257296865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34333362754200496686124973 12875011032825186257296865)
    ·
      refine ⟨9656258274618889692972649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12875011032825186257296865 9656258274618889692972649)
      ·
        refine ⟨7242193705964167269729487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9656258274618889692972649 7242193705964167269729487)
        ·
          refine ⟨10863290558946250904594231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7242193705964167269729487 10863290558946250904594231)
          ·
            refine ⟨16294935838419376356891347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10863290558946250904594231 16294935838419376356891347)
            ·
              refine ⟨24442403757629064535337021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16294935838419376356891347 24442403757629064535337021)
              ·
                refine ⟨9165901409110899200751383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24442403757629064535337021 9165901409110899200751383)
                ·
                  refine ⟨13748852113666348801127075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9165901409110899200751383 13748852113666348801127075)
                  ·
                    refine ⟨20623278170499523201690613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13748852113666348801127075 20623278170499523201690613)
                    ·
                      refine ⟨1933432328484330300158495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20623278170499523201690613 1933432328484330300158495)
                      ·
                        rfl

theorem cell23_3765346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_3765346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765346 prefixEnd_3765346 := by exact prefixLift 3765346
  have htrace : WordTrace (prefixWord ++ tailWord_3765346) baseStart_3765346 baseEnd_3765346 := by
    simpa [prefixWord, tailWord_3765346, baseEnd_3765346] using wordTrace_append hprefix tailTrace_3765346
  have hstable : (prefixWord ++ tailWord_3765346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765346).length < 2 ^ (prefixWord ++ tailWord_3765346).sum := by decide
  have hdescent : baseEnd_3765346 < baseStart_3765346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765374 : List Nat := [4, 2, 4, 1, 2, 1, 1, 2, 1, 5]
def baseStart_3765374 : Nat := 118140960795 + 3765374 * 2 ^ 59
def prefixEnd_3765374 : Nat := 4983230072969 + 3 ^ 40 * 3765374 * 2
def baseEnd_3765374 : Nat := 644482235314218730202789

theorem tailTrace_3765374 : CollatzResearch.WordTrace tailWord_3765374 prefixEnd_3765374 644482235314218730202789 := by
  unfold tailWord_3765374
  simp only [CollatzResearch.WordTrace]
  refine ⟨17166809032587568440814897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91556314840467031684346117 17166809032587568440814897)
  ·
    refine ⟨12875106774440676330611173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17166809032587568440814897 12875106774440676330611173)
    ·
      refine ⟨2414082520207626811989595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12875106774440676330611173 2414082520207626811989595)
      ·
        refine ⟨3621123780311440217984393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2414082520207626811989595 3621123780311440217984393)
        ·
          refine ⟨2715842835233580163488295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3621123780311440217984393 2715842835233580163488295)
          ·
            refine ⟨4073764252850370245232443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2715842835233580163488295 4073764252850370245232443)
            ·
              refine ⟨6110646379275555367848665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4073764252850370245232443 6110646379275555367848665)
              ·
                refine ⟨4582984784456666525886499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6110646379275555367848665 4582984784456666525886499)
                ·
                  refine ⟨6874477176684999788829749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4582984784456666525886499 6874477176684999788829749)
                  ·
                    refine ⟨644482235314218730202789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6874477176684999788829749 644482235314218730202789)
                    ·
                      rfl

theorem cell23_3765374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_3765374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765374 prefixEnd_3765374 := by exact prefixLift 3765374
  have htrace : WordTrace (prefixWord ++ tailWord_3765374) baseStart_3765374 baseEnd_3765374 := by
    simpa [prefixWord, tailWord_3765374, baseEnd_3765374] using wordTrace_append hprefix tailTrace_3765374
  have hstable : (prefixWord ++ tailWord_3765374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765374).length < 2 ^ (prefixWord ++ tailWord_3765374).sum := by decide
  have hdescent : baseEnd_3765374 < baseStart_3765374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765392 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 3, 8]
def baseStart_3765392 : Nat := 118140960795 + 3765392 * 2 ^ 59
def prefixEnd_3765392 : Nat := 4983230072969 + 3 ^ 40 * 3765392 * 2
def baseEnd_3765392 : Nat := 644485316198145706727761

theorem tailTrace_3765392 : CollatzResearch.WordTrace tailWord_3765392 prefixEnd_3765392 644485316198145706727761 := by
  unfold tailWord_3765392
  simp only [CollatzResearch.WordTrace]
  refine ⟨68667564387317668300337215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91556752516423557733782953 68667564387317668300337215)
  ·
    refine ⟨103001346580976502450505823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68667564387317668300337215 103001346580976502450505823)
    ·
      refine ⟨154502019871464753675758735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103001346580976502450505823 154502019871464753675758735)
      ·
        refine ⟨231753029807197130513638103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154502019871464753675758735 231753029807197130513638103)
        ·
          refine ⟨347629544710795695770457155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231753029807197130513638103 347629544710795695770457155)
          ·
            refine ⟨521444317066193543655685733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347629544710795695770457155 521444317066193543655685733)
            ·
              refine ⟨97770809449911289435441075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 521444317066193543655685733 97770809449911289435441075)
              ·
                refine ⟨146656214174866934153161613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97770809449911289435441075 146656214174866934153161613)
                ·
                  refine ⟨54996080315575100307435605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146656214174866934153161613 54996080315575100307435605)
                  ·
                    refine ⟨644485316198145706727761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54996080315575100307435605 644485316198145706727761)
                    ·
                      rfl

theorem cell23_3765392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 3, 8].length) (baseStart_3765392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765392 prefixEnd_3765392 := by exact prefixLift 3765392
  have htrace : WordTrace (prefixWord ++ tailWord_3765392) baseStart_3765392 baseEnd_3765392 := by
    simpa [prefixWord, tailWord_3765392, baseEnd_3765392] using wordTrace_append hprefix tailTrace_3765392
  have hstable : (prefixWord ++ tailWord_3765392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765392).length < 2 ^ (prefixWord ++ tailWord_3765392).sum := by decide
  have hdescent : baseEnd_3765392 < baseStart_3765392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765409 : List Nat := [1, 2, 3, 3, 1, 1, 2, 2, 2, 6]
def baseStart_3765409 : Nat := 118140960795 + 3765409 * 2 ^ 59
def prefixEnd_3765409 : Nat := 4983230072969 + 3 ^ 40 * 3765409 * 2
def baseEnd_3765409 : Nat := 644488225921854517890235

theorem tailTrace_3765409 : CollatzResearch.WordTrace tailWord_3765409 prefixEnd_3765409 644488225921854517890235 := by
  unfold tailWord_3765409
  simp only [CollatzResearch.WordTrace]
  refine ⟨137335748815573748504043281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91557165877049165669362187 137335748815573748504043281)
  ·
    refine ⟨103001811611680311378032461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137335748815573748504043281 103001811611680311378032461)
    ·
      refine ⟨38625679354380116766762173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103001811611680311378032461 38625679354380116766762173)
      ·
        refine ⟨14484629757892543787535815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38625679354380116766762173 14484629757892543787535815)
        ·
          refine ⟨21726944636838815681303723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14484629757892543787535815 21726944636838815681303723)
          ·
            refine ⟨32590416955258223521955585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21726944636838815681303723 32590416955258223521955585)
            ·
              refine ⟨24442812716443667641466689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32590416955258223521955585 24442812716443667641466689)
              ·
                refine ⟨18332109537332750731100017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24442812716443667641466689 18332109537332750731100017)
                ·
                  refine ⟨13749082152999563048325013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18332109537332750731100017 13749082152999563048325013)
                  ·
                    refine ⟨644488225921854517890235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13749082152999563048325013 644488225921854517890235)
                    ·
                      rfl

theorem cell23_3765409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_3765409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765409 prefixEnd_3765409 := by exact prefixLift 3765409
  have htrace : WordTrace (prefixWord ++ tailWord_3765409) baseStart_3765409 baseEnd_3765409 := by
    simpa [prefixWord, tailWord_3765409, baseEnd_3765409] using wordTrace_append hprefix tailTrace_3765409
  have hstable : (prefixWord ++ tailWord_3765409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765409).length < 2 ^ (prefixWord ++ tailWord_3765409).sum := by decide
  have hdescent : baseEnd_3765409 < baseStart_3765409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765433 : List Nat := [1, 2, 1, 4, 1, 4, 2, 1, 1, 4, 2]
def baseStart_3765433 : Nat := 118140960795 + 3765433 * 2 ^ 59
def prefixEnd_3765433 : Nat := 4983230072969 + 3 ^ 40 * 3765433 * 2
def baseEnd_3765433 : Nat := 1933477001301271459770595

theorem tailTrace_3765433 : CollatzResearch.WordTrace tailWord_3765433 prefixEnd_3765433 1933477001301271459770595 := by
  unfold tailWord_3765433
  simp only [CollatzResearch.WordTrace]
  refine ⟨137336624167486800602916953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91557749444991200401944635 137336624167486800602916953)
  ·
    refine ⟨103002468125615100452187715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137336624167486800602916953 103002468125615100452187715)
    ·
      refine ⟨154503702188422650678281573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103002468125615100452187715 154503702188422650678281573)
      ·
        refine ⟨28969444160329247002177795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154503702188422650678281573 28969444160329247002177795)
        ·
          refine ⟨43454166240493870503266693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28969444160329247002177795 43454166240493870503266693)
          ·
            refine ⟨8147656170092600719362505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43454166240493870503266693 8147656170092600719362505)
            ·
              refine ⟨6110742127569450539521879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8147656170092600719362505 6110742127569450539521879)
              ·
                refine ⟨9166113191354175809282819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6110742127569450539521879 9166113191354175809282819)
                ·
                  refine ⟨13749169787031263713924229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9166113191354175809282819 13749169787031263713924229)
                  ·
                    refine ⟨2577969335068361946360793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13749169787031263713924229 2577969335068361946360793)
                    ·
                      refine ⟨1933477001301271459770595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2577969335068361946360793 1933477001301271459770595)
                      ·
                        rfl

theorem cell23_3765433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_3765433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765433 prefixEnd_3765433 := by exact prefixLift 3765433
  have htrace : WordTrace (prefixWord ++ tailWord_3765433) baseStart_3765433 baseEnd_3765433 := by
    simpa [prefixWord, tailWord_3765433, baseEnd_3765433] using wordTrace_append hprefix tailTrace_3765433
  have hstable : (prefixWord ++ tailWord_3765433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765433).length < 2 ^ (prefixWord ++ tailWord_3765433).sum := by decide
  have hdescent : baseEnd_3765433 < baseStart_3765433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765454 : List Nat := [4, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2]
def baseStart_3765454 : Nat := 118140960795 + 3765454 * 2 ^ 59
def prefixEnd_3765454 : Nat := 4983230072969 + 3 ^ 40 * 3765454 * 2
def baseEnd_3765454 : Nat := 1933487784395015877607999

theorem tailTrace_3765454 : CollatzResearch.WordTrace tailWord_3765454 prefixEnd_3765454 1933487784395015877607999 := by
  unfold tailWord_3765454
  simp only [CollatzResearch.WordTrace]
  refine ⟨17167173762551340148678927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91558260066940480792954277 17167173762551340148678927)
  ·
    refine ⟨25750760643827010223018391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17167173762551340148678927 25750760643827010223018391)
    ·
      refine ⟨38626140965740515334527587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25750760643827010223018391 38626140965740515334527587)
      ·
        refine ⟨57939211448610773001791381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38626140965740515334527587 57939211448610773001791381)
        ·
          refine ⟨2715900536653629984458971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 57939211448610773001791381 2715900536653629984458971)
          ·
            refine ⟨4073850804980444976688457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2715900536653629984458971 4073850804980444976688457)
            ·
              refine ⟨3055388103735333732516343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4073850804980444976688457 3055388103735333732516343)
              ·
                refine ⟨4583082155603000598774515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3055388103735333732516343 4583082155603000598774515)
                ·
                  refine ⟨6874623233404500898161773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4583082155603000598774515 6874623233404500898161773)
                  ·
                    refine ⟨2577983712526687836810665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6874623233404500898161773 2577983712526687836810665)
                    ·
                      refine ⟨1933487784395015877607999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2577983712526687836810665 1933487784395015877607999)
                      ·
                        rfl

theorem cell23_3765454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2].length) (baseStart_3765454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765454 prefixEnd_3765454 := by exact prefixLift 3765454
  have htrace : WordTrace (prefixWord ++ tailWord_3765454) baseStart_3765454 baseEnd_3765454 := by
    simpa [prefixWord, tailWord_3765454, baseEnd_3765454] using wordTrace_append hprefix tailTrace_3765454
  have hstable : (prefixWord ++ tailWord_3765454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765454).length < 2 ^ (prefixWord ++ tailWord_3765454).sum := by decide
  have hdescent : baseEnd_3765454 < baseStart_3765454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765476 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 1, 7, 2]
def baseStart_3765476 : Nat := 118140960795 + 3765476 * 2 ^ 59
def prefixEnd_3765476 : Nat := 4983230072969 + 3 ^ 40 * 3765476 * 2
def baseEnd_3765476 : Nat := 1933499080969414791532897

theorem tailTrace_3765476 : CollatzResearch.WordTrace tailWord_3765476 prefixEnd_3765476 1933499080969414791532897 := by
  unfold tailWord_3765476
  simp only [CollatzResearch.WordTrace]
  refine ⟨68669096253165509473366141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91558795004220679297821521 68669096253165509473366141)
  ·
    refine ⟨25750911094937066052512303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68669096253165509473366141 25750911094937066052512303)
    ·
      refine ⟨38626366642405599078768455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25750911094937066052512303 38626366642405599078768455)
      ·
        refine ⟨57939549963608398618152683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38626366642405599078768455 57939549963608398618152683)
        ·
          refine ⟨86909324945412597927229025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57939549963608398618152683 86909324945412597927229025)
          ·
            refine ⟨65181993709059448445421769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86909324945412597927229025 65181993709059448445421769)
            ·
              refine ⟨48886495281794586334066327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65181993709059448445421769 48886495281794586334066327)
              ·
                refine ⟨73329742922691879501099491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48886495281794586334066327 73329742922691879501099491)
                ·
                  refine ⟨109994614384037819251649237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73329742922691879501099491 109994614384037819251649237)
                  ·
                    refine ⟨2577998774625886388710529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 109994614384037819251649237 2577998774625886388710529)
                    ·
                      refine ⟨1933499080969414791532897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2577998774625886388710529 1933499080969414791532897)
                      ·
                        rfl

theorem cell23_3765476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 1, 7, 2].length) (baseStart_3765476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765476 prefixEnd_3765476 := by exact prefixLift 3765476
  have htrace : WordTrace (prefixWord ++ tailWord_3765476) baseStart_3765476 baseEnd_3765476 := by
    simpa [prefixWord, tailWord_3765476, baseEnd_3765476] using wordTrace_append hprefix tailTrace_3765476
  have hstable : (prefixWord ++ tailWord_3765476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765476).length < 2 ^ (prefixWord ++ tailWord_3765476).sum := by decide
  have hdescent : baseEnd_3765476 < baseStart_3765476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765613 : List Nat := [1, 5, 1, 1, 1, 3, 2, 1, 3, 1, 4]
def baseStart_3765613 : Nat := 118140960795 + 3765613 * 2 ^ 59
def prefixEnd_3765613 : Nat := 4983230072969 + 3 ^ 40 * 3765613 * 2
def baseEnd_3765613 : Nat := 1933569427819080755519767

theorem tailTrace_3765613 : CollatzResearch.WordTrace tailWord_3765613 prefixEnd_3765613 1933569427819080755519767 := by
  unfold tailWord_3765613
  simp only [CollatzResearch.WordTrace]
  refine ⟨137343189306834691344469493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91562126204556460896312995 137343189306834691344469493)
  ·
    refine ⟨12875923997515752313544015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137343189306834691344469493 12875923997515752313544015)
    ·
      refine ⟨19313885996273628470316023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12875923997515752313544015 19313885996273628470316023)
      ·
        refine ⟨28970828994410442705474035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19313885996273628470316023 28970828994410442705474035)
        ·
          refine ⟨43456243491615664058211053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28970828994410442705474035 43456243491615664058211053)
          ·
            refine ⟨16296091309355874021829145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43456243491615664058211053 16296091309355874021829145)
            ·
              refine ⟨12222068482016905516371859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16296091309355874021829145 12222068482016905516371859)
              ·
                refine ⟨18333102723025358274557789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12222068482016905516371859 18333102723025358274557789)
                ·
                  refine ⟨6874913521134509352959171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18333102723025358274557789 6874913521134509352959171)
                  ·
                    refine ⟨10312370281701764029438757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6874913521134509352959171 10312370281701764029438757)
                    ·
                      refine ⟨1933569427819080755519767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10312370281701764029438757 1933569427819080755519767)
                      ·
                        rfl

theorem cell23_3765613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_3765613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765613 prefixEnd_3765613 := by exact prefixLift 3765613
  have htrace : WordTrace (prefixWord ++ tailWord_3765613) baseStart_3765613 baseEnd_3765613 := by
    simpa [prefixWord, tailWord_3765613, baseEnd_3765613] using wordTrace_append hprefix tailTrace_3765613
  have hstable : (prefixWord ++ tailWord_3765613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765613).length < 2 ^ (prefixWord ++ tailWord_3765613).sum := by decide
  have hdescent : baseEnd_3765613 < baseStart_3765613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765636 : List Nat := [2, 3, 2, 1, 1, 4, 10]
def baseStart_3765636 : Nat := 118140960795 + 3765636 * 2 ^ 59
def prefixEnd_3765636 : Nat := 4983230072969 + 3 ^ 40 * 3765636 * 2
def baseEnd_3765636 : Nat := 23871373307088076117681

theorem tailTrace_3765636 : CollatzResearch.WordTrace tailWord_3765636 prefixEnd_3765636 23871373307088076117681 := by
  unfold tailWord_3765636
  simp only [CollatzResearch.WordTrace]
  refine ⟨68672014092875683136278381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91562685457167577515037841 68672014092875683136278381)
  ·
    refine ⟨25752005284828381176104393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68672014092875683136278381 25752005284828381176104393)
    ·
      refine ⟨19314003963621285882078295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25752005284828381176104393 19314003963621285882078295)
      ·
        refine ⟨28971005945431928823117443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19314003963621285882078295 28971005945431928823117443)
        ·
          refine ⟨43456508918147893234676165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28971005945431928823117443 43456508918147893234676165)
          ·
            refine ⟨8148095422152729981501781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43456508918147893234676165 8148095422152729981501781)
            ·
              refine ⟨23871373307088076117681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8148095422152729981501781 23871373307088076117681)
              ·
                rfl

theorem cell23_3765636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 10].length) (baseStart_3765636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765636 prefixEnd_3765636 := by exact prefixLift 3765636
  have htrace : WordTrace (prefixWord ++ tailWord_3765636) baseStart_3765636 baseEnd_3765636 := by
    simpa [prefixWord, tailWord_3765636, baseEnd_3765636] using wordTrace_append hprefix tailTrace_3765636
  have hstable : (prefixWord ++ tailWord_3765636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765636).length < 2 ^ (prefixWord ++ tailWord_3765636).sum := by decide
  have hdescent : baseEnd_3765636 < baseStart_3765636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765640 : List Nat := [2, 1, 3, 3, 1, 2, 3, 2, 2, 4]
def baseStart_3765640 : Nat := 118140960795 + 3765640 * 2 ^ 59
def prefixEnd_3765640 : Nat := 4983230072969 + 3 ^ 40 * 3765640 * 2
def baseEnd_3765640 : Nat := 644527763932250716627381

theorem tailTrace_3765640 : CollatzResearch.WordTrace tailWord_3765640 prefixEnd_3765640 644527763932250716627381 := by
  unfold tailWord_3765640
  simp only [CollatzResearch.WordTrace]
  refine ⟨68672087038868437477851187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91562782718491249970468249 68672087038868437477851187)
  ·
    refine ⟨103008130558302656216776781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68672087038868437477851187 103008130558302656216776781)
    ·
      refine ⟨38628048959363496081291293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103008130558302656216776781 38628048959363496081291293)
      ·
        refine ⟨14485518359761311030484235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38628048959363496081291293 14485518359761311030484235)
        ·
          refine ⟨21728277539641966545726353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14485518359761311030484235 21728277539641966545726353)
          ·
            refine ⟨16296208154731474909294765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21728277539641966545726353 16296208154731474909294765)
            ·
              refine ⟨6111078058024303090985537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16296208154731474909294765 6111078058024303090985537)
              ·
                refine ⟨4583308543518227318239153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6111078058024303090985537 4583308543518227318239153)
                ·
                  refine ⟨3437481407638670488679365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4583308543518227318239153 3437481407638670488679365)
                  ·
                    refine ⟨644527763932250716627381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3437481407638670488679365 644527763932250716627381)
                    ·
                      rfl

theorem cell23_3765640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_3765640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765640 prefixEnd_3765640 := by exact prefixLift 3765640
  have htrace : WordTrace (prefixWord ++ tailWord_3765640) baseStart_3765640 baseEnd_3765640 := by
    simpa [prefixWord, tailWord_3765640, baseEnd_3765640] using wordTrace_append hprefix tailTrace_3765640
  have hstable : (prefixWord ++ tailWord_3765640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765640).length < 2 ^ (prefixWord ++ tailWord_3765640).sum := by decide
  have hdescent : baseEnd_3765640 < baseStart_3765640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765660 : List Nat := [2, 2, 3, 4, 1, 1, 1, 1, 1, 1, 6]
def baseStart_3765660 : Nat := 118140960795 + 3765660 * 2 ^ 59
def prefixEnd_3765660 : Nat := 4983230072969 + 3 ^ 40 * 3765660 * 2
def baseEnd_3765660 : Nat := 1933593561409842071632051

theorem tailTrace_3765660 : CollatzResearch.WordTrace tailWord_3765660 prefixEnd_3765660 1933593561409842071632051 := by
  unfold tailWord_3765660
  simp only [CollatzResearch.WordTrace]
  refine ⟨68672451768832209185715217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91563269025109612247620289 68672451768832209185715217)
  ·
    refine ⟨51504338826624156889286413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68672451768832209185715217 51504338826624156889286413)
    ·
      refine ⟨19314127059984058833482405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51504338826624156889286413 19314127059984058833482405)
      ·
        refine ⟨3621398823747011031277951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19314127059984058833482405 3621398823747011031277951)
        ·
          refine ⟨5432098235620516546916927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3621398823747011031277951 5432098235620516546916927)
          ·
            refine ⟨8148147353430774820375391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5432098235620516546916927 8148147353430774820375391)
            ·
              refine ⟨12222221030146162230563087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8148147353430774820375391 12222221030146162230563087)
              ·
                refine ⟨18333331545219243345844631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12222221030146162230563087 18333331545219243345844631)
                ·
                  refine ⟨27499997317828865018766947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18333331545219243345844631 27499997317828865018766947)
                  ·
                    refine ⟨41249995976743297528150421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27499997317828865018766947 41249995976743297528150421)
                    ·
                      refine ⟨1933593561409842071632051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41249995976743297528150421 1933593561409842071632051)
                      ·
                        rfl

theorem cell23_3765660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_3765660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765660 prefixEnd_3765660 := by exact prefixLift 3765660
  have htrace : WordTrace (prefixWord ++ tailWord_3765660) baseStart_3765660 baseEnd_3765660 := by
    simpa [prefixWord, tailWord_3765660, baseEnd_3765660] using wordTrace_append hprefix tailTrace_3765660
  have hstable : (prefixWord ++ tailWord_3765660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765660).length < 2 ^ (prefixWord ++ tailWord_3765660).sum := by decide
  have hdescent : baseEnd_3765660 < baseStart_3765660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765676 : List Nat := [2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 5]
def baseStart_3765676 : Nat := 118140960795 + 3765676 * 2 ^ 59
def prefixEnd_3765676 : Nat := 4983230072969 + 3 ^ 40 * 3765676 * 2
def baseEnd_3765676 : Nat := 1933601777100314009031977

theorem tailTrace_3765676 : CollatzResearch.WordTrace tailWord_3765676 prefixEnd_3765676 1933601777100314009031977 := by
  unfold tailWord_3765676
  simp only [CollatzResearch.WordTrace]
  refine ⟨68672743552803226552006441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91563658070404302069341921 68672743552803226552006441)
  ·
    refine ⟨51504557664602419914004831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68672743552803226552006441 51504557664602419914004831)
    ·
      refine ⟨77256836496903629871007247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51504557664602419914004831 77256836496903629871007247)
      ·
        refine ⟨115885254745355444806510871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77256836496903629871007247 115885254745355444806510871)
        ·
          refine ⟨173827882118033167209766307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115885254745355444806510871 173827882118033167209766307)
          ·
            refine ⟨260741823177049750814649461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173827882118033167209766307 260741823177049750814649461)
            ·
              refine ⟨24444545922848414138873387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 260741823177049750814649461 24444545922848414138873387)
              ·
                refine ⟨36666818884272621208310081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24444545922848414138873387 36666818884272621208310081)
                ·
                  refine ⟨27500114163204465906232561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36666818884272621208310081 27500114163204465906232561)
                  ·
                    refine ⟨20625085622403349429674421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27500114163204465906232561 20625085622403349429674421)
                    ·
                      refine ⟨1933601777100314009031977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20625085622403349429674421 1933601777100314009031977)
                      ·
                        rfl

theorem cell23_3765676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_3765676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765676 prefixEnd_3765676 := by exact prefixLift 3765676
  have htrace : WordTrace (prefixWord ++ tailWord_3765676) baseStart_3765676 baseEnd_3765676 := by
    simpa [prefixWord, tailWord_3765676, baseEnd_3765676] using wordTrace_append hprefix tailTrace_3765676
  have hstable : (prefixWord ++ tailWord_3765676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765676).length < 2 ^ (prefixWord ++ tailWord_3765676).sum := by decide
  have hdescent : baseEnd_3765676 < baseStart_3765676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765696 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 4, 6]
def baseStart_3765696 : Nat := 118140960795 + 3765696 * 2 ^ 59
def prefixEnd_3765696 : Nat := 4983230072969 + 3 ^ 40 * 3765696 * 2
def baseEnd_3765696 : Nat := 644537348904467976927295

theorem tailTrace_3765696 : CollatzResearch.WordTrace tailWord_3765696 prefixEnd_3765696 644537348904467976927295 := by
  unfold tailWord_3765696
  simp only [CollatzResearch.WordTrace]
  refine ⟨68673108282766998259870471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91564144377022664346493961 68673108282766998259870471)
  ·
    refine ⟨103009662424150497389805707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68673108282766998259870471 103009662424150497389805707)
    ·
      refine ⟨154514493636225746084708561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103009662424150497389805707 154514493636225746084708561)
      ·
        refine ⟨115885870227169309563531421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154514493636225746084708561 115885870227169309563531421)
        ·
          refine ⟨43457201335188491086324283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115885870227169309563531421 43457201335188491086324283)
          ·
            refine ⟨65185802002782736629486425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43457201335188491086324283 65185802002782736629486425)
            ·
              refine ⟨48889351502087052472114819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65185802002782736629486425 48889351502087052472114819)
              ·
                refine ⟨73334027253130578708172229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48889351502087052472114819 73334027253130578708172229)
                ·
                  refine ⟨13750130109961983507782293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73334027253130578708172229 13750130109961983507782293)
                  ·
                    refine ⟨644537348904467976927295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13750130109961983507782293 644537348904467976927295)
                    ·
                      rfl

theorem cell23_3765696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 4, 6].length) (baseStart_3765696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765696 prefixEnd_3765696 := by exact prefixLift 3765696
  have htrace : WordTrace (prefixWord ++ tailWord_3765696) baseStart_3765696 baseEnd_3765696 := by
    simpa [prefixWord, tailWord_3765696, baseEnd_3765696] using wordTrace_append hprefix tailTrace_3765696
  have hstable : (prefixWord ++ tailWord_3765696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765696).length < 2 ^ (prefixWord ++ tailWord_3765696).sum := by decide
  have hdescent : baseEnd_3765696 < baseStart_3765696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765741 : List Nat := [1, 5, 1, 3, 2, 1, 3, 1, 1, 3, 2]
def baseStart_3765741 : Nat := 118140960795 + 3765741 * 2 ^ 59
def prefixEnd_3765741 : Nat := 4983230072969 + 3 ^ 40 * 3765741 * 2
def baseEnd_3765741 : Nat := 1933635153342856254719179

theorem tailTrace_3765741 : CollatzResearch.WordTrace tailWord_3765741 prefixEnd_3765741 1933635153342856254719179 := by
  unfold tailWord_3765741
  simp only [CollatzResearch.WordTrace]
  refine ⟨137347857850370969205129077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91565238566913979470086051 137347857850370969205129077)
  ·
    refine ⟨12876361673472278362980851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137347857850370969205129077 12876361673472278362980851)
    ·
      refine ⟨19314542510208417544471277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12876361673472278362980851 19314542510208417544471277)
      ·
        refine ⟨7242953441328156579176729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19314542510208417544471277 7242953441328156579176729)
        ·
          refine ⟨5432215080996117434382547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7242953441328156579176729 5432215080996117434382547)
          ·
            refine ⟨8148322621494176151573821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5432215080996117434382547 8148322621494176151573821)
            ·
              refine ⟨3055620983060316056840183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8148322621494176151573821 3055620983060316056840183)
              ·
                refine ⟨4583431474590474085260275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3055620983060316056840183 4583431474590474085260275)
                ·
                  refine ⟨6875147211885711127890413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4583431474590474085260275 6875147211885711127890413)
                  ·
                    refine ⟨2578180204457141672958905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6875147211885711127890413 2578180204457141672958905)
                    ·
                      refine ⟨1933635153342856254719179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2578180204457141672958905 1933635153342856254719179)
                      ·
                        rfl

theorem cell23_3765741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_3765741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765741 prefixEnd_3765741 := by exact prefixLift 3765741
  have htrace : WordTrace (prefixWord ++ tailWord_3765741) baseStart_3765741 baseEnd_3765741 := by
    simpa [prefixWord, tailWord_3765741, baseEnd_3765741] using wordTrace_append hprefix tailTrace_3765741
  have hstable : (prefixWord ++ tailWord_3765741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765741).length < 2 ^ (prefixWord ++ tailWord_3765741).sum := by decide
  have hdescent : baseEnd_3765741 < baseStart_3765741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765753 : List Nat := [1, 2, 1, 3, 1, 2, 1, 4, 2, 3, 3]
def baseStart_3765753 : Nat := 118140960795 + 3765753 * 2 ^ 59
def prefixEnd_3765753 : Nat := 4983230072969 + 3 ^ 40 * 3765753 * 2
def baseEnd_3765753 : Nat := 1933641315110710207769123

theorem tailTrace_3765753 : CollatzResearch.WordTrace tailWord_3765753 prefixEnd_3765753 1933641315110710207769123 := by
  unfold tailWord_3765753
  simp only [CollatzResearch.WordTrace]
  refine ⟨137348295526327495254565913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91565530350884996836377275 137348295526327495254565913)
  ·
    refine ⟨103011221644745621440924435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137348295526327495254565913 103011221644745621440924435)
    ·
      refine ⟨154516832467118432161386653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103011221644745621440924435 154516832467118432161386653)
      ·
        refine ⟨57943812175169412060519995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154516832467118432161386653 57943812175169412060519995)
        ·
          refine ⟨86915718262754118090779993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57943812175169412060519995 86915718262754118090779993)
          ·
            refine ⟨65186788697065588568084995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86915718262754118090779993 65186788697065588568084995)
            ·
              refine ⟨97780183045598382852127493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65186788697065588568084995 97780183045598382852127493)
              ·
                refine ⟨18333784321049696784773905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97780183045598382852127493 18333784321049696784773905)
                ·
                  refine ⟨13750338240787272588580429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18333784321049696784773905 13750338240787272588580429)
                  ·
                    refine ⟨5156376840295227220717661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13750338240787272588580429 5156376840295227220717661)
                    ·
                      refine ⟨1933641315110710207769123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5156376840295227220717661 1933641315110710207769123)
                      ·
                        rfl

theorem cell23_3765753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_3765753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765753 prefixEnd_3765753 := by exact prefixLift 3765753
  have htrace : WordTrace (prefixWord ++ tailWord_3765753) baseStart_3765753 baseEnd_3765753 := by
    simpa [prefixWord, tailWord_3765753, baseEnd_3765753] using wordTrace_append hprefix tailTrace_3765753
  have hstable : (prefixWord ++ tailWord_3765753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765753).length < 2 ^ (prefixWord ++ tailWord_3765753).sum := by decide
  have hdescent : baseEnd_3765753 < baseStart_3765753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765770 : List Nat := [3, 1, 2, 2, 2, 3, 1, 1, 2, 3, 3]
def baseStart_3765770 : Nat := 118140960795 + 3765770 * 2 ^ 59
def prefixEnd_3765770 : Nat := 4983230072969 + 3 ^ 40 * 3765770 * 2
def baseEnd_3765770 : Nat := 1933650044281836641256545

theorem tailTrace_3765770 : CollatzResearch.WordTrace tailWord_3765770 prefixEnd_3765770 1933650044281836641256545 := by
  unfold tailWord_3765770
  simp only [CollatzResearch.WordTrace]
  refine ⟨34337228891816476789483691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91565943711510604771956509 34337228891816476789483691)
  ·
    refine ⟨51505843337724715184225537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34337228891816476789483691 51505843337724715184225537)
    ·
      refine ⟨38629382503293536388169153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51505843337724715184225537 38629382503293536388169153)
      ·
        refine ⟨28972036877470152291126865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38629382503293536388169153 28972036877470152291126865)
        ·
          refine ⟨21729027658102614218345149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28972036877470152291126865 21729027658102614218345149)
          ·
            refine ⟨8148385371788480331879431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21729027658102614218345149 8148385371788480331879431)
            ·
              refine ⟨12222578057682720497819147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8148385371788480331879431 12222578057682720497819147)
              ·
                refine ⟨18333867086524080746728721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12222578057682720497819147 18333867086524080746728721)
                ·
                  refine ⟨13750400314893060560046541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18333867086524080746728721 13750400314893060560046541)
                  ·
                    refine ⟨5156400118084897710017453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13750400314893060560046541 5156400118084897710017453)
                    ·
                      refine ⟨1933650044281836641256545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5156400118084897710017453 1933650044281836641256545)
                      ·
                        rfl

theorem cell23_3765770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_3765770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765770 prefixEnd_3765770 := by exact prefixLift 3765770
  have htrace : WordTrace (prefixWord ++ tailWord_3765770) baseStart_3765770 baseEnd_3765770 := by
    simpa [prefixWord, tailWord_3765770, baseEnd_3765770] using wordTrace_append hprefix tailTrace_3765770
  have hstable : (prefixWord ++ tailWord_3765770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765770).length < 2 ^ (prefixWord ++ tailWord_3765770).sum := by decide
  have hdescent : baseEnd_3765770 < baseStart_3765770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765776 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 8]
def baseStart_3765776 : Nat := 118140960795 + 3765776 * 2 ^ 59
def prefixEnd_3765776 : Nat := 4983230072969 + 3 ^ 40 * 3765776 * 2
def baseEnd_3765776 : Nat := 1933653125165763617781517

theorem tailTrace_3765776 : CollatzResearch.WordTrace tailWord_3765776 prefixEnd_3765776 1933653125165763617781517 := by
  unfold tailWord_3765776
  simp only [CollatzResearch.WordTrace]
  refine ⟨68674567202622085091326591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91566089603496113455102121 68674567202622085091326591)
  ·
    refine ⟨103011850803933127636989887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68674567202622085091326591 103011850803933127636989887)
    ·
      refine ⟨154517776205899691455484831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103011850803933127636989887 154517776205899691455484831)
      ·
        refine ⟨231776664308849537183227247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154517776205899691455484831 231776664308849537183227247)
        ·
          refine ⟨347664996463274305774840871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231776664308849537183227247 347664996463274305774840871)
          ·
            refine ⟨521497494694911458662261307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347664996463274305774840871 521497494694911458662261307)
            ·
              refine ⟨782246242042367187993391961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 521497494694911458662261307 782246242042367187993391961)
              ·
                refine ⟨586684681531775390995043971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 782246242042367187993391961 586684681531775390995043971)
                ·
                  refine ⟨880027022297663086492565957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 586684681531775390995043971 880027022297663086492565957)
                  ·
                    refine ⟨165005066680811828717356117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 880027022297663086492565957 165005066680811828717356117)
                    ·
                      refine ⟨1933653125165763617781517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 165005066680811828717356117 1933653125165763617781517)
                      ·
                        rfl

theorem cell23_3765776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 8].length) (baseStart_3765776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765776 prefixEnd_3765776 := by exact prefixLift 3765776
  have htrace : WordTrace (prefixWord ++ tailWord_3765776) baseStart_3765776 baseEnd_3765776 := by
    simpa [prefixWord, tailWord_3765776, baseEnd_3765776] using wordTrace_append hprefix tailTrace_3765776
  have hstable : (prefixWord ++ tailWord_3765776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765776).length < 2 ^ (prefixWord ++ tailWord_3765776).sum := by decide
  have hdescent : baseEnd_3765776 < baseStart_3765776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765833 : List Nat := [1, 2, 1, 1, 2, 2, 1, 7, 6]
def baseStart_3765833 : Nat := 118140960795 + 3765833 * 2 ^ 59
def prefixEnd_3765833 : Nat := 4983230072969 + 3 ^ 40 * 3765833 * 2
def baseEnd_3765833 : Nat := 214853599284785543863195

theorem tailTrace_3765833 : CollatzResearch.WordTrace tailWord_3765833 prefixEnd_3765833 214853599284785543863195 := by
  unfold tailWord_3765833
  simp only [CollatzResearch.WordTrace]
  refine ⟨137351213366037668917478153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91567475577358445944985435 137351213366037668917478153)
  ·
    refine ⟨103013410024528251688108615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137351213366037668917478153 103013410024528251688108615)
    ·
      refine ⟨154520115036792377532162923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103013410024528251688108615 154520115036792377532162923)
      ·
        refine ⟨231780172555188566298244385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154520115036792377532162923 231780172555188566298244385)
        ·
          refine ⟨173835129416391424723683289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231780172555188566298244385 173835129416391424723683289)
          ·
            refine ⟨130376347062293568542762467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173835129416391424723683289 130376347062293568542762467)
            ·
              refine ⟨195564520593440352814143701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130376347062293568542762467 195564520593440352814143701)
              ·
                refine ⟨4583543451408758269081493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 195564520593440352814143701 4583543451408758269081493)
                ·
                  refine ⟨214853599284785543863195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4583543451408758269081493 214853599284785543863195)
                  ·
                    rfl

theorem cell23_3765833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 6].length) (baseStart_3765833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765833 prefixEnd_3765833 := by exact prefixLift 3765833
  have htrace : WordTrace (prefixWord ++ tailWord_3765833) baseStart_3765833 baseEnd_3765833 := by
    simpa [prefixWord, tailWord_3765833, baseEnd_3765833] using wordTrace_append hprefix tailTrace_3765833
  have hstable : (prefixWord ++ tailWord_3765833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765833).length < 2 ^ (prefixWord ++ tailWord_3765833).sum := by decide
  have hdescent : baseEnd_3765833 < baseStart_3765833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765900 : List Nat := [2, 2, 1, 2, 1, 1, 5, 1, 3, 1, 4]
def baseStart_3765900 : Nat := 118140960795 + 3765900 * 2 ^ 59
def prefixEnd_3765900 : Nat := 4983230072969 + 3 ^ 40 * 3765900 * 2
def baseEnd_3765900 : Nat := 1933716796766921132630947

theorem tailTrace_3765900 : CollatzResearch.WordTrace tailWord_3765900 prefixEnd_3765900 1933716796766921132630947 := by
  unfold tailWord_3765900
  simp only [CollatzResearch.WordTrace]
  refine ⟨68676828528397469680083577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91569104704529959573444769 68676828528397469680083577)
  ·
    refine ⟨51507621396298102260062683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68676828528397469680083577 51507621396298102260062683)
    ·
      refine ⟨77261432094447153390094025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51507621396298102260062683 77261432094447153390094025)
      ·
        refine ⟨57946074070835365042570519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77261432094447153390094025 57946074070835365042570519)
        ·
          refine ⟨86919111106253047563855779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57946074070835365042570519 86919111106253047563855779)
          ·
            refine ⟨130378666659379571345783669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86919111106253047563855779 130378666659379571345783669)
            ·
              refine ⟨12222999999316834813667219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130378666659379571345783669 12222999999316834813667219)
              ·
                refine ⟨18334499998975252220500829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12222999999316834813667219 18334499998975252220500829)
                ·
                  refine ⟨6875437499615719582687811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18334499998975252220500829 6875437499615719582687811)
                  ·
                    refine ⟨10313156249423579374031717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6875437499615719582687811 10313156249423579374031717)
                    ·
                      refine ⟨1933716796766921132630947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10313156249423579374031717 1933716796766921132630947)
                      ·
                        rfl

theorem cell23_3765900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_3765900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765900 prefixEnd_3765900 := by exact prefixLift 3765900
  have htrace : WordTrace (prefixWord ++ tailWord_3765900) baseStart_3765900 baseEnd_3765900 := by
    simpa [prefixWord, tailWord_3765900, baseEnd_3765900] using wordTrace_append hprefix tailTrace_3765900
  have hstable : (prefixWord ++ tailWord_3765900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765900).length < 2 ^ (prefixWord ++ tailWord_3765900).sum := by decide
  have hdescent : baseEnd_3765900 < baseStart_3765900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765913 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 3, 1, 6]
def baseStart_3765913 : Nat := 118140960795 + 3765913 * 2 ^ 59
def prefixEnd_3765913 : Nat := 4983230072969 + 3 ^ 40 * 3765913 * 2
def baseEnd_3765913 : Nat := 1933723472015429581768387

theorem tailTrace_3765913 : CollatzResearch.WordTrace tailWord_3765913 prefixEnd_3765913 1933723472015429581768387 := by
  unfold tailWord_3765913
  simp only [CollatzResearch.WordTrace]
  refine ⟨137354131205747842580390393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91569420803831895053593595 137354131205747842580390393)
  ·
    refine ⟨103015598404310881935292795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137354131205747842580390393 103015598404310881935292795)
    ·
      refine ⟨154523397606466322902939193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103015598404310881935292795 154523397606466322902939193)
      ·
        refine ⟨115892548204849742177204395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154523397606466322902939193 115892548204849742177204395)
        ·
          refine ⟨173838822307274613265806593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115892548204849742177204395 173838822307274613265806593)
          ·
            refine ⟨130379116730455959949354945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173838822307274613265806593 130379116730455959949354945)
            ·
              refine ⟨97784337547841969962016209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130379116730455959949354945 97784337547841969962016209)
              ·
                refine ⟨73338253160881477471512157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97784337547841969962016209 73338253160881477471512157)
                ·
                  refine ⟨27501844935330554051817059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73338253160881477471512157 27501844935330554051817059)
                  ·
                    refine ⟨41252767402995831077725589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27501844935330554051817059 41252767402995831077725589)
                    ·
                      refine ⟨1933723472015429581768387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41252767402995831077725589 1933723472015429581768387)
                      ·
                        rfl

theorem cell23_3765913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_3765913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765913 prefixEnd_3765913 := by exact prefixLift 3765913
  have htrace : WordTrace (prefixWord ++ tailWord_3765913) baseStart_3765913 baseEnd_3765913 := by
    simpa [prefixWord, tailWord_3765913, baseEnd_3765913] using wordTrace_append hprefix tailTrace_3765913
  have hstable : (prefixWord ++ tailWord_3765913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765913).length < 2 ^ (prefixWord ++ tailWord_3765913).sum := by decide
  have hdescent : baseEnd_3765913 < baseStart_3765913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765974 : List Nat := [5, 2, 1, 3, 1, 1, 10]
def baseStart_3765974 : Nat := 118140960795 + 3765974 * 2 ^ 59
def prefixEnd_3765974 : Nat := 4983230072969 + 3 ^ 40 * 3765974 * 2
def baseEnd_3765974 : Nat := 23873515979448812877847

theorem tailTrace_3765974 : CollatzResearch.WordTrace tailWord_3765974 prefixEnd_3765974 23873515979448812877847 := by
  unfold tailWord_3765974
  simp only [CollatzResearch.WordTrace]
  refine ⟨8584772253657928124897561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91570904039017899998907317 8584772253657928124897561)
  ·
    refine ⟨6438579190243446093673171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8584772253657928124897561 6438579190243446093673171)
    ·
      refine ⟨9657868785365169140509757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6438579190243446093673171 9657868785365169140509757)
      ·
        refine ⟨3621700794511938427691159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9657868785365169140509757 3621700794511938427691159)
        ·
          refine ⟨5432551191767907641536739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3621700794511938427691159 5432551191767907641536739)
          ·
            refine ⟨8148826787651861462305109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5432551191767907641536739 8148826787651861462305109)
            ·
              refine ⟨23873515979448812877847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8148826787651861462305109 23873515979448812877847)
              ·
                rfl

theorem cell23_3765974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 10].length) (baseStart_3765974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765974 prefixEnd_3765974 := by exact prefixLift 3765974
  have htrace : WordTrace (prefixWord ++ tailWord_3765974) baseStart_3765974 baseEnd_3765974 := by
    simpa [prefixWord, tailWord_3765974, baseEnd_3765974] using wordTrace_append hprefix tailTrace_3765974
  have hstable : (prefixWord ++ tailWord_3765974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765974).length < 2 ^ (prefixWord ++ tailWord_3765974).sum := by decide
  have hdescent : baseEnd_3765974 < baseStart_3765974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765984 : List Nat := [2, 1, 1, 3, 1, 2, 5, 2, 2, 1, 3]
def baseStart_3765984 : Nat := 118140960795 + 3765984 * 2 ^ 59
def prefixEnd_3765984 : Nat := 4983230072969 + 3 ^ 40 * 3765984 * 2
def baseEnd_3765984 : Nat := 1933759929141898803980561

theorem tailTrace_3765984 : CollatzResearch.WordTrace tailWord_3765984 prefixEnd_3765984 1933759929141898803980561 := by
  unfold tailWord_3765984
  simp only [CollatzResearch.WordTrace]
  refine ⟨68678360394245310853112503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91571147192327081137483337 68678360394245310853112503)
  ·
    refine ⟨103017540591367966279668755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68678360394245310853112503 103017540591367966279668755)
    ·
      refine ⟨154526310887051949419503133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103017540591367966279668755 154526310887051949419503133)
      ·
        refine ⟨57947366582644481032313675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154526310887051949419503133 57947366582644481032313675)
        ·
          refine ⟨86921049873966721548470513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57947366582644481032313675 86921049873966721548470513)
          ·
            refine ⟨65190787405475041161352885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86921049873966721548470513 65190787405475041161352885)
            ·
              refine ⟨6111636319263285108876833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65190787405475041161352885 6111636319263285108876833)
              ·
                refine ⟨4583727239447463831657625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6111636319263285108876833 4583727239447463831657625)
                ·
                  refine ⟨3437795429585597873743219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4583727239447463831657625 3437795429585597873743219)
                  ·
                    refine ⟨5156693144378396810614829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3437795429585597873743219 5156693144378396810614829)
                    ·
                      refine ⟨1933759929141898803980561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5156693144378396810614829 1933759929141898803980561)
                      ·
                        rfl

theorem cell23_3765984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 2, 1, 3].length) (baseStart_3765984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3765984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3765984 prefixEnd_3765984 := by exact prefixLift 3765984
  have htrace : WordTrace (prefixWord ++ tailWord_3765984) baseStart_3765984 baseEnd_3765984 := by
    simpa [prefixWord, tailWord_3765984, baseEnd_3765984] using wordTrace_append hprefix tailTrace_3765984
  have hstable : (prefixWord ++ tailWord_3765984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765984).length < 2 ^ (prefixWord ++ tailWord_3765984).sum := by decide
  have hdescent : baseEnd_3765984 < baseStart_3765984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766001 : List Nat := [1, 2, 2, 2, 2, 4, 3, 1, 2, 1, 3]
def baseStart_3766001 : Nat := 118140960795 + 3766001 * 2 ^ 59
def prefixEnd_3766001 : Nat := 4983230072969 + 3 ^ 40 * 3766001 * 2
def baseEnd_3766001 : Nat := 1933768658313025237467983

theorem tailTrace_3766001 : CollatzResearch.WordTrace tailWord_3766001 prefixEnd_3766001 1933768658313025237467983 := by
  unfold tailWord_3766001
  simp only [CollatzResearch.WordTrace]
  refine ⟨137357340829429033609593857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91571560552952689073062571 137357340829429033609593857)
  ·
    refine ⟨103018005622071775207195393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137357340829429033609593857 103018005622071775207195393)
    ·
      refine ⟨77263504216553831405396545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103018005622071775207195393 77263504216553831405396545)
      ·
        refine ⟨57947628162415373554047409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77263504216553831405396545 57947628162415373554047409)
        ·
          refine ⟨43460721121811530165535557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57947628162415373554047409 43460721121811530165535557)
          ·
            refine ⟨8148885210339661906037917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43460721121811530165535557 8148885210339661906037917)
            ·
              refine ⟨3055831953877373214764219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8148885210339661906037917 3055831953877373214764219)
              ·
                refine ⟨4583747930816059822146329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3055831953877373214764219 4583747930816059822146329)
                ·
                  refine ⟨3437810948112044866609747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4583747930816059822146329 3437810948112044866609747)
                  ·
                    refine ⟨5156716422168067299914621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3437810948112044866609747 5156716422168067299914621)
                    ·
                      refine ⟨1933768658313025237467983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5156716422168067299914621 1933768658313025237467983)
                      ·
                        rfl

theorem cell23_3766001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 2, 1, 3].length) (baseStart_3766001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766001 prefixEnd_3766001 := by exact prefixLift 3766001
  have htrace : WordTrace (prefixWord ++ tailWord_3766001) baseStart_3766001 baseEnd_3766001 := by
    simpa [prefixWord, tailWord_3766001, baseEnd_3766001] using wordTrace_append hprefix tailTrace_3766001
  have hstable : (prefixWord ++ tailWord_3766001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766001).length < 2 ^ (prefixWord ++ tailWord_3766001).sum := by decide
  have hdescent : baseEnd_3766001 < baseStart_3766001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766010 : List Nat := [3, 1, 1, 1, 1, 3, 1, 4, 2, 1, 5]
def baseStart_3766010 : Nat := 118140960795 + 3766010 * 2 ^ 59
def prefixEnd_3766010 : Nat := 4983230072969 + 3 ^ 40 * 3766010 * 2
def baseEnd_3766010 : Nat := 1933773279638915702255441

theorem tailTrace_3766010 : CollatzResearch.WordTrace tailWord_3766010 prefixEnd_3766010 1933773279638915702255441 := by
  unfold tailWord_3766010
  simp only [CollatzResearch.WordTrace]
  refine ⟨34339417271599107036667871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91571779390930952097780989 34339417271599107036667871)
  ·
    refine ⟨51509125907398660555001807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34339417271599107036667871 51509125907398660555001807)
    ·
      refine ⟨77263688861097990832502711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51509125907398660555001807 77263688861097990832502711)
      ·
        refine ⟨115895533291646986248754067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77263688861097990832502711 115895533291646986248754067)
        ·
          refine ⟨173843299937470479373131101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115895533291646986248754067 173843299937470479373131101)
          ·
            refine ⟨65191237476551429764924163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173843299937470479373131101 65191237476551429764924163)
            ·
              refine ⟨97786856214827144647386245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65191237476551429764924163 97786856214827144647386245)
              ·
                refine ⟨18335035540280089621384921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97786856214827144647386245 18335035540280089621384921)
                ·
                  refine ⟨13751276655210067216038691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18335035540280089621384921 13751276655210067216038691)
                  ·
                    refine ⟨20626914982815100824058037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13751276655210067216038691 20626914982815100824058037)
                    ·
                      refine ⟨1933773279638915702255441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20626914982815100824058037 1933773279638915702255441)
                      ·
                        rfl

theorem cell23_3766010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_3766010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766010 prefixEnd_3766010 := by exact prefixLift 3766010
  have htrace : WordTrace (prefixWord ++ tailWord_3766010) baseStart_3766010 baseEnd_3766010 := by
    simpa [prefixWord, tailWord_3766010, baseEnd_3766010] using wordTrace_append hprefix tailTrace_3766010
  have hstable : (prefixWord ++ tailWord_3766010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766010).length < 2 ^ (prefixWord ++ tailWord_3766010).sum := by decide
  have hdescent : baseEnd_3766010 < baseStart_3766010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766024 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 6, 2, 2]
def baseStart_3766024 : Nat := 118140960795 + 3766024 * 2 ^ 59
def prefixEnd_3766024 : Nat := 4983230072969 + 3 ^ 40 * 3766024 * 2
def baseEnd_3766024 : Nat := 1933780468368078647480377

theorem tailTrace_3766024 : CollatzResearch.WordTrace tailWord_3766024 prefixEnd_3766024 1933780468368078647480377 := by
  unfold tailWord_3766024
  simp only [CollatzResearch.WordTrace]
  refine ⟨68679089854172854268840563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91572119805563805691787417 68679089854172854268840563)
  ·
    refine ⟨103018634781259281403260845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68679089854172854268840563 103018634781259281403260845)
    ·
      refine ⟨38631988042972230526222817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103018634781259281403260845 38631988042972230526222817)
      ·
        refine ⟨28973991032229172894667113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38631988042972230526222817 28973991032229172894667113)
        ·
          refine ⟨21730493274171879671000335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28973991032229172894667113 21730493274171879671000335)
          ·
            refine ⟨32595739911257819506500503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21730493274171879671000335 32595739911257819506500503)
            ·
              refine ⟨48893609866886729259750755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32595739911257819506500503 48893609866886729259750755)
              ·
                refine ⟨73340414800330093889626133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48893609866886729259750755 73340414800330093889626133)
                ·
                  refine ⟨3437831943765473151076225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73340414800330093889626133 3437831943765473151076225)
                  ·
                    refine ⟨2578373957824104863307169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3437831943765473151076225 2578373957824104863307169)
                    ·
                      refine ⟨1933780468368078647480377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2578373957824104863307169 1933780468368078647480377)
                      ·
                        rfl

theorem cell23_3766024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_3766024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766024 prefixEnd_3766024 := by exact prefixLift 3766024
  have htrace : WordTrace (prefixWord ++ tailWord_3766024) baseStart_3766024 baseEnd_3766024 := by
    simpa [prefixWord, tailWord_3766024, baseEnd_3766024] using wordTrace_append hprefix tailTrace_3766024
  have hstable : (prefixWord ++ tailWord_3766024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766024).length < 2 ^ (prefixWord ++ tailWord_3766024).sum := by decide
  have hdescent : baseEnd_3766024 < baseStart_3766024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766030 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 9]
def baseStart_3766030 : Nat := 118140960795 + 3766030 * 2 ^ 59
def prefixEnd_3766030 : Nat := 4983230072969 + 3 ^ 40 * 3766030 * 2
def baseEnd_3766030 : Nat := 214864838805778402667261

theorem tailTrace_3766030 : CollatzResearch.WordTrace tailWord_3766030 prefixEnd_3766030 214864838805778402667261 := by
  unfold tailWord_3766030
  simp only [CollatzResearch.WordTrace]
  refine ⟨17169799818290496445299943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91572265697549314374933029 17169799818290496445299943)
  ·
    refine ⟨25754699727435744667949915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17169799818290496445299943 25754699727435744667949915)
    ·
      refine ⟨38632049591153617001924873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25754699727435744667949915 38632049591153617001924873)
      ·
        refine ⟨28974037193365212751443655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38632049591153617001924873 28974037193365212751443655)
        ·
          refine ⟨43461055790047819127165483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28974037193365212751443655 43461055790047819127165483)
          ·
            refine ⟨65191583685071728690748225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43461055790047819127165483 65191583685071728690748225)
            ·
              refine ⟨48893687763803796518061169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65191583685071728690748225 48893687763803796518061169)
              ·
                refine ⟨36670265822852847388545877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48893687763803796518061169 36670265822852847388545877)
                ·
                  refine ⟨214864838805778402667261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 36670265822852847388545877 214864838805778402667261)
                  ·
                    rfl

theorem cell23_3766030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 9].length) (baseStart_3766030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766030 prefixEnd_3766030 := by exact prefixLift 3766030
  have htrace : WordTrace (prefixWord ++ tailWord_3766030) baseStart_3766030 baseEnd_3766030 := by
    simpa [prefixWord, tailWord_3766030, baseEnd_3766030] using wordTrace_append hprefix tailTrace_3766030
  have hstable : (prefixWord ++ tailWord_3766030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766030).length < 2 ^ (prefixWord ++ tailWord_3766030).sum := by decide
  have hdescent : baseEnd_3766030 < baseStart_3766030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766117 : List Nat := [1, 3, 1, 3, 1, 1, 1, 4, 1, 4, 3]
def baseStart_3766117 : Nat := 118140960795 + 3766117 * 2 ^ 59
def prefixEnd_3766117 : Nat := 4983230072969 + 3 ^ 40 * 3766117 * 2
def baseEnd_3766117 : Nat := 1933828222068946783617449

theorem tailTrace_3766117 : CollatzResearch.WordTrace tailWord_3766117 prefixEnd_3766117 1933828222068946783617449 := by
  unfold tailWord_3766117
  simp only [CollatzResearch.WordTrace]
  refine ⟨137361571697008785420816605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91574381131339190280544403 137361571697008785420816605)
  ·
    refine ⟨51510589386378294532806227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137361571697008785420816605 51510589386378294532806227)
    ·
      refine ⟨77265884079567441799209341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51510589386378294532806227 77265884079567441799209341)
      ·
        refine ⟨28974706529837790674703503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77265884079567441799209341 28974706529837790674703503)
        ·
          refine ⟨43462059794756686012055255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28974706529837790674703503 43462059794756686012055255)
          ·
            refine ⟨65193089692135029018082883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43462059794756686012055255 65193089692135029018082883)
            ·
              refine ⟨97789634538202543527124325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65193089692135029018082883 97789634538202543527124325)
              ·
                refine ⟨18335556475912976911335811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97789634538202543527124325 18335556475912976911335811)
                ·
                  refine ⟨27503334713869465367003717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18335556475912976911335811 27503334713869465367003717)
                  ·
                    refine ⟨5156875258850524756313197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27503334713869465367003717 5156875258850524756313197)
                    ·
                      refine ⟨1933828222068946783617449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5156875258850524756313197 1933828222068946783617449)
                      ·
                        rfl

theorem cell23_3766117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_3766117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766117 prefixEnd_3766117 := by exact prefixLift 3766117
  have htrace : WordTrace (prefixWord ++ tailWord_3766117) baseStart_3766117 baseEnd_3766117 := by
    simpa [prefixWord, tailWord_3766117, baseEnd_3766117] using wordTrace_append hprefix tailTrace_3766117
  have hstable : (prefixWord ++ tailWord_3766117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766117).length < 2 ^ (prefixWord ++ tailWord_3766117).sum := by decide
  have hdescent : baseEnd_3766117 < baseStart_3766117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766124 : List Nat := [2, 2, 1, 1, 4, 3, 1, 2, 3, 4]
def baseStart_3766124 : Nat := 118140960795 + 3766124 * 2 ^ 59
def prefixEnd_3766124 : Nat := 4983230072969 + 3 ^ 40 * 3766124 * 2
def baseEnd_3766124 : Nat := 644610605477842752076639

theorem tailTrace_3766124 : CollatzResearch.WordTrace tailWord_3766124 prefixEnd_3766124 644610605477842752076639 := by
  unfold tailWord_3766124
  simp only [CollatzResearch.WordTrace]
  refine ⟨68680913503991712808160713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91574551338655617077547617 68680913503991712808160713)
  ·
    refine ⟨51510685127993784606120535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68680913503991712808160713 51510685127993784606120535)
    ·
      refine ⟨77266027691990676909180803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51510685127993784606120535 77266027691990676909180803)
      ·
        refine ⟨115899041537986015363771205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77266027691990676909180803 115899041537986015363771205)
        ·
          refine ⟨21731070288372377880707101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115899041537986015363771205 21731070288372377880707101)
          ·
            refine ⟨8149151358139641705265163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21731070288372377880707101 8149151358139641705265163)
            ·
              refine ⟨12223727037209462557897745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8149151358139641705265163 12223727037209462557897745)
              ·
                refine ⟨9167795277907096918423309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12223727037209462557897745 9167795277907096918423309)
                ·
                  refine ⟨3437923229215161344408741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9167795277907096918423309 3437923229215161344408741)
                  ·
                    refine ⟨644610605477842752076639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3437923229215161344408741 644610605477842752076639)
                    ·
                      rfl

theorem cell23_3766124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 4].length) (baseStart_3766124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766124 prefixEnd_3766124 := by exact prefixLift 3766124
  have htrace : WordTrace (prefixWord ++ tailWord_3766124) baseStart_3766124 baseEnd_3766124 := by
    simpa [prefixWord, tailWord_3766124, baseEnd_3766124] using wordTrace_append hprefix tailTrace_3766124
  have hstable : (prefixWord ++ tailWord_3766124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766124).length < 2 ^ (prefixWord ++ tailWord_3766124).sum := by decide
  have hdescent : baseEnd_3766124 < baseStart_3766124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766154 : List Nat := [3, 1, 2, 4, 2, 1, 1, 1, 8]
def baseStart_3766154 : Nat := 118140960795 + 3766154 * 2 ^ 59
def prefixEnd_3766154 : Nat := 4983230072969 + 3 ^ 40 * 3766154 * 2
def baseEnd_3766154 : Nat := 214871913428129237650531

theorem tailTrace_3766154 : CollatzResearch.WordTrace tailWord_3766154 prefixEnd_3766154 214871913428129237650531 := by
  unfold tailWord_3766154
  simp only [CollatzResearch.WordTrace]
  refine ⟨34340730299468685184978379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91575280798583160493275677 34340730299468685184978379)
  ·
    refine ⟨51511095449203027777467569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34340730299468685184978379 51511095449203027777467569)
    ·
      refine ⟨38633321586902270833100677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51511095449203027777467569 38633321586902270833100677)
      ·
        refine ⟨7243747797544175781206377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38633321586902270833100677 7243747797544175781206377)
        ·
          refine ⟨5432810848158131835904783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7243747797544175781206377 5432810848158131835904783)
          ·
            refine ⟨8149216272237197753857175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5432810848158131835904783 8149216272237197753857175)
            ·
              refine ⟨12223824408355796630785763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8149216272237197753857175 12223824408355796630785763)
              ·
                refine ⟨18335736612533694946178645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12223824408355796630785763 18335736612533694946178645)
                ·
                  refine ⟨214871913428129237650531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18335736612533694946178645 214871913428129237650531)
                  ·
                    rfl

theorem cell23_3766154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 8].length) (baseStart_3766154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766154 prefixEnd_3766154 := by exact prefixLift 3766154
  have htrace : WordTrace (prefixWord ++ tailWord_3766154) baseStart_3766154 baseEnd_3766154 := by
    simpa [prefixWord, tailWord_3766154, baseEnd_3766154] using wordTrace_append hprefix tailTrace_3766154
  have hstable : (prefixWord ++ tailWord_3766154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766154).length < 2 ^ (prefixWord ++ tailWord_3766154).sum := by decide
  have hdescent : baseEnd_3766154 < baseStart_3766154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766158 : List Nat := [4, 1, 1, 5, 1, 1, 2, 1, 3, 4]
def baseStart_3766158 : Nat := 118140960795 + 3766158 * 2 ^ 59
def prefixEnd_3766158 : Nat := 4983230072969 + 3 ^ 40 * 3766158 * 2
def baseEnd_3766158 : Nat := 644616424925260374401587

theorem tailTrace_3766158 : CollatzResearch.WordTrace tailWord_3766158 prefixEnd_3766158 644616424925260374401587 := by
  unfold tailWord_3766158
  simp only [CollatzResearch.WordTrace]
  refine ⟨17170383386232531177882391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91575378059906832948706085 17170383386232531177882391)
  ·
    refine ⟨25755575079348796766823587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17170383386232531177882391 25755575079348796766823587)
    ·
      refine ⟨38633362619023195150235381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25755575079348796766823587 38633362619023195150235381)
      ·
        refine ⟨3621877745533424545334567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38633362619023195150235381 3621877745533424545334567)
        ·
          refine ⟨5432816618300136818001851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3621877745533424545334567 5432816618300136818001851)
          ·
            refine ⟨8149224927450205227002777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5432816618300136818001851 8149224927450205227002777)
            ·
              refine ⟨6111918695587653920252083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8149224927450205227002777 6111918695587653920252083)
              ·
                refine ⟨9167878043381480880378125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6111918695587653920252083 9167878043381480880378125)
                ·
                  refine ⟨3437954266268055330141797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9167878043381480880378125 3437954266268055330141797)
                  ·
                    refine ⟨644616424925260374401587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3437954266268055330141797 644616424925260374401587)
                    ·
                      rfl

theorem cell23_3766158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_3766158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766158 prefixEnd_3766158 := by exact prefixLift 3766158
  have htrace : WordTrace (prefixWord ++ tailWord_3766158) baseStart_3766158 baseEnd_3766158 := by
    simpa [prefixWord, tailWord_3766158, baseEnd_3766158] using wordTrace_append hprefix tailTrace_3766158
  have hstable : (prefixWord ++ tailWord_3766158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766158).length < 2 ^ (prefixWord ++ tailWord_3766158).sum := by decide
  have hdescent : baseEnd_3766158 < baseStart_3766158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766217 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 3, 2, 4]
def baseStart_3766217 : Nat := 118140960795 + 3766217 * 2 ^ 59
def prefixEnd_3766217 : Nat := 4983230072969 + 3 ^ 40 * 3766217 * 2
def baseEnd_3766217 : Nat := 1933879570134396392366989

theorem tailTrace_3766217 : CollatzResearch.WordTrace tailWord_3766217 prefixEnd_3766217 1933879570134396392366989 := by
  unfold tailWord_3766217
  simp only [CollatzResearch.WordTrace]
  refine ⟨137365218996646502499456905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91576812664431001666304603 137365218996646502499456905)
  ·
    refine ⟨103023914247484876874592679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137365218996646502499456905 103023914247484876874592679)
    ·
      refine ⟨154535871371227315311889019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103023914247484876874592679 154535871371227315311889019)
      ·
        refine ⟨231803807056840972967833529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154535871371227315311889019 231803807056840972967833529)
        ·
          refine ⟨173852855292630729725875147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231803807056840972967833529 173852855292630729725875147)
          ·
            refine ⟨260779282938946094588812721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173852855292630729725875147 260779282938946094588812721)
            ·
              refine ⟨195584462204209570941609541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260779282938946094588812721 195584462204209570941609541)
              ·
                refine ⟨36672086663289294551551789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195584462204209570941609541 36672086663289294551551789)
                ·
                  refine ⟨13752032498733485456831921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36672086663289294551551789 13752032498733485456831921)
                  ·
                    refine ⟨10314024374050114092623941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13752032498733485456831921 10314024374050114092623941)
                    ·
                      refine ⟨1933879570134396392366989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10314024374050114092623941 1933879570134396392366989)
                      ·
                        rfl

theorem cell23_3766217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 2, 4].length) (baseStart_3766217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766217 prefixEnd_3766217 := by exact prefixLift 3766217
  have htrace : WordTrace (prefixWord ++ tailWord_3766217) baseStart_3766217 baseEnd_3766217 := by
    simpa [prefixWord, tailWord_3766217, baseEnd_3766217] using wordTrace_append hprefix tailTrace_3766217
  have hstable : (prefixWord ++ tailWord_3766217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766217).length < 2 ^ (prefixWord ++ tailWord_3766217).sum := by decide
  have hdescent : baseEnd_3766217 < baseStart_3766217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766241 : List Nat := [1, 2, 3, 1, 2, 1, 5, 2, 1, 2, 3]
def baseStart_3766241 : Nat := 118140960795 + 3766241 * 2 ^ 59
def prefixEnd_3766241 : Nat := 4983230072969 + 3 ^ 40 * 3766241 * 2
def baseEnd_3766241 : Nat := 1933891893670104298466879

theorem tailTrace_3766241 : CollatzResearch.WordTrace tailWord_3766241 prefixEnd_3766241 1933891893670104298466879 := by
  unfold tailWord_3766241
  simp only [CollatzResearch.WordTrace]
  refine ⟨137366094348559554598330577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91577396232373036398887051 137366094348559554598330577)
  ·
    refine ⟨103024570761419665948747933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137366094348559554598330577 103024570761419665948747933)
    ·
      refine ⟨38634214035532374730780475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103024570761419665948747933 38634214035532374730780475)
      ·
        refine ⟨57951321053298562096170713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38634214035532374730780475 57951321053298562096170713)
        ·
          refine ⟨43463490789973921572128035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57951321053298562096170713 43463490789973921572128035)
          ·
            refine ⟨65195236184960882358192053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43463490789973921572128035 65195236184960882358192053)
            ·
              refine ⟨6112053392340082721080505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65195236184960882358192053 6112053392340082721080505)
              ·
                refine ⟨4584040044255062040810379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6112053392340082721080505 4584040044255062040810379)
                ·
                  refine ⟨6876060066382593061215569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4584040044255062040810379 6876060066382593061215569)
                  ·
                    refine ⟨5157045049786944795911677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6876060066382593061215569 5157045049786944795911677)
                    ·
                      refine ⟨1933891893670104298466879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5157045049786944795911677 1933891893670104298466879)
                      ·
                        rfl

theorem cell23_3766241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_3766241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766241 prefixEnd_3766241 := by exact prefixLift 3766241
  have htrace : WordTrace (prefixWord ++ tailWord_3766241) baseStart_3766241 baseEnd_3766241 := by
    simpa [prefixWord, tailWord_3766241, baseEnd_3766241] using wordTrace_append hprefix tailTrace_3766241
  have hstable : (prefixWord ++ tailWord_3766241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766241).length < 2 ^ (prefixWord ++ tailWord_3766241).sum := by decide
  have hdescent : baseEnd_3766241 < baseStart_3766241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766267 : List Nat := [1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 5]
def baseStart_3766267 : Nat := 118140960795 + 3766267 * 2 ^ 59
def prefixEnd_3766267 : Nat := 4983230072969 + 3 ^ 40 * 3766267 * 2
def baseEnd_3766267 : Nat := 1933905244167121196741759

theorem tailTrace_3766267 : CollatzResearch.WordTrace tailWord_3766267 prefixEnd_3766267 1933905244167121196741759 := by
  unfold tailWord_3766267
  simp only [CollatzResearch.WordTrace]
  refine ⟨137367042646465361038777055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91578028430976907359184703 137367042646465361038777055)
  ·
    refine ⟨206050563969698041558165583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137367042646465361038777055 206050563969698041558165583)
    ·
      refine ⟨309075845954547062337248375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206050563969698041558165583 309075845954547062337248375)
      ·
        refine ⟨463613768931820593505872563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309075845954547062337248375 463613768931820593505872563)
        ·
          refine ⟨695420653397730890258808845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463613768931820593505872563 695420653397730890258808845)
          ·
            refine ⟨260782745024149083847053317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 695420653397730890258808845 260782745024149083847053317)
            ·
              refine ⟨48896764692027953221322497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 260782745024149083847053317 48896764692027953221322497)
              ·
                refine ⟨36672573519020964915991873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48896764692027953221322497 36672573519020964915991873)
                ·
                  refine ⟨27504430139265723686993905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36672573519020964915991873 27504430139265723686993905)
                  ·
                    refine ⟨20628322604449292765245429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27504430139265723686993905 20628322604449292765245429)
                    ·
                      refine ⟨1933905244167121196741759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20628322604449292765245429 1933905244167121196741759)
                      ·
                        rfl

theorem cell23_3766267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 5].length) (baseStart_3766267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766267 prefixEnd_3766267 := by exact prefixLift 3766267
  have htrace : WordTrace (prefixWord ++ tailWord_3766267) baseStart_3766267 baseEnd_3766267 := by
    simpa [prefixWord, tailWord_3766267, baseEnd_3766267] using wordTrace_append hprefix tailTrace_3766267
  have hstable : (prefixWord ++ tailWord_3766267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766267).length < 2 ^ (prefixWord ++ tailWord_3766267).sum := by decide
  have hdescent : baseEnd_3766267 < baseStart_3766267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766344 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 1, 5, 3]
def baseStart_3766344 : Nat := 118140960795 + 3766344 * 2 ^ 59
def prefixEnd_3766344 : Nat := 4983230072969 + 3 ^ 40 * 3766344 * 2
def baseEnd_3766344 : Nat := 1933944782177517395478905

theorem tailTrace_3766344 : CollatzResearch.WordTrace tailWord_3766344 prefixEnd_3766344 1933944782177517395478905 := by
  unfold tailWord_3766344
  simp only [CollatzResearch.WordTrace]
  refine ⟨68684925533593201594665043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91579900711457602126220057 68684925533593201594665043)
  ·
    refine ⟨103027388300389802391997565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68684925533593201594665043 103027388300389802391997565)
    ·
      refine ⟨38635270612646175896999087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103027388300389802391997565 38635270612646175896999087)
      ·
        refine ⟨57952905918969263845498631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38635270612646175896999087 57952905918969263845498631)
        ·
          refine ⟨86929358878453895768247947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57952905918969263845498631 86929358878453895768247947)
          ·
            refine ⟨130394038317680843652371921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86929358878453895768247947 130394038317680843652371921)
            ·
              refine ⟨97795528738260632739278941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130394038317680843652371921 97795528738260632739278941)
              ·
                refine ⟨36673323276847737277229603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97795528738260632739278941 36673323276847737277229603)
                ·
                  refine ⟨55009984915271605915844405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36673323276847737277229603 55009984915271605915844405)
                  ·
                    refine ⟨5157186085806713054610413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55009984915271605915844405 5157186085806713054610413)
                    ·
                      refine ⟨1933944782177517395478905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5157186085806713054610413 1933944782177517395478905)
                      ·
                        rfl

theorem cell23_3766344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_3766344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766344 prefixEnd_3766344 := by exact prefixLift 3766344
  have htrace : WordTrace (prefixWord ++ tailWord_3766344) baseStart_3766344 baseEnd_3766344 := by
    simpa [prefixWord, tailWord_3766344, baseEnd_3766344] using wordTrace_append hprefix tailTrace_3766344
  have hstable : (prefixWord ++ tailWord_3766344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766344).length < 2 ^ (prefixWord ++ tailWord_3766344).sum := by decide
  have hdescent : baseEnd_3766344 < baseStart_3766344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766345 : List Nat := [1, 2, 1, 1, 2, 2, 7, 1, 2, 2, 2]
def baseStart_3766345 : Nat := 118140960795 + 3766345 * 2 ^ 59
def prefixEnd_3766345 : Nat := 4983230072969 + 3 ^ 40 * 3766345 * 2
def baseEnd_3766345 : Nat := 1933945295658171891566401

theorem tailTrace_3766345 : CollatzResearch.WordTrace tailWord_3766345 prefixEnd_3766345 1933945295658171891566401 := by
  unfold tailWord_3766345
  simp only [CollatzResearch.WordTrace]
  refine ⟨137369887540182780360116489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91579925026788520240077659 137369887540182780360116489)
  ·
    refine ⟨103027415655137085270087367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137369887540182780360116489 103027415655137085270087367)
    ·
      refine ⟨154541123482705627905131051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103027415655137085270087367 154541123482705627905131051)
      ·
        refine ⟨231811685224058441857696577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154541123482705627905131051 231811685224058441857696577)
        ·
          refine ⟨173858763918043831393272433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231811685224058441857696577 173858763918043831393272433)
          ·
            refine ⟨130394072938532873544954325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173858763918043831393272433 130394072938532873544954325)
            ·
              refine ⟨3056111084496864223709867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 130394072938532873544954325 3056111084496864223709867)
              ·
                refine ⟨4584166626745296335564801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3056111084496864223709867 4584166626745296335564801)
                ·
                  refine ⟨3438124970058972251673601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4584166626745296335564801 3438124970058972251673601)
                  ·
                    refine ⟨2578593727544229188755201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3438124970058972251673601 2578593727544229188755201)
                    ·
                      refine ⟨1933945295658171891566401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2578593727544229188755201 1933945295658171891566401)
                      ·
                        rfl

theorem cell23_3766345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 1, 2, 2, 2].length) (baseStart_3766345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766345 prefixEnd_3766345 := by exact prefixLift 3766345
  have htrace : WordTrace (prefixWord ++ tailWord_3766345) baseStart_3766345 baseEnd_3766345 := by
    simpa [prefixWord, tailWord_3766345, baseEnd_3766345] using wordTrace_append hprefix tailTrace_3766345
  have hstable : (prefixWord ++ tailWord_3766345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766345).length < 2 ^ (prefixWord ++ tailWord_3766345).sum := by decide
  have hdescent : baseEnd_3766345 < baseStart_3766345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766368 : List Nat := [2, 1, 1, 3, 2, 5, 1, 3, 5]
def baseStart_3766368 : Nat := 118140960795 + 3766368 * 2 ^ 59
def prefixEnd_3766368 : Nat := 4983230072969 + 3 ^ 40 * 3766368 * 2
def baseEnd_3766368 : Nat := 214884122857025033508755

theorem tailTrace_3766368 : CollatzResearch.WordTrace tailWord_3766368 prefixEnd_3766368 214884122857025033508755 := by
  unfold tailWord_3766368
  simp only [CollatzResearch.WordTrace]
  refine ⟨68685363209549727644101879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91580484279399636858802505 68685363209549727644101879)
  ·
    refine ⟨103028044814324591466152819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68685363209549727644101879 103028044814324591466152819)
    ·
      refine ⟨154542067221486887199229229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103028044814324591466152819 154542067221486887199229229)
      ·
        refine ⟨57953275208057582699710961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154542067221486887199229229 57953275208057582699710961)
        ·
          refine ⟨43464956406043187024783221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57953275208057582699710961 43464956406043187024783221)
          ·
            refine ⟨4074839663066548783573427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43464956406043187024783221 4074839663066548783573427)
            ·
              refine ⟨6112259494599823175360141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4074839663066548783573427 6112259494599823175360141)
              ·
                refine ⟨2292097310474933690760053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6112259494599823175360141 2292097310474933690760053)
                ·
                  refine ⟨214884122857025033508755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2292097310474933690760053 214884122857025033508755)
                  ·
                    rfl

theorem cell23_3766368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 3, 5].length) (baseStart_3766368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766368 prefixEnd_3766368 := by exact prefixLift 3766368
  have htrace : WordTrace (prefixWord ++ tailWord_3766368) baseStart_3766368 baseEnd_3766368 := by
    simpa [prefixWord, tailWord_3766368, baseEnd_3766368] using wordTrace_append hprefix tailTrace_3766368
  have hstable : (prefixWord ++ tailWord_3766368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766368).length < 2 ^ (prefixWord ++ tailWord_3766368).sum := by decide
  have hdescent : baseEnd_3766368 < baseStart_3766368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766381 : List Nat := [1, 5, 1, 1, 2, 1, 3, 2, 2, 5]
def baseStart_3766381 : Nat := 118140960795 + 3766381 * 2 ^ 59
def prefixEnd_3766381 : Nat := 4983230072969 + 3 ^ 40 * 3766381 * 2
def baseEnd_3766381 : Nat := 644654593653911250238745

theorem tailTrace_3766381 : CollatzResearch.WordTrace tailWord_3766381 prefixEnd_3766381 644654593653911250238745 := by
  unfold tailWord_3766381
  simp only [CollatzResearch.WordTrace]
  refine ⟨137371200568052358508426997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91580800378701572338951331 137371200568052358508426997)
  ·
    refine ⟨12878550053254908610165031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137371200568052358508426997 12878550053254908610165031)
    ·
      refine ⟨19317825079882362915247547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12878550053254908610165031 19317825079882362915247547)
      ·
        refine ⟨28976737619823544372871321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19317825079882362915247547 28976737619823544372871321)
        ·
          refine ⟨21732553214867658279653491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28976737619823544372871321 21732553214867658279653491)
          ·
            refine ⟨32598829822301487419480237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21732553214867658279653491 32598829822301487419480237)
            ·
              refine ⟨12224561183363057782305089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32598829822301487419480237 12224561183363057782305089)
              ·
                refine ⟨9168420887522293336728817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12224561183363057782305089 9168420887522293336728817)
                ·
                  refine ⟨6876315665641720002546613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9168420887522293336728817 6876315665641720002546613)
                  ·
                    refine ⟨644654593653911250238745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6876315665641720002546613 644654593653911250238745)
                    ·
                      rfl

theorem cell23_3766381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_3766381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766381 prefixEnd_3766381 := by exact prefixLift 3766381
  have htrace : WordTrace (prefixWord ++ tailWord_3766381) baseStart_3766381 baseEnd_3766381 := by
    simpa [prefixWord, tailWord_3766381, baseEnd_3766381] using wordTrace_append hprefix tailTrace_3766381
  have hstable : (prefixWord ++ tailWord_3766381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766381).length < 2 ^ (prefixWord ++ tailWord_3766381).sum := by decide
  have hdescent : baseEnd_3766381 < baseStart_3766381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766418 : List Nat := [3, 2, 3, 1, 1, 1, 4, 1, 2, 1, 4]
def baseStart_3766418 : Nat := 118140960795 + 3766418 * 2 ^ 59
def prefixEnd_3766418 : Nat := 4983230072969 + 3 ^ 40 * 3766418 * 2
def baseEnd_3766418 : Nat := 1933982779745950105953565

theorem tailTrace_3766418 : CollatzResearch.WordTrace tailWord_3766418 prefixEnd_3766418 1933982779745950105953565 := by
  unfold tailWord_3766418
  simp only [CollatzResearch.WordTrace]
  refine ⟨34343137517229578456880977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91581700045945542551682605 34343137517229578456880977)
  ·
    refine ⟨25757353137922183842660733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34343137517229578456880977 25757353137922183842660733)
    ·
      refine ⟨9659007426720818940997775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25757353137922183842660733 9659007426720818940997775)
      ·
        refine ⟨14488511140081228411496663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9659007426720818940997775 14488511140081228411496663)
        ·
          refine ⟨21732766710121842617244995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14488511140081228411496663 21732766710121842617244995)
          ·
            refine ⟨32599150065182763925867493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21732766710121842617244995 32599150065182763925867493)
            ·
              refine ⟨6112340637221768236100155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32599150065182763925867493 6112340637221768236100155)
              ·
                refine ⟨9168510955832652354150233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6112340637221768236100155 9168510955832652354150233)
                ·
                  refine ⟨6876383216874489265612675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9168510955832652354150233 6876383216874489265612675)
                  ·
                    refine ⟨10314574825311733898419013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6876383216874489265612675 10314574825311733898419013)
                    ·
                      refine ⟨1933982779745950105953565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10314574825311733898419013 1933982779745950105953565)
                      ·
                        rfl

theorem cell23_3766418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_3766418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766418 prefixEnd_3766418 := by exact prefixLift 3766418
  have htrace : WordTrace (prefixWord ++ tailWord_3766418) baseStart_3766418 baseEnd_3766418 := by
    simpa [prefixWord, tailWord_3766418, baseEnd_3766418] using wordTrace_append hprefix tailTrace_3766418
  have hstable : (prefixWord ++ tailWord_3766418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766418).length < 2 ^ (prefixWord ++ tailWord_3766418).sum := by decide
  have hdescent : baseEnd_3766418 < baseStart_3766418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766488 : List Nat := [2, 1, 2, 2, 4, 2, 1, 3, 1, 5]
def baseStart_3766488 : Nat := 118140960795 + 3766488 * 2 ^ 59
def prefixEnd_3766488 : Nat := 4983230072969 + 3 ^ 40 * 3766488 * 2
def baseEnd_3766488 : Nat := 644672907797254944026081

theorem tailTrace_3766488 : CollatzResearch.WordTrace tailWord_3766488 prefixEnd_3766488 644672907797254944026081 := by
  unfold tailWord_3766488
  simp only [CollatzResearch.WordTrace]
  refine ⟨68687551589332357891286059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91583402119109810521714745 68687551589332357891286059)
  ·
    refine ⟨103031327383998536836929089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68687551589332357891286059 103031327383998536836929089)
    ·
      refine ⟨77273495537998902627696817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103031327383998536836929089 77273495537998902627696817)
      ·
        refine ⟨57955121653499176970772613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77273495537998902627696817 57955121653499176970772613)
        ·
          refine ⟨10866585310031095682019865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57955121653499176970772613 10866585310031095682019865)
          ·
            refine ⟨8149938982523321761514899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10866585310031095682019865 8149938982523321761514899)
            ·
              refine ⟨12224908473784982642272349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8149938982523321761514899 12224908473784982642272349)
              ·
                refine ⟨4584340677669368490852131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12224908473784982642272349 4584340677669368490852131)
                ·
                  refine ⟨6876511016504052736278197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4584340677669368490852131 6876511016504052736278197)
                  ·
                    refine ⟨644672907797254944026081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6876511016504052736278197 644672907797254944026081)
                    ·
                      rfl

theorem cell23_3766488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 3, 1, 5].length) (baseStart_3766488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766488 prefixEnd_3766488 := by exact prefixLift 3766488
  have htrace : WordTrace (prefixWord ++ tailWord_3766488) baseStart_3766488 baseEnd_3766488 := by
    simpa [prefixWord, tailWord_3766488, baseEnd_3766488] using wordTrace_append hprefix tailTrace_3766488
  have hstable : (prefixWord ++ tailWord_3766488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766488).length < 2 ^ (prefixWord ++ tailWord_3766488).sum := by decide
  have hdescent : baseEnd_3766488 < baseStart_3766488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766492 : List Nat := [2, 2, 5, 2, 1, 2, 1, 2, 6]
def baseStart_3766492 : Nat := 118140960795 + 3766492 * 2 ^ 59
def prefixEnd_3766492 : Nat := 4983230072969 + 3 ^ 40 * 3766492 * 2
def baseEnd_3766492 : Nat := 214891197479375868492025

theorem tailTrace_3766492 : CollatzResearch.WordTrace tailWord_3766492 prefixEnd_3766492 214891197479375868492025 := by
  unfold tailWord_3766492
  simp only [CollatzResearch.WordTrace]
  refine ⟨68687624535325112232858865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91583499380433482977145153 68687624535325112232858865)
  ·
    refine ⟨51515718401493834174644149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68687624535325112232858865 51515718401493834174644149)
    ·
      refine ⟨4829598600140046953872889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51515718401493834174644149 4829598600140046953872889)
      ·
        refine ⟨3622198950105035215404667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4829598600140046953872889 3622198950105035215404667)
        ·
          refine ⟨5433298425157552823107001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3622198950105035215404667 5433298425157552823107001)
          ·
            refine ⟨4074973818868164617330251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5433298425157552823107001 4074973818868164617330251)
            ·
              refine ⟨6112460728302246925995377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4074973818868164617330251 6112460728302246925995377)
              ·
                refine ⟨4584345546226685194496533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6112460728302246925995377 4584345546226685194496533)
                ·
                  refine ⟨214891197479375868492025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4584345546226685194496533 214891197479375868492025)
                  ·
                    rfl

theorem cell23_3766492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 2, 6].length) (baseStart_3766492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766492 prefixEnd_3766492 := by exact prefixLift 3766492
  have htrace : WordTrace (prefixWord ++ tailWord_3766492) baseStart_3766492 baseEnd_3766492 := by
    simpa [prefixWord, tailWord_3766492, baseEnd_3766492] using wordTrace_append hprefix tailTrace_3766492
  have hstable : (prefixWord ++ tailWord_3766492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766492).length < 2 ^ (prefixWord ++ tailWord_3766492).sum := by decide
  have hdescent : baseEnd_3766492 < baseStart_3766492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766511 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 5]
def baseStart_3766511 : Nat := 118140960795 + 3766511 * 2 ^ 59
def prefixEnd_3766511 : Nat := 4983230072969 + 3 ^ 40 * 3766511 * 2
def baseEnd_3766511 : Nat := 1934030533446818242090637

theorem tailTrace_3766511 : CollatzResearch.WordTrace tailWord_3766511 prefixEnd_3766511 1934030533446818242090637 := by
  unfold tailWord_3766511
  simp only [CollatzResearch.WordTrace]
  refine ⟨137375942057581390710659387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91583961371720927140439591 137375942057581390710659387)
  ·
    refine ⟨206063913086372086065989081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137375942057581390710659387 206063913086372086065989081)
    ·
      refine ⟨154547934814779064549491811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206063913086372086065989081 154547934814779064549491811)
      ·
        refine ⟨231821902222168596824237717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154547934814779064549491811 231821902222168596824237717)
        ·
          refine ⟨10866651666664152976136143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 231821902222168596824237717 10866651666664152976136143)
          ·
            refine ⟨16299977499996229464204215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10866651666664152976136143 16299977499996229464204215)
            ·
              refine ⟨24449966249994344196306323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16299977499996229464204215 24449966249994344196306323)
              ·
                refine ⟨36674949374991516294459485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24449966249994344196306323 36674949374991516294459485)
                ·
                  refine ⟨13753106015621818610422307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36674949374991516294459485 13753106015621818610422307)
                  ·
                    refine ⟨20629659023432727915633461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13753106015621818610422307 20629659023432727915633461)
                    ·
                      refine ⟨1934030533446818242090637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20629659023432727915633461 1934030533446818242090637)
                      ·
                        rfl

theorem cell23_3766511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 5].length) (baseStart_3766511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766511 prefixEnd_3766511 := by exact prefixLift 3766511
  have htrace : WordTrace (prefixWord ++ tailWord_3766511) baseStart_3766511 baseEnd_3766511 := by
    simpa [prefixWord, tailWord_3766511, baseEnd_3766511] using wordTrace_append hprefix tailTrace_3766511
  have hstable : (prefixWord ++ tailWord_3766511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766511).length < 2 ^ (prefixWord ++ tailWord_3766511).sum := by decide
  have hdescent : baseEnd_3766511 < baseStart_3766511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766518 : List Nat := [5, 1, 1, 1, 1, 1, 5, 1, 1, 6]
def baseStart_3766518 : Nat := 118140960795 + 3766518 * 2 ^ 59
def prefixEnd_3766518 : Nat := 4983230072969 + 3 ^ 40 * 3766518 * 2
def baseEnd_3766518 : Nat := 644678042603799904901035

theorem tailTrace_3766518 : CollatzResearch.WordTrace tailWord_3766518 prefixEnd_3766518 644678042603799904901035 := by
  unfold tailWord_3766518
  simp only [CollatzResearch.WordTrace]
  refine ⟨8586012335534751931635263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91584131579037353937442805 8586012335534751931635263)
  ·
    refine ⟨12879018503302127897452895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8586012335534751931635263 12879018503302127897452895)
    ·
      refine ⟨19318527754953191846179343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12879018503302127897452895 19318527754953191846179343)
      ·
        refine ⟨28977791632429787769269015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19318527754953191846179343 28977791632429787769269015)
        ·
          refine ⟨43466687448644681653903523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28977791632429787769269015 43466687448644681653903523)
          ·
            refine ⟨65200031172967022480855285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43466687448644681653903523 65200031172967022480855285)
            ·
              refine ⟨6112502922465658357580183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65200031172967022480855285 6112502922465658357580183)
              ·
                refine ⟨9168754383698487536370275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6112502922465658357580183 9168754383698487536370275)
                ·
                  refine ⟨13753131575547731304555413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9168754383698487536370275 13753131575547731304555413)
                  ·
                    refine ⟨644678042603799904901035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13753131575547731304555413 644678042603799904901035)
                    ·
                      rfl

theorem cell23_3766518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_3766518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766518 prefixEnd_3766518 := by exact prefixLift 3766518
  have htrace : WordTrace (prefixWord ++ tailWord_3766518) baseStart_3766518 baseEnd_3766518 := by
    simpa [prefixWord, tailWord_3766518, baseEnd_3766518] using wordTrace_append hprefix tailTrace_3766518
  have hstable : (prefixWord ++ tailWord_3766518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766518).length < 2 ^ (prefixWord ++ tailWord_3766518).sum := by decide
  have hdescent : baseEnd_3766518 < baseStart_3766518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766521 : List Nat := [1, 2, 1, 3, 1, 1, 2, 5, 1, 2, 4]
def baseStart_3766521 : Nat := 118140960795 + 3766521 * 2 ^ 59
def prefixEnd_3766521 : Nat := 4983230072969 + 3 ^ 40 * 3766521 * 2
def baseEnd_3766521 : Nat := 1934035668253363202965591

theorem tailTrace_3766521 : CollatzResearch.WordTrace tailWord_3766521 prefixEnd_3766521 1934035668253363202965591 := by
  unfold tailWord_3766521
  simp only [CollatzResearch.WordTrace]
  refine ⟨137376306787545162418523417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91584204525030108279015611 137376306787545162418523417)
  ·
    refine ⟨103032230090658871813892563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137376306787545162418523417 103032230090658871813892563)
    ·
      refine ⟨154548345135988307720838845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103032230090658871813892563 154548345135988307720838845)
      ·
        refine ⟨57955629425995615395314567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154548345135988307720838845 57955629425995615395314567)
        ·
          refine ⟨86933444138993423092971851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57955629425995615395314567 86933444138993423092971851)
          ·
            refine ⟨130400166208490134639457777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86933444138993423092971851 130400166208490134639457777)
            ·
              refine ⟨97800124656367600979593333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130400166208490134639457777 97800124656367600979593333)
              ·
                refine ⟨9168761686534462591836875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97800124656367600979593333 9168761686534462591836875)
                ·
                  refine ⟨13753142529801693887755313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9168761686534462591836875 13753142529801693887755313)
                  ·
                    refine ⟨10314856897351270415816485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13753142529801693887755313 10314856897351270415816485)
                    ·
                      refine ⟨1934035668253363202965591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10314856897351270415816485 1934035668253363202965591)
                      ·
                        rfl

theorem cell23_3766521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_3766521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766521 prefixEnd_3766521 := by exact prefixLift 3766521
  have htrace : WordTrace (prefixWord ++ tailWord_3766521) baseStart_3766521 baseEnd_3766521 := by
    simpa [prefixWord, tailWord_3766521, baseEnd_3766521] using wordTrace_append hprefix tailTrace_3766521
  have hstable : (prefixWord ++ tailWord_3766521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766521).length < 2 ^ (prefixWord ++ tailWord_3766521).sum := by decide
  have hdescent : baseEnd_3766521 < baseStart_3766521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766528 : List Nat := [2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 3]
def baseStart_3766528 : Nat := 118140960795 + 3766528 * 2 ^ 59
def prefixEnd_3766528 : Nat := 4983230072969 + 3 ^ 40 * 3766528 * 2
def baseEnd_3766528 : Nat := 1934039262617944675578059

theorem tailTrace_3766528 : CollatzResearch.WordTrace tailWord_3766528 prefixEnd_3766528 1934039262617944675578059 := by
  unfold tailWord_3766528
  simp only [CollatzResearch.WordTrace]
  refine ⟨68688281049259901307014119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91584374732346535076018825 68688281049259901307014119)
  ·
    refine ⟨103032421573889851960521179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68688281049259901307014119 103032421573889851960521179)
    ·
      refine ⟨154548632360834777940781769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103032421573889851960521179 154548632360834777940781769)
      ·
        refine ⟨115911474270626083455586327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154548632360834777940781769 115911474270626083455586327)
        ·
          refine ⟨173867211405939125183379491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115911474270626083455586327 173867211405939125183379491)
          ·
            refine ⟨260800817108908687775069237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173867211405939125183379491 260800817108908687775069237)
            ·
              refine ⟨24450076603960189478912741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 260800817108908687775069237 24450076603960189478912741)
              ·
                refine ⟨4584389363242535527296139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24450076603960189478912741 4584389363242535527296139)
                ·
                  refine ⟨6876584044863803290944209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4584389363242535527296139 6876584044863803290944209)
                  ·
                    refine ⟨5157438033647852468208157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6876584044863803290944209 5157438033647852468208157)
                    ·
                      refine ⟨1934039262617944675578059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5157438033647852468208157 1934039262617944675578059)
                      ·
                        rfl

theorem cell23_3766528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 3].length) (baseStart_3766528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766528 prefixEnd_3766528 := by exact prefixLift 3766528
  have htrace : WordTrace (prefixWord ++ tailWord_3766528) baseStart_3766528 baseEnd_3766528 := by
    simpa [prefixWord, tailWord_3766528, baseEnd_3766528] using wordTrace_append hprefix tailTrace_3766528
  have hstable : (prefixWord ++ tailWord_3766528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766528).length < 2 ^ (prefixWord ++ tailWord_3766528).sum := by decide
  have hdescent : baseEnd_3766528 < baseStart_3766528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766628 : List Nat := [2, 3, 1, 1, 3, 1, 3, 1, 2, 2, 4]
def baseStart_3766628 : Nat := 118140960795 + 3766628 * 2 ^ 59
def prefixEnd_3766628 : Nat := 4983230072969 + 3 ^ 40 * 3766628 * 2
def baseEnd_3766628 : Nat := 1934090610683394284327599

theorem tailTrace_3766628 : CollatzResearch.WordTrace tailWord_3766628 prefixEnd_3766628 1934090610683394284327599 := by
  unfold tailWord_3766628
  simp only [CollatzResearch.WordTrace]
  refine ⟨68690104699078759846334269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91586806265438346461779025 68690104699078759846334269)
  ·
    refine ⟨25758789262154534942375351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68690104699078759846334269 25758789262154534942375351)
    ·
      refine ⟨38638183893231802413563027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25758789262154534942375351 38638183893231802413563027)
      ·
        refine ⟨57957275839847703620344541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38638183893231802413563027 57957275839847703620344541)
        ·
          refine ⟨21733978439942888857629203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57957275839847703620344541 21733978439942888857629203)
          ·
            refine ⟨32600967659914333286443805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21733978439942888857629203 32600967659914333286443805)
            ·
              refine ⟨12225362872467874982416427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32600967659914333286443805 12225362872467874982416427)
              ·
                refine ⟨18338044308701812473624641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12225362872467874982416427 18338044308701812473624641)
                ·
                  refine ⟨13753533231526359355218481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18338044308701812473624641 13753533231526359355218481)
                  ·
                    refine ⟨10315149923644769516413861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13753533231526359355218481 10315149923644769516413861)
                    ·
                      refine ⟨1934090610683394284327599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10315149923644769516413861 1934090610683394284327599)
                      ·
                        rfl

theorem cell23_3766628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_3766628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3766628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3766628 prefixEnd_3766628 := by exact prefixLift 3766628
  have htrace : WordTrace (prefixWord ++ tailWord_3766628) baseStart_3766628 baseEnd_3766628 := by
    simpa [prefixWord, tailWord_3766628, baseEnd_3766628] using wordTrace_append hprefix tailTrace_3766628
  have hstable : (prefixWord ++ tailWord_3766628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766628).length < 2 ^ (prefixWord ++ tailWord_3766628).sum := by decide
  have hdescent : baseEnd_3766628 < baseStart_3766628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
