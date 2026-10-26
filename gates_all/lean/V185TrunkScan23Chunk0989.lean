import V185TrunkScan23Chunk0988

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5855107 : List Nat := [1, 1, 1, 3, 4, 2, 1, 4, 1, 1, 4]
def baseStart_5855107 : Nat := 118140960795 + 5855107 * 2 ^ 59
def prefixEnd_5855107 : Nat := 4983230072969 + 3 ^ 40 * 5855107 * 2
def baseEnd_5855107 : Nat := 3006484174504728600635359

theorem tailTrace_5855107 : CollatzResearch.WordTrace tailWord_5855107 prefixEnd_5855107 3006484174504728600635359 := by
  unfold tailWord_5855107
  simp only [CollatzResearch.WordTrace]
  refine ⟨213553296398954786508819575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142368864265969857672546383 213553296398954786508819575)
  ·
    refine ⟨320329944598432179763229363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213553296398954786508819575 320329944598432179763229363)
    ·
      refine ⟨480494916897648269644844045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320329944598432179763229363 480494916897648269644844045)
      ·
        refine ⟨180185593836618101116816517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 480494916897648269644844045 180185593836618101116816517)
        ·
          refine ⟨33784798844365893959403097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180185593836618101116816517 33784798844365893959403097)
          ·
            refine ⟨25338599133274420469552323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33784798844365893959403097 25338599133274420469552323)
            ·
              refine ⟨38007898699911630704328485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25338599133274420469552323 38007898699911630704328485)
              ·
                refine ⟨7126481006233430757061591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38007898699911630704328485 7126481006233430757061591)
                ·
                  refine ⟨10689721509350146135592387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7126481006233430757061591 10689721509350146135592387)
                  ·
                    refine ⟨16034582264025219203388581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10689721509350146135592387 16034582264025219203388581)
                    ·
                      refine ⟨3006484174504728600635359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16034582264025219203388581 3006484174504728600635359)
                      ·
                        rfl

theorem cell23_5855107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 1, 4].length) (baseStart_5855107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855107 prefixEnd_5855107 := by exact prefixLift 5855107
  have htrace : WordTrace (prefixWord ++ tailWord_5855107) baseStart_5855107 baseEnd_5855107 := by
    simpa [prefixWord, tailWord_5855107, baseEnd_5855107] using wordTrace_append hprefix tailTrace_5855107
  have hstable : (prefixWord ++ tailWord_5855107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855107).length < 2 ^ (prefixWord ++ tailWord_5855107).sum := by decide
  have hdescent : baseEnd_5855107 < baseStart_5855107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855124 : List Nat := [2, 4, 2, 1, 1, 2, 2, 3, 1, 1, 4]
def baseStart_5855124 : Nat := 118140960795 + 5855124 * 2 ^ 59
def prefixEnd_5855124 : Nat := 4983230072969 + 3 ^ 40 * 5855124 * 2
def baseEnd_5855124 : Nat := 3006492903675855034122781

theorem tailTrace_5855124 : CollatzResearch.WordTrace tailWord_5855124 prefixEnd_5855124 3006492903675855034122781 := by
  unfold tailWord_5855124
  simp only [CollatzResearch.WordTrace]
  refine ⟨106776958219946599206094213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142369277626595465608125617 106776958219946599206094213)
  ·
    refine ⟨20020679666239987351142665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106776958219946599206094213 20020679666239987351142665)
    ·
      refine ⟨15015509749679990513356999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20020679666239987351142665 15015509749679990513356999)
      ·
        refine ⟨22523264624519985770035499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15015509749679990513356999 22523264624519985770035499)
        ·
          refine ⟨33784896936779978655053249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22523264624519985770035499 33784896936779978655053249)
          ·
            refine ⟨25338672702584983991289937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33784896936779978655053249 25338672702584983991289937)
            ·
              refine ⟨19004004526938737993467453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25338672702584983991289937 19004004526938737993467453)
              ·
                refine ⟨7126501697602026747550295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19004004526938737993467453 7126501697602026747550295)
                ·
                  refine ⟨10689752546403040121325443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7126501697602026747550295 10689752546403040121325443)
                  ·
                    refine ⟨16034628819604560181988165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10689752546403040121325443 16034628819604560181988165)
                    ·
                      refine ⟨3006492903675855034122781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16034628819604560181988165 3006492903675855034122781)
                      ·
                        rfl

theorem cell23_5855124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_5855124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855124 prefixEnd_5855124 := by exact prefixLift 5855124
  have htrace : WordTrace (prefixWord ++ tailWord_5855124) baseStart_5855124 baseEnd_5855124 := by
    simpa [prefixWord, tailWord_5855124, baseEnd_5855124] using wordTrace_append hprefix tailTrace_5855124
  have hstable : (prefixWord ++ tailWord_5855124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855124).length < 2 ^ (prefixWord ++ tailWord_5855124).sum := by decide
  have hdescent : baseEnd_5855124 < baseStart_5855124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855127 : List Nat := [1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 5]
def baseStart_5855127 : Nat := 118140960795 + 5855127 * 2 ^ 59
def prefixEnd_5855127 : Nat := 4983230072969 + 3 ^ 40 * 5855127 * 2
def baseEnd_5855127 : Nat := 3006494444117818522385267

theorem tailTrace_5855127 : CollatzResearch.WordTrace tailWord_5855127 prefixEnd_5855127 3006494444117818522385267 := by
  unfold tailWord_5855127
  simp only [CollatzResearch.WordTrace]
  refine ⟨213554025858882329924547635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142369350572588219949698423 213554025858882329924547635)
  ·
    refine ⟨320331038788323494886821453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213554025858882329924547635 320331038788323494886821453)
    ·
      refine ⟨120124139545621310582558045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 320331038788323494886821453 120124139545621310582558045)
      ·
        refine ⟨45046552329607991468459267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120124139545621310582558045 45046552329607991468459267)
        ·
          refine ⟨67569828494411987202688901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45046552329607991468459267 67569828494411987202688901)
          ·
            refine ⟨12669342842702247600504169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67569828494411987202688901 12669342842702247600504169)
            ·
              refine ⟨9502007132026685700378127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12669342842702247600504169 9502007132026685700378127)
              ·
                refine ⟨14253010698040028550567191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9502007132026685700378127 14253010698040028550567191)
                ·
                  refine ⟨21379516047060042825850787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14253010698040028550567191 21379516047060042825850787)
                  ·
                    refine ⟨32069274070590064238776181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21379516047060042825850787 32069274070590064238776181)
                    ·
                      refine ⟨3006494444117818522385267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32069274070590064238776181 3006494444117818522385267)
                      ·
                        rfl

theorem cell23_5855127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_5855127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855127 prefixEnd_5855127 := by exact prefixLift 5855127
  have htrace : WordTrace (prefixWord ++ tailWord_5855127) baseStart_5855127 baseEnd_5855127 := by
    simpa [prefixWord, tailWord_5855127, baseEnd_5855127] using wordTrace_append hprefix tailTrace_5855127
  have hstable : (prefixWord ++ tailWord_5855127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855127).length < 2 ^ (prefixWord ++ tailWord_5855127).sum := by decide
  have hdescent : baseEnd_5855127 < baseStart_5855127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855130 : List Nat := [3, 1, 1, 4, 2, 1, 11]
def baseStart_5855130 : Nat := 118140960795 + 5855130 * 2 ^ 59
def prefixEnd_5855130 : Nat := 4983230072969 + 3 ^ 40 * 5855130 * 2
def baseEnd_5855130 : Nat := 37117234377281259390713

theorem tailTrace_5855130 : CollatzResearch.WordTrace tailWord_5855130 prefixEnd_5855130 37117234377281259390713 := by
  unfold tailWord_5855130
  simp only [CollatzResearch.WordTrace]
  refine ⟨53388533819467865359226711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142369423518580974291271229 53388533819467865359226711)
  ·
    refine ⟨80082800729201798038840067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53388533819467865359226711 80082800729201798038840067)
    ·
      refine ⟨120124201093802697058260101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80082800729201798038840067 120124201093802697058260101)
      ·
        refine ⟨22523287705088005698423769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120124201093802697058260101 22523287705088005698423769)
        ·
          refine ⟨16892465778816004273817827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22523287705088005698423769 16892465778816004273817827)
          ·
            refine ⟨25338698668224006410726741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16892465778816004273817827 25338698668224006410726741)
            ·
              refine ⟨37117234377281259390713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 25338698668224006410726741 37117234377281259390713)
              ·
                rfl

theorem cell23_5855130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 11].length) (baseStart_5855130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855130 prefixEnd_5855130 := by exact prefixLift 5855130
  have htrace : WordTrace (prefixWord ++ tailWord_5855130) baseStart_5855130 baseEnd_5855130 := by
    simpa [prefixWord, tailWord_5855130, baseEnd_5855130] using wordTrace_append hprefix tailTrace_5855130
  have hstable : (prefixWord ++ tailWord_5855130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855130).length < 2 ^ (prefixWord ++ tailWord_5855130).sum := by decide
  have hdescent : baseEnd_5855130 < baseStart_5855130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855141 : List Nat := [1, 3, 1, 2, 1, 1, 1, 8, 1, 2, 2]
def baseStart_5855141 : Nat := 118140960795 + 5855141 * 2 ^ 59
def prefixEnd_5855141 : Nat := 4983230072969 + 3 ^ 40 * 5855141 * 2
def baseEnd_5855141 : Nat := 3006501632846981467610203

theorem tailTrace_5855141 : CollatzResearch.WordTrace tailWord_5855141 prefixEnd_5855141 3006501632846981467610203 := by
  unfold tailWord_5855141
  simp only [CollatzResearch.WordTrace]
  refine ⟨213554536480831610315557277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142369690987221073543704851 213554536480831610315557277)
  ·
    refine ⟨80082951180311853868333979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213554536480831610315557277 80082951180311853868333979)
    ·
      refine ⟨120124426770467780802500969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80082951180311853868333979 120124426770467780802500969)
      ·
        refine ⟨90093320077850835601875727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120124426770467780802500969 90093320077850835601875727)
        ·
          refine ⟨135139980116776253402813591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90093320077850835601875727 135139980116776253402813591)
          ·
            refine ⟨202709970175164380104220387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135139980116776253402813591 202709970175164380104220387)
            ·
              refine ⟨304064955262746570156330581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202709970175164380104220387 304064955262746570156330581)
              ·
                refine ⟨3563261194485311369019499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 304064955262746570156330581 3563261194485311369019499)
                ·
                  refine ⟨5344891791727967053529249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3563261194485311369019499 5344891791727967053529249)
                  ·
                    refine ⟨4008668843795975290146937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5344891791727967053529249 4008668843795975290146937)
                    ·
                      refine ⟨3006501632846981467610203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4008668843795975290146937 3006501632846981467610203)
                      ·
                        rfl

theorem cell23_5855141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 8, 1, 2, 2].length) (baseStart_5855141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855141 prefixEnd_5855141 := by exact prefixLift 5855141
  have htrace : WordTrace (prefixWord ++ tailWord_5855141) baseStart_5855141 baseEnd_5855141 := by
    simpa [prefixWord, tailWord_5855141, baseEnd_5855141] using wordTrace_append hprefix tailTrace_5855141
  have hstable : (prefixWord ++ tailWord_5855141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855141).length < 2 ^ (prefixWord ++ tailWord_5855141).sum := by decide
  have hdescent : baseEnd_5855141 < baseStart_5855141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855184 : List Nat := [2, 1, 1, 1, 1, 2, 4, 5, 1, 3, 2]
def baseStart_5855184 : Nat := 118140960795 + 5855184 * 2 ^ 59
def prefixEnd_5855184 : Nat := 4983230072969 + 3 ^ 40 * 5855184 * 2
def baseEnd_5855184 : Nat := 3006523712515124799372505

theorem tailTrace_5855184 : CollatzResearch.WordTrace tailWord_5855184 prefixEnd_5855184 3006523712515124799372505 := by
  unfold tailWord_5855184
  simp only [CollatzResearch.WordTrace]
  refine ⟨106778052409837914329686303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142370736546450552439581737 106778052409837914329686303)
  ·
    refine ⟨160167078614756871494529455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106778052409837914329686303 160167078614756871494529455)
    ·
      refine ⟨240250617922135307241794183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160167078614756871494529455 240250617922135307241794183)
      ·
        refine ⟨360375926883202960862691275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240250617922135307241794183 360375926883202960862691275)
        ·
          refine ⟨540563890324804441294036913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360375926883202960862691275 540563890324804441294036913)
          ·
            refine ⟨405422917743603330970527685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 540563890324804441294036913 405422917743603330970527685)
            ·
              refine ⟨76016797076925624556973941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 405422917743603330970527685 76016797076925624556973941)
              ·
                refine ⟨7126574725961777302216307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76016797076925624556973941 7126574725961777302216307)
                ·
                  refine ⟨10689862088942665953324461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7126574725961777302216307 10689862088942665953324461)
                  ·
                    refine ⟨4008698283353499732496673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10689862088942665953324461 4008698283353499732496673)
                    ·
                      refine ⟨3006523712515124799372505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4008698283353499732496673 3006523712515124799372505)
                      ·
                        rfl

theorem cell23_5855184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 1, 3, 2].length) (baseStart_5855184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855184 prefixEnd_5855184 := by exact prefixLift 5855184
  have htrace : WordTrace (prefixWord ++ tailWord_5855184) baseStart_5855184 baseEnd_5855184 := by
    simpa [prefixWord, tailWord_5855184, baseEnd_5855184] using wordTrace_append hprefix tailTrace_5855184
  have hstable : (prefixWord ++ tailWord_5855184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855184).length < 2 ^ (prefixWord ++ tailWord_5855184).sum := by decide
  have hdescent : baseEnd_5855184 < baseStart_5855184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855200 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 5]
def baseStart_5855200 : Nat := 118140960795 + 5855200 * 2 ^ 59
def prefixEnd_5855200 : Nat := 4983230072969 + 3 ^ 40 * 5855200 * 2
def baseEnd_5855200 : Nat := 3006531928205596736772431

theorem tailTrace_5855200 : CollatzResearch.WordTrace tailWord_5855200 prefixEnd_5855200 3006531928205596736772431 := by
  unfold tailWord_5855200
  simp only [CollatzResearch.WordTrace]
  refine ⟨106778344193808931695977527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142371125591745242261303369 106778344193808931695977527)
  ·
    refine ⟨160167516290713397543966291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106778344193808931695977527 160167516290713397543966291)
    ·
      refine ⟨240251274436070096315949437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160167516290713397543966291 240251274436070096315949437)
      ·
        refine ⟨90094227913526286118481039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240251274436070096315949437 90094227913526286118481039)
        ·
          refine ⟨135141341870289429177721559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90094227913526286118481039 135141341870289429177721559)
          ·
            refine ⟨202712012805434143766582339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135141341870289429177721559 202712012805434143766582339)
            ·
              refine ⟨304068019208151215649873509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202712012805434143766582339 304068019208151215649873509)
              ·
                refine ⟨57012753601528352934351283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 304068019208151215649873509 57012753601528352934351283)
                ·
                  refine ⟨85519130402292529401526925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57012753601528352934351283 85519130402292529401526925)
                  ·
                    refine ⟨32069673900859698525572597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85519130402292529401526925 32069673900859698525572597)
                    ·
                      refine ⟨3006531928205596736772431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32069673900859698525572597 3006531928205596736772431)
                      ·
                        rfl

theorem cell23_5855200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_5855200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855200 prefixEnd_5855200 := by exact prefixLift 5855200
  have htrace : WordTrace (prefixWord ++ tailWord_5855200) baseStart_5855200 baseEnd_5855200 := by
    simpa [prefixWord, tailWord_5855200, baseEnd_5855200] using wordTrace_append hprefix tailTrace_5855200
  have hstable : (prefixWord ++ tailWord_5855200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855200).length < 2 ^ (prefixWord ++ tailWord_5855200).sum := by decide
  have hdescent : baseEnd_5855200 < baseStart_5855200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855265 : List Nat := [1, 2, 3, 2, 4, 1, 3, 1, 2, 2, 2]
def baseStart_5855265 : Nat := 118140960795 + 5855265 * 2 ^ 59
def prefixEnd_5855265 : Nat := 4983230072969 + 3 ^ 40 * 5855265 * 2
def baseEnd_5855265 : Nat := 3006565304448138982459633

theorem tailTrace_5855265 : CollatzResearch.WordTrace tailWord_5855265 prefixEnd_5855265 3006565304448138982459633 := by
  unfold tailWord_5855265
  simp only [CollatzResearch.WordTrace]
  refine ⟨213559059132382379493071249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142372706088254919662047499 213559059132382379493071249)
  ·
    refine ⟨160169294349286784619803437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213559059132382379493071249 160169294349286784619803437)
    ·
      refine ⟨60063485380982544232426289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160169294349286784619803437 60063485380982544232426289)
      ·
        refine ⟨45047614035736908174319717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60063485380982544232426289 45047614035736908174319717)
        ·
          refine ⟨8446427631700670282684947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45047614035736908174319717 8446427631700670282684947)
          ·
            refine ⟨12669641447551005424027421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8446427631700670282684947 12669641447551005424027421)
            ·
              refine ⟨4751115542831627034010283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12669641447551005424027421 4751115542831627034010283)
              ·
                refine ⟨7126673314247440551015425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4751115542831627034010283 7126673314247440551015425)
                ·
                  refine ⟨5345004985685580413261569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7126673314247440551015425 5345004985685580413261569)
                  ·
                    refine ⟨4008753739264185309946177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5345004985685580413261569 4008753739264185309946177)
                    ·
                      refine ⟨3006565304448138982459633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4008753739264185309946177 3006565304448138982459633)
                      ·
                        rfl

theorem cell23_5855265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_5855265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855265 prefixEnd_5855265 := by exact prefixLift 5855265
  have htrace : WordTrace (prefixWord ++ tailWord_5855265) baseStart_5855265 baseEnd_5855265 := by
    simpa [prefixWord, tailWord_5855265, baseEnd_5855265] using wordTrace_append hprefix tailTrace_5855265
  have hstable : (prefixWord ++ tailWord_5855265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855265).length < 2 ^ (prefixWord ++ tailWord_5855265).sum := by decide
  have hdescent : baseEnd_5855265 < baseStart_5855265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855287 : List Nat := [1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 4]
def baseStart_5855287 : Nat := 118140960795 + 5855287 * 2 ^ 59
def prefixEnd_5855287 : Nat := 4983230072969 + 3 ^ 40 * 5855287 * 2
def baseEnd_5855287 : Nat := 3006576601022537896384531

theorem tailTrace_5855287 : CollatzResearch.WordTrace tailWord_5855287 prefixEnd_5855287 3006576601022537896384531 := by
  unfold tailWord_5855287
  simp only [CollatzResearch.WordTrace]
  refine ⟨213559861538302677250372115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142373241025535118166914743 213559861538302677250372115)
  ·
    refine ⟨320339792307454015875558173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213559861538302677250372115 320339792307454015875558173)
    ·
      refine ⟨120127422115295255953334315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 320339792307454015875558173 120127422115295255953334315)
      ·
        refine ⟨180191133172942883930001473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120127422115295255953334315 180191133172942883930001473)
        ·
          refine ⟨135143349879707162947501105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180191133172942883930001473 135143349879707162947501105)
          ·
            refine ⟨101357512409780372210625829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135143349879707162947501105 101357512409780372210625829)
            ·
              refine ⟨19004533576833819789492343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101357512409780372210625829 19004533576833819789492343)
              ·
                refine ⟨28506800365250729684238515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19004533576833819789492343 28506800365250729684238515)
                ·
                  refine ⟨42760200547876094526357773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28506800365250729684238515 42760200547876094526357773)
                  ·
                    refine ⟨16035075205453535447384165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42760200547876094526357773 16035075205453535447384165)
                    ·
                      refine ⟨3006576601022537896384531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16035075205453535447384165 3006576601022537896384531)
                      ·
                        rfl

theorem cell23_5855287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_5855287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855287 prefixEnd_5855287 := by exact prefixLift 5855287
  have htrace : WordTrace (prefixWord ++ tailWord_5855287) baseStart_5855287 baseEnd_5855287 := by
    simpa [prefixWord, tailWord_5855287, baseEnd_5855287] using wordTrace_append hprefix tailTrace_5855287
  have hstable : (prefixWord ++ tailWord_5855287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855287).length < 2 ^ (prefixWord ++ tailWord_5855287).sum := by decide
  have hdescent : baseEnd_5855287 < baseStart_5855287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855288 : List Nat := [2, 1, 2, 1, 7, 1, 1, 3, 5]
def baseStart_5855288 : Nat := 118140960795 + 5855288 * 2 ^ 59
def prefixEnd_5855288 : Nat := 4983230072969 + 3 ^ 40 * 5855288 * 2
def baseEnd_5855288 : Nat := 334064123833688043608003

theorem tailTrace_5855288 : CollatzResearch.WordTrace tailWord_5855288 prefixEnd_5855288 334064123833688043608003 := by
  unfold tailWord_5855288
  simp only [CollatzResearch.WordTrace]
  refine ⟨106779949005649527210579259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142373265340866036280772345 106779949005649527210579259)
  ·
    refine ⟨160169923508474290815868889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106779949005649527210579259 160169923508474290815868889)
    ·
      refine ⟨120127442631355718111901667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160169923508474290815868889 120127442631355718111901667)
      ·
        refine ⟨180191163947033577167852501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120127442631355718111901667 180191163947033577167852501)
        ·
          refine ⟨4223230405008599464871543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 180191163947033577167852501 4223230405008599464871543)
          ·
            refine ⟨6334845607512899197307315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4223230405008599464871543 6334845607512899197307315)
            ·
              refine ⟨9502268411269348795960973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6334845607512899197307315 9502268411269348795960973)
              ·
                refine ⟨3563350654226005798485365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9502268411269348795960973 3563350654226005798485365)
                ·
                  refine ⟨334064123833688043608003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3563350654226005798485365 334064123833688043608003)
                  ·
                    rfl

theorem cell23_5855288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 3, 5].length) (baseStart_5855288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855288 prefixEnd_5855288 := by exact prefixLift 5855288
  have htrace : WordTrace (prefixWord ++ tailWord_5855288) baseStart_5855288 baseEnd_5855288 := by
    simpa [prefixWord, tailWord_5855288, baseEnd_5855288] using wordTrace_append hprefix tailTrace_5855288
  have hstable : (prefixWord ++ tailWord_5855288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855288).length < 2 ^ (prefixWord ++ tailWord_5855288).sum := by decide
  have hdescent : baseEnd_5855288 < baseStart_5855288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855304 : List Nat := [2, 1, 3, 1, 1, 1, 2, 4, 2, 4, 2]
def baseStart_5855304 : Nat := 118140960795 + 5855304 * 2 ^ 59
def prefixEnd_5855304 : Nat := 4983230072969 + 3 ^ 40 * 5855304 * 2
def baseEnd_5855304 : Nat := 3006585330193664329871953

theorem tailTrace_5855304 : CollatzResearch.WordTrace tailWord_5855304 prefixEnd_5855304 3006585330193664329871953 := by
  unfold tailWord_5855304
  simp only [CollatzResearch.WordTrace]
  refine ⟨106780240789620544576870483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142373654386160726102493977 106780240789620544576870483)
  ·
    refine ⟨160170361184430816865305725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106780240789620544576870483 160170361184430816865305725)
    ·
      refine ⟨60063885444161556324489647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160170361184430816865305725 60063885444161556324489647)
      ·
        refine ⟨90095828166242334486734471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60063885444161556324489647 90095828166242334486734471)
        ·
          refine ⟨135143742249363501730101707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90095828166242334486734471 135143742249363501730101707)
          ·
            refine ⟨202715613374045252595152561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135143742249363501730101707 202715613374045252595152561)
            ·
              refine ⟨152036710030533939446364421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202715613374045252595152561 152036710030533939446364421)
              ·
                refine ⟨28506883130725113646193329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152036710030533939446364421 28506883130725113646193329)
                ·
                  refine ⟨21380162348043835234644997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28506883130725113646193329 21380162348043835234644997)
                  ·
                    refine ⟨4008780440258219106495937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21380162348043835234644997 4008780440258219106495937)
                    ·
                      refine ⟨3006585330193664329871953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4008780440258219106495937 3006585330193664329871953)
                      ·
                        rfl

theorem cell23_5855304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 2, 4, 2].length) (baseStart_5855304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855304 prefixEnd_5855304 := by exact prefixLift 5855304
  have htrace : WordTrace (prefixWord ++ tailWord_5855304) baseStart_5855304 baseEnd_5855304 := by
    simpa [prefixWord, tailWord_5855304, baseEnd_5855304] using wordTrace_append hprefix tailTrace_5855304
  have hstable : (prefixWord ++ tailWord_5855304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855304).length < 2 ^ (prefixWord ++ tailWord_5855304).sum := by decide
  have hdescent : baseEnd_5855304 < baseStart_5855304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855341 : List Nat := [1, 5, 1, 1, 2, 1, 4, 1, 2, 2, 3]
def baseStart_5855341 : Nat := 118140960795 + 5855341 * 2 ^ 59
def prefixEnd_5855341 : Nat := 4983230072969 + 3 ^ 40 * 5855341 * 2
def baseEnd_5855341 : Nat := 3006604328977880685109283

theorem tailTrace_5855341 : CollatzResearch.WordTrace tailWord_5855341 prefixEnd_5855341 3006604328977880685109283 := by
  unfold tailWord_5855341
  simp only [CollatzResearch.WordTrace]
  refine ⟨213561831080107044472837877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142374554053404696315225251 213561831080107044472837877)
  ·
    refine ⟨20021421663760035419328551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 213561831080107044472837877 20021421663760035419328551)
    ·
      refine ⟨30032132495640053128992827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20021421663760035419328551 30032132495640053128992827)
      ·
        refine ⟨45048198743460079693489241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30032132495640053128992827 45048198743460079693489241)
        ·
          refine ⟨33786149057595059770116931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45048198743460079693489241 33786149057595059770116931)
          ·
            refine ⟨50679223586392589655175397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33786149057595059770116931 50679223586392589655175397)
            ·
              refine ⟨9502354422448610560345387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50679223586392589655175397 9502354422448610560345387)
              ·
                refine ⟨14253531633672915840518081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9502354422448610560345387 14253531633672915840518081)
                ·
                  refine ⟨10690148725254686880388561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14253531633672915840518081 10690148725254686880388561)
                  ·
                    refine ⟨8017611543941015160291421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10690148725254686880388561 8017611543941015160291421)
                    ·
                      refine ⟨3006604328977880685109283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8017611543941015160291421 3006604328977880685109283)
                      ·
                        rfl

theorem cell23_5855341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_5855341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855341 prefixEnd_5855341 := by exact prefixLift 5855341
  have htrace : WordTrace (prefixWord ++ tailWord_5855341) baseStart_5855341 baseEnd_5855341 := by
    simpa [prefixWord, tailWord_5855341, baseEnd_5855341] using wordTrace_append hprefix tailTrace_5855341
  have hstable : (prefixWord ++ tailWord_5855341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855341).length < 2 ^ (prefixWord ++ tailWord_5855341).sum := by decide
  have hdescent : baseEnd_5855341 < baseStart_5855341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855361 : List Nat := [1, 2, 4, 2, 3, 1, 2, 2, 6]
def baseStart_5855361 : Nat := 118140960795 + 5855361 * 2 ^ 59
def prefixEnd_5855361 : Nat := 4983230072969 + 3 ^ 40 * 5855361 * 2
def baseEnd_5855361 : Nat := 334068288732330067428799

theorem tailTrace_5855361 : CollatzResearch.WordTrace tailWord_5855361 prefixEnd_5855361 334068288732330067428799 := by
  unfold tailWord_5855361
  simp only [CollatzResearch.WordTrace]
  refine ⟨213562560540034587888565937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142375040360023058592377291 213562560540034587888565937)
  ·
    refine ⟨160171920405025940916424453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213562560540034587888565937 160171920405025940916424453)
    ·
      refine ⟨30032235075942363921829585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160171920405025940916424453 30032235075942363921829585)
      ·
        refine ⟨22524176306956772941372189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30032235075942363921829585 22524176306956772941372189)
        ·
          refine ⟨8446566115108789853014571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22524176306956772941372189 8446566115108789853014571)
          ·
            refine ⟨12669849172663184779521857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8446566115108789853014571 12669849172663184779521857)
            ·
              refine ⟨9502386879497388584641393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12669849172663184779521857 9502386879497388584641393)
              ·
                refine ⟨7126790159623041438481045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9502386879497388584641393 7126790159623041438481045)
                ·
                  refine ⟨334068288732330067428799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7126790159623041438481045 334068288732330067428799)
                  ·
                    rfl

theorem cell23_5855361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 6].length) (baseStart_5855361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855361 prefixEnd_5855361 := by exact prefixLift 5855361
  have htrace : WordTrace (prefixWord ++ tailWord_5855361) baseStart_5855361 baseEnd_5855361 := by
    simpa [prefixWord, tailWord_5855361, baseEnd_5855361] using wordTrace_append hprefix tailTrace_5855361
  have hstable : (prefixWord ++ tailWord_5855361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855361).length < 2 ^ (prefixWord ++ tailWord_5855361).sum := by decide
  have hdescent : baseEnd_5855361 < baseStart_5855361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855365 : List Nat := [1, 3, 1, 1, 5, 3, 2, 2, 1, 4]
def baseStart_5855365 : Nat := 118140960795 + 5855365 * 2 ^ 59
def prefixEnd_5855365 : Nat := 4983230072969 + 3 ^ 40 * 5855365 * 2
def baseEnd_5855365 : Nat := 1002205550837862863736391

theorem tailTrace_5855365 : CollatzResearch.WordTrace tailWord_5855365 prefixEnd_5855365 1002205550837862863736391 := by
  unfold tailWord_5855365
  simp only [CollatzResearch.WordTrace]
  refine ⟨213562706432020096571711549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142375137621346731047807699 213562706432020096571711549)
  ·
    refine ⟨80086014912007536214391831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213562706432020096571711549 80086014912007536214391831)
    ·
      refine ⟨120129022368011304321587747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80086014912007536214391831 120129022368011304321587747)
      ·
        refine ⟨180193533552016956482381621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120129022368011304321587747 180193533552016956482381621)
        ·
          refine ⟨16893143770501589670223277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 180193533552016956482381621 16893143770501589670223277)
          ·
            refine ⟨6334928913938096126333729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16893143770501589670223277 6334928913938096126333729)
            ·
              refine ⟨4751196685453572094750297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6334928913938096126333729 4751196685453572094750297)
              ·
                refine ⟨3563397514090179071062723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4751196685453572094750297 3563397514090179071062723)
                ·
                  refine ⟨5345096271135268606594085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3563397514090179071062723 5345096271135268606594085)
                  ·
                    refine ⟨1002205550837862863736391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5345096271135268606594085 1002205550837862863736391)
                    ·
                      rfl

theorem cell23_5855365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 2, 1, 4].length) (baseStart_5855365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855365 prefixEnd_5855365 := by exact prefixLift 5855365
  have htrace : WordTrace (prefixWord ++ tailWord_5855365) baseStart_5855365 baseEnd_5855365 := by
    simpa [prefixWord, tailWord_5855365, baseEnd_5855365] using wordTrace_append hprefix tailTrace_5855365
  have hstable : (prefixWord ++ tailWord_5855365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855365).length < 2 ^ (prefixWord ++ tailWord_5855365).sum := by decide
  have hdescent : baseEnd_5855365 < baseStart_5855365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855405 : List Nat := [1, 5, 2, 1, 2, 1, 1, 5, 1, 1, 3]
def baseStart_5855405 : Nat := 118140960795 + 5855405 * 2 ^ 59
def prefixEnd_5855405 : Nat := 4983230072969 + 3 ^ 40 * 5855405 * 2
def baseEnd_5855405 : Nat := 3006637191739768434708989

theorem tailTrace_5855405 : CollatzResearch.WordTrace tailWord_5855405 prefixEnd_5855405 3006637191739768434708989 := by
  unfold tailWord_5855405
  simp only [CollatzResearch.WordTrace]
  refine ⟨213564165351875183403167669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142376110234583455602111779 213564165351875183403167669)
  ·
    refine ⟨20021640501738298444046969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 213564165351875183403167669 20021640501738298444046969)
    ·
      refine ⟨15016230376303723833035227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20021640501738298444046969 15016230376303723833035227)
      ·
        refine ⟨22524345564455585749552841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15016230376303723833035227 22524345564455585749552841)
        ·
          refine ⟨16893259173341689312164631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22524345564455585749552841 16893259173341689312164631)
          ·
            refine ⟨25339888760012533968246947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16893259173341689312164631 25339888760012533968246947)
            ·
              refine ⟨38009833140018800952370421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25339888760012533968246947 38009833140018800952370421)
              ·
                refine ⟨3563421856876762589284727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38009833140018800952370421 3563421856876762589284727)
                ·
                  refine ⟨5345132785315143883927091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3563421856876762589284727 5345132785315143883927091)
                  ·
                    refine ⟨8017699177972715825890637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5345132785315143883927091 8017699177972715825890637)
                    ·
                      refine ⟨3006637191739768434708989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8017699177972715825890637 3006637191739768434708989)
                      ·
                        rfl

theorem cell23_5855405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_5855405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855405 prefixEnd_5855405 := by exact prefixLift 5855405
  have htrace : WordTrace (prefixWord ++ tailWord_5855405) baseStart_5855405 baseEnd_5855405 := by
    simpa [prefixWord, tailWord_5855405, baseEnd_5855405] using wordTrace_append hprefix tailTrace_5855405
  have hstable : (prefixWord ++ tailWord_5855405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855405).length < 2 ^ (prefixWord ++ tailWord_5855405).sum := by decide
  have hdescent : baseEnd_5855405 < baseStart_5855405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855407 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 6]
def baseStart_5855407 : Nat := 118140960795 + 5855407 * 2 ^ 59
def prefixEnd_5855407 : Nat := 4983230072969 + 3 ^ 40 * 5855407 * 2
def baseEnd_5855407 : Nat := 3006638218701077426883979

theorem tailTrace_5855407 : CollatzResearch.WordTrace tailWord_5855407 prefixEnd_5855407 3006638218701077426883979 := by
  unfold tailWord_5855407
  simp only [CollatzResearch.WordTrace]
  refine ⟨213564238297867937744740475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142376158865245291829826983 213564238297867937744740475)
  ·
    refine ⟨320346357446801906617110713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213564238297867937744740475 320346357446801906617110713)
    ·
      refine ⟨240259768085101429962833035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320346357446801906617110713 240259768085101429962833035)
      ·
        refine ⟨360389652127652144944249553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240259768085101429962833035 360389652127652144944249553)
        ·
          refine ⟨270292239095739108708187165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360389652127652144944249553 270292239095739108708187165)
          ·
            refine ⟨101359589660902165765570187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 270292239095739108708187165 101359589660902165765570187)
            ·
              refine ⟨152039384491353248648355281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101359589660902165765570187 152039384491353248648355281)
              ·
                refine ⟨114029538368514936486266461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152039384491353248648355281 114029538368514936486266461)
                ·
                  refine ⟨42761076888193101182349923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114029538368514936486266461 42761076888193101182349923)
                  ·
                    refine ⟨64141615332289651773524885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42761076888193101182349923 64141615332289651773524885)
                    ·
                      refine ⟨3006638218701077426883979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64141615332289651773524885 3006638218701077426883979)
                      ·
                        rfl

theorem cell23_5855407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 6].length) (baseStart_5855407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855407 prefixEnd_5855407 := by exact prefixLift 5855407
  have htrace : WordTrace (prefixWord ++ tailWord_5855407) baseStart_5855407 baseEnd_5855407 := by
    simpa [prefixWord, tailWord_5855407, baseEnd_5855407] using wordTrace_append hprefix tailTrace_5855407
  have hstable : (prefixWord ++ tailWord_5855407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855407).length < 2 ^ (prefixWord ++ tailWord_5855407).sum := by decide
  have hdescent : baseEnd_5855407 < baseStart_5855407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855411 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 7, 2, 2]
def baseStart_5855411 : Nat := 118140960795 + 5855411 * 2 ^ 59
def prefixEnd_5855411 : Nat := 4983230072969 + 3 ^ 40 * 5855411 * 2
def baseEnd_5855411 : Nat := 3006640272623695411233961

theorem tailTrace_5855411 : CollatzResearch.WordTrace tailWord_5855411 prefixEnd_5855411 3006640272623695411233961 := by
  unfold tailWord_5855411
  simp only [CollatzResearch.WordTrace]
  refine ⟨213564384189853446427886087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142376256126568964285257391 213564384189853446427886087)
  ·
    refine ⟨320346576284780169641829131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213564384189853446427886087 320346576284780169641829131)
    ·
      refine ⟨480519864427170254462743697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320346576284780169641829131 480519864427170254462743697)
      ·
        refine ⟨360389898320377690847057773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 480519864427170254462743697 360389898320377690847057773)
        ·
          refine ⟨135146211870141634067646665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 360389898320377690847057773 135146211870141634067646665)
          ·
            refine ⟨101359658902606225550734999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135146211870141634067646665 101359658902606225550734999)
            ·
              refine ⟨152039488353909338326102499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101359658902606225550734999 152039488353909338326102499)
              ·
                refine ⟨228059232530864007489153749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152039488353909338326102499 228059232530864007489153749)
                ·
                  refine ⟨5345138262442125175527041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 228059232530864007489153749 5345138262442125175527041)
                  ·
                    refine ⟨4008853696831593881645281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5345138262442125175527041 4008853696831593881645281)
                    ·
                      refine ⟨3006640272623695411233961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4008853696831593881645281 3006640272623695411233961)
                      ·
                        rfl

theorem cell23_5855411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 7, 2, 2].length) (baseStart_5855411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855411 prefixEnd_5855411 := by exact prefixLift 5855411
  have htrace : WordTrace (prefixWord ++ tailWord_5855411) baseStart_5855411 baseEnd_5855411 := by
    simpa [prefixWord, tailWord_5855411, baseEnd_5855411] using wordTrace_append hprefix tailTrace_5855411
  have hstable : (prefixWord ++ tailWord_5855411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855411).length < 2 ^ (prefixWord ++ tailWord_5855411).sum := by decide
  have hdescent : baseEnd_5855411 < baseStart_5855411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855412 : List Nat := [2, 5, 3, 1, 1, 2, 1, 2, 6]
def baseStart_5855412 : Nat := 118140960795 + 5855412 * 2 ^ 59
def prefixEnd_5855412 : Nat := 4983230072969 + 3 ^ 40 * 5855412 * 2
def baseEnd_5855412 : Nat := 334071198456038878591273

theorem tailTrace_5855412 : CollatzResearch.WordTrace tailWord_5855412 prefixEnd_5855412 334071198456038878591273 := by
  unfold tailWord_5855412
  simp only [CollatzResearch.WordTrace]
  refine ⟨106782210331424911799336245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142376280441899882399114993 106782210331424911799336245)
  ·
    refine ⟨10010832218571085481187773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106782210331424911799336245 10010832218571085481187773)
    ·
      refine ⟨3754062081964157055445415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10010832218571085481187773 3754062081964157055445415)
      ·
        refine ⟨5631093122946235583168123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3754062081964157055445415 5631093122946235583168123)
        ·
          refine ⟨8446639684419353374752185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5631093122946235583168123 8446639684419353374752185)
          ·
            refine ⟨6334979763314515031064139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8446639684419353374752185 6334979763314515031064139)
            ·
              refine ⟨9502469644971772546596209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6334979763314515031064139 9502469644971772546596209)
              ·
                refine ⟨7126852233728829409947157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9502469644971772546596209 7126852233728829409947157)
                ·
                  refine ⟨334071198456038878591273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7126852233728829409947157 334071198456038878591273)
                  ·
                    rfl

theorem cell23_5855412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_5855412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855412 prefixEnd_5855412 := by exact prefixLift 5855412
  have htrace : WordTrace (prefixWord ++ tailWord_5855412) baseStart_5855412 baseEnd_5855412 := by
    simpa [prefixWord, tailWord_5855412, baseEnd_5855412] using wordTrace_append hprefix tailTrace_5855412
  have hstable : (prefixWord ++ tailWord_5855412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855412).length < 2 ^ (prefixWord ++ tailWord_5855412).sum := by decide
  have hdescent : baseEnd_5855412 < baseStart_5855412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855417 : List Nat := [1, 2, 1, 4, 1, 2, 12]
def baseStart_5855417 : Nat := 118140960795 + 5855417 * 2 ^ 59
def prefixEnd_5855417 : Nat := 4983230072969 + 3 ^ 40 * 5855417 * 2
def baseEnd_5855417 : Nat := 37119053747007683799493

theorem tailTrace_5855417 : CollatzResearch.WordTrace tailWord_5855417 prefixEnd_5855417 37119053747007683799493 := by
  unfold tailWord_5855417
  simp only [CollatzResearch.WordTrace]
  refine ⟨213564603027831709452604505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142376402018554472968403003 213564603027831709452604505)
  ·
    refine ⟨160173452270873782089453379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213564603027831709452604505 160173452270873782089453379)
    ·
      refine ⟨240260178406310673134180069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160173452270873782089453379 240260178406310673134180069)
      ·
        refine ⟨45048783451183251212658763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 240260178406310673134180069 45048783451183251212658763)
        ·
          refine ⟨67573175176774876818988145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45048783451183251212658763 67573175176774876818988145)
          ·
            refine ⟨50679881382581157614241109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67573175176774876818988145 50679881382581157614241109)
            ·
              refine ⟨37119053747007683799493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 50679881382581157614241109 37119053747007683799493)
              ·
                rfl

theorem cell23_5855417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 12].length) (baseStart_5855417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855417 prefixEnd_5855417 := by exact prefixLift 5855417
  have htrace : WordTrace (prefixWord ++ tailWord_5855417) baseStart_5855417 baseEnd_5855417 := by
    simpa [prefixWord, tailWord_5855417, baseEnd_5855417] using wordTrace_append hprefix tailTrace_5855417
  have hstable : (prefixWord ++ tailWord_5855417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855417).length < 2 ^ (prefixWord ++ tailWord_5855417).sum := by decide
  have hdescent : baseEnd_5855417 < baseStart_5855417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855448 : List Nat := [2, 1, 2, 2, 4, 2, 2, 2, 1, 2, 3]
def baseStart_5855448 : Nat := 118140960795 + 5855448 * 2 ^ 59
def prefixEnd_5855448 : Nat := 4983230072969 + 3 ^ 40 * 5855448 * 2
def baseEnd_5855448 : Nat := 3006659271407911766471291

theorem tailTrace_5855448 : CollatzResearch.WordTrace tailWord_5855448 prefixEnd_5855448 3006659271407911766471291 := by
  unfold tailWord_5855448
  simp only [CollatzResearch.WordTrace]
  refine ⟨106782866845359700873491499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142377155793812934497988665 106782866845359700873491499)
  ·
    refine ⟨160174300268039551310237249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106782866845359700873491499 160174300268039551310237249)
    ·
      refine ⟨120130725201029663482677937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160174300268039551310237249 120130725201029663482677937)
      ·
        refine ⟨90098043900772247612008453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120130725201029663482677937 90098043900772247612008453)
        ·
          refine ⟨16893383231394796427251585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90098043900772247612008453 16893383231394796427251585)
          ·
            refine ⟨12670037423546097320438689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16893383231394796427251585 12670037423546097320438689)
            ·
              refine ⟨9502528067659572990329017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12670037423546097320438689 9502528067659572990329017)
              ·
                refine ⟨7126896050744679742746763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9502528067659572990329017 7126896050744679742746763)
                ·
                  refine ⟨10690344076117019614120145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7126896050744679742746763 10690344076117019614120145)
                  ·
                    refine ⟨8017758057087764710590109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10690344076117019614120145 8017758057087764710590109)
                    ·
                      refine ⟨3006659271407911766471291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8017758057087764710590109 3006659271407911766471291)
                      ·
                        rfl

theorem cell23_5855448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_5855448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855448 prefixEnd_5855448 := by exact prefixLift 5855448
  have htrace : WordTrace (prefixWord ++ tailWord_5855448) baseStart_5855448 baseEnd_5855448 := by
    simpa [prefixWord, tailWord_5855448, baseEnd_5855448] using wordTrace_append hprefix tailTrace_5855448
  have hstable : (prefixWord ++ tailWord_5855448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855448).length < 2 ^ (prefixWord ++ tailWord_5855448).sum := by decide
  have hdescent : baseEnd_5855448 < baseStart_5855448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855478 : List Nat := [5, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3]
def baseStart_5855478 : Nat := 118140960795 + 5855478 * 2 ^ 59
def prefixEnd_5855478 : Nat := 4983230072969 + 3 ^ 40 * 5855478 * 2
def baseEnd_5855478 : Nat := 3006674675827546649096153

theorem tailTrace_5855478 : CollatzResearch.WordTrace tailWord_5855478 prefixEnd_5855478 3006674675827546649096153 := by
  unfold tailWord_5855478
  simp only [CollatzResearch.WordTrace]
  refine ⟨13347926742538169804410943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142377885253740477913716725 13347926742538169804410943)
  ·
    refine ⟨20021890113807254706616415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13347926742538169804410943 20021890113807254706616415)
    ·
      refine ⟨30032835170710882059924623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20021890113807254706616415 30032835170710882059924623)
      ·
        refine ⟨45049252756066323089886935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30032835170710882059924623 45049252756066323089886935)
        ·
          refine ⟨67573879134099484634830403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45049252756066323089886935 67573879134099484634830403)
          ·
            refine ⟨101360818701149226952245605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67573879134099484634830403 101360818701149226952245605)
            ·
              refine ⟨19005153506465480053546051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101360818701149226952245605 19005153506465480053546051)
              ·
                refine ⟨28507730259698220080319077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19005153506465480053546051 28507730259698220080319077)
                ·
                  refine ⟨5345199423693416265059827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28507730259698220080319077 5345199423693416265059827)
                  ·
                    refine ⟨8017799135540124397589741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5345199423693416265059827 8017799135540124397589741)
                    ·
                      refine ⟨3006674675827546649096153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8017799135540124397589741 3006674675827546649096153)
                      ·
                        rfl

theorem cell23_5855478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_5855478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855478 prefixEnd_5855478 := by exact prefixLift 5855478
  have htrace : WordTrace (prefixWord ++ tailWord_5855478) baseStart_5855478 baseEnd_5855478 := by
    simpa [prefixWord, tailWord_5855478, baseEnd_5855478] using wordTrace_append hprefix tailTrace_5855478
  have hstable : (prefixWord ++ tailWord_5855478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855478).length < 2 ^ (prefixWord ++ tailWord_5855478).sum := by decide
  have hdescent : baseEnd_5855478 < baseStart_5855478 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855505 : List Nat := [1, 2, 2, 1, 1, 7, 1, 2, 1, 3, 2]
def baseStart_5855505 : Nat := 118140960795 + 5855505 * 2 ^ 59
def prefixEnd_5855505 : Nat := 4983230072969 + 3 ^ 40 * 5855505 * 2
def baseEnd_5855505 : Nat := 3006688539805218043458529

theorem tailTrace_5855505 : CollatzResearch.WordTrace tailWord_5855505 prefixEnd_5855505 3006688539805218043458529 := by
  unfold tailWord_5855505
  simp only [CollatzResearch.WordTrace]
  refine ⟨213567812651512900481807969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142378541767675266987871979 213567812651512900481807969)
  ·
    refine ⟨160175859488634675361355977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213567812651512900481807969 160175859488634675361355977)
    ·
      refine ⟨120131894616476006521016983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160175859488634675361355977 120131894616476006521016983)
      ·
        refine ⟨180197841924714009781525475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120131894616476006521016983 180197841924714009781525475)
        ·
          refine ⟨270296762887071014672288213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180197841924714009781525475 270296762887071014672288213)
          ·
            refine ⟨6335080380165726906381755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 270296762887071014672288213 6335080380165726906381755)
            ·
              refine ⟨9502620570248590359572633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6335080380165726906381755 9502620570248590359572633)
              ·
                refine ⟨7126965427686442769679475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9502620570248590359572633 7126965427686442769679475)
                ·
                  refine ⟨10690448141529664154519213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7126965427686442769679475 10690448141529664154519213)
                  ·
                    refine ⟨4008918053073624057944705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10690448141529664154519213 4008918053073624057944705)
                    ·
                      refine ⟨3006688539805218043458529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4008918053073624057944705 3006688539805218043458529)
                      ·
                        rfl

theorem cell23_5855505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 3, 2].length) (baseStart_5855505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855505 prefixEnd_5855505 := by exact prefixLift 5855505
  have htrace : WordTrace (prefixWord ++ tailWord_5855505) baseStart_5855505 baseEnd_5855505 := by
    simpa [prefixWord, tailWord_5855505, baseEnd_5855505] using wordTrace_append hprefix tailTrace_5855505
  have hstable : (prefixWord ++ tailWord_5855505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855505).length < 2 ^ (prefixWord ++ tailWord_5855505).sum := by decide
  have hdescent : baseEnd_5855505 < baseStart_5855505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855522 : List Nat := [3, 3, 1, 1, 3, 2, 3, 1, 1, 3, 2]
def baseStart_5855522 : Nat := 118140960795 + 5855522 * 2 ^ 59
def prefixEnd_5855522 : Nat := 4983230072969 + 3 ^ 40 * 5855522 * 2
def baseEnd_5855522 : Nat := 3006697268976344476945951

theorem tailTrace_5855522 : CollatzResearch.WordTrace tailWord_5855522 prefixEnd_5855522 3006697268976344476945951 := by
  unfold tailWord_5855522
  simp only [CollatzResearch.WordTrace]
  refine ⟨53392108173112828096294205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142378955128300874923451213 53392108173112828096294205)
  ·
    refine ⟨20022040564917310536110327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53392108173112828096294205 20022040564917310536110327)
    ·
      refine ⟨30033060847375965804165491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20022040564917310536110327 30033060847375965804165491)
      ·
        refine ⟨45049591271063948706248237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30033060847375965804165491 45049591271063948706248237)
        ·
          refine ⟨16893596726648980764843089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45049591271063948706248237 16893596726648980764843089)
          ·
            refine ⟨12670197544986735573632317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16893596726648980764843089 12670197544986735573632317)
            ·
              refine ⟨4751324079370025840112119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12670197544986735573632317 4751324079370025840112119)
              ·
                refine ⟨7126986119055038760168179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4751324079370025840112119 7126986119055038760168179)
                ·
                  refine ⟨10690479178582558140252269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7126986119055038760168179 10690479178582558140252269)
                  ·
                    refine ⟨4008929691968459302594601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10690479178582558140252269 4008929691968459302594601)
                    ·
                      refine ⟨3006697268976344476945951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4008929691968459302594601 3006697268976344476945951)
                      ·
                        rfl

theorem cell23_5855522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_5855522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855522 prefixEnd_5855522 := by exact prefixLift 5855522
  have htrace : WordTrace (prefixWord ++ tailWord_5855522) baseStart_5855522 baseEnd_5855522 := by
    simpa [prefixWord, tailWord_5855522, baseEnd_5855522] using wordTrace_append hprefix tailTrace_5855522
  have hstable : (prefixWord ++ tailWord_5855522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855522).length < 2 ^ (prefixWord ++ tailWord_5855522).sum := by decide
  have hdescent : baseEnd_5855522 < baseStart_5855522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855551 : List Nat := [1, 1, 2, 2, 4, 1, 3, 1, 2, 3, 3]
def baseStart_5855551 : Nat := 118140960795 + 5855551 * 2 ^ 59
def prefixEnd_5855551 : Nat := 4983230072969 + 3 ^ 40 * 5855551 * 2
def baseEnd_5855551 : Nat := 3006712159915324863483317

theorem tailTrace_5855551 : CollatzResearch.WordTrace tailWord_5855551 prefixEnd_5855551 3006712159915324863483317 := by
  unfold tailWord_5855551
  simp only [CollatzResearch.WordTrace]
  refine ⟨213569490409346250337982507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142379660272897500225321671 213569490409346250337982507)
  ·
    refine ⟨320354235614019375506973761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213569490409346250337982507 320354235614019375506973761)
    ·
      refine ⟨240265676710514531630230321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320354235614019375506973761 240265676710514531630230321)
      ·
        refine ⟨180199257532885898722672741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240265676710514531630230321 180199257532885898722672741)
        ·
          refine ⟨33787360787416106010501139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180199257532885898722672741 33787360787416106010501139)
          ·
            refine ⟨50681041181124159015751709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33787360787416106010501139 50681041181124159015751709)
            ·
              refine ⟨19005390442921559630906891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50681041181124159015751709 19005390442921559630906891)
              ·
                refine ⟨28508085664382339446360337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19005390442921559630906891 28508085664382339446360337)
                ·
                  refine ⟨21381064248286754584770253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28508085664382339446360337 21381064248286754584770253)
                  ·
                    refine ⟨8017899093107532969288845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21381064248286754584770253 8017899093107532969288845)
                    ·
                      refine ⟨3006712159915324863483317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8017899093107532969288845 3006712159915324863483317)
                      ·
                        rfl

theorem cell23_5855551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 3, 3].length) (baseStart_5855551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855551 prefixEnd_5855551 := by exact prefixLift 5855551
  have htrace : WordTrace (prefixWord ++ tailWord_5855551) baseStart_5855551 baseEnd_5855551 := by
    simpa [prefixWord, tailWord_5855551, baseEnd_5855551] using wordTrace_append hprefix tailTrace_5855551
  have hstable : (prefixWord ++ tailWord_5855551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855551).length < 2 ^ (prefixWord ++ tailWord_5855551).sum := by decide
  have hdescent : baseEnd_5855551 < baseStart_5855551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855561 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 4, 5, 2]
def baseStart_5855561 : Nat := 118140960795 + 5855561 * 2 ^ 59
def prefixEnd_5855561 : Nat := 4983230072969 + 3 ^ 40 * 5855561 * 2
def baseEnd_5855561 : Nat := 3006717294721869824358271

theorem tailTrace_5855561 : CollatzResearch.WordTrace tailWord_5855561 prefixEnd_5855561 3006717294721869824358271 := by
  unfold tailWord_5855561
  simp only [CollatzResearch.WordTrace]
  refine ⟨213569855139310022045846537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142379903426206681363897691 213569855139310022045846537)
  ·
    refine ⟨160177391354482516534384903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213569855139310022045846537 160177391354482516534384903)
    ·
      refine ⟨240266087031723774801577355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160177391354482516534384903 240266087031723774801577355)
      ·
        refine ⟨360399130547585662202366033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240266087031723774801577355 360399130547585662202366033)
        ·
          refine ⟨270299347910689246651774525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360399130547585662202366033 270299347910689246651774525)
          ·
            refine ⟨101362255466508467494415447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 270299347910689246651774525 101362255466508467494415447)
            ·
              refine ⟨152043383199762701241623171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101362255466508467494415447 152043383199762701241623171)
              ·
                refine ⟨228065074799644051862434757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152043383199762701241623171 228065074799644051862434757)
                ·
                  refine ⟨42762201524933259724206517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 228065074799644051862434757 42762201524933259724206517)
                  ·
                    refine ⟨4008956392962493099144361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42762201524933259724206517 4008956392962493099144361)
                    ·
                      refine ⟨3006717294721869824358271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4008956392962493099144361 3006717294721869824358271)
                      ·
                        rfl

theorem cell23_5855561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 5, 2].length) (baseStart_5855561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855561 prefixEnd_5855561 := by exact prefixLift 5855561
  have htrace : WordTrace (prefixWord ++ tailWord_5855561) baseStart_5855561 baseEnd_5855561 := by
    simpa [prefixWord, tailWord_5855561, baseEnd_5855561] using wordTrace_append hprefix tailTrace_5855561
  have hstable : (prefixWord ++ tailWord_5855561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855561).length < 2 ^ (prefixWord ++ tailWord_5855561).sum := by decide
  have hdescent : baseEnd_5855561 < baseStart_5855561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855611 : List Nat := [1, 1, 1, 1, 1, 7, 1, 2, 1, 4, 3]
def baseStart_5855611 : Nat := 118140960795 + 5855611 * 2 ^ 59
def prefixEnd_5855611 : Nat := 4983230072969 + 3 ^ 40 * 5855611 * 2
def baseEnd_5855611 : Nat := 3006742968754594628733041

theorem tailTrace_5855611 : CollatzResearch.WordTrace tailWord_5855611 prefixEnd_5855611 3006742968754594628733041 := by
  unfold tailWord_5855611
  simp only [CollatzResearch.WordTrace]
  refine ⟨213571678789128880585166687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142381119192752587056777791 213571678789128880585166687)
  ·
    refine ⟨320357518183693320877750031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213571678789128880585166687 320357518183693320877750031)
    ·
      refine ⟨480536277275539981316625047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320357518183693320877750031 480536277275539981316625047)
      ·
        refine ⟨720804415913309971974937571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480536277275539981316625047 720804415913309971974937571)
        ·
          refine ⟨1081206623869964957962406357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 720804415913309971974937571 1081206623869964957962406357)
          ·
            refine ⟨25340780246952303702243899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1081206623869964957962406357 25340780246952303702243899)
            ·
              refine ⟨38011170370428455553365849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25340780246952303702243899 38011170370428455553365849)
              ·
                refine ⟨28508377777821341665024387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38011170370428455553365849 28508377777821341665024387)
                ·
                  refine ⟨42762566666732012497536581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28508377777821341665024387 42762566666732012497536581)
                  ·
                    refine ⟨8017981250012252343288109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42762566666732012497536581 8017981250012252343288109)
                    ·
                      refine ⟨3006742968754594628733041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8017981250012252343288109 3006742968754594628733041)
                      ·
                        rfl

theorem cell23_5855611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 4, 3].length) (baseStart_5855611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855611 prefixEnd_5855611 := by exact prefixLift 5855611
  have htrace : WordTrace (prefixWord ++ tailWord_5855611) baseStart_5855611 baseEnd_5855611 := by
    simpa [prefixWord, tailWord_5855611, baseEnd_5855611] using wordTrace_append hprefix tailTrace_5855611
  have hstable : (prefixWord ++ tailWord_5855611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855611).length < 2 ^ (prefixWord ++ tailWord_5855611).sum := by decide
  have hdescent : baseEnd_5855611 < baseStart_5855611 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855645 : List Nat := [1, 4, 2, 1, 4, 1, 1, 2, 2, 2, 3]
def baseStart_5855645 : Nat := 118140960795 + 5855645 * 2 ^ 59
def prefixEnd_5855645 : Nat := 4983230072969 + 3 ^ 40 * 5855645 * 2
def baseEnd_5855645 : Nat := 3006760427096847495707885

theorem tailTrace_5855645 : CollatzResearch.WordTrace tailWord_5855645 prefixEnd_5855645 3006760427096847495707885 := by
  unfold tailWord_5855645
  simp only [CollatzResearch.WordTrace]
  refine ⟨213572918871005704391904389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142381945914003802927936259 213572918871005704391904389)
  ·
    refine ⟨40044922288313569573482073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213572918871005704391904389 40044922288313569573482073)
    ·
      refine ⟨30033691716235177180111555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40044922288313569573482073 30033691716235177180111555)
      ·
        refine ⟨45050537574352765770167333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30033691716235177180111555 45050537574352765770167333)
        ·
          refine ⟨8446975795191143581906375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45050537574352765770167333 8446975795191143581906375)
          ·
            refine ⟨12670463692786715372859563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8446975795191143581906375 12670463692786715372859563)
            ·
              refine ⟨19005695539180073059289345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12670463692786715372859563 19005695539180073059289345)
              ·
                refine ⟨14254271654385054794467009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19005695539180073059289345 14254271654385054794467009)
                ·
                  refine ⟨10690703740788791095850257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14254271654385054794467009 10690703740788791095850257)
                  ·
                    refine ⟨8018027805591593321887693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10690703740788791095850257 8018027805591593321887693)
                    ·
                      refine ⟨3006760427096847495707885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8018027805591593321887693 3006760427096847495707885)
                      ·
                        rfl

theorem cell23_5855645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_5855645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855645 prefixEnd_5855645 := by exact prefixLift 5855645
  have htrace : WordTrace (prefixWord ++ tailWord_5855645) baseStart_5855645 baseEnd_5855645 := by
    simpa [prefixWord, tailWord_5855645, baseEnd_5855645] using wordTrace_append hprefix tailTrace_5855645
  have hstable : (prefixWord ++ tailWord_5855645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855645).length < 2 ^ (prefixWord ++ tailWord_5855645).sum := by decide
  have hdescent : baseEnd_5855645 < baseStart_5855645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855665 : List Nat := [1, 2, 2, 4, 1, 4, 2, 1, 6]
def baseStart_5855665 : Nat := 118140960795 + 5855665 * 2 ^ 59
def prefixEnd_5855665 : Nat := 4983230072969 + 3 ^ 40 * 5855665 * 2
def baseEnd_5855665 : Nat := 334085632967770824161977

theorem tailTrace_5855665 : CollatzResearch.WordTrace tailWord_5855665 prefixEnd_5855665 334085632967770824161977 := by
  unfold tailWord_5855665
  simp only [CollatzResearch.WordTrace]
  refine ⟨213573648330933247807632449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142382432220622165205088299 213573648330933247807632449)
  ·
    refine ⟨160180236248199935855724337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213573648330933247807632449 160180236248199935855724337)
    ·
      refine ⟨120135177186149951891793253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160180236248199935855724337 120135177186149951891793253)
      ·
        refine ⟨22525345722403115979711235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120135177186149951891793253 22525345722403115979711235)
        ·
          refine ⟨33788018583604673969566853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22525345722403115979711235 33788018583604673969566853)
          ·
            refine ⟨6335253484425876369293785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33788018583604673969566853 6335253484425876369293785)
            ·
              refine ⟨4751440113319407276970339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6335253484425876369293785 4751440113319407276970339)
              ·
                refine ⟨7127160169979110915455509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4751440113319407276970339 7127160169979110915455509)
                ·
                  refine ⟨334085632967770824161977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7127160169979110915455509 334085632967770824161977)
                  ·
                    rfl

theorem cell23_5855665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 6].length) (baseStart_5855665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855665 prefixEnd_5855665 := by exact prefixLift 5855665
  have htrace : WordTrace (prefixWord ++ tailWord_5855665) baseStart_5855665 baseEnd_5855665 := by
    simpa [prefixWord, tailWord_5855665, baseEnd_5855665] using wordTrace_append hprefix tailTrace_5855665
  have hstable : (prefixWord ++ tailWord_5855665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855665).length < 2 ^ (prefixWord ++ tailWord_5855665).sum := by decide
  have hdescent : baseEnd_5855665 < baseStart_5855665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855702 : List Nat := [5, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2]
def baseStart_5855702 : Nat := 118140960795 + 5855702 * 2 ^ 59
def prefixEnd_5855702 : Nat := 4983230072969 + 3 ^ 40 * 5855702 * 2
def baseEnd_5855702 : Nat := 3006789695494153772695123

theorem tailTrace_5855702 : CollatzResearch.WordTrace tailWord_5855702 prefixEnd_5855702 3006789695494153772695123 := by
  unfold tailWord_5855702
  simp only [CollatzResearch.WordTrace]
  refine ⟨13348437364487450195420585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142383331887866135417819573 13348437364487450195420585)
  ·
    refine ⟨10011328023365587646565439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13348437364487450195420585 10011328023365587646565439)
    ·
      refine ⟨15016992035048381469848159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10011328023365587646565439 15016992035048381469848159)
      ·
        refine ⟨22525488052572572204772239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15016992035048381469848159 22525488052572572204772239)
        ·
          refine ⟨33788232078858858307158359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22525488052572572204772239 33788232078858858307158359)
          ·
            refine ⟨50682348118288287460737539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33788232078858858307158359 50682348118288287460737539)
            ·
              refine ⟨76023522177432431191106309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50682348118288287460737539 76023522177432431191106309)
              ·
                refine ⟨14254410408268580848332433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76023522177432431191106309 14254410408268580848332433)
                ·
                  refine ⟨10690807806201435636249325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14254410408268580848332433 10690807806201435636249325)
                  ·
                    refine ⟨4009052927325538363593497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10690807806201435636249325 4009052927325538363593497)
                    ·
                      refine ⟨3006789695494153772695123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4009052927325538363593497 3006789695494153772695123)
                      ·
                        rfl

theorem cell23_5855702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_5855702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855702 prefixEnd_5855702 := by exact prefixLift 5855702
  have htrace : WordTrace (prefixWord ++ tailWord_5855702) baseStart_5855702 baseEnd_5855702 := by
    simpa [prefixWord, tailWord_5855702, baseEnd_5855702] using wordTrace_append hprefix tailTrace_5855702
  have hstable : (prefixWord ++ tailWord_5855702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855702).length < 2 ^ (prefixWord ++ tailWord_5855702).sum := by decide
  have hdescent : baseEnd_5855702 < baseStart_5855702 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855725 : List Nat := [1, 5, 1, 3, 1, 2, 2, 1, 1, 6]
def baseStart_5855725 : Nat := 118140960795 + 5855725 * 2 ^ 59
def prefixEnd_5855725 : Nat := 4983230072969 + 3 ^ 40 * 5855725 * 2
def baseEnd_5855725 : Nat := 1002267168516402394235839

theorem tailTrace_5855725 : CollatzResearch.WordTrace tailWord_5855725 prefixEnd_5855725 1002267168516402394235839 := by
  unfold tailWord_5855725
  simp only [CollatzResearch.WordTrace]
  refine ⟨213575836710715878054816629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142383891140477252036544419 213575836710715878054816629)
  ·
    refine ⟨20022734691629613567639059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 213575836710715878054816629 20022734691629613567639059)
    ·
      refine ⟨30034102037444420351458589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20022734691629613567639059 30034102037444420351458589)
      ·
        refine ⟨11262788264041657631796971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30034102037444420351458589 11262788264041657631796971)
        ·
          refine ⟨16894182396062486447695457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11262788264041657631796971 16894182396062486447695457)
          ·
            refine ⟨12670636797046864835771593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16894182396062486447695457 12670636797046864835771593)
            ·
              refine ⟨9502977597785148626828695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12670636797046864835771593 9502977597785148626828695)
              ·
                refine ⟨14254466396677722940243043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9502977597785148626828695 14254466396677722940243043)
                ·
                  refine ⟨21381699595016584410364565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14254466396677722940243043 21381699595016584410364565)
                  ·
                    refine ⟨1002267168516402394235839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21381699595016584410364565 1002267168516402394235839)
                    ·
                      rfl

theorem cell23_5855725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_5855725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855725 prefixEnd_5855725 := by exact prefixLift 5855725
  have htrace : WordTrace (prefixWord ++ tailWord_5855725) baseStart_5855725 baseEnd_5855725 := by
    simpa [prefixWord, tailWord_5855725, baseEnd_5855725] using wordTrace_append hprefix tailTrace_5855725
  have hstable : (prefixWord ++ tailWord_5855725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855725).length < 2 ^ (prefixWord ++ tailWord_5855725).sum := by decide
  have hdescent : baseEnd_5855725 < baseStart_5855725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855728 : List Nat := [2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 4]
def baseStart_5855728 : Nat := 118140960795 + 5855728 * 2 ^ 59
def prefixEnd_5855728 : Nat := 4983230072969 + 3 ^ 40 * 5855728 * 2
def baseEnd_5855728 : Nat := 3006803045991170670970003

theorem tailTrace_5855728 : CollatzResearch.WordTrace tailWord_5855728 prefixEnd_5855728 3006803045991170670970003 := by
  unfold tailWord_5855728
  simp only [CollatzResearch.WordTrace]
  refine ⟨106787973064852504783587919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142383964086470006378117225 106787973064852504783587919)
  ·
    refine ⟨160181959597278757175381879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106787973064852504783587919 160181959597278757175381879)
    ·
      refine ⟨240272939395918135763072819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160181959597278757175381879 240272939395918135763072819)
      ·
        refine ⟨360409409093877203644609229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240272939395918135763072819 360409409093877203644609229)
        ·
          refine ⟨135153528410203951366728461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 360409409093877203644609229 135153528410203951366728461)
          ·
            refine ⟨50682573153826481762523173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135153528410203951366728461 50682573153826481762523173)
            ·
              refine ⟨9502982466342465330473095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50682573153826481762523173 9502982466342465330473095)
              ·
                refine ⟨14254473699513697995709643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9502982466342465330473095 14254473699513697995709643)
                ·
                  refine ⟨21381710549270546993564465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14254473699513697995709643 21381710549270546993564465)
                  ·
                    refine ⟨16036282911952910245173349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21381710549270546993564465 16036282911952910245173349)
                    ·
                      refine ⟨3006803045991170670970003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16036282911952910245173349 3006803045991170670970003)
                      ·
                        rfl

theorem cell23_5855728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 4].length) (baseStart_5855728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855728 prefixEnd_5855728 := by exact prefixLift 5855728
  have htrace : WordTrace (prefixWord ++ tailWord_5855728) baseStart_5855728 baseEnd_5855728 := by
    simpa [prefixWord, tailWord_5855728, baseEnd_5855728] using wordTrace_append hprefix tailTrace_5855728
  have hstable : (prefixWord ++ tailWord_5855728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855728).length < 2 ^ (prefixWord ++ tailWord_5855728).sum := by decide
  have hdescent : baseEnd_5855728 < baseStart_5855728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855746 : List Nat := [3, 4, 1, 2, 3, 1, 2, 1, 1, 5]
def baseStart_5855746 : Nat := 118140960795 + 5855746 * 2 ^ 59
def prefixEnd_5855746 : Nat := 4983230072969 + 3 ^ 40 * 5855746 * 2
def baseEnd_5855746 : Nat := 1002270762880983866848307

theorem tailTrace_5855746 : CollatzResearch.WordTrace tailWord_5855746 prefixEnd_5855746 1002270762880983866848307 := by
  unfold tailWord_5855746
  simp only [CollatzResearch.WordTrace]
  refine ⟨53394150660909949660332773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142384401762426532427554061 53394150660909949660332773)
  ·
    refine ⟨10011403248920615561312395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53394150660909949660332773 10011403248920615561312395)
    ·
      refine ⟨15017104873380923341968593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10011403248920615561312395 15017104873380923341968593)
      ·
        refine ⟨11262828655035692506476445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15017104873380923341968593 11262828655035692506476445)
        ·
          refine ⟨4223560745638384689928667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11262828655035692506476445 4223560745638384689928667)
          ·
            refine ⟨6335341118457577034893001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4223560745638384689928667 6335341118457577034893001)
            ·
              refine ⟨4751505838843182776169751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6335341118457577034893001 4751505838843182776169751)
              ·
                refine ⟨7127258758264774164254627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4751505838843182776169751 7127258758264774164254627)
                ·
                  refine ⟨10690888137397161246381941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7127258758264774164254627 10690888137397161246381941)
                  ·
                    refine ⟨1002270762880983866848307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10690888137397161246381941 1002270762880983866848307)
                    ·
                      rfl

theorem cell23_5855746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_5855746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855746 prefixEnd_5855746 := by exact prefixLift 5855746
  have htrace : WordTrace (prefixWord ++ tailWord_5855746) baseStart_5855746 baseEnd_5855746 := by
    simpa [prefixWord, tailWord_5855746, baseEnd_5855746] using wordTrace_append hprefix tailTrace_5855746
  have hstable : (prefixWord ++ tailWord_5855746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855746).length < 2 ^ (prefixWord ++ tailWord_5855746).sum := by decide
  have hdescent : baseEnd_5855746 < baseStart_5855746 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855761 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 5]
def baseStart_5855761 : Nat := 118140960795 + 5855761 * 2 ^ 59
def prefixEnd_5855761 : Nat := 4983230072969 + 3 ^ 40 * 5855761 * 2
def baseEnd_5855761 : Nat := 3006819990852769041857351

theorem tailTrace_5855761 : CollatzResearch.WordTrace tailWord_5855761 prefixEnd_5855761 3006819990852769041857351 := by
  unfold tailWord_5855761
  simp only [CollatzResearch.WordTrace]
  refine ⟨213577149738585456203127137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142384766492390304135418091 213577149738585456203127137)
  ·
    refine ⟨160182862303939092152345353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213577149738585456203127137 160182862303939092152345353)
    ·
      refine ⟨120137146727954319114259015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160182862303939092152345353 120137146727954319114259015)
      ·
        refine ⟨180205720091931478671388523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120137146727954319114259015 180205720091931478671388523)
        ·
          refine ⟨270308580137897218007082785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180205720091931478671388523 270308580137897218007082785)
          ·
            refine ⟨202731435103422913505312089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270308580137897218007082785 202731435103422913505312089)
            ·
              refine ⟨152048576327567185128984067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202731435103422913505312089 152048576327567185128984067)
              ·
                refine ⟨228072864491350777693476101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152048576327567185128984067 228072864491350777693476101)
                ·
                  refine ⟨42763662092128270817526769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 228072864491350777693476101 42763662092128270817526769)
                  ·
                    refine ⟨32072746569096203113145077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42763662092128270817526769 32072746569096203113145077)
                    ·
                      refine ⟨3006819990852769041857351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32072746569096203113145077 3006819990852769041857351)
                      ·
                        rfl

theorem cell23_5855761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_5855761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855761 prefixEnd_5855761 := by exact prefixLift 5855761
  have htrace : WordTrace (prefixWord ++ tailWord_5855761) baseStart_5855761 baseEnd_5855761 := by
    simpa [prefixWord, tailWord_5855761, baseEnd_5855761] using wordTrace_append hprefix tailTrace_5855761
  have hstable : (prefixWord ++ tailWord_5855761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855761).length < 2 ^ (prefixWord ++ tailWord_5855761).sum := by decide
  have hdescent : baseEnd_5855761 < baseStart_5855761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855765 : List Nat := [1, 3, 2, 1, 3, 1, 3, 1, 4, 1, 3]
def baseStart_5855765 : Nat := 118140960795 + 5855765 * 2 ^ 59
def prefixEnd_5855765 : Nat := 4983230072969 + 3 ^ 40 * 5855765 * 2
def baseEnd_5855765 : Nat := 3006822044775387026207333

theorem tailTrace_5855765 : CollatzResearch.WordTrace tailWord_5855765 prefixEnd_5855765 3006822044775387026207333 := by
  unfold tailWord_5855765
  simp only [CollatzResearch.WordTrace]
  refine ⟨213577295630570964886272749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142384863753713976590848499 213577295630570964886272749)
  ·
    refine ⟨80091485861464111832352281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213577295630570964886272749 80091485861464111832352281)
    ·
      refine ⟨60068614396098083874264211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80091485861464111832352281 60068614396098083874264211)
      ·
        refine ⟨90102921594147125811396317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60068614396098083874264211 90102921594147125811396317)
        ·
          refine ⟨33788595597805172179273619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90102921594147125811396317 33788595597805172179273619)
          ·
            refine ⟨50682893396707758268910429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33788595597805172179273619 50682893396707758268910429)
            ·
              refine ⟨19006085023765409350841411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50682893396707758268910429 19006085023765409350841411)
              ·
                refine ⟨28509127535648114026262117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19006085023765409350841411 28509127535648114026262117)
                ·
                  refine ⟨5345461412934021379924147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28509127535648114026262117 5345461412934021379924147)
                  ·
                    refine ⟨8018192119401032069886221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5345461412934021379924147 8018192119401032069886221)
                    ·
                      refine ⟨3006822044775387026207333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8018192119401032069886221 3006822044775387026207333)
                      ·
                        rfl

theorem cell23_5855765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 4, 1, 3].length) (baseStart_5855765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855765 prefixEnd_5855765 := by exact prefixLift 5855765
  have htrace : WordTrace (prefixWord ++ tailWord_5855765) baseStart_5855765 baseEnd_5855765 := by
    simpa [prefixWord, tailWord_5855765, baseEnd_5855765] using wordTrace_append hprefix tailTrace_5855765
  have hstable : (prefixWord ++ tailWord_5855765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855765).length < 2 ^ (prefixWord ++ tailWord_5855765).sum := by decide
  have hdescent : baseEnd_5855765 < baseStart_5855765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855791 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 5]
def baseStart_5855791 : Nat := 118140960795 + 5855791 * 2 ^ 59
def prefixEnd_5855791 : Nat := 4983230072969 + 3 ^ 40 * 5855791 * 2
def baseEnd_5855791 : Nat := 3006835395272403924482213

theorem tailTrace_5855791 : CollatzResearch.WordTrace tailWord_5855791 prefixEnd_5855791 3006835395272403924482213 := by
  unfold tailWord_5855791
  simp only [CollatzResearch.WordTrace]
  refine ⟨213578243928476771326719227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142385495952317847551146151 213578243928476771326719227)
  ·
    refine ⟨320367365892715156990078841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213578243928476771326719227 320367365892715156990078841)
    ·
      refine ⟨240275524419536367742559131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320367365892715156990078841 240275524419536367742559131)
      ·
        refine ⟨360413286629304551613838697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240275524419536367742559131 360413286629304551613838697)
        ·
          refine ⟨270309964971978413710379023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360413286629304551613838697 270309964971978413710379023)
          ·
            refine ⟨405464947457967620565568535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270309964971978413710379023 405464947457967620565568535)
            ·
              refine ⟨608197421186951430848352803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 405464947457967620565568535 608197421186951430848352803)
              ·
                refine ⟨912296131780427146272529205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 608197421186951430848352803 912296131780427146272529205)
                ·
                  refine ⟨85527762354415044963049613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 912296131780427146272529205 85527762354415044963049613)
                  ·
                    refine ⟨32072910882905641861143605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85527762354415044963049613 32072910882905641861143605)
                    ·
                      refine ⟨3006835395272403924482213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32072910882905641861143605 3006835395272403924482213)
                      ·
                        rfl

theorem cell23_5855791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 5].length) (baseStart_5855791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855791 prefixEnd_5855791 := by exact prefixLift 5855791
  have htrace : WordTrace (prefixWord ++ tailWord_5855791) baseStart_5855791 baseEnd_5855791 := by
    simpa [prefixWord, tailWord_5855791, baseEnd_5855791] using wordTrace_append hprefix tailTrace_5855791
  have hstable : (prefixWord ++ tailWord_5855791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855791).length < 2 ^ (prefixWord ++ tailWord_5855791).sum := by decide
  have hdescent : baseEnd_5855791 < baseStart_5855791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855811 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 9]
def baseStart_5855811 : Nat := 118140960795 + 5855811 * 2 ^ 59
def prefixEnd_5855811 : Nat := 4983230072969 + 3 ^ 40 * 5855811 * 2
def baseEnd_5855811 : Nat := 334093962765054871803569

theorem tailTrace_5855811 : CollatzResearch.WordTrace tailWord_5855811 prefixEnd_5855811 334093962765054871803569 := by
  unfold tailWord_5855811
  simp only [CollatzResearch.WordTrace]
  refine ⟨213578973388404314742447287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142385982258936209828298191 213578973388404314742447287)
  ·
    refine ⟨320368460082606472113670931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213578973388404314742447287 320368460082606472113670931)
    ·
      refine ⟨480552690123909708170506397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320368460082606472113670931 480552690123909708170506397)
      ·
        refine ⟨180207258796466140563939899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 480552690123909708170506397 180207258796466140563939899)
        ·
          refine ⟨270310888194699210845909849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180207258796466140563939899 270310888194699210845909849)
          ·
            refine ⟨202733166146024408134432387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270310888194699210845909849 202733166146024408134432387)
            ·
              refine ⟨304099749219036612201648581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202733166146024408134432387 304099749219036612201648581)
              ·
                refine ⟨57018702978569364787809109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 304099749219036612201648581 57018702978569364787809109)
                ·
                  refine ⟨334093962765054871803569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57018702978569364787809109 334093962765054871803569)
                  ·
                    rfl

theorem cell23_5855811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 9].length) (baseStart_5855811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855811 prefixEnd_5855811 := by exact prefixLift 5855811
  have htrace : WordTrace (prefixWord ++ tailWord_5855811) baseStart_5855811 baseEnd_5855811 := by
    simpa [prefixWord, tailWord_5855811, baseEnd_5855811] using wordTrace_append hprefix tailTrace_5855811
  have hstable : (prefixWord ++ tailWord_5855811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855811).length < 2 ^ (prefixWord ++ tailWord_5855811).sum := by decide
  have hdescent : baseEnd_5855811 < baseStart_5855811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855822 : List Nat := [4, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2]
def baseStart_5855822 : Nat := 118140960795 + 5855822 * 2 ^ 59
def prefixEnd_5855822 : Nat := 4983230072969 + 3 ^ 40 * 5855822 * 2
def baseEnd_5855822 : Nat := 3006851313172693303194571

theorem tailTrace_5855822 : CollatzResearch.WordTrace tailWord_5855822 prefixEnd_5855822 3006851313172693303194571 := by
  unfold tailWord_5855822
  simp only [CollatzResearch.WordTrace]
  refine ⟨26697421823920557952637215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142386249727576309080731813 26697421823920557952637215)
  ·
    refine ⟨40046132735880836928955823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26697421823920557952637215 40046132735880836928955823)
    ·
      refine ⟨60069199103821255393433735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40046132735880836928955823 60069199103821255393433735)
      ·
        refine ⟨90103798655731883090150603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60069199103821255393433735 90103798655731883090150603)
        ·
          refine ⟨135155697983597824635225905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90103798655731883090150603 135155697983597824635225905)
          ·
            refine ⟨101366773487698368476419429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135155697983597824635225905 101366773487698368476419429)
            ·
              refine ⟨19006270028943444089328643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101366773487698368476419429 19006270028943444089328643)
              ·
                refine ⟨28509405043415166133992965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19006270028943444089328643 28509405043415166133992965)
                ·
                  refine ⟨5345513445640343650123681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28509405043415166133992965 5345513445640343650123681)
                  ·
                    refine ⟨4009135084230257737592761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5345513445640343650123681 4009135084230257737592761)
                    ·
                      refine ⟨3006851313172693303194571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4009135084230257737592761 3006851313172693303194571)
                      ·
                        rfl

theorem cell23_5855822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 4, 2, 2].length) (baseStart_5855822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855822 prefixEnd_5855822 := by exact prefixLift 5855822
  have htrace : WordTrace (prefixWord ++ tailWord_5855822) baseStart_5855822 baseEnd_5855822 := by
    simpa [prefixWord, tailWord_5855822, baseEnd_5855822] using wordTrace_append hprefix tailTrace_5855822
  have hstable : (prefixWord ++ tailWord_5855822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855822).length < 2 ^ (prefixWord ++ tailWord_5855822).sum := by decide
  have hdescent : baseEnd_5855822 < baseStart_5855822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855868 : List Nat := [2, 2, 2, 1, 1, 2, 3, 2, 1, 2, 5]
def baseStart_5855868 : Nat := 118140960795 + 5855868 * 2 ^ 59
def prefixEnd_5855868 : Nat := 4983230072969 + 3 ^ 40 * 5855868 * 2
def baseEnd_5855868 : Nat := 3006874933282800123219359

theorem tailTrace_5855868 : CollatzResearch.WordTrace tailWord_5855868 prefixEnd_5855868 3006874933282800123219359 := by
  unfold tailWord_5855868
  simp only [CollatzResearch.WordTrace]
  refine ⟨106790526174598906738636129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142387368232798542318181505 106790526174598906738636129)
  ·
    refine ⟨80092894630949180053977097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106790526174598906738636129 80092894630949180053977097)
    ·
      refine ⟨60069670973211885040482823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80092894630949180053977097 60069670973211885040482823)
      ·
        refine ⟨90104506459817827560724235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60069670973211885040482823 90104506459817827560724235)
        ·
          refine ⟨135156759689726741341086353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90104506459817827560724235 135156759689726741341086353)
          ·
            refine ⟨101367569767295056005814765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135156759689726741341086353 101367569767295056005814765)
            ·
              refine ⟨38012838662735646002180537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101367569767295056005814765 38012838662735646002180537)
              ·
                refine ⟨28509628997051734501635403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38012838662735646002180537 28509628997051734501635403)
                ·
                  refine ⟨42764443495577601752453105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28509628997051734501635403 42764443495577601752453105)
                  ·
                    refine ⟨32073332621683201314339829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42764443495577601752453105 32073332621683201314339829)
                    ·
                      refine ⟨3006874933282800123219359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32073332621683201314339829 3006874933282800123219359)
                      ·
                        rfl

theorem cell23_5855868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_5855868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855868 prefixEnd_5855868 := by exact prefixLift 5855868
  have htrace : WordTrace (prefixWord ++ tailWord_5855868) baseStart_5855868 baseEnd_5855868 := by
    simpa [prefixWord, tailWord_5855868, baseEnd_5855868] using wordTrace_append hprefix tailTrace_5855868
  have hstable : (prefixWord ++ tailWord_5855868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855868).length < 2 ^ (prefixWord ++ tailWord_5855868).sum := by decide
  have hdescent : baseEnd_5855868 < baseStart_5855868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855925 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 2, 1, 6]
def baseStart_5855925 : Nat := 118140960795 + 5855925 * 2 ^ 59
def prefixEnd_5855925 : Nat := 4983230072969 + 3 ^ 40 * 5855925 * 2
def baseEnd_5855925 : Nat := 3006904201680106400206597

theorem tailTrace_5855925 : CollatzResearch.WordTrace tailWord_5855925 prefixEnd_5855925 3006904201680106400206597 := by
  unfold tailWord_5855925
  simp only [CollatzResearch.WordTrace]
  refine ⟨213583131309991312212097229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142388754206660874808064819 213583131309991312212097229)
  ·
    refine ⟨80093674241246742079536461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213583131309991312212097229 80093674241246742079536461)
    ·
      refine ⟨30035127840467528279826173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80093674241246742079536461 30035127840467528279826173)
      ·
        refine ⟨11263172940175323104934815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30035127840467528279826173 11263172940175323104934815)
        ·
          refine ⟨16894759410262984657402223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11263172940175323104934815 16894759410262984657402223)
          ·
            refine ⟨25342139115394476986103335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16894759410262984657402223 25342139115394476986103335)
            ·
              refine ⟨38013208673091715479155003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25342139115394476986103335 38013208673091715479155003)
              ·
                refine ⟨57019813009637573218732505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38013208673091715479155003 57019813009637573218732505)
                ·
                  refine ⟨42764859757228179914049379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57019813009637573218732505 42764859757228179914049379)
                  ·
                    refine ⟨64147289635842269871074069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42764859757228179914049379 64147289635842269871074069)
                    ·
                      refine ⟨3006904201680106400206597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64147289635842269871074069 3006904201680106400206597)
                      ·
                        rfl

theorem cell23_5855925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_5855925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855925 prefixEnd_5855925 := by exact prefixLift 5855925
  have htrace : WordTrace (prefixWord ++ tailWord_5855925) baseStart_5855925 baseEnd_5855925 := by
    simpa [prefixWord, tailWord_5855925, baseEnd_5855925] using wordTrace_append hprefix tailTrace_5855925
  have hstable : (prefixWord ++ tailWord_5855925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855925).length < 2 ^ (prefixWord ++ tailWord_5855925).sum := by decide
  have hdescent : baseEnd_5855925 < baseStart_5855925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855935 : List Nat := [1, 1, 2, 2, 2, 4, 3, 2, 6]
def baseStart_5855935 : Nat := 118140960795 + 5855935 * 2 ^ 59
def prefixEnd_5855935 : Nat := 4983230072969 + 3 ^ 40 * 5855935 * 2
def baseEnd_5855935 : Nat := 334101037387405706786839

theorem tailTrace_5855935 : CollatzResearch.WordTrace tailWord_5855935 prefixEnd_5855935 334101037387405706786839 := by
  unfold tailWord_5855935
  simp only [CollatzResearch.WordTrace]
  refine ⟨213583496039955083919961259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142388997359970055946640839 213583496039955083919961259)
  ·
    refine ⟨320375244059932625879941889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213583496039955083919961259 320375244059932625879941889)
    ·
      refine ⟨240281433044949469409956417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320375244059932625879941889 240281433044949469409956417)
      ·
        refine ⟨180211074783712102057467313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240281433044949469409956417 180211074783712102057467313)
        ·
          refine ⟨135158306087784076543100485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180211074783712102057467313 135158306087784076543100485)
          ·
            refine ⟨25342182391459514351831341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135158306087784076543100485 25342182391459514351831341)
            ·
              refine ⟨9503318396797317881936753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25342182391459514351831341 9503318396797317881936753)
              ·
                refine ⟨7127488797597988411452565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9503318396797317881936753 7127488797597988411452565)
                ·
                  refine ⟨334101037387405706786839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7127488797597988411452565 334101037387405706786839)
                  ·
                    rfl

theorem cell23_5855935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 6].length) (baseStart_5855935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855935 prefixEnd_5855935 := by exact prefixLift 5855935
  have htrace : WordTrace (prefixWord ++ tailWord_5855935) baseStart_5855935 baseEnd_5855935 := by
    simpa [prefixWord, tailWord_5855935, baseEnd_5855935] using wordTrace_append hprefix tailTrace_5855935
  have hstable : (prefixWord ++ tailWord_5855935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855935).length < 2 ^ (prefixWord ++ tailWord_5855935).sum := by decide
  have hdescent : baseEnd_5855935 < baseStart_5855935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855962 : List Nat := [3, 1, 1, 2, 2, 2, 1, 4, 3, 1, 3]
def baseStart_5855962 : Nat := 118140960795 + 5855962 * 2 ^ 59
def prefixEnd_5855962 : Nat := 4983230072969 + 3 ^ 40 * 5855962 * 2
def baseEnd_5855962 : Nat := 3006923200464322755443927

theorem tailTrace_5855962 : CollatzResearch.WordTrace tailWord_5855962 prefixEnd_5855962 3006923200464322755443927 := by
  unfold tailWord_5855962
  simp only [CollatzResearch.WordTrace]
  refine ⟨53396120202714316882798535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142389653873904845020796093 53396120202714316882798535)
  ·
    refine ⟨80094180304071475324197803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53396120202714316882798535 80094180304071475324197803)
    ·
      refine ⟨120141270456107212986296705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80094180304071475324197803 120141270456107212986296705)
      ·
        refine ⟨90105952842080409739722529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120141270456107212986296705 90105952842080409739722529)
        ·
          refine ⟨67579464631560307304791897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90105952842080409739722529 67579464631560307304791897)
          ·
            refine ⟨50684598473670230478593923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67579464631560307304791897 50684598473670230478593923)
            ·
              refine ⟨76026897710505345717890885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50684598473670230478593923 76026897710505345717890885)
              ·
                refine ⟨14255043320719752322104541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76026897710505345717890885 14255043320719752322104541)
                ·
                  refine ⟨5345641245269907120789203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14255043320719752322104541 5345641245269907120789203)
                  ·
                    refine ⟨8018461867904860681183805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5345641245269907120789203 8018461867904860681183805)
                    ·
                      refine ⟨3006923200464322755443927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8018461867904860681183805 3006923200464322755443927)
                      ·
                        rfl

theorem cell23_5855962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 3, 1, 3].length) (baseStart_5855962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855962 prefixEnd_5855962 := by exact prefixLift 5855962
  have htrace : WordTrace (prefixWord ++ tailWord_5855962) baseStart_5855962 baseEnd_5855962 := by
    simpa [prefixWord, tailWord_5855962, baseEnd_5855962] using wordTrace_append hprefix tailTrace_5855962
  have hstable : (prefixWord ++ tailWord_5855962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855962).length < 2 ^ (prefixWord ++ tailWord_5855962).sum := by decide
  have hdescent : baseEnd_5855962 < baseStart_5855962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855972 : List Nat := [2, 3, 1, 1, 1, 4, 2, 1, 1, 5, 2]
def baseStart_5855972 : Nat := 118140960795 + 5855972 * 2 ^ 59
def prefixEnd_5855972 : Nat := 4983230072969 + 3 ^ 40 * 5855972 * 2
def baseEnd_5855972 : Nat := 3006928335270867716318881

theorem tailTrace_5855972 : CollatzResearch.WordTrace tailWord_5855972 prefixEnd_5855972 3006928335270867716318881 := by
  unfold tailWord_5855972
  simp only [CollatzResearch.WordTrace]
  refine ⟨106792422770410519619529085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142389897027214026159372113 106792422770410519619529085)
  ·
    refine ⟨40047158538903944857323407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106792422770410519619529085 40047158538903944857323407)
    ·
      refine ⟨60070737808355917285985111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40047158538903944857323407 60070737808355917285985111)
      ·
        refine ⟨90106106712533875928977667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60070737808355917285985111 90106106712533875928977667)
        ·
          refine ⟨135159160068800813893466501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90106106712533875928977667 135159160068800813893466501)
          ·
            refine ⟨25342342512900152605024969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135159160068800813893466501 25342342512900152605024969)
            ·
              refine ⟨19006756884675114453768727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25342342512900152605024969 19006756884675114453768727)
              ·
                refine ⟨28510135327012671680653091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19006756884675114453768727 28510135327012671680653091)
                ·
                  refine ⟨42765202990519007520979637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28510135327012671680653091 42765202990519007520979637)
                  ·
                    refine ⟨4009237780361156955091841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42765202990519007520979637 4009237780361156955091841)
                    ·
                      refine ⟨3006928335270867716318881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4009237780361156955091841 3006928335270867716318881)
                      ·
                        rfl

theorem cell23_5855972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 1, 5, 2].length) (baseStart_5855972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855972 prefixEnd_5855972 := by exact prefixLift 5855972
  have htrace : WordTrace (prefixWord ++ tailWord_5855972) baseStart_5855972 baseEnd_5855972 := by
    simpa [prefixWord, tailWord_5855972, baseEnd_5855972] using wordTrace_append hprefix tailTrace_5855972
  have hstable : (prefixWord ++ tailWord_5855972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855972).length < 2 ^ (prefixWord ++ tailWord_5855972).sum := by decide
  have hdescent : baseEnd_5855972 < baseStart_5855972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5855982 : List Nat := [4, 1, 2, 1, 1, 3, 2, 3, 1, 5]
def baseStart_5855982 : Nat := 118140960795 + 5855982 * 2 ^ 59
def prefixEnd_5855982 : Nat := 4983230072969 + 3 ^ 40 * 5855982 * 2
def baseEnd_5855982 : Nat := 1002311156692470892397945

theorem tailTrace_5855982 : CollatzResearch.WordTrace tailWord_5855982 prefixEnd_5855982 1002311156692470892397945 := by
  unfold tailWord_5855982
  simp only [CollatzResearch.WordTrace]
  refine ⟨26698151283848101368365275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142390140180523207297948133 26698151283848101368365275)
  ·
    refine ⟨40047226925772152052547913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26698151283848101368365275 40047226925772152052547913)
    ·
      refine ⟨30035420194329114039410935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40047226925772152052547913 30035420194329114039410935)
      ·
        refine ⟨45053130291493671059116403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30035420194329114039410935 45053130291493671059116403)
        ·
          refine ⟨67579695437240506588674605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45053130291493671059116403 67579695437240506588674605)
          ·
            refine ⟨25342385788965189970752977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67579695437240506588674605 25342385788965189970752977)
            ·
              refine ⟨19006789341723892478064733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25342385788965189970752977 19006789341723892478064733)
              ·
                refine ⟨7127546003146459679274275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19006789341723892478064733 7127546003146459679274275)
                ·
                  refine ⟨10691319004719689518911413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7127546003146459679274275 10691319004719689518911413)
                  ·
                    refine ⟨1002311156692470892397945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10691319004719689518911413 1002311156692470892397945)
                    ·
                      rfl

theorem cell23_5855982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_5855982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5855982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5855982 prefixEnd_5855982 := by exact prefixLift 5855982
  have htrace : WordTrace (prefixWord ++ tailWord_5855982) baseStart_5855982 baseEnd_5855982 := by
    simpa [prefixWord, tailWord_5855982, baseEnd_5855982] using wordTrace_append hprefix tailTrace_5855982
  have hstable : (prefixWord ++ tailWord_5855982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5855982).length < 2 ^ (prefixWord ++ tailWord_5855982).sum := by decide
  have hdescent : baseEnd_5855982 < baseStart_5855982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5855982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856015 : List Nat := [1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 4]
def baseStart_5856015 : Nat := 118140960795 + 5856015 * 2 ^ 59
def prefixEnd_5856015 : Nat := 4983230072969 + 3 ^ 40 * 5856015 * 2
def baseEnd_5856015 : Nat := 3006950414939011048081183

theorem tailTrace_5856015 : CollatzResearch.WordTrace tailWord_5856015 prefixEnd_5856015 3006950414939011048081183 := by
  unfold tailWord_5856015
  simp only [CollatzResearch.WordTrace]
  refine ⟨213586413879665257582873499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142390942586443505055248999 213586413879665257582873499)
  ·
    refine ⟨320379620819497886374310249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213586413879665257582873499 320379620819497886374310249)
    ·
      refine ⟨240284715614623414780732687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320379620819497886374310249 240284715614623414780732687)
      ·
        refine ⟨360427073421935122171099031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240284715614623414780732687 360427073421935122171099031)
        ·
          refine ⟨540640610132902683256648547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360427073421935122171099031 540640610132902683256648547)
          ·
            refine ⟨810960915199354024884972821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540640610132902683256648547 810960915199354024884972821)
            ·
              refine ⟨38013792899969719916483101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 810960915199354024884972821 38013792899969719916483101)
              ·
                refine ⟨14255172337488644968681163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38013792899969719916483101 14255172337488644968681163)
                ·
                  refine ⟨21382758506232967453021745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14255172337488644968681163 21382758506232967453021745)
                  ·
                    refine ⟨16037068879674725589766309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21382758506232967453021745 16037068879674725589766309)
                    ·
                      refine ⟨3006950414939011048081183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16037068879674725589766309 3006950414939011048081183)
                      ·
                        rfl

theorem cell23_5856015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 4].length) (baseStart_5856015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856015 prefixEnd_5856015 := by exact prefixLift 5856015
  have htrace : WordTrace (prefixWord ++ tailWord_5856015) baseStart_5856015 baseEnd_5856015 := by
    simpa [prefixWord, tailWord_5856015, baseEnd_5856015] using wordTrace_append hprefix tailTrace_5856015
  have hstable : (prefixWord ++ tailWord_5856015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856015).length < 2 ^ (prefixWord ++ tailWord_5856015).sum := by decide
  have hdescent : baseEnd_5856015 < baseStart_5856015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856029 : List Nat := [1, 4, 2, 4, 1, 1, 1, 2, 1, 6]
def baseStart_5856029 : Nat := 118140960795 + 5856029 * 2 ^ 59
def prefixEnd_5856029 : Nat := 4983230072969 + 3 ^ 40 * 5856029 * 2
def baseEnd_5856029 : Nat := 1002319201222724664435373

theorem tailTrace_5856029 : CollatzResearch.WordTrace tailWord_5856029 prefixEnd_5856029 1002319201222724664435373 := by
  unfold tailWord_5856029
  simp only [CollatzResearch.WordTrace]
  refine ⟨213586924501614537973883141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142391283001076358649255427 213586924501614537973883141)
  ·
    refine ⟨40047548344052725870103089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213586924501614537973883141 40047548344052725870103089)
    ·
      refine ⟨30035661258039544402577317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40047548344052725870103089 30035661258039544402577317)
      ·
        refine ⟨5631686485882414575483247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30035661258039544402577317 5631686485882414575483247)
        ·
          refine ⟨8447529728823621863224871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5631686485882414575483247 8447529728823621863224871)
          ·
            refine ⟨12671294593235432794837307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8447529728823621863224871 12671294593235432794837307)
            ·
              refine ⟨19006941889853149192255961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12671294593235432794837307 19006941889853149192255961)
              ·
                refine ⟨14255206417389861894191971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19006941889853149192255961 14255206417389861894191971)
                ·
                  refine ⟨21382809626084792841287957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14255206417389861894191971 21382809626084792841287957)
                  ·
                    refine ⟨1002319201222724664435373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21382809626084792841287957 1002319201222724664435373)
                    ·
                      rfl

theorem cell23_5856029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_5856029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856029 prefixEnd_5856029 := by exact prefixLift 5856029
  have htrace : WordTrace (prefixWord ++ tailWord_5856029) baseStart_5856029 baseEnd_5856029 := by
    simpa [prefixWord, tailWord_5856029, baseEnd_5856029] using wordTrace_append hprefix tailTrace_5856029
  have hstable : (prefixWord ++ tailWord_5856029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856029).length < 2 ^ (prefixWord ++ tailWord_5856029).sum := by decide
  have hdescent : baseEnd_5856029 < baseStart_5856029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856032 : List Nat := [2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 4]
def baseStart_5856032 : Nat := 118140960795 + 5856032 * 2 ^ 59
def prefixEnd_5856032 : Nat := 4983230072969 + 3 ^ 40 * 5856032 * 2
def baseEnd_5856032 : Nat := 3006959144110137481568605

theorem tailTrace_5856032 : CollatzResearch.WordTrace tailWord_5856032 prefixEnd_5856032 3006959144110137481568605 := by
  unfold tailWord_5856032
  simp only [CollatzResearch.WordTrace]
  refine ⟨106793516960301834743121175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142391355947069112990828233 106793516960301834743121175)
  ·
    refine ⟨160190275440452752114681763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106793516960301834743121175 160190275440452752114681763)
    ·
      refine ⟨240285413160679128172022645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160190275440452752114681763 240285413160679128172022645)
      ·
        refine ⟨22526757483813668266127123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 240285413160679128172022645 22526757483813668266127123)
        ·
          refine ⟨33790136225720502399190685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22526757483813668266127123 33790136225720502399190685)
          ·
            refine ⟨12671301084645188399696507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33790136225720502399190685 12671301084645188399696507)
            ·
              refine ⟨19006951626967782599544761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12671301084645188399696507 19006951626967782599544761)
              ·
                refine ⟨14255213720225836949658571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19006951626967782599544761 14255213720225836949658571)
                ·
                  refine ⟨21382820580338755424487857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14255213720225836949658571 21382820580338755424487857)
                  ·
                    refine ⟨16037115435254066568365893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21382820580338755424487857 16037115435254066568365893)
                    ·
                      refine ⟨3006959144110137481568605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16037115435254066568365893 3006959144110137481568605)
                      ·
                        rfl

theorem cell23_5856032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_5856032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856032 prefixEnd_5856032 := by exact prefixLift 5856032
  have htrace : WordTrace (prefixWord ++ tailWord_5856032) baseStart_5856032 baseEnd_5856032 := by
    simpa [prefixWord, tailWord_5856032, baseEnd_5856032] using wordTrace_append hprefix tailTrace_5856032
  have hstable : (prefixWord ++ tailWord_5856032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856032).length < 2 ^ (prefixWord ++ tailWord_5856032).sum := by decide
  have hdescent : baseEnd_5856032 < baseStart_5856032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856036 : List Nat := [2, 3, 1, 3, 3, 1, 3, 1, 1, 1, 4]
def baseStart_5856036 : Nat := 118140960795 + 5856036 * 2 ^ 59
def prefixEnd_5856036 : Nat := 4983230072969 + 3 ^ 40 * 5856036 * 2
def baseEnd_5856036 : Nat := 3006961198032755465918587

theorem tailTrace_5856036 : CollatzResearch.WordTrace tailWord_5856036 prefixEnd_5856036 3006961198032755465918587 := by
  unfold tailWord_5856036
  simp only [CollatzResearch.WordTrace]
  refine ⟨106793589906294589084693981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142391453208392785446258641 106793589906294589084693981)
  ·
    refine ⟨40047596214860470906760243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106793589906294589084693981 40047596214860470906760243)
    ·
      refine ⟨60071394322290706360140365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40047596214860470906760243 60071394322290706360140365)
      ·
        refine ⟨22526772870859014885052637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60071394322290706360140365 22526772870859014885052637)
        ·
          refine ⟨8447539826572130581894739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22526772870859014885052637 8447539826572130581894739)
          ·
            refine ⟨12671309739858195872842109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8447539826572130581894739 12671309739858195872842109)
            ·
              refine ⟨4751741152446823452315791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12671309739858195872842109 4751741152446823452315791)
              ·
                refine ⟨7127611728670235178473687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4751741152446823452315791 7127611728670235178473687)
                ·
                  refine ⟨10691417593005352767710531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7127611728670235178473687 10691417593005352767710531)
                  ·
                    refine ⟨16037126389508029151565797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10691417593005352767710531 16037126389508029151565797)
                    ·
                      refine ⟨3006961198032755465918587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16037126389508029151565797 3006961198032755465918587)
                      ·
                        rfl

theorem cell23_5856036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_5856036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856036 prefixEnd_5856036 := by exact prefixLift 5856036
  have htrace : WordTrace (prefixWord ++ tailWord_5856036) baseStart_5856036 baseEnd_5856036 := by
    simpa [prefixWord, tailWord_5856036, baseEnd_5856036] using wordTrace_append hprefix tailTrace_5856036
  have hstable : (prefixWord ++ tailWord_5856036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856036).length < 2 ^ (prefixWord ++ tailWord_5856036).sum := by decide
  have hdescent : baseEnd_5856036 < baseStart_5856036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856042 : List Nat := [3, 1, 4, 3, 1, 11]
def baseStart_5856042 : Nat := 118140960795 + 5856042 * 2 ^ 59
def prefixEnd_5856042 : Nat := 4983230072969 + 3 ^ 40 * 5856042 * 2
def baseEnd_5856042 : Nat := 12374338596364948322813

theorem tailTrace_5856042 : CollatzResearch.WordTrace tailWord_5856042 prefixEnd_5856042 12374338596364948322813 := by
  unfold tailWord_5856042
  simp only [CollatzResearch.WordTrace]
  refine ⟨53396849662641860298526595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142391599100378294129404253 53396849662641860298526595)
  ·
    refine ⟨80095274493962790447789893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53396849662641860298526595 80095274493962790447789893)
    ·
      refine ⟨15017863967618023208960605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80095274493962790447789893 15017863967618023208960605)
      ·
        refine ⟨5631698987856758703360227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15017863967618023208960605 5631698987856758703360227)
        ·
          refine ⟨8447548481785138055040341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5631698987856758703360227 8447548481785138055040341)
          ·
            refine ⟨12374338596364948322813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8447548481785138055040341 12374338596364948322813)
            ·
              rfl

theorem cell23_5856042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 11].length) (baseStart_5856042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856042 prefixEnd_5856042 := by exact prefixLift 5856042
  have htrace : WordTrace (prefixWord ++ tailWord_5856042) baseStart_5856042 baseEnd_5856042 := by
    simpa [prefixWord, tailWord_5856042, baseEnd_5856042] using wordTrace_append hprefix tailTrace_5856042
  have hstable : (prefixWord ++ tailWord_5856042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856042).length < 2 ^ (prefixWord ++ tailWord_5856042).sum := by decide
  have hdescent : baseEnd_5856042 < baseStart_5856042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856046 : List Nat := [4, 1, 3, 2, 1, 2, 2, 2, 2, 4]
def baseStart_5856046 : Nat := 118140960795 + 5856046 * 2 ^ 59
def prefixEnd_5856046 : Nat := 4983230072969 + 3 ^ 40 * 5856046 * 2
def baseEnd_5856046 : Nat := 1002322110946433475597847

theorem tailTrace_5856046 : CollatzResearch.WordTrace tailWord_5856046 prefixEnd_5856046 1002322110946433475597847 := by
  unfold tailWord_5856046
  simp only [CollatzResearch.WordTrace]
  refine ⟨26698443067819118734656499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142391696361701966584834661 26698443067819118734656499)
  ·
    refine ⟨40047664601728678101984749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26698443067819118734656499 40047664601728678101984749)
    ·
      refine ⟨15017874225648254288244281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40047664601728678101984749 15017874225648254288244281)
      ·
        refine ⟨11263405669236190716183211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15017874225648254288244281 11263405669236190716183211)
        ·
          refine ⟨16895108503854286074274817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11263405669236190716183211 16895108503854286074274817)
          ·
            refine ⟨12671331377890714555706113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16895108503854286074274817 12671331377890714555706113)
            ·
              refine ⟨9503498533418035916779585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12671331377890714555706113 9503498533418035916779585)
              ·
                refine ⟨7127623900063526937584689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9503498533418035916779585 7127623900063526937584689)
                ·
                  refine ⟨5345717925047645203188517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7127623900063526937584689 5345717925047645203188517)
                  ·
                    refine ⟨1002322110946433475597847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5345717925047645203188517 1002322110946433475597847)
                    ·
                      rfl

theorem cell23_5856046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_5856046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856046 prefixEnd_5856046 := by exact prefixLift 5856046
  have htrace : WordTrace (prefixWord ++ tailWord_5856046) baseStart_5856046 baseEnd_5856046 := by
    simpa [prefixWord, tailWord_5856046, baseEnd_5856046] using wordTrace_append hprefix tailTrace_5856046
  have hstable : (prefixWord ++ tailWord_5856046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856046).length < 2 ^ (prefixWord ++ tailWord_5856046).sum := by decide
  have hdescent : baseEnd_5856046 < baseStart_5856046 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856053 : List Nat := [1, 3, 3, 1, 3, 2, 1, 4, 1, 2, 2]
def baseStart_5856053 : Nat := 118140960795 + 5856053 * 2 ^ 59
def prefixEnd_5856053 : Nat := 4983230072969 + 3 ^ 40 * 5856053 * 2
def baseEnd_5856053 : Nat := 3006969927203881899406009

theorem tailTrace_5856053 : CollatzResearch.WordTrace tailWord_5856053 prefixEnd_5856053 3006969927203881899406009 := by
  unfold tailWord_5856053
  simp only [CollatzResearch.WordTrace]
  refine ⟨213587799853527590072756813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142391866569018393381837875 213587799853527590072756813)
  ·
    refine ⟨80095424945072846277283805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213587799853527590072756813 80095424945072846277283805)
    ·
      refine ⟨30035784354402317353981427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80095424945072846277283805 30035784354402317353981427)
      ·
        refine ⟨45053676531603476030972141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30035784354402317353981427 45053676531603476030972141)
        ·
          refine ⟨16895128699351303511614553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45053676531603476030972141 16895128699351303511614553)
          ·
            refine ⟨12671346524513477633710915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16895128699351303511614553 12671346524513477633710915)
            ·
              refine ⟨19007019786770216450566373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12671346524513477633710915 19007019786770216450566373)
              ·
                refine ⟨3563816210019415584481195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19007019786770216450566373 3563816210019415584481195)
                ·
                  refine ⟨5345724315029123376721793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3563816210019415584481195 5345724315029123376721793)
                  ·
                    refine ⟨4009293236271842532541345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5345724315029123376721793 4009293236271842532541345)
                    ·
                      refine ⟨3006969927203881899406009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4009293236271842532541345 3006969927203881899406009)
                      ·
                        rfl

theorem cell23_5856053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_5856053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856053 prefixEnd_5856053 := by exact prefixLift 5856053
  have htrace : WordTrace (prefixWord ++ tailWord_5856053) baseStart_5856053 baseEnd_5856053 := by
    simpa [prefixWord, tailWord_5856053, baseEnd_5856053] using wordTrace_append hprefix tailTrace_5856053
  have hstable : (prefixWord ++ tailWord_5856053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856053).length < 2 ^ (prefixWord ++ tailWord_5856053).sum := by decide
  have hdescent : baseEnd_5856053 < baseStart_5856053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856070 : List Nat := [6, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2]
def baseStart_5856070 : Nat := 118140960795 + 5856070 * 2 ^ 59
def prefixEnd_5856070 : Nat := 4983230072969 + 3 ^ 40 * 5856070 * 2
def baseEnd_5856070 : Nat := 3006978656375008332893431

theorem tailTrace_5856070 : CollatzResearch.WordTrace tailWord_5856070 prefixEnd_5856070 3006978656375008332893431 := by
  unfold tailWord_5856070
  simp only [CollatzResearch.WordTrace]
  refine ⟨6674638121702062561753927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 142392279929644001317417109 6674638121702062561753927)
  ·
    refine ⟨10011957182553093842630891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6674638121702062561753927 10011957182553093842630891)
    ·
      refine ⟨15017935773829640763946337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10011957182553093842630891 15017935773829640763946337)
      ·
        refine ⟨11263451830372230572959753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15017935773829640763946337 11263451830372230572959753)
        ·
          refine ⟨8447588872779172929719815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11263451830372230572959753 8447588872779172929719815)
          ·
            refine ⟨12671383309168759394579723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8447588872779172929719815 12671383309168759394579723)
            ·
              refine ⟨19007074963753139091869585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12671383309168759394579723 19007074963753139091869585)
              ·
                refine ⟨14255306222814854318902189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19007074963753139091869585 14255306222814854318902189)
                ·
                  refine ⟨5345739833555570369588321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14255306222814854318902189 5345739833555570369588321)
                  ·
                    refine ⟨4009304875166677777191241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5345739833555570369588321 4009304875166677777191241)
                    ·
                      refine ⟨3006978656375008332893431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4009304875166677777191241 3006978656375008332893431)
                      ·
                        rfl

theorem cell23_5856070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_5856070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856070 prefixEnd_5856070 := by exact prefixLift 5856070
  have htrace : WordTrace (prefixWord ++ tailWord_5856070) baseStart_5856070 baseEnd_5856070 := by
    simpa [prefixWord, tailWord_5856070, baseEnd_5856070] using wordTrace_append hprefix tailTrace_5856070
  have hstable : (prefixWord ++ tailWord_5856070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856070).length < 2 ^ (prefixWord ++ tailWord_5856070).sum := by decide
  have hdescent : baseEnd_5856070 < baseStart_5856070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856085 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 1, 8]
def baseStart_5856085 : Nat := 118140960795 + 5856085 * 2 ^ 59
def prefixEnd_5856085 : Nat := 4983230072969 + 3 ^ 40 * 5856085 * 2
def baseEnd_5856085 : Nat := 1002328786194941924735287

theorem tailTrace_5856085 : CollatzResearch.WordTrace tailWord_5856085 prefixEnd_5856085 1002328786194941924735287 := by
  unfold tailWord_5856085
  simp only [CollatzResearch.WordTrace]
  refine ⟨213588966989411659537921709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142392644659607773025281139 213588966989411659537921709)
  ·
    refine ⟨80095862621029372326720641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213588966989411659537921709 80095862621029372326720641)
    ·
      refine ⟨60071896965772029245040481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80095862621029372326720641 60071896965772029245040481)
      ·
        refine ⟨45053922724329021933780361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60071896965772029245040481 45053922724329021933780361)
        ·
          refine ⟨33790442043246766450335271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45053922724329021933780361 33790442043246766450335271)
          ·
            refine ⟨50685663064870149675502907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33790442043246766450335271 50685663064870149675502907)
            ·
              refine ⟨76028494597305224513254361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50685663064870149675502907 76028494597305224513254361)
              ·
                refine ⟨57021370947978918384940771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76028494597305224513254361 57021370947978918384940771)
                ·
                  refine ⟨85532056421968377577411157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57021370947978918384940771 85532056421968377577411157)
                  ·
                    refine ⟨1002328786194941924735287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 85532056421968377577411157 1002328786194941924735287)
                    ·
                      rfl

theorem cell23_5856085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_5856085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856085 prefixEnd_5856085 := by exact prefixLift 5856085
  have htrace : WordTrace (prefixWord ++ tailWord_5856085) baseStart_5856085 baseEnd_5856085 := by
    simpa [prefixWord, tailWord_5856085, baseEnd_5856085] using wordTrace_append hprefix tailTrace_5856085
  have hstable : (prefixWord ++ tailWord_5856085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856085).length < 2 ^ (prefixWord ++ tailWord_5856085).sum := by decide
  have hdescent : baseEnd_5856085 < baseStart_5856085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856095 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 5]
def baseStart_5856095 : Nat := 118140960795 + 5856095 * 2 ^ 59
def prefixEnd_5856095 : Nat := 4983230072969 + 3 ^ 40 * 5856095 * 2
def baseEnd_5856095 : Nat := 3006991493391370735080815

theorem tailTrace_5856095 : CollatzResearch.WordTrace tailWord_5856095 prefixEnd_5856095 3006991493391370735080815 := by
  unfold tailWord_5856095
  simp only [CollatzResearch.WordTrace]
  refine ⟨213589331719375431245785739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142392887812916954163857159 213589331719375431245785739)
  ·
    refine ⟨320383997579063146868678609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213589331719375431245785739 320383997579063146868678609)
    ·
      refine ⟨240287998184297360151508957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320383997579063146868678609 240287998184297360151508957)
      ·
        refine ⟨90107999319111510056815859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240287998184297360151508957 90107999319111510056815859)
        ·
          refine ⟨135161998978667265085223789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90107999319111510056815859 135161998978667265085223789)
          ·
            refine ⟨50685749617000224406958921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135161998978667265085223789 50685749617000224406958921)
            ·
              refine ⟨38014312212750168305219191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50685749617000224406958921 38014312212750168305219191)
              ·
                refine ⟨57021468319125252457828787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38014312212750168305219191 57021468319125252457828787)
                ·
                  refine ⟨85532202478687878686743181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57021468319125252457828787 85532202478687878686743181)
                  ·
                    refine ⟨32074575929507954507528693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85532202478687878686743181 32074575929507954507528693)
                    ·
                      refine ⟨3006991493391370735080815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32074575929507954507528693 3006991493391370735080815)
                      ·
                        rfl

theorem cell23_5856095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_5856095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856095 prefixEnd_5856095 := by exact prefixLift 5856095
  have htrace : WordTrace (prefixWord ++ tailWord_5856095) baseStart_5856095 baseEnd_5856095 := by
    simpa [prefixWord, tailWord_5856095, baseEnd_5856095] using wordTrace_append hprefix tailTrace_5856095
  have hstable : (prefixWord ++ tailWord_5856095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856095).length < 2 ^ (prefixWord ++ tailWord_5856095).sum := by decide
  have hdescent : baseEnd_5856095 < baseStart_5856095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856115 : List Nat := [1, 1, 1, 2, 2, 1, 5, 3, 7]
def baseStart_5856115 : Nat := 118140960795 + 5856115 * 2 ^ 59
def prefixEnd_5856115 : Nat := 4983230072969 + 3 ^ 40 * 5856115 * 2
def baseEnd_5856115 : Nat := 334111307000495628536747

theorem tailTrace_5856115 : CollatzResearch.WordTrace tailWord_5856115 prefixEnd_5856115 334111307000495628536747 := by
  unfold tailWord_5856115
  simp only [CollatzResearch.WordTrace]
  refine ⟨213590061179302974661513799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142393374119535316441009199 213590061179302974661513799)
  ·
    refine ⟨320385091768954461992270699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213590061179302974661513799 320385091768954461992270699)
    ·
      refine ⟨480577637653431692988406049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320385091768954461992270699 480577637653431692988406049)
      ·
        refine ⟨360433228240073769741304537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 480577637653431692988406049 360433228240073769741304537)
        ·
          refine ⟨270324921180055327305978403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360433228240073769741304537 270324921180055327305978403)
          ·
            refine ⟨405487381770082990958967605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270324921180055327305978403 405487381770082990958967605)
            ·
              refine ⟨38014442040945280402403213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 405487381770082990958967605 38014442040945280402403213)
              ·
                refine ⟨14255415765354480150901205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38014442040945280402403213 14255415765354480150901205)
                ·
                  refine ⟨334111307000495628536747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14255415765354480150901205 334111307000495628536747)
                  ·
                    rfl

theorem cell23_5856115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 7].length) (baseStart_5856115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856115 prefixEnd_5856115 := by exact prefixLift 5856115
  have htrace : WordTrace (prefixWord ++ tailWord_5856115) baseStart_5856115 baseEnd_5856115 := by
    simpa [prefixWord, tailWord_5856115, baseEnd_5856115] using wordTrace_append hprefix tailTrace_5856115
  have hstable : (prefixWord ++ tailWord_5856115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856115).length < 2 ^ (prefixWord ++ tailWord_5856115).sum := by decide
  have hdescent : baseEnd_5856115 < baseStart_5856115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856149 : List Nat := [1, 3, 2, 1, 1, 4, 3, 3, 5]
def baseStart_5856149 : Nat := 118140960795 + 5856149 * 2 ^ 59
def prefixEnd_5856149 : Nat := 4983230072969 + 3 ^ 40 * 5856149 * 2
def baseEnd_5856149 : Nat := 334113246816301502645063

theorem tailTrace_5856149 : CollatzResearch.WordTrace tailWord_5856149 prefixEnd_5856149 334113246816301502645063 := by
  unfold tailWord_5856149
  simp only [CollatzResearch.WordTrace]
  refine ⟨213591301261179798468251501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142394200840786532312167667 213591301261179798468251501)
  ·
    refine ⟨80096737972942424425594313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213591301261179798468251501 80096737972942424425594313)
    ·
      refine ⟨60072553479706818319195735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80096737972942424425594313 60072553479706818319195735)
      ·
        refine ⟨90108830219560227478793603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60072553479706818319195735 90108830219560227478793603)
        ·
          refine ⟨135163245329340341218190405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90108830219560227478793603 135163245329340341218190405)
          ·
            refine ⟨25343108499251313978410701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135163245329340341218190405 25343108499251313978410701)
            ·
              refine ⟨9503665687219242741904013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25343108499251313978410701 9503665687219242741904013)
              ·
                refine ⟨3563874632707216028214005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9503665687219242741904013 3563874632707216028214005)
                ·
                  refine ⟨334113246816301502645063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3563874632707216028214005 334113246816301502645063)
                  ·
                    rfl

theorem cell23_5856149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 3, 5].length) (baseStart_5856149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856149 prefixEnd_5856149 := by exact prefixLift 5856149
  have htrace : WordTrace (prefixWord ++ tailWord_5856149) baseStart_5856149 baseEnd_5856149 := by
    simpa [prefixWord, tailWord_5856149, baseEnd_5856149] using wordTrace_append hprefix tailTrace_5856149
  have hstable : (prefixWord ++ tailWord_5856149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856149).length < 2 ^ (prefixWord ++ tailWord_5856149).sum := by decide
  have hdescent : baseEnd_5856149 < baseStart_5856149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856165 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 2, 2, 8]
def baseStart_5856165 : Nat := 118140960795 + 5856165 * 2 ^ 59
def prefixEnd_5856165 : Nat := 4983230072969 + 3 ^ 40 * 5856165 * 2
def baseEnd_5856165 : Nat := 3007027437037185461205493

theorem tailTrace_5856165 : CollatzResearch.WordTrace tailWord_5856165 prefixEnd_5856165 3007027437037185461205493 := by
  unfold tailWord_5856165
  simp only [CollatzResearch.WordTrace]
  refine ⟨213591884829121833200833949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142394589886081222133889299 213591884829121833200833949)
  ·
    refine ⟨80096956810920687450312731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213591884829121833200833949 80096956810920687450312731)
    ·
      refine ⟨120145435216381031175469097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80096956810920687450312731 120145435216381031175469097)
      ·
        refine ⟨90109076412285773381601823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120145435216381031175469097 90109076412285773381601823)
        ·
          refine ⟨135163614618428660072402735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90109076412285773381601823 135163614618428660072402735)
          ·
            refine ⟨202745421927642990108604103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135163614618428660072402735 202745421927642990108604103)
            ·
              refine ⟨304118132891464485162906155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202745421927642990108604103 304118132891464485162906155)
              ·
                refine ⟨456177199337196727744359233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304118132891464485162906155 456177199337196727744359233)
                ·
                  refine ⟨342132899502897545808269425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 456177199337196727744359233 342132899502897545808269425)
                  ·
                    refine ⟨256599674627173159356202069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 342132899502897545808269425 256599674627173159356202069)
                    ·
                      refine ⟨3007027437037185461205493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 256599674627173159356202069 3007027437037185461205493)
                      ·
                        rfl

theorem cell23_5856165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_5856165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856165 prefixEnd_5856165 := by exact prefixLift 5856165
  have htrace : WordTrace (prefixWord ++ tailWord_5856165) baseStart_5856165 baseEnd_5856165 := by
    simpa [prefixWord, tailWord_5856165, baseEnd_5856165] using wordTrace_append hprefix tailTrace_5856165
  have hstable : (prefixWord ++ tailWord_5856165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856165).length < 2 ^ (prefixWord ++ tailWord_5856165).sum := by decide
  have hdescent : baseEnd_5856165 < baseStart_5856165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856175 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 2, 8]
def baseStart_5856175 : Nat := 118140960795 + 5856175 * 2 ^ 59
def prefixEnd_5856175 : Nat := 4983230072969 + 3 ^ 40 * 5856175 * 2
def baseEnd_5856175 : Nat := 1002344190614576807360149

theorem tailTrace_5856175 : CollatzResearch.WordTrace tailWord_5856175 prefixEnd_5856175 1002344190614576807360149 := by
  unfold tailWord_5856175
  simp only [CollatzResearch.WordTrace]
  refine ⟨213592249559085604908697979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142394833039390403272465319 213592249559085604908697979)
  ·
    refine ⟨320388374338628407363046969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213592249559085604908697979 320388374338628407363046969)
    ·
      refine ⟨240291280753971305522285227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320388374338628407363046969 240291280753971305522285227)
      ·
        refine ⟨360436921130956958283427841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240291280753971305522285227 360436921130956958283427841)
        ·
          refine ⟨270327690848217718712570881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360436921130956958283427841 270327690848217718712570881)
          ·
            refine ⟨202745768136163289034428161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270327690848217718712570881 202745768136163289034428161)
            ·
              refine ⟨152059326102122466775821121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202745768136163289034428161 152059326102122466775821121)
              ·
                refine ⟨114044494576591850081865841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152059326102122466775821121 114044494576591850081865841)
                ·
                  refine ⟨85533370932443887561399381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114044494576591850081865841 85533370932443887561399381)
                  ·
                    refine ⟨1002344190614576807360149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 85533370932443887561399381 1002344190614576807360149)
                    ·
                      rfl

theorem cell23_5856175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 8].length) (baseStart_5856175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856175 prefixEnd_5856175 := by exact prefixLift 5856175
  have htrace : WordTrace (prefixWord ++ tailWord_5856175) baseStart_5856175 baseEnd_5856175 := by
    simpa [prefixWord, tailWord_5856175, baseEnd_5856175] using wordTrace_append hprefix tailTrace_5856175
  have hstable : (prefixWord ++ tailWord_5856175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856175).length < 2 ^ (prefixWord ++ tailWord_5856175).sum := by decide
  have hdescent : baseEnd_5856175 < baseStart_5856175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856177 : List Nat := [1, 2, 2, 4, 4, 1, 2, 1, 2, 2, 2]
def baseStart_5856177 : Nat := 118140960795 + 5856177 * 2 ^ 59
def prefixEnd_5856177 : Nat := 4983230072969 + 3 ^ 40 * 5856177 * 2
def baseEnd_5856177 : Nat := 3007033598805039414255439

theorem tailTrace_5856177 : CollatzResearch.WordTrace tailWord_5856177 prefixEnd_5856177 3007033598805039414255439 := by
  unfold tailWord_5856177
  simp only [CollatzResearch.WordTrace]
  refine ⟨213592322505078359250270785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142394881670052239500180523 213592322505078359250270785)
  ·
    refine ⟨160194241878808769437703089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213592322505078359250270785 160194241878808769437703089)
    ·
      refine ⟨120145681409106577078277317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160194241878808769437703089 120145681409106577078277317)
      ·
        refine ⟨22527315264207483202176997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120145681409106577078277317 22527315264207483202176997)
        ·
          refine ⟨4223871612038903100408187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22527315264207483202176997 4223871612038903100408187)
          ·
            refine ⟨6335807418058354650612281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4223871612038903100408187 6335807418058354650612281)
            ·
              refine ⟨4751855563543765987959211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6335807418058354650612281 4751855563543765987959211)
              ·
                refine ⟨7127783345315648981938817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4751855563543765987959211 7127783345315648981938817)
                ·
                  refine ⟨5345837508986736736454113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7127783345315648981938817 5345837508986736736454113)
                  ·
                    refine ⟨4009378131740052552340585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5345837508986736736454113 4009378131740052552340585)
                    ·
                      refine ⟨3007033598805039414255439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4009378131740052552340585 3007033598805039414255439)
                      ·
                        rfl

theorem cell23_5856177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_5856177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856177 prefixEnd_5856177 := by exact prefixLift 5856177
  have htrace : WordTrace (prefixWord ++ tailWord_5856177) baseStart_5856177 baseEnd_5856177 := by
    simpa [prefixWord, tailWord_5856177, baseEnd_5856177] using wordTrace_append hprefix tailTrace_5856177
  have hstable : (prefixWord ++ tailWord_5856177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856177).length < 2 ^ (prefixWord ++ tailWord_5856177).sum := by decide
  have hdescent : baseEnd_5856177 < baseStart_5856177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856306 : List Nat := [3, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4]
def baseStart_5856306 : Nat := 118140960795 + 5856306 * 2 ^ 59
def prefixEnd_5856306 : Nat := 4983230072969 + 3 ^ 40 * 5856306 * 2
def baseEnd_5856306 : Nat := 3007099837809469409542345

theorem tailTrace_5856306 : CollatzResearch.WordTrace tailWord_5856306 prefixEnd_5856306 3007099837809469409542345 := by
  unfold tailWord_5856306
  simp only [CollatzResearch.WordTrace]
  refine ⟨53399256880402753570429193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142398018347740676187811181 53399256880402753570429193)
  ·
    refine ⟨40049442660302065177821895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53399256880402753570429193 40049442660302065177821895)
    ·
      refine ⟨60074163990453097766732843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40049442660302065177821895 60074163990453097766732843)
      ·
        refine ⟨90111245985679646650099265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60074163990453097766732843 90111245985679646650099265)
        ·
          refine ⟨67583434489259734987574449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90111245985679646650099265 67583434489259734987574449)
          ·
            refine ⟨50687575866944801240680837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67583434489259734987574449 50687575866944801240680837)
            ·
              refine ⟨9503920475052150232627657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50687575866944801240680837 9503920475052150232627657)
              ·
                refine ⟨7127940356289112674470743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9503920475052150232627657 7127940356289112674470743)
                ·
                  refine ⟨10691910534433669011706115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7127940356289112674470743 10691910534433669011706115)
                  ·
                    refine ⟨16037865801650503517559173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10691910534433669011706115 16037865801650503517559173)
                    ·
                      refine ⟨3007099837809469409542345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16037865801650503517559173 3007099837809469409542345)
                      ·
                        rfl

theorem cell23_5856306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_5856306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856306 prefixEnd_5856306 := by exact prefixLift 5856306
  have htrace : WordTrace (prefixWord ++ tailWord_5856306) baseStart_5856306 baseEnd_5856306 := by
    simpa [prefixWord, tailWord_5856306, baseEnd_5856306] using wordTrace_append hprefix tailTrace_5856306
  have hstable : (prefixWord ++ tailWord_5856306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856306).length < 2 ^ (prefixWord ++ tailWord_5856306).sum := by decide
  have hdescent : baseEnd_5856306 < baseStart_5856306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856340 : List Nat := [2, 4, 1, 1, 1, 1, 2, 6, 1, 2, 2]
def baseStart_5856340 : Nat := 118140960795 + 5856340 * 2 ^ 59
def prefixEnd_5856340 : Nat := 4983230072969 + 3 ^ 40 * 5856340 * 2
def baseEnd_5856340 : Nat := 3007117296151722276517189

theorem tailTrace_5856340 : CollatzResearch.WordTrace tailWord_5856340 prefixEnd_5856340 3007117296151722276517189 := by
  unfold tailWord_5856340
  simp only [CollatzResearch.WordTrace]
  refine ⟨106799133801743919044227237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142398845068991892058969649 106799133801743919044227237)
  ·
    refine ⟨20024837587826984820792607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106799133801743919044227237 20024837587826984820792607)
    ·
      refine ⟨30037256381740477231188911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20024837587826984820792607 30037256381740477231188911)
      ·
        refine ⟨45055884572610715846783367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30037256381740477231188911 45055884572610715846783367)
        ·
          refine ⟨67583826858916073770175051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45055884572610715846783367 67583826858916073770175051)
          ·
            refine ⟨101375740288374110655262577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67583826858916073770175051 101375740288374110655262577)
            ·
              refine ⟨76031805216280582991446933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101375740288374110655262577 76031805216280582991446933)
              ·
                refine ⟨3563990869513152327724075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76031805216280582991446933 3563990869513152327724075)
                ·
                  refine ⟨5345986304269728491586113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3563990869513152327724075 5345986304269728491586113)
                  ·
                    refine ⟨4009489728202296368689585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5345986304269728491586113 4009489728202296368689585)
                    ·
                      refine ⟨3007117296151722276517189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4009489728202296368689585 3007117296151722276517189)
                      ·
                        rfl

theorem cell23_5856340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_5856340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856340 prefixEnd_5856340 := by exact prefixLift 5856340
  have htrace : WordTrace (prefixWord ++ tailWord_5856340) baseStart_5856340 baseEnd_5856340 := by
    simpa [prefixWord, tailWord_5856340, baseEnd_5856340] using wordTrace_append hprefix tailTrace_5856340
  have hstable : (prefixWord ++ tailWord_5856340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856340).length < 2 ^ (prefixWord ++ tailWord_5856340).sum := by decide
  have hdescent : baseEnd_5856340 < baseStart_5856340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856413 : List Nat := [1, 4, 2, 1, 1, 2, 4, 1, 1, 4, 2]
def baseStart_5856413 : Nat := 118140960795 + 5856413 * 2 ^ 59
def prefixEnd_5856413 : Nat := 4983230072969 + 3 ^ 40 * 5856413 * 2
def baseEnd_5856413 : Nat := 3007154780239500490904353

theorem tailTrace_5856413 : CollatzResearch.WordTrace tailWord_5856413 prefixEnd_5856413 3007154780239500490904353 := by
  unfold tailWord_5856413
  simp only [CollatzResearch.WordTrace]
  refine ⟨213600930132223371555861893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142400620088148914370574595 213600930132223371555861893)
  ·
    refine ⟨40050174399791882166724105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213600930132223371555861893 40050174399791882166724105)
    ·
      refine ⟨30037630799843911625043079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40050174399791882166724105 30037630799843911625043079)
      ·
        refine ⟨45056446199765867437564619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30037630799843911625043079 45056446199765867437564619)
        ·
          refine ⟨67584669299648801156346929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45056446199765867437564619 67584669299648801156346929)
          ·
            refine ⟨50688501974736600867260197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67584669299648801156346929 50688501974736600867260197)
            ·
              refine ⟨9504094120263112662611287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50688501974736600867260197 9504094120263112662611287)
              ·
                refine ⟨14256141180394668993916931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9504094120263112662611287 14256141180394668993916931)
                ·
                  refine ⟨21384211770592003490875397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14256141180394668993916931 21384211770592003490875397)
                  ·
                    refine ⟨4009539706986000654539137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21384211770592003490875397 4009539706986000654539137)
                    ·
                      refine ⟨3007154780239500490904353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4009539706986000654539137 3007154780239500490904353)
                      ·
                        rfl

theorem cell23_5856413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_5856413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856413 prefixEnd_5856413 := by exact prefixLift 5856413
  have htrace : WordTrace (prefixWord ++ tailWord_5856413) baseStart_5856413 baseEnd_5856413 := by
    simpa [prefixWord, tailWord_5856413, baseEnd_5856413] using wordTrace_append hprefix tailTrace_5856413
  have hstable : (prefixWord ++ tailWord_5856413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856413).length < 2 ^ (prefixWord ++ tailWord_5856413).sum := by decide
  have hdescent : baseEnd_5856413 < baseStart_5856413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856456 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 1, 7, 2]
def baseStart_5856456 : Nat := 118140960795 + 5856456 * 2 ^ 59
def prefixEnd_5856456 : Nat := 4983230072969 + 3 ^ 40 * 5856456 * 2
def baseEnd_5856456 : Nat := 3007176859907643822666655

theorem tailTrace_5856456 : CollatzResearch.WordTrace tailWord_5856456 prefixEnd_5856456 3007176859907643822666655 := by
  unfold tailWord_5856456
  simp only [CollatzResearch.WordTrace]
  refine ⟨106801249235533794949838611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142401665647378393266451481 106801249235533794949838611)
  ·
    refine ⟨160201873853300692424757917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106801249235533794949838611 160201873853300692424757917)
    ·
      refine ⟨60075702694987759659284219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160201873853300692424757917 60075702694987759659284219)
      ·
        refine ⟨90113554042481639488926329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60075702694987759659284219 90113554042481639488926329)
        ·
          refine ⟨67585165531861229616694747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90113554042481639488926329 67585165531861229616694747)
          ·
            refine ⟨101377748297791844425042121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67585165531861229616694747 101377748297791844425042121)
            ·
              refine ⟨76033311223343883318781591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101377748297791844425042121 76033311223343883318781591)
              ·
                refine ⟨114049966835015824978172387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76033311223343883318781591 114049966835015824978172387)
                ·
                  refine ⟨171074950252523737467258581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114049966835015824978172387 171074950252523737467258581)
                  ·
                    refine ⟨4009569146543525096888873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 171074950252523737467258581 4009569146543525096888873)
                    ·
                      refine ⟨3007176859907643822666655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4009569146543525096888873 3007176859907643822666655)
                      ·
                        rfl

theorem cell23_5856456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 1, 7, 2].length) (baseStart_5856456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856456 prefixEnd_5856456 := by exact prefixLift 5856456
  have htrace : WordTrace (prefixWord ++ tailWord_5856456) baseStart_5856456 baseEnd_5856456 := by
    simpa [prefixWord, tailWord_5856456, baseEnd_5856456] using wordTrace_append hprefix tailTrace_5856456
  have hstable : (prefixWord ++ tailWord_5856456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856456).length < 2 ^ (prefixWord ++ tailWord_5856456).sum := by decide
  have hdescent : baseEnd_5856456 < baseStart_5856456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856487 : List Nat := [1, 1, 5, 3, 3, 1, 1, 3, 5]
def baseStart_5856487 : Nat := 118140960795 + 5856487 * 2 ^ 59
def prefixEnd_5856487 : Nat := 4983230072969 + 3 ^ 40 * 5856487 * 2
def baseEnd_5856487 : Nat := 334132530867548133486557

theorem tailTrace_5856487 : CollatzResearch.WordTrace tailWord_5856487 prefixEnd_5856487 334132530867548133486557 := by
  unfold tailWord_5856487
  simp only [CollatzResearch.WordTrace]
  refine ⟨213603629133955282194055715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142402419422636854796037143 213603629133955282194055715)
  ·
    refine ⟨320405443700932923291083573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213603629133955282194055715 320405443700932923291083573)
    ·
      refine ⟨30038010346962461558539085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 320405443700932923291083573 30038010346962461558539085)
      ·
        refine ⟨11264253880110923084452157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30038010346962461558539085 11264253880110923084452157)
        ·
          refine ⟨4224095205041596156669559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11264253880110923084452157 4224095205041596156669559)
          ·
            refine ⟨6336142807562394235004339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4224095205041596156669559 6336142807562394235004339)
            ·
              refine ⟨9504214211343591352506509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6336142807562394235004339 9504214211343591352506509)
              ·
                refine ⟨3564080329253846757189941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9504214211343591352506509 3564080329253846757189941)
                ·
                  refine ⟨334132530867548133486557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3564080329253846757189941 334132530867548133486557)
                  ·
                    rfl

theorem cell23_5856487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 3, 5].length) (baseStart_5856487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856487 prefixEnd_5856487 := by exact prefixLift 5856487
  have htrace : WordTrace (prefixWord ++ tailWord_5856487) baseStart_5856487 baseEnd_5856487 := by
    simpa [prefixWord, tailWord_5856487, baseEnd_5856487] using wordTrace_append hprefix tailTrace_5856487
  have hstable : (prefixWord ++ tailWord_5856487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856487).length < 2 ^ (prefixWord ++ tailWord_5856487).sum := by decide
  have hdescent : baseEnd_5856487 < baseStart_5856487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856513 : List Nat := [1, 2, 4, 1, 1, 3, 3, 1, 3, 4]
def baseStart_5856513 : Nat := 118140960795 + 5856513 * 2 ^ 59
def prefixEnd_5856513 : Nat := 4983230072969 + 3 ^ 40 * 5856513 * 2
def baseEnd_5856513 : Nat := 1002402042768316699884631

theorem tailTrace_5856513 : CollatzResearch.WordTrace tailWord_5856513 prefixEnd_5856513 1002402042768316699884631 := by
  unfold tailWord_5856513
  simp only [CollatzResearch.WordTrace]
  refine ⟨213604577431861088634502193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142403051621240725756334795 213604577431861088634502193)
  ·
    refine ⟨160203433073895816475876645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213604577431861088634502193 160203433073895816475876645)
    ·
      refine ⟨30038143701355465589226871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160203433073895816475876645 30038143701355465589226871)
      ·
        refine ⟨45057215552033198383840307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30038143701355465589226871 45057215552033198383840307)
        ·
          refine ⟨67585823328049797575760461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45057215552033198383840307 67585823328049797575760461)
          ·
            refine ⟨25344683748018674090910173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67585823328049797575760461 25344683748018674090910173)
            ·
              refine ⟨9504256405507002784091315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25344683748018674090910173 9504256405507002784091315)
              ·
                refine ⟨14256384608260504176136973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9504256405507002784091315 14256384608260504176136973)
                ·
                  refine ⟨5346144228097689066051365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14256384608260504176136973 5346144228097689066051365)
                  ·
                    refine ⟨1002402042768316699884631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5346144228097689066051365 1002402042768316699884631)
                    ·
                      rfl

theorem cell23_5856513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_5856513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856513 prefixEnd_5856513 := by exact prefixLift 5856513
  have htrace : WordTrace (prefixWord ++ tailWord_5856513) baseStart_5856513 baseEnd_5856513 := by
    simpa [prefixWord, tailWord_5856513, baseEnd_5856513] using wordTrace_append hprefix tailTrace_5856513
  have hstable : (prefixWord ++ tailWord_5856513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856513).length < 2 ^ (prefixWord ++ tailWord_5856513).sum := by decide
  have hdescent : baseEnd_5856513 < baseStart_5856513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856576 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 4]
def baseStart_5856576 : Nat := 118140960795 + 5856576 * 2 ^ 59
def prefixEnd_5856576 : Nat := 4983230072969 + 3 ^ 40 * 5856576 * 2
def baseEnd_5856576 : Nat := 3007238477586183353166103

theorem tailTrace_5856576 : CollatzResearch.WordTrace tailWord_5856576 prefixEnd_5856576 3007238477586183353166103 := by
  unfold tailWord_5856576
  simp only [CollatzResearch.WordTrace]
  refine ⟨106803437615316425197022791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142404583487088566929363721 106803437615316425197022791)
  ·
    refine ⟨160205156422974637795534187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106803437615316425197022791 160205156422974637795534187)
    ·
      refine ⟨240307734634461956693301281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160205156422974637795534187 240307734634461956693301281)
      ·
        refine ⟨180230800975846467519975961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240307734634461956693301281 180230800975846467519975961)
        ·
          refine ⟨135173100731884850639981971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180230800975846467519975961 135173100731884850639981971)
          ·
            refine ⟨202759651097827275959972957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135173100731884850639981971 202759651097827275959972957)
            ·
              refine ⟨76034869161685228484989859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202759651097827275959972957 76034869161685228484989859)
              ·
                refine ⟨114052303742527842727484789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76034869161685228484989859 114052303742527842727484789)
                ·
                  refine ⟨10692403475861985255701699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114052303742527842727484789 10692403475861985255701699)
                  ·
                    refine ⟨16038605213792977883552549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10692403475861985255701699 16038605213792977883552549)
                    ·
                      refine ⟨3007238477586183353166103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16038605213792977883552549 3007238477586183353166103)
                      ·
                        rfl

theorem cell23_5856576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 4].length) (baseStart_5856576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856576 prefixEnd_5856576 := by exact prefixLift 5856576
  have htrace : WordTrace (prefixWord ++ tailWord_5856576) baseStart_5856576 baseEnd_5856576 := by
    simpa [prefixWord, tailWord_5856576, baseEnd_5856576] using wordTrace_append hprefix tailTrace_5856576
  have hstable : (prefixWord ++ tailWord_5856576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856576).length < 2 ^ (prefixWord ++ tailWord_5856576).sum := by decide
  have hdescent : baseEnd_5856576 < baseStart_5856576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856593 : List Nat := [1, 2, 2, 1, 4, 1, 2, 4, 1, 1, 4]
def baseStart_5856593 : Nat := 118140960795 + 5856593 * 2 ^ 59
def prefixEnd_5856593 : Nat := 4983230072969 + 3 ^ 40 * 5856593 * 2
def baseEnd_5856593 : Nat := 3007247206757309786653525

theorem tailTrace_5856593 : CollatzResearch.WordTrace tailWord_5856593 prefixEnd_5856593 3007247206757309786653525 := by
  unfold tailWord_5856593
  simp only [CollatzResearch.WordTrace]
  refine ⟨213607495271571262297414433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142404996847714174864942955 213607495271571262297414433)
  ·
    refine ⟨160205621453678446723060825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213607495271571262297414433 160205621453678446723060825)
    ·
      refine ⟨120154216090258835042295619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160205621453678446723060825 120154216090258835042295619)
      ·
        refine ⟨180231324135388252563443429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120154216090258835042295619 180231324135388252563443429)
        ·
          refine ⟨33793373275385297355645643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180231324135388252563443429 33793373275385297355645643)
          ·
            refine ⟨50690059913077946033468465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33793373275385297355645643 50690059913077946033468465)
            ·
              refine ⟨38017544934808459525101349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50690059913077946033468465 38017544934808459525101349)
              ·
                refine ⟨7128289675276586160956503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38017544934808459525101349 7128289675276586160956503)
                ·
                  refine ⟨10692434512914879241434755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7128289675276586160956503 10692434512914879241434755)
                  ·
                    refine ⟨16038651769372318862152133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10692434512914879241434755 16038651769372318862152133)
                    ·
                      refine ⟨3007247206757309786653525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16038651769372318862152133 3007247206757309786653525)
                      ·
                        rfl

theorem cell23_5856593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 1, 4].length) (baseStart_5856593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856593 prefixEnd_5856593 := by exact prefixLift 5856593
  have htrace : WordTrace (prefixWord ++ tailWord_5856593) baseStart_5856593 baseEnd_5856593 := by
    simpa [prefixWord, tailWord_5856593, baseEnd_5856593] using wordTrace_append hprefix tailTrace_5856593
  have hstable : (prefixWord ++ tailWord_5856593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856593).length < 2 ^ (prefixWord ++ tailWord_5856593).sum := by decide
  have hdescent : baseEnd_5856593 < baseStart_5856593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856597 : List Nat := [1, 3, 2, 2, 3, 3, 1, 1, 2, 3, 2]
def baseStart_5856597 : Nat := 118140960795 + 5856597 * 2 ^ 59
def prefixEnd_5856597 : Nat := 4983230072969 + 3 ^ 40 * 5856597 * 2
def baseEnd_5856597 : Nat := 3007249260679927771003507

theorem tailTrace_5856597 : CollatzResearch.WordTrace tailWord_5856597 prefixEnd_5856597 3007249260679927771003507 := by
  unfold tailWord_5856597
  simp only [CollatzResearch.WordTrace]
  refine ⟨213607641163556770980560045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142405094109037847320373363 213607641163556770980560045)
  ·
    refine ⟨80102865436333789117710017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213607641163556770980560045 80102865436333789117710017)
    ·
      refine ⟨60077149077250341838282513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80102865436333789117710017 60077149077250341838282513)
      ·
        refine ⟨45057861807937756378711885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60077149077250341838282513 45057861807937756378711885)
        ·
          refine ⟨16896698177976658642016957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45057861807937756378711885 16896698177976658642016957)
          ·
            refine ⟨6336261816741246990756359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16896698177976658642016957 6336261816741246990756359)
            ·
              refine ⟨9504392725111870486134539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6336261816741246990756359 9504392725111870486134539)
              ·
                refine ⟨14256589087667805729201809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9504392725111870486134539 14256589087667805729201809)
                ·
                  refine ⟨10692441815750854296901357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14256589087667805729201809 10692441815750854296901357)
                  ·
                    refine ⟨4009665680906570361338009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10692441815750854296901357 4009665680906570361338009)
                    ·
                      refine ⟨3007249260679927771003507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4009665680906570361338009 3007249260679927771003507)
                      ·
                        rfl

theorem cell23_5856597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_5856597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856597 prefixEnd_5856597 := by exact prefixLift 5856597
  have htrace : WordTrace (prefixWord ++ tailWord_5856597) baseStart_5856597 baseEnd_5856597 := by
    simpa [prefixWord, tailWord_5856597, baseEnd_5856597] using wordTrace_append hprefix tailTrace_5856597
  have hstable : (prefixWord ++ tailWord_5856597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856597).length < 2 ^ (prefixWord ++ tailWord_5856597).sum := by decide
  have hdescent : baseEnd_5856597 < baseStart_5856597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856598 : List Nat := [5, 2, 3, 1, 1, 1, 2, 3, 1, 4]
def baseStart_5856598 : Nat := 118140960795 + 5856598 * 2 ^ 59
def prefixEnd_5856598 : Nat := 4983230072969 + 3 ^ 40 * 5856598 * 2
def baseEnd_5856598 : Nat := 1002416591386860755697001

theorem tailTrace_5856598 : CollatzResearch.WordTrace tailWord_5856598 prefixEnd_5856598 1002416591386860755697001 := by
  unfold tailWord_5856598
  simp only [CollatzResearch.WordTrace]
  refine ⟨13350479852284571759459153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142405118424368765434230965 13350479852284571759459153)
  ·
    refine ⟨10012859889213428819594365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13350479852284571759459153 10012859889213428819594365)
    ·
      refine ⟨3754822458455035807347887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10012859889213428819594365 3754822458455035807347887)
      ·
        refine ⟨5632233687682553711021831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3754822458455035807347887 5632233687682553711021831)
        ·
          refine ⟨8448350531523830566532747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5632233687682553711021831 8448350531523830566532747)
          ·
            refine ⟨12672525797285745849799121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8448350531523830566532747 12672525797285745849799121)
            ·
              refine ⟨9504394347964309387349341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12672525797285745849799121 9504394347964309387349341)
              ·
                refine ⟨3564147880486616020256003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9504394347964309387349341 3564147880486616020256003)
                ·
                  refine ⟨5346221820729924030384005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3564147880486616020256003 5346221820729924030384005)
                  ·
                    refine ⟨1002416591386860755697001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5346221820729924030384005 1002416591386860755697001)
                    ·
                      rfl

theorem cell23_5856598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_5856598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856598 prefixEnd_5856598 := by exact prefixLift 5856598
  have htrace : WordTrace (prefixWord ++ tailWord_5856598) baseStart_5856598 baseEnd_5856598 := by
    simpa [prefixWord, tailWord_5856598, baseEnd_5856598] using wordTrace_append hprefix tailTrace_5856598
  have hstable : (prefixWord ++ tailWord_5856598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856598).length < 2 ^ (prefixWord ++ tailWord_5856598).sum := by decide
  have hdescent : baseEnd_5856598 < baseStart_5856598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856610 : List Nat := [3, 3, 2, 1, 1, 1, 3, 3, 1, 1, 4]
def baseStart_5856610 : Nat := 118140960795 + 5856610 * 2 ^ 59
def prefixEnd_5856610 : Nat := 4983230072969 + 3 ^ 40 * 5856610 * 2
def baseEnd_5856610 : Nat := 3007255935928436220140947

theorem tailTrace_5856610 : CollatzResearch.WordTrace tailWord_5856610 prefixEnd_5856610 3007255935928436220140947 := by
  unfold tailWord_5856610
  simp only [CollatzResearch.WordTrace]
  refine ⟨53402028828127418550195821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142405410208339782800522189 53402028828127418550195821)
  ·
    refine ⟨20025760810547781956323433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53402028828127418550195821 20025760810547781956323433)
    ·
      refine ⟨15019320607910836467242575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20025760810547781956323433 15019320607910836467242575)
      ·
        refine ⟨22528980911866254700863863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15019320607910836467242575 22528980911866254700863863)
        ·
          refine ⟨33793471367799382051295795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22528980911866254700863863 33793471367799382051295795)
          ·
            refine ⟨50690207051699073076943693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33793471367799382051295795 50690207051699073076943693)
            ·
              refine ⟨19008827644387152403853885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50690207051699073076943693 19008827644387152403853885)
              ·
                refine ⟨7128310366645182151445207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19008827644387152403853885 7128310366645182151445207)
                ·
                  refine ⟨10692465549967773227167811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7128310366645182151445207 10692465549967773227167811)
                  ·
                    refine ⟨16038698324951659840751717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10692465549967773227167811 16038698324951659840751717)
                    ·
                      refine ⟨3007255935928436220140947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16038698324951659840751717 3007255935928436220140947)
                      ·
                        rfl

theorem cell23_5856610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_5856610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856610 prefixEnd_5856610 := by exact prefixLift 5856610
  have htrace : WordTrace (prefixWord ++ tailWord_5856610) baseStart_5856610 baseEnd_5856610 := by
    simpa [prefixWord, tailWord_5856610, baseEnd_5856610] using wordTrace_append hprefix tailTrace_5856610
  have hstable : (prefixWord ++ tailWord_5856610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856610).length < 2 ^ (prefixWord ++ tailWord_5856610).sum := by decide
  have hdescent : baseEnd_5856610 < baseStart_5856610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856620 : List Nat := [2, 2, 1, 1, 5, 1, 3, 2, 2, 4]
def baseStart_5856620 : Nat := 118140960795 + 5856620 * 2 ^ 59
def prefixEnd_5856620 : Nat := 4983230072969 + 3 ^ 40 * 5856620 * 2
def baseEnd_5856620 : Nat := 1002420356911660393671967

theorem tailTrace_5856620 : CollatzResearch.WordTrace tailWord_5856620 prefixEnd_5856620 1002420356911660393671967 := by
  unfold tailWord_5856620
  simp only [CollatzResearch.WordTrace]
  refine ⟨106804240021236722954323657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142405653361648963939098209 106804240021236722954323657)
  ·
    refine ⟨80103180015927542215742743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106804240021236722954323657 80103180015927542215742743)
    ·
      refine ⟨120154770023891313323614115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80103180015927542215742743 120154770023891313323614115)
      ·
        refine ⟨180232155035836969985421173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120154770023891313323614115 180232155035836969985421173)
        ·
          refine ⟨16896764534609715936133235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 180232155035836969985421173 16896764534609715936133235)
          ·
            refine ⟨25345146801914573904199853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16896764534609715936133235 25345146801914573904199853)
            ·
              refine ⟨9504430050717965214074945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25345146801914573904199853 9504430050717965214074945)
              ·
                refine ⟨7128322538038473910556209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9504430050717965214074945 7128322538038473910556209)
                ·
                  refine ⟨5346241903528855432917157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7128322538038473910556209 5346241903528855432917157)
                  ·
                    refine ⟨1002420356911660393671967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5346241903528855432917157 1002420356911660393671967)
                    ·
                      rfl

theorem cell23_5856620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 4].length) (baseStart_5856620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856620 prefixEnd_5856620 := by exact prefixLift 5856620
  have htrace : WordTrace (prefixWord ++ tailWord_5856620) baseStart_5856620 baseEnd_5856620 := by
    simpa [prefixWord, tailWord_5856620, baseEnd_5856620] using wordTrace_append hprefix tailTrace_5856620
  have hstable : (prefixWord ++ tailWord_5856620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856620).length < 2 ^ (prefixWord ++ tailWord_5856620).sum := by decide
  have hdescent : baseEnd_5856620 < baseStart_5856620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856750 : List Nat := [4, 1, 2, 1, 2, 1, 3, 1, 2, 3, 3]
def baseStart_5856750 : Nat := 118140960795 + 5856750 * 2 ^ 59
def prefixEnd_5856750 : Nat := 4983230072969 + 3 ^ 40 * 5856750 * 2
def baseEnd_5856750 : Nat := 3007327823220065672390303

theorem tailTrace_5856750 : CollatzResearch.WordTrace tailWord_5856750 prefixEnd_5856750 3007327823220065672390303 := by
  unfold tailWord_5856750
  simp only [CollatzResearch.WordTrace]
  refine ⟨26701652691500309763859963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142408814354668318740586469 26701652691500309763859963)
  ·
    refine ⟨40052479037250464645789945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26701652691500309763859963 40052479037250464645789945)
    ·
      refine ⟨30039359277937848484342459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40052479037250464645789945 30039359277937848484342459)
      ·
        refine ⟨45059038916906772726513689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30039359277937848484342459 45059038916906772726513689)
        ·
          refine ⟨33794279187680079544885267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45059038916906772726513689 33794279187680079544885267)
          ·
            refine ⟨50691418781520119317327901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33794279187680079544885267 50691418781520119317327901)
            ·
              refine ⟨19009282043070044743997963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50691418781520119317327901 19009282043070044743997963)
              ·
                refine ⟨28513923064605067115996945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19009282043070044743997963 28513923064605067115996945)
                ·
                  refine ⟨21385442298453800336997709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28513923064605067115996945 21385442298453800336997709)
                  ·
                    refine ⟨8019540861920175126374141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21385442298453800336997709 8019540861920175126374141)
                    ·
                      refine ⟨3007327823220065672390303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8019540861920175126374141 3007327823220065672390303)
                      ·
                        rfl

theorem cell23_5856750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_5856750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856750 prefixEnd_5856750 := by exact prefixLift 5856750
  have htrace : WordTrace (prefixWord ++ tailWord_5856750) baseStart_5856750 baseEnd_5856750 := by
    simpa [prefixWord, tailWord_5856750, baseEnd_5856750] using wordTrace_append hprefix tailTrace_5856750
  have hstable : (prefixWord ++ tailWord_5856750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856750).length < 2 ^ (prefixWord ++ tailWord_5856750).sum := by decide
  have hdescent : baseEnd_5856750 < baseStart_5856750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856793 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 5, 4, 3]
def baseStart_5856793 : Nat := 118140960795 + 5856793 * 2 ^ 59
def prefixEnd_5856793 : Nat := 4983230072969 + 3 ^ 40 * 5856793 * 2
def baseEnd_5856793 : Nat := 3007349902888209004152605

theorem tailTrace_5856793 : CollatzResearch.WordTrace tailWord_5856793 prefixEnd_5856793 3007349902888209004152605 := by
  unfold tailWord_5856793
  simp only [CollatzResearch.WordTrace]
  refine ⟨213614789870846696454695033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142409859913897797636463355 213614789870846696454695033)
  ·
    refine ⟨160211092403135022341021275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213614789870846696454695033 160211092403135022341021275)
    ·
      refine ⟨240316638604702533511531913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160211092403135022341021275 240316638604702533511531913)
      ·
        refine ⟨180237478953526900133648935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240316638604702533511531913 180237478953526900133648935)
        ·
          refine ⟨270356218430290350200473403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180237478953526900133648935 270356218430290350200473403)
          ·
            refine ⟨405534327645435525300710105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270356218430290350200473403 405534327645435525300710105)
            ·
              refine ⟨304150745734076643975532579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 405534327645435525300710105 304150745734076643975532579)
              ·
                refine ⟨456226118601114965963298869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304150745734076643975532579 456226118601114965963298869)
                ·
                  refine ⟨42771198618854528059059269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 456226118601114965963298869 42771198618854528059059269)
                  ·
                    refine ⟨8019599741035224011073613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42771198618854528059059269 8019599741035224011073613)
                    ·
                      refine ⟨3007349902888209004152605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8019599741035224011073613 3007349902888209004152605)
                      ·
                        rfl

theorem cell23_5856793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 4, 3].length) (baseStart_5856793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856793 prefixEnd_5856793 := by exact prefixLift 5856793
  have htrace : WordTrace (prefixWord ++ tailWord_5856793) baseStart_5856793 baseEnd_5856793 := by
    simpa [prefixWord, tailWord_5856793, baseEnd_5856793] using wordTrace_append hprefix tailTrace_5856793
  have hstable : (prefixWord ++ tailWord_5856793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856793).length < 2 ^ (prefixWord ++ tailWord_5856793).sum := by decide
  have hdescent : baseEnd_5856793 < baseStart_5856793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856810 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 3, 4, 3]
def baseStart_5856810 : Nat := 118140960795 + 5856810 * 2 ^ 59
def prefixEnd_5856810 : Nat := 4983230072969 + 3 ^ 40 * 5856810 * 2
def baseEnd_5856810 : Nat := 3007358632059335437640027

theorem tailTrace_5856810 : CollatzResearch.WordTrace tailWord_5856810 prefixEnd_5856810 3007358632059335437640027 := by
  unfold tailWord_5856810
  simp only [CollatzResearch.WordTrace]
  refine ⟨53403852477946277089515971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142410273274523405572042589 53403852477946277089515971)
  ·
    refine ⟨80105778716919415634273957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53403852477946277089515971 80105778716919415634273957)
    ·
      refine ⟨15019833509422390431426367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80105778716919415634273957 15019833509422390431426367)
      ·
        refine ⟨22529750264133585647139551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15019833509422390431426367 22529750264133585647139551)
        ·
          refine ⟨33794625396200378470709327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22529750264133585647139551 33794625396200378470709327)
          ·
            refine ⟨50691938094300567706063991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33794625396200378470709327 50691938094300567706063991)
            ·
              refine ⟨76037907141450851559095987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50691938094300567706063991 76037907141450851559095987)
              ·
                refine ⟨114056860712176277338643981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76037907141450851559095987 114056860712176277338643981)
                ·
                  refine ⟨42771322767066104001991493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114056860712176277338643981 42771322767066104001991493)
                  ·
                    refine ⟨8019623018824894500373405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42771322767066104001991493 8019623018824894500373405)
                    ·
                      refine ⟨3007358632059335437640027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8019623018824894500373405 3007358632059335437640027)
                      ·
                        rfl

theorem cell23_5856810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_5856810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856810 prefixEnd_5856810 := by exact prefixLift 5856810
  have htrace : WordTrace (prefixWord ++ tailWord_5856810) baseStart_5856810 baseEnd_5856810 := by
    simpa [prefixWord, tailWord_5856810, baseEnd_5856810] using wordTrace_append hprefix tailTrace_5856810
  have hstable : (prefixWord ++ tailWord_5856810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856810).length < 2 ^ (prefixWord ++ tailWord_5856810).sum := by decide
  have hdescent : baseEnd_5856810 < baseStart_5856810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856843 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 5, 5]
def baseStart_5856843 : Nat := 118140960795 + 5856843 * 2 ^ 59
def prefixEnd_5856843 : Nat := 4983230072969 + 3 ^ 40 * 5856843 * 2
def baseEnd_5856843 : Nat := 1002458525640311269509125

theorem tailTrace_5856843 : CollatzResearch.WordTrace tailWord_5856843 prefixEnd_5856843 1002458525640311269509125 := by
  unfold tailWord_5856843
  simp only [CollatzResearch.WordTrace]
  refine ⟨213616613520665554994015183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142411075680443703329343455 213616613520665554994015183)
  ·
    refine ⟨320424920280998332491022775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213616613520665554994015183 320424920280998332491022775)
    ·
      refine ⟨480637380421497498736534163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320424920280998332491022775 480637380421497498736534163)
      ·
        refine ⟨720956070632246248104801245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480637380421497498736534163 720956070632246248104801245)
        ·
          refine ⟨270358526487092343039300467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 720956070632246248104801245 270358526487092343039300467)
          ·
            refine ⟨405537789730638514558950701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270358526487092343039300467 405537789730638514558950701)
            ·
              refine ⟨152076671148989442959606513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 405537789730638514558950701 152076671148989442959606513)
              ·
                refine ⟨114057503361742082219704885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152076671148989442959606513 114057503361742082219704885)
                ·
                  refine ⟨10692890940163320208097333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114057503361742082219704885 10692890940163320208097333)
                  ·
                    refine ⟨1002458525640311269509125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10692890940163320208097333 1002458525640311269509125)
                    ·
                      rfl

theorem cell23_5856843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 5].length) (baseStart_5856843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856843 prefixEnd_5856843 := by exact prefixLift 5856843
  have htrace : WordTrace (prefixWord ++ tailWord_5856843) baseStart_5856843 baseEnd_5856843 := by
    simpa [prefixWord, tailWord_5856843, baseEnd_5856843] using wordTrace_append hprefix tailTrace_5856843
  have hstable : (prefixWord ++ tailWord_5856843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856843).length < 2 ^ (prefixWord ++ tailWord_5856843).sum := by decide
  have hdescent : baseEnd_5856843 < baseStart_5856843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856853 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 2, 1, 7]
def baseStart_5856853 : Nat := 118140960795 + 5856853 * 2 ^ 59
def prefixEnd_5856853 : Nat := 4983230072969 + 3 ^ 40 * 5856853 * 2
def baseEnd_5856853 : Nat := 3007380711727478769402329

theorem tailTrace_5856853 : CollatzResearch.WordTrace tailWord_5856853 prefixEnd_5856853 3007380711727478769402329 := by
  unfold tailWord_5856853
  simp only [CollatzResearch.WordTrace]
  refine ⟨213616978250629326701879213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142411318833752884467919475 213616978250629326701879213)
  ·
    refine ⟨80106366843985997513204705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213616978250629326701879213 80106366843985997513204705)
    ·
      refine ⟨60079775132989498134903529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80106366843985997513204705 60079775132989498134903529)
      ·
        refine ⟨45059831349742123601177647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60079775132989498134903529 45059831349742123601177647)
        ·
          refine ⟨67589747024613185401766471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45059831349742123601177647 67589747024613185401766471)
          ·
            refine ⟨101384620536919778102649707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67589747024613185401766471 101384620536919778102649707)
            ·
              refine ⟨152076930805379667153974561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101384620536919778102649707 152076930805379667153974561)
              ·
                refine ⟨114057698104034750365480921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152076930805379667153974561 114057698104034750365480921)
                ·
                  refine ⟨85543273578026062774110691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114057698104034750365480921 85543273578026062774110691)
                  ·
                    refine ⟨128314910367039094161166037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85543273578026062774110691 128314910367039094161166037)
                    ·
                      refine ⟨3007380711727478769402329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 128314910367039094161166037 3007380711727478769402329)
                      ·
                        rfl

theorem cell23_5856853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_5856853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856853 prefixEnd_5856853 := by exact prefixLift 5856853
  have htrace : WordTrace (prefixWord ++ tailWord_5856853) baseStart_5856853 baseEnd_5856853 := by
    simpa [prefixWord, tailWord_5856853, baseEnd_5856853] using wordTrace_append hprefix tailTrace_5856853
  have hstable : (prefixWord ++ tailWord_5856853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856853).length < 2 ^ (prefixWord ++ tailWord_5856853).sum := by decide
  have hdescent : baseEnd_5856853 < baseStart_5856853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856863 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 4]
def baseStart_5856863 : Nat := 118140960795 + 5856863 * 2 ^ 59
def prefixEnd_5856863 : Nat := 4983230072969 + 3 ^ 40 * 5856863 * 2
def baseEnd_5856863 : Nat := 3007385846534023730277283

theorem tailTrace_5856863 : CollatzResearch.WordTrace tailWord_5856863 prefixEnd_5856863 3007385846534023730277283 := by
  unfold tailWord_5856863
  simp only [CollatzResearch.WordTrace]
  refine ⟨213617342980593098409743243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142411561987062065606495495 213617342980593098409743243)
  ·
    refine ⟨320426014470889647614614865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213617342980593098409743243 320426014470889647614614865)
    ·
      refine ⟨240319510853167235710961149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320426014470889647614614865 240319510853167235710961149)
      ·
        refine ⟨90119816569937713391610431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240319510853167235710961149 90119816569937713391610431)
        ·
          refine ⟨135179724854906570087415647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90119816569937713391610431 135179724854906570087415647)
          ·
            refine ⟨202769587282359855131123471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135179724854906570087415647 202769587282359855131123471)
            ·
              refine ⟨304154380923539782696685207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202769587282359855131123471 304154380923539782696685207)
              ·
                refine ⟨456231571385309674045027811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304154380923539782696685207 456231571385309674045027811)
                ·
                  refine ⟨684347357077964511067541717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 456231571385309674045027811 684347357077964511067541717)
                  ·
                    refine ⟨16039391181514793228145509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 684347357077964511067541717 16039391181514793228145509)
                    ·
                      refine ⟨3007385846534023730277283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16039391181514793228145509 3007385846534023730277283)
                      ·
                        rfl

theorem cell23_5856863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_5856863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856863 prefixEnd_5856863 := by exact prefixLift 5856863
  have htrace : WordTrace (prefixWord ++ tailWord_5856863) baseStart_5856863 baseEnd_5856863 := by
    simpa [prefixWord, tailWord_5856863, baseEnd_5856863] using wordTrace_append hprefix tailTrace_5856863
  have hstable : (prefixWord ++ tailWord_5856863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856863).length < 2 ^ (prefixWord ++ tailWord_5856863).sum := by decide
  have hdescent : baseEnd_5856863 < baseStart_5856863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856877 : List Nat := [1, 5, 1, 1, 4, 1, 1, 1, 3, 5]
def baseStart_5856877 : Nat := 118140960795 + 5856877 * 2 ^ 59
def prefixEnd_5856877 : Nat := 4983230072969 + 3 ^ 40 * 5856877 * 2
def baseEnd_5856877 : Nat := 1002464345087728891834073

theorem tailTrace_5856877 : CollatzResearch.WordTrace tailWord_5856877 prefixEnd_5856877 1002464345087728891834073 := by
  unfold tailWord_5856877
  simp only [CollatzResearch.WordTrace]
  refine ⟨213617853602542378800752885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142411902401694919200501923 213617853602542378800752885)
  ·
    refine ⟨20026673775238348012570583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 213617853602542378800752885 20026673775238348012570583)
    ·
      refine ⟨30040010662857522018855875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20026673775238348012570583 30040010662857522018855875)
      ·
        refine ⟨45060015994286283028283813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30040010662857522018855875 45060015994286283028283813)
        ·
          refine ⟨8448752998928678067803215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45060015994286283028283813 8448752998928678067803215)
          ·
            refine ⟨12673129498393017101704823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8448752998928678067803215 12673129498393017101704823)
            ·
              refine ⟨19009694247589525652557235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12673129498393017101704823 19009694247589525652557235)
              ·
                refine ⟨28514541371384288478835853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19009694247589525652557235 28514541371384288478835853)
                ·
                  refine ⟨10692953014269108179563445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28514541371384288478835853 10692953014269108179563445)
                  ·
                    refine ⟨1002464345087728891834073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10692953014269108179563445 1002464345087728891834073)
                    ·
                      rfl

theorem cell23_5856877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_5856877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856877 prefixEnd_5856877 := by exact prefixLift 5856877
  have htrace : WordTrace (prefixWord ++ tailWord_5856877) baseStart_5856877 baseEnd_5856877 := by
    simpa [prefixWord, tailWord_5856877, baseEnd_5856877] using wordTrace_append hprefix tailTrace_5856877
  have hstable : (prefixWord ++ tailWord_5856877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856877).length < 2 ^ (prefixWord ++ tailWord_5856877).sum := by decide
  have hdescent : baseEnd_5856877 < baseStart_5856877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856890 : List Nat := [3, 1, 1, 1, 1, 1, 1, 6, 4, 4]
def baseStart_5856890 : Nat := 118140960795 + 5856890 * 2 ^ 59
def prefixEnd_5856890 : Nat := 4983230072969 + 3 ^ 40 * 5856890 * 2
def baseEnd_5856890 : Nat := 1002466570170565041546553

theorem tailTrace_5856890 : CollatzResearch.WordTrace tailWord_5856890 prefixEnd_5856890 1002466570170565041546553 := by
  unfold tailWord_5856890
  simp only [CollatzResearch.WordTrace]
  refine ⟨53404581937873820505244031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142412218500996854680650749 53404581937873820505244031)
  ·
    refine ⟨80106872906810730757866047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53404581937873820505244031 80106872906810730757866047)
    ·
      refine ⟨120160309360216096136799071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80106872906810730757866047 120160309360216096136799071)
      ·
        refine ⟨180240464040324144205198607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120160309360216096136799071 180240464040324144205198607)
        ·
          refine ⟨270360696060486216307797911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180240464040324144205198607 270360696060486216307797911)
          ·
            refine ⟨405541044090729324461696867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270360696060486216307797911 405541044090729324461696867)
            ·
              refine ⟨608311566136093986692545301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 405541044090729324461696867 608311566136093986692545301)
              ·
                refine ⟨28514604662629405626213061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 608311566136093986692545301 28514604662629405626213061)
                ·
                  refine ⟨5346488374243013554914949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28514604662629405626213061 5346488374243013554914949)
                  ·
                    refine ⟨1002466570170565041546553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5346488374243013554914949 1002466570170565041546553)
                    ·
                      rfl

theorem cell23_5856890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 4, 4].length) (baseStart_5856890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856890 prefixEnd_5856890 := by exact prefixLift 5856890
  have htrace : WordTrace (prefixWord ++ tailWord_5856890) baseStart_5856890 baseEnd_5856890 := by
    simpa [prefixWord, tailWord_5856890, baseEnd_5856890] using wordTrace_append hprefix tailTrace_5856890
  have hstable : (prefixWord ++ tailWord_5856890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856890).length < 2 ^ (prefixWord ++ tailWord_5856890).sum := by decide
  have hdescent : baseEnd_5856890 < baseStart_5856890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856903 : List Nat := [1, 1, 4, 2, 1, 14]
def baseStart_5856903 : Nat := 118140960795 + 5856903 * 2 ^ 59
def prefixEnd_5856903 : Nat := 4983230072969 + 3 ^ 40 * 5856903 * 2
def baseEnd_5856903 : Nat := 12376157966091372731593

theorem tailTrace_5856903 : CollatzResearch.WordTrace tailWord_5856903 prefixEnd_5856903 12376157966091372731593 := by
  unfold tailWord_5856903
  simp only [CollatzResearch.WordTrace]
  refine ⟨213618801900448185241199363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142412534600298790160799575 213618801900448185241199363)
  ·
    refine ⟨320428202850672277861799045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213618801900448185241199363 320428202850672277861799045)
    ·
      refine ⟨60080288034501052099087321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 320428202850672277861799045 60080288034501052099087321)
      ·
        refine ⟨45060216025875789074315491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60080288034501052099087321 45060216025875789074315491)
        ·
          refine ⟨67590324038813683611473237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45060216025875789074315491 67590324038813683611473237)
          ·
            refine ⟨12376157966091372731593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 67590324038813683611473237 12376157966091372731593)
            ·
              rfl

theorem cell23_5856903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 14].length) (baseStart_5856903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856903 prefixEnd_5856903 := by exact prefixLift 5856903
  have htrace : WordTrace (prefixWord ++ tailWord_5856903) baseStart_5856903 baseEnd_5856903 := by
    simpa [prefixWord, tailWord_5856903, baseEnd_5856903] using wordTrace_append hprefix tailTrace_5856903
  have hstable : (prefixWord ++ tailWord_5856903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856903).length < 2 ^ (prefixWord ++ tailWord_5856903).sum := by decide
  have hdescent : baseEnd_5856903 < baseStart_5856903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856907 : List Nat := [1, 1, 1, 1, 4, 1, 6, 2, 2, 4]
def baseStart_5856907 : Nat := 118140960795 + 5856907 * 2 ^ 59
def prefixEnd_5856907 : Nat := 4983230072969 + 3 ^ 40 * 5856907 * 2
def baseEnd_5856907 : Nat := 1002469479894273852709027

theorem tailTrace_5856907 : CollatzResearch.WordTrace tailWord_5856907 prefixEnd_5856907 1002469479894273852709027 := by
  unfold tailWord_5856907
  simp only [CollatzResearch.WordTrace]
  refine ⟨213618947792433693924344975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142412631861622462616229983 213618947792433693924344975)
  ·
    refine ⟨320428421688650540886517463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213618947792433693924344975 320428421688650540886517463)
    ·
      refine ⟨480642632532975811329776195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320428421688650540886517463 480642632532975811329776195)
      ·
        refine ⟨720963948799463716994664293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480642632532975811329776195 720963948799463716994664293)
        ·
          refine ⟨135180740399899446936499555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 720963948799463716994664293 135180740399899446936499555)
          ·
            refine ⟨202771110599849170404749333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135180740399899446936499555 202771110599849170404749333)
            ·
              refine ⟨9504895809367929862722625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 202771110599849170404749333 9504895809367929862722625)
              ·
                refine ⟨7128671857025947397041969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9504895809367929862722625 7128671857025947397041969)
                ·
                  refine ⟨5346503892769460547781477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7128671857025947397041969 5346503892769460547781477)
                  ·
                    refine ⟨1002469479894273852709027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5346503892769460547781477 1002469479894273852709027)
                    ·
                      rfl

theorem cell23_5856907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 2, 4].length) (baseStart_5856907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856907 prefixEnd_5856907 := by exact prefixLift 5856907
  have htrace : WordTrace (prefixWord ++ tailWord_5856907) baseStart_5856907 baseEnd_5856907 := by
    simpa [prefixWord, tailWord_5856907, baseEnd_5856907] using wordTrace_append hprefix tailTrace_5856907
  have hstable : (prefixWord ++ tailWord_5856907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856907).length < 2 ^ (prefixWord ++ tailWord_5856907).sum := by decide
  have hdescent : baseEnd_5856907 < baseStart_5856907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856913 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 7]
def baseStart_5856913 : Nat := 118140960795 + 5856913 * 2 ^ 59
def prefixEnd_5856913 : Nat := 4983230072969 + 3 ^ 40 * 5856913 * 2
def baseEnd_5856913 : Nat := 3007411520566748534652053

theorem tailTrace_5856913 : CollatzResearch.WordTrace tailWord_5856913 prefixEnd_5856913 3007411520566748534652053 := by
  unfold tailWord_5856913
  simp only [CollatzResearch.WordTrace]
  refine ⟨213619166630411956949063393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142412777753607971299375595 213619166630411956949063393)
  ·
    refine ⟨160214374972808967711797545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213619166630411956949063393 160214374972808967711797545)
    ·
      refine ⟨120160781229606725783848159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160214374972808967711797545 120160781229606725783848159)
      ·
        refine ⟨180241171844410088675772239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120160781229606725783848159 180241171844410088675772239)
        ·
          refine ⟨270361757766615133013658359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180241171844410088675772239 270361757766615133013658359)
          ·
            refine ⟨405542636649922699520487539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270361757766615133013658359 405542636649922699520487539)
            ·
              refine ⟨608313954974884049280731309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 405542636649922699520487539 608313954974884049280731309)
              ·
                refine ⟨228117733115581518480274241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 608313954974884049280731309 228117733115581518480274241)
                ·
                  refine ⟨171088299836686138860205681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 228117733115581518480274241 171088299836686138860205681)
                  ·
                    refine ⟨128316224877514604145154261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 171088299836686138860205681 128316224877514604145154261)
                    ·
                      refine ⟨3007411520566748534652053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 128316224877514604145154261 3007411520566748534652053)
                      ·
                        rfl

theorem cell23_5856913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_5856913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856913 prefixEnd_5856913 := by exact prefixLift 5856913
  have htrace : WordTrace (prefixWord ++ tailWord_5856913) baseStart_5856913 baseEnd_5856913 := by
    simpa [prefixWord, tailWord_5856913, baseEnd_5856913] using wordTrace_append hprefix tailTrace_5856913
  have hstable : (prefixWord ++ tailWord_5856913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856913).length < 2 ^ (prefixWord ++ tailWord_5856913).sum := by decide
  have hdescent : baseEnd_5856913 < baseStart_5856913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856920 : List Nat := [2, 1, 2, 4, 1, 2, 3, 8]
def baseStart_5856920 : Nat := 118140960795 + 5856920 * 2 ^ 59
def prefixEnd_5856920 : Nat := 4983230072969 + 3 ^ 40 * 5856920 * 2
def baseEnd_5856920 : Nat := 111385744997456666935723

theorem tailTrace_5856920 : CollatzResearch.WordTrace tailWord_5856920 prefixEnd_5856920 111385744997456666935723 := by
  unfold tailWord_5856920
  simp only [CollatzResearch.WordTrace]
  refine ⟨106809710970693298572284107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142412947960924398096378809 106809710970693298572284107)
  ·
    refine ⟨160214566456039947858426161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106809710970693298572284107 160214566456039947858426161)
    ·
      refine ⟨120160924842029960893819621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160214566456039947858426161 120160924842029960893819621)
      ·
        refine ⟨22530173407880617667591179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120160924842029960893819621 22530173407880617667591179)
        ·
          refine ⟨33795260111820926501386769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22530173407880617667591179 33795260111820926501386769)
          ·
            refine ⟨25346445083865694876040077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33795260111820926501386769 25346445083865694876040077)
            ·
              refine ⟨9504916906449635578515029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25346445083865694876040077 9504916906449635578515029)
              ·
                refine ⟨111385744997456666935723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9504916906449635578515029 111385744997456666935723)
                ·
                  rfl

theorem cell23_5856920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 8].length) (baseStart_5856920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856920 prefixEnd_5856920 := by exact prefixLift 5856920
  have htrace : WordTrace (prefixWord ++ tailWord_5856920) baseStart_5856920 baseEnd_5856920 := by
    simpa [prefixWord, tailWord_5856920, baseEnd_5856920] using wordTrace_append hprefix tailTrace_5856920
  have hstable : (prefixWord ++ tailWord_5856920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856920).length < 2 ^ (prefixWord ++ tailWord_5856920).sum := by decide
  have hdescent : baseEnd_5856920 < baseStart_5856920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856947 : List Nat := [1, 1, 1, 2, 3, 3, 2, 2, 4, 1, 3]
def baseStart_5856947 : Nat := 118140960795 + 5856947 * 2 ^ 59
def prefixEnd_5856947 : Nat := 4983230072969 + 3 ^ 40 * 5856947 * 2
def baseEnd_5856947 : Nat := 3007428978909001401626897

theorem tailTrace_5856947 : CollatzResearch.WordTrace tailWord_5856947 prefixEnd_5856947 3007428978909001401626897 := by
  unfold tailWord_5856947
  simp only [CollatzResearch.WordTrace]
  refine ⟨213620406712288780755801095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142413604474859187170534063 213620406712288780755801095)
  ·
    refine ⟨320430610068433171133701643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213620406712288780755801095 320430610068433171133701643)
    ·
      refine ⟨480645915102649756700552465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320430610068433171133701643 480645915102649756700552465)
      ·
        refine ⟨360484436326987317525414349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 480645915102649756700552465 360484436326987317525414349)
        ·
          refine ⟨135181663622620244072030381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 360484436326987317525414349 135181663622620244072030381)
          ·
            refine ⟨50693123858482591527011393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135181663622620244072030381 50693123858482591527011393)
            ·
              refine ⟨38019842893861943645258545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50693123858482591527011393 38019842893861943645258545)
              ·
                refine ⟨28514882170396457733943909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38019842893861943645258545 28514882170396457733943909)
                ·
                  refine ⟨5346540406949335825114483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28514882170396457733943909 5346540406949335825114483)
                  ·
                    refine ⟨8019810610424003737671725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5346540406949335825114483 8019810610424003737671725)
                    ·
                      refine ⟨3007428978909001401626897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8019810610424003737671725 3007428978909001401626897)
                      ·
                        rfl

theorem cell23_5856947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 4, 1, 3].length) (baseStart_5856947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856947 prefixEnd_5856947 := by exact prefixLift 5856947
  have htrace : WordTrace (prefixWord ++ tailWord_5856947) baseStart_5856947 baseEnd_5856947 := by
    simpa [prefixWord, tailWord_5856947, baseEnd_5856947] using wordTrace_append hprefix tailTrace_5856947
  have hstable : (prefixWord ++ tailWord_5856947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856947).length < 2 ^ (prefixWord ++ tailWord_5856947).sum := by decide
  have hdescent : baseEnd_5856947 < baseStart_5856947 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856951 : List Nat := [1, 1, 3, 1, 5, 3, 2, 1, 1, 2, 3]
def baseStart_5856951 : Nat := 118140960795 + 5856951 * 2 ^ 59
def prefixEnd_5856951 : Nat := 4983230072969 + 3 ^ 40 * 5856951 * 2
def baseEnd_5856951 : Nat := 3007431032831619385976879

theorem tailTrace_5856951 : CollatzResearch.WordTrace tailWord_5856951 prefixEnd_5856951 3007431032831619385976879 := by
  unfold tailWord_5856951
  simp only [CollatzResearch.WordTrace]
  refine ⟨213620552604274289438946707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142413701736182859625964471 213620552604274289438946707)
  ·
    refine ⟨320430828906411434158420061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213620552604274289438946707 320430828906411434158420061)
    ·
      refine ⟨120161560839904287809407523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 320430828906411434158420061 120161560839904287809407523)
      ·
        refine ⟨180242341259856431714111285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120161560839904287809407523 180242341259856431714111285)
        ·
          refine ⟨16897719493111540473197933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 180242341259856431714111285 16897719493111540473197933)
          ·
            refine ⟨6336644809916827677449225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16897719493111540473197933 6336644809916827677449225)
            ·
              refine ⟨4752483607437620758086919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6336644809916827677449225 4752483607437620758086919)
              ·
                refine ⟨7128725411156431137130379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4752483607437620758086919 7128725411156431137130379)
                ·
                  refine ⟨10693088116734646705695569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7128725411156431137130379 10693088116734646705695569)
                  ·
                    refine ⟨8019816087550985029271677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10693088116734646705695569 8019816087550985029271677)
                    ·
                      refine ⟨3007431032831619385976879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8019816087550985029271677 3007431032831619385976879)
                      ·
                        rfl

theorem cell23_5856951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 1, 2, 3].length) (baseStart_5856951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856951 prefixEnd_5856951 := by exact prefixLift 5856951
  have htrace : WordTrace (prefixWord ++ tailWord_5856951) baseStart_5856951 baseEnd_5856951 := by
    simpa [prefixWord, tailWord_5856951, baseEnd_5856951] using wordTrace_append hprefix tailTrace_5856951
  have hstable : (prefixWord ++ tailWord_5856951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856951).length < 2 ^ (prefixWord ++ tailWord_5856951).sum := by decide
  have hdescent : baseEnd_5856951 < baseStart_5856951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5856964 : List Nat := [2, 3, 3, 1, 1, 1, 3, 1, 4, 1, 3]
def baseStart_5856964 : Nat := 118140960795 + 5856964 * 2 ^ 59
def prefixEnd_5856964 : Nat := 4983230072969 + 3 ^ 40 * 5856964 * 2
def baseEnd_5856964 : Nat := 3007437708080127835114319

theorem tailTrace_5856964 : CollatzResearch.WordTrace tailWord_5856964 prefixEnd_5856964 3007437708080127835114319 := by
  unfold tailWord_5856964
  simp only [CollatzResearch.WordTrace]
  refine ⟨106810513376613596329584973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142414017835484795106113297 106810513376613596329584973)
  ·
    refine ⟨40053942516230098623594365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106810513376613596329584973 40053942516230098623594365)
    ·
      refine ⟨15020228443586286983847887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40053942516230098623594365 15020228443586286983847887)
      ·
        refine ⟨22530342665379430475771831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15020228443586286983847887 22530342665379430475771831)
        ·
          refine ⟨33795513998069145713657747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22530342665379430475771831 33795513998069145713657747)
          ·
            refine ⟨50693270997103718570486621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33795513998069145713657747 50693270997103718570486621)
            ·
              refine ⟨19009976623913894463932483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50693270997103718570486621 19009976623913894463932483)
              ·
                refine ⟨28514964935870841695898725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19009976623913894463932483 28514964935870841695898725)
                ·
                  refine ⟨5346555925475782817981011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28514964935870841695898725 5346555925475782817981011)
                  ·
                    refine ⟨8019833888213674226971517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5346555925475782817981011 8019833888213674226971517)
                    ·
                      refine ⟨3007437708080127835114319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8019833888213674226971517 3007437708080127835114319)
                      ·
                        rfl

theorem cell23_5856964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_5856964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5856964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5856964 prefixEnd_5856964 := by exact prefixLift 5856964
  have htrace : WordTrace (prefixWord ++ tailWord_5856964) baseStart_5856964 baseEnd_5856964 := by
    simpa [prefixWord, tailWord_5856964, baseEnd_5856964] using wordTrace_append hprefix tailTrace_5856964
  have hstable : (prefixWord ++ tailWord_5856964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5856964).length < 2 ^ (prefixWord ++ tailWord_5856964).sum := by decide
  have hdescent : baseEnd_5856964 < baseStart_5856964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5856964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857004 : List Nat := [2, 2, 1, 1, 2, 2, 3, 2, 4, 2, 2]
def baseStart_5857004 : Nat := 118140960795 + 5857004 * 2 ^ 59
def prefixEnd_5857004 : Nat := 4983230072969 + 3 ^ 40 * 5857004 * 2
def baseEnd_5857004 : Nat := 3007458247306307678614135

theorem tailTrace_5857004 : CollatzResearch.WordTrace tailWord_5857004 prefixEnd_5857004 3007458247306307678614135 := by
  unfold tailWord_5857004
  simp only [CollatzResearch.WordTrace]
  refine ⟨106811242836541139745313033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142414990448721519660417377 106811242836541139745313033)
  ·
    refine ⟨80108432127405854808984775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106811242836541139745313033 80108432127405854808984775)
    ·
      refine ⟨120162648191108782213477163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80108432127405854808984775 120162648191108782213477163)
      ·
        refine ⟨180243972286663173320215745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120162648191108782213477163 180243972286663173320215745)
        ·
          refine ⟨135182979214997379990161809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180243972286663173320215745 135182979214997379990161809)
          ·
            refine ⟨101387234411248034992621357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135182979214997379990161809 101387234411248034992621357)
            ·
              refine ⟨38020212904218013122233009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101387234411248034992621357 38020212904218013122233009)
              ·
                refine ⟨28515159678163509841674757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38020212904218013122233009 28515159678163509841674757)
                ·
                  refine ⟨5346592439655658095314017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28515159678163509841674757 5346592439655658095314017)
                  ·
                    refine ⟨4009944329741743571485513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5346592439655658095314017 4009944329741743571485513)
                    ·
                      refine ⟨3007458247306307678614135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4009944329741743571485513 3007458247306307678614135)
                      ·
                        rfl

theorem cell23_5857004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 2, 2].length) (baseStart_5857004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857004 prefixEnd_5857004 := by exact prefixLift 5857004
  have htrace : WordTrace (prefixWord ++ tailWord_5857004) baseStart_5857004 baseEnd_5857004 := by
    simpa [prefixWord, tailWord_5857004, baseEnd_5857004] using wordTrace_append hprefix tailTrace_5857004
  have hstable : (prefixWord ++ tailWord_5857004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857004).length < 2 ^ (prefixWord ++ tailWord_5857004).sum := by decide
  have hdescent : baseEnd_5857004 < baseStart_5857004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857020 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 1, 2, 7]
def baseStart_5857020 : Nat := 118140960795 + 5857020 * 2 ^ 59
def prefixEnd_5857020 : Nat := 4983230072969 + 3 ^ 40 * 5857020 * 2
def baseEnd_5857020 : Nat := 3007466462996779616014061

theorem tailTrace_5857020 : CollatzResearch.WordTrace tailWord_5857020 prefixEnd_5857020 3007466462996779616014061 := by
  unfold tailWord_5857020
  simp only [CollatzResearch.WordTrace]
  refine ⟨106811534620512157111604257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142415379494016209482139009 106811534620512157111604257)
  ·
    refine ⟨80108650965384117833703193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106811534620512157111604257 80108650965384117833703193)
    ·
      refine ⟨60081488224038088375277395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80108650965384117833703193 60081488224038088375277395)
      ·
        refine ⟨90122232336057132562916093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60081488224038088375277395 90122232336057132562916093)
        ·
          refine ⟨33795837126021424711093535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90122232336057132562916093 33795837126021424711093535)
          ·
            refine ⟨50693755689032137066640303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33795837126021424711093535 50693755689032137066640303)
            ·
              refine ⟨76040633533548205599960455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50693755689032137066640303 76040633533548205599960455)
              ·
                refine ⟨114060950300322308399940683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76040633533548205599960455 114060950300322308399940683)
                ·
                  refine ⟨171091425450483462599911025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114060950300322308399940683 171091425450483462599911025)
                  ·
                    refine ⟨128318569087862596949933269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 171091425450483462599911025 128318569087862596949933269)
                    ·
                      refine ⟨3007466462996779616014061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 128318569087862596949933269 3007466462996779616014061)
                      ·
                        rfl

theorem cell23_5857020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_5857020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857020 prefixEnd_5857020 := by exact prefixLift 5857020
  have htrace : WordTrace (prefixWord ++ tailWord_5857020) baseStart_5857020 baseEnd_5857020 := by
    simpa [prefixWord, tailWord_5857020, baseEnd_5857020] using wordTrace_append hprefix tailTrace_5857020
  have hstable : (prefixWord ++ tailWord_5857020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857020).length < 2 ^ (prefixWord ++ tailWord_5857020).sum := by decide
  have hdescent : baseEnd_5857020 < baseStart_5857020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857027 : List Nat := [1, 1, 1, 3, 2, 2, 2, 6, 5]
def baseStart_5857027 : Nat := 118140960795 + 5857027 * 2 ^ 59
def prefixEnd_5857027 : Nat := 4983230072969 + 3 ^ 40 * 5857027 * 2
def baseEnd_5857027 : Nat := 334163339706817898736281

theorem tailTrace_5857027 : CollatzResearch.WordTrace tailWord_5857027 prefixEnd_5857027 334163339706817898736281 := by
  unfold tailWord_5857027
  simp only [CollatzResearch.WordTrace]
  refine ⟨213623324551998954418713335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142415549701332636279142223 213623324551998954418713335)
  ·
    refine ⟨320434986827998431628070003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213623324551998954418713335 320434986827998431628070003)
    ·
      refine ⟨480652480241997647442105005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320434986827998431628070003 480652480241997647442105005)
      ·
        refine ⟨180244680090749117790789377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 480652480241997647442105005 180244680090749117790789377)
        ·
          refine ⟨135183510068061838343092033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180244680090749117790789377 135183510068061838343092033)
          ·
            refine ⟨101387632551046378757319025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135183510068061838343092033 101387632551046378757319025)
            ·
              refine ⟨76040724413284784067989269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101387632551046378757319025 76040724413284784067989269)
              ·
                refine ⟨3564408956872724253186997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76040724413284784067989269 3564408956872724253186997)
                ·
                  refine ⟨334163339706817898736281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3564408956872724253186997 334163339706817898736281)
                  ·
                    rfl

theorem cell23_5857027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 6, 5].length) (baseStart_5857027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857027 prefixEnd_5857027 := by exact prefixLift 5857027
  have htrace : WordTrace (prefixWord ++ tailWord_5857027) baseStart_5857027 baseEnd_5857027 := by
    simpa [prefixWord, tailWord_5857027, baseEnd_5857027] using wordTrace_append hprefix tailTrace_5857027
  have hstable : (prefixWord ++ tailWord_5857027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857027).length < 2 ^ (prefixWord ++ tailWord_5857027).sum := by decide
  have hdescent : baseEnd_5857027 < baseStart_5857027 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857038 : List Nat := [4, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2]
def baseStart_5857038 : Nat := 118140960795 + 5857038 * 2 ^ 59
def prefixEnd_5857038 : Nat := 4983230072969 + 3 ^ 40 * 5857038 * 2
def baseEnd_5857038 : Nat := 3007475705648560545588979

theorem tailTrace_5857038 : CollatzResearch.WordTrace tailWord_5857038 prefixEnd_5857038 3007475705648560545588979 := by
  unfold tailWord_5857038
  simp only [CollatzResearch.WordTrace]
  refine ⟨26702965719369887912170471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142415817169972735531575845 26702965719369887912170471)
  ·
    refine ⟨40054448579054831868255707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26702965719369887912170471 40054448579054831868255707)
    ·
      refine ⟨60081672868582247802383561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40054448579054831868255707 60081672868582247802383561)
      ·
        refine ⟨45061254651436685851787671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60081672868582247802383561 45061254651436685851787671)
        ·
          refine ⟨67591881977155028777681507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45061254651436685851787671 67591881977155028777681507)
          ·
            refine ⟨101387822965732543166522261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67591881977155028777681507 101387822965732543166522261)
            ·
              refine ⟨4752554201518712960930731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 101387822965732543166522261 4752554201518712960930731)
              ·
                refine ⟨7128831302278069441396097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4752554201518712960930731 7128831302278069441396097)
                ·
                  refine ⟨5346623476708552081047073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7128831302278069441396097 5346623476708552081047073)
                  ·
                    refine ⟨4009967607531414060785305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5346623476708552081047073 4009967607531414060785305)
                    ·
                      refine ⟨3007475705648560545588979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4009967607531414060785305 3007475705648560545588979)
                      ·
                        rfl

theorem cell23_5857038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_5857038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857038 prefixEnd_5857038 := by exact prefixLift 5857038
  have htrace : WordTrace (prefixWord ++ tailWord_5857038) baseStart_5857038 baseEnd_5857038 := by
    simpa [prefixWord, tailWord_5857038, baseEnd_5857038] using wordTrace_append hprefix tailTrace_5857038
  have hstable : (prefixWord ++ tailWord_5857038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857038).length < 2 ^ (prefixWord ++ tailWord_5857038).sum := by decide
  have hdescent : baseEnd_5857038 < baseStart_5857038 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857057 : List Nat := [1, 2, 3, 2, 1, 3, 1, 3, 2, 5]
def baseStart_5857057 : Nat := 118140960795 + 5857057 * 2 ^ 59
def prefixEnd_5857057 : Nat := 4983230072969 + 3 ^ 40 * 5857057 * 2
def baseEnd_5857057 : Nat := 1002495153926998657083797

theorem tailTrace_5857057 : CollatzResearch.WordTrace tailWord_5857057 prefixEnd_5857057 1002495153926998657083797 := by
  unfold tailWord_5857057
  simp only [CollatzResearch.WordTrace]
  refine ⟨213624418741890269542305425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142416279161260179694870283 213624418741890269542305425)
  ·
    refine ⟨160218314056417702156729069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213624418741890269542305425 160218314056417702156729069)
    ·
      refine ⟨60081867771156638308773401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160218314056417702156729069 60081867771156638308773401)
      ·
        refine ⟨45061400828367478731580051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60081867771156638308773401 45061400828367478731580051)
        ·
          refine ⟨67592101242551218097370077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45061400828367478731580051 67592101242551218097370077)
          ·
            refine ⟨25347037965956706786513779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67592101242551218097370077 25347037965956706786513779)
            ·
              refine ⟨38020556948935060179770669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25347037965956706786513779 38020556948935060179770669)
              ·
                refine ⟨14257708855850647567414001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38020556948935060179770669 14257708855850647567414001)
                ·
                  refine ⟨10693281641887985675560501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14257708855850647567414001 10693281641887985675560501)
                  ·
                    refine ⟨1002495153926998657083797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10693281641887985675560501 1002495153926998657083797)
                    ·
                      rfl

theorem cell23_5857057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_5857057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857057 prefixEnd_5857057 := by exact prefixLift 5857057
  have htrace : WordTrace (prefixWord ++ tailWord_5857057) baseStart_5857057 baseEnd_5857057 := by
    simpa [prefixWord, tailWord_5857057, baseEnd_5857057] using wordTrace_append hprefix tailTrace_5857057
  have hstable : (prefixWord ++ tailWord_5857057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857057).length < 2 ^ (prefixWord ++ tailWord_5857057).sum := by decide
  have hdescent : baseEnd_5857057 < baseStart_5857057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857078 : List Nat := [5, 1, 2, 2, 1, 1, 4, 2, 5]
def baseStart_5857078 : Nat := 118140960795 + 5857078 * 2 ^ 59
def prefixEnd_5857078 : Nat := 4983230072969 + 3 ^ 40 * 5857078 * 2
def baseEnd_5857078 : Nat := 334166249430526709898755

theorem tailTrace_5857078 : CollatzResearch.WordTrace tailWord_5857078 prefixEnd_5857078 334166249430526709898755 := by
  unfold tailWord_5857078
  simp only [CollatzResearch.WordTrace]
  refine ⟨13351574042175886883051243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142416789783209460085879925 13351574042175886883051243)
  ·
    refine ⟨20027361063263830324576865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13351574042175886883051243 20027361063263830324576865)
    ·
      refine ⟨15020520797447872743432649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20027361063263830324576865 15020520797447872743432649)
      ·
        refine ⟨11265390598085904557574487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15020520797447872743432649 11265390598085904557574487)
        ·
          refine ⟨16898085897128856836361731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11265390598085904557574487 16898085897128856836361731)
          ·
            refine ⟨25347128845693285254542597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16898085897128856836361731 25347128845693285254542597)
            ·
              refine ⟨4752586658567490985226737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25347128845693285254542597 4752586658567490985226737)
              ·
                refine ⟨3564439993925618238920053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4752586658567490985226737 3564439993925618238920053)
                ·
                  refine ⟨334166249430526709898755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3564439993925618238920053 334166249430526709898755)
                  ·
                    rfl

theorem cell23_5857078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_5857078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857078 prefixEnd_5857078 := by exact prefixLift 5857078
  have htrace : WordTrace (prefixWord ++ tailWord_5857078) baseStart_5857078 baseEnd_5857078 := by
    simpa [prefixWord, tailWord_5857078, baseEnd_5857078] using wordTrace_append hprefix tailTrace_5857078
  have hstable : (prefixWord ++ tailWord_5857078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857078).length < 2 ^ (prefixWord ++ tailWord_5857078).sum := by decide
  have hdescent : baseEnd_5857078 < baseStart_5857078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857097 : List Nat := [1, 2, 1, 1, 2, 4, 2, 2, 1, 4, 3]
def baseStart_5857097 : Nat := 118140960795 + 5857097 * 2 ^ 59
def prefixEnd_5857097 : Nat := 4983230072969 + 3 ^ 40 * 5857097 * 2
def baseEnd_5857097 : Nat := 3007506001007175814751207

theorem tailTrace_5857097 : CollatzResearch.WordTrace tailWord_5857097 prefixEnd_5857097 3007506001007175814751207 := by
  unfold tailWord_5857097
  simp only [CollatzResearch.WordTrace]
  refine ⟨213625877661745356373761545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142417251774496904249174363 213625877661745356373761545)
  ·
    refine ⟨160219408246309017280321159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213625877661745356373761545 160219408246309017280321159)
    ·
      refine ⟨240329112369463525920481739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160219408246309017280321159 240329112369463525920481739)
      ·
        refine ⟨360493668554195288880722609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240329112369463525920481739 360493668554195288880722609)
        ·
          refine ⟨270370251415646466660541957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360493668554195288880722609 270370251415646466660541957)
          ·
            refine ⟨50694422140433712498851617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 270370251415646466660541957 50694422140433712498851617)
            ·
              refine ⟨38020816605325284374138713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50694422140433712498851617 38020816605325284374138713)
              ·
                refine ⟨28515612453993963280604035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38020816605325284374138713 28515612453993963280604035)
                ·
                  refine ⟨42773418680990944920906053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28515612453993963280604035 42773418680990944920906053)
                  ·
                    refine ⟨8020016002685802172669885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42773418680990944920906053 8020016002685802172669885)
                    ·
                      refine ⟨3007506001007175814751207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8020016002685802172669885 3007506001007175814751207)
                      ·
                        rfl

theorem cell23_5857097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 4, 3].length) (baseStart_5857097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857097 prefixEnd_5857097 := by exact prefixLift 5857097
  have htrace : WordTrace (prefixWord ++ tailWord_5857097) baseStart_5857097 baseEnd_5857097 := by
    simpa [prefixWord, tailWord_5857097, baseEnd_5857097] using wordTrace_append hprefix tailTrace_5857097
  have hstable : (prefixWord ++ tailWord_5857097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857097).length < 2 ^ (prefixWord ++ tailWord_5857097).sum := by decide
  have hdescent : baseEnd_5857097 < baseStart_5857097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857111 : List Nat := [1, 1, 3, 2, 5, 2, 1, 1, 2, 1, 4]
def baseStart_5857111 : Nat := 118140960795 + 5857111 * 2 ^ 59
def prefixEnd_5857111 : Nat := 4983230072969 + 3 ^ 40 * 5857111 * 2
def baseEnd_5857111 : Nat := 3007513189736338759976143

theorem tailTrace_5857111 : CollatzResearch.WordTrace tailWord_5857111 prefixEnd_5857111 3007513189736338759976143 := by
  unfold tailWord_5857111
  simp only [CollatzResearch.WordTrace]
  refine ⟨213626388283694636764771187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142417592189129757843180791 213626388283694636764771187)
  ·
    refine ⟨320439582425541955147156781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213626388283694636764771187 320439582425541955147156781)
    ·
      refine ⟨120164843409578233180183793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 320439582425541955147156781 120164843409578233180183793)
      ·
        refine ⟨90123632557183674885137845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120164843409578233180183793 90123632557183674885137845)
        ·
          refine ⟨8449090552235969520481673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90123632557183674885137845 8449090552235969520481673)
          ·
            refine ⟨6336817914176977140361255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8449090552235969520481673 6336817914176977140361255)
            ·
              refine ⟨9505226871265465710541883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6336817914176977140361255 9505226871265465710541883)
              ·
                refine ⟨14257840306898198565812825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9505226871265465710541883 14257840306898198565812825)
                ·
                  refine ⟨10693380230173648924359619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14257840306898198565812825 10693380230173648924359619)
                  ·
                    refine ⟨16040070345260473386539429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10693380230173648924359619 16040070345260473386539429)
                    ·
                      refine ⟨3007513189736338759976143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16040070345260473386539429 3007513189736338759976143)
                      ·
                        rfl

theorem cell23_5857111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_5857111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857111 prefixEnd_5857111 := by exact prefixLift 5857111
  have htrace : WordTrace (prefixWord ++ tailWord_5857111) baseStart_5857111 baseEnd_5857111 := by
    simpa [prefixWord, tailWord_5857111, baseEnd_5857111] using wordTrace_append hprefix tailTrace_5857111
  have hstable : (prefixWord ++ tailWord_5857111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857111).length < 2 ^ (prefixWord ++ tailWord_5857111).sum := by decide
  have hdescent : baseEnd_5857111 < baseStart_5857111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857121 : List Nat := [1, 2, 3, 1, 1, 1, 6, 3, 1, 4]
def baseStart_5857121 : Nat := 118140960795 + 5857121 * 2 ^ 59
def prefixEnd_5857121 : Nat := 4983230072969 + 3 ^ 40 * 5857121 * 2
def baseEnd_5857121 : Nat := 1002506108180961240283699

theorem tailTrace_5857121 : CollatzResearch.WordTrace tailWord_5857121 prefixEnd_5857121 1002506108180961240283699 := by
  unfold tailWord_5857121
  simp only [CollatzResearch.WordTrace]
  refine ⟨213626753013658408472635217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142417835342438938981756811 213626753013658408472635217)
  ·
    refine ⟨160220064760243806354476413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213626753013658408472635217 160220064760243806354476413)
    ·
      refine ⟨60082524285091427382928655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160220064760243806354476413 60082524285091427382928655)
      ·
        refine ⟨90123786427637141074392983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60082524285091427382928655 90123786427637141074392983)
        ·
          refine ⟨135185679641455711611589475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90123786427637141074392983 135185679641455711611589475)
          ·
            refine ⟨202778519462183567417384213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135185679641455711611589475 202778519462183567417384213)
            ·
              refine ⟨9505243099789854722689885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 202778519462183567417384213 9505243099789854722689885)
              ·
                refine ⟨3564466162421195521008707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9505243099789854722689885 3564466162421195521008707)
                ·
                  refine ⟨5346699243631793281513061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3564466162421195521008707 5346699243631793281513061)
                  ·
                    refine ⟨1002506108180961240283699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5346699243631793281513061 1002506108180961240283699)
                    ·
                      rfl

theorem cell23_5857121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 3, 1, 4].length) (baseStart_5857121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857121 prefixEnd_5857121 := by exact prefixLift 5857121
  have htrace : WordTrace (prefixWord ++ tailWord_5857121) baseStart_5857121 baseEnd_5857121 := by
    simpa [prefixWord, tailWord_5857121, baseEnd_5857121] using wordTrace_append hprefix tailTrace_5857121
  have hstable : (prefixWord ++ tailWord_5857121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857121).length < 2 ^ (prefixWord ++ tailWord_5857121).sum := by decide
  have hdescent : baseEnd_5857121 < baseStart_5857121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857134 : List Nat := [4, 1, 2, 3, 1, 2, 1, 1, 8]
def baseStart_5857134 : Nat := 118140960795 + 5857134 * 2 ^ 59
def prefixEnd_5857134 : Nat := 4983230072969 + 3 ^ 40 * 5857134 * 2
def baseEnd_5857134 : Nat := 334169444421265796665393

theorem tailTrace_5857134 : CollatzResearch.WordTrace tailWord_5857134 prefixEnd_5857134 334169444421265796665393 := by
  unfold tailWord_5857134
  simp only [CollatzResearch.WordTrace]
  refine ⟨26703403395326413961607307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142418151441740874461905637 26703403395326413961607307)
  ·
    refine ⟨40055105092989620942410961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26703403395326413961607307 40055105092989620942410961)
    ·
      refine ⟨30041328819742215706808221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40055105092989620942410961 30041328819742215706808221)
      ·
        refine ⟨11265498307403330890053083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30041328819742215706808221 11265498307403330890053083)
        ·
          refine ⟨16898247461104996335079625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11265498307403330890053083 16898247461104996335079625)
          ·
            refine ⟨12673685595828747251309719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16898247461104996335079625 12673685595828747251309719)
            ·
              refine ⟨19010528393743120876964579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12673685595828747251309719 19010528393743120876964579)
              ·
                refine ⟨28515792590614681315446869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19010528393743120876964579 28515792590614681315446869)
                ·
                  refine ⟨334169444421265796665393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28515792590614681315446869 334169444421265796665393)
                  ·
                    rfl

theorem cell23_5857134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 8].length) (baseStart_5857134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857134 prefixEnd_5857134 := by exact prefixLift 5857134
  have htrace : WordTrace (prefixWord ++ tailWord_5857134) baseStart_5857134 baseEnd_5857134 := by
    simpa [prefixWord, tailWord_5857134, baseEnd_5857134] using wordTrace_append hprefix tailTrace_5857134
  have hstable : (prefixWord ++ tailWord_5857134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857134).length < 2 ^ (prefixWord ++ tailWord_5857134).sum := by decide
  have hdescent : baseEnd_5857134 < baseStart_5857134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857167 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 4]
def baseStart_5857167 : Nat := 118140960795 + 5857167 * 2 ^ 59
def prefixEnd_5857167 : Nat := 4983230072969 + 3 ^ 40 * 5857167 * 2
def baseEnd_5857167 : Nat := 3007541944652990540875885

theorem tailTrace_5857167 : CollatzResearch.WordTrace tailWord_5857167 prefixEnd_5857167 3007541944652990540875885 := by
  unfold tailWord_5857167
  simp only [CollatzResearch.WordTrace]
  refine ⟨213628430771491758328809755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142418953847661172219206503 213628430771491758328809755)
  ·
    refine ⟨320442646157237637493214633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213628430771491758328809755 320442646157237637493214633)
    ·
      refine ⟨240331984617928228119910975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320442646157237637493214633 240331984617928228119910975)
      ·
        refine ⟨360497976926892342179866463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240331984617928228119910975 360497976926892342179866463)
        ·
          refine ⟨540746965390338513269799695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360497976926892342179866463 540746965390338513269799695)
          ·
            refine ⟨811120448085507769904699543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540746965390338513269799695 811120448085507769904699543)
            ·
              refine ⟨1216680672128261654857049315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 811120448085507769904699543 1216680672128261654857049315)
              ·
                refine ⟨1825021008192392482285573973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1216680672128261654857049315 1825021008192392482285573973)
                ·
                  refine ⟨10693482469877299700892035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1825021008192392482285573973 10693482469877299700892035)
                  ·
                    refine ⟨16040223704815949551338053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10693482469877299700892035 16040223704815949551338053)
                    ·
                      refine ⟨3007541944652990540875885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16040223704815949551338053 3007541944652990540875885)
                      ·
                        rfl

theorem cell23_5857167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 4].length) (baseStart_5857167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857167 prefixEnd_5857167 := by exact prefixLift 5857167
  have htrace : WordTrace (prefixWord ++ tailWord_5857167) baseStart_5857167 baseEnd_5857167 := by
    simpa [prefixWord, tailWord_5857167, baseEnd_5857167] using wordTrace_append hprefix tailTrace_5857167
  have hstable : (prefixWord ++ tailWord_5857167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857167).length < 2 ^ (prefixWord ++ tailWord_5857167).sum := by decide
  have hdescent : baseEnd_5857167 < baseStart_5857167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857177 : List Nat := [1, 2, 1, 2, 1, 3, 2, 4, 1, 6]
def baseStart_5857177 : Nat := 118140960795 + 5857177 * 2 ^ 59
def prefixEnd_5857177 : Nat := 4983230072969 + 3 ^ 40 * 5857177 * 2
def baseEnd_5857177 : Nat := 1002515693153178500583613

theorem tailTrace_5857177 : CollatzResearch.WordTrace tailWord_5857177 prefixEnd_5857177 1002515693153178500583613 := by
  unfold tailWord_5857177
  simp only [CollatzResearch.WordTrace]
  refine ⟨213628795501455530036673785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142419197000970353357782523 213628795501455530036673785)
  ·
    refine ⟨160221596626091647527505339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213628795501455530036673785 160221596626091647527505339)
    ·
      refine ⟨240332394939137471291258009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160221596626091647527505339 240332394939137471291258009)
      ·
        refine ⟨180249296204353103468443507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240332394939137471291258009 180249296204353103468443507)
        ·
          refine ⟨270373944306529655202665261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180249296204353103468443507 270373944306529655202665261)
          ·
            refine ⟨101390229114948620700999473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 270373944306529655202665261 101390229114948620700999473)
            ·
              refine ⟨76042671836211465525749605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101390229114948620700999473 76042671836211465525749605)
              ·
                refine ⟨14258000969289649786078051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76042671836211465525749605 14258000969289649786078051)
                ·
                  refine ⟨21387001453934474679117077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14258000969289649786078051 21387001453934474679117077)
                  ·
                    refine ⟨1002515693153178500583613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21387001453934474679117077 1002515693153178500583613)
                    ·
                      rfl

theorem cell23_5857177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 6].length) (baseStart_5857177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857177 prefixEnd_5857177 := by exact prefixLift 5857177
  have htrace : WordTrace (prefixWord ++ tailWord_5857177) baseStart_5857177 baseEnd_5857177 := by
    simpa [prefixWord, tailWord_5857177, baseEnd_5857177] using wordTrace_append hprefix tailTrace_5857177
  have hstable : (prefixWord ++ tailWord_5857177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857177).length < 2 ^ (prefixWord ++ tailWord_5857177).sum := by decide
  have hdescent : baseEnd_5857177 < baseStart_5857177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857214 : List Nat := [4, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6]
def baseStart_5857214 : Nat := 118140960795 + 5857214 * 2 ^ 59
def prefixEnd_5857214 : Nat := 4983230072969 + 3 ^ 40 * 5857214 * 2
def baseEnd_5857214 : Nat := 3007566078243751856988169

theorem tailTrace_5857214 : CollatzResearch.WordTrace tailWord_5857214 prefixEnd_5857214 3007566078243751856988169 := by
  unfold tailWord_5857214
  simp only [CollatzResearch.WordTrace]
  refine ⟨26703768125290185669471337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142420096668214323570513797 26703768125290185669471337)
  ·
    refine ⟨20027826093967639252103503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26703768125290185669471337 20027826093967639252103503)
    ·
      refine ⟨30041739140951458878155255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20027826093967639252103503 30041739140951458878155255)
      ·
        refine ⟨45062608711427188317232883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30041739140951458878155255 45062608711427188317232883)
        ·
          refine ⟨67593913067140782475849325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45062608711427188317232883 67593913067140782475849325)
          ·
            refine ⟨25347717400177793428443497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67593913067140782475849325 25347717400177793428443497)
            ·
              refine ⟨19010788050133345071332623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25347717400177793428443497 19010788050133345071332623)
              ·
                refine ⟨28516182075200017606998935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19010788050133345071332623 28516182075200017606998935)
                ·
                  refine ⟨42774273112800026410498403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28516182075200017606998935 42774273112800026410498403)
                  ·
                    refine ⟨64161409669200039615747605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42774273112800026410498403 64161409669200039615747605)
                    ·
                      refine ⟨3007566078243751856988169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64161409669200039615747605 3007566078243751856988169)
                      ·
                        rfl

theorem cell23_5857214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_5857214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857214 prefixEnd_5857214 := by exact prefixLift 5857214
  have htrace : WordTrace (prefixWord ++ tailWord_5857214) baseStart_5857214 baseEnd_5857214 := by
    simpa [prefixWord, tailWord_5857214, baseEnd_5857214] using wordTrace_append hprefix tailTrace_5857214
  have hstable : (prefixWord ++ tailWord_5857214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857214).length < 2 ^ (prefixWord ++ tailWord_5857214).sum := by decide
  have hdescent : baseEnd_5857214 < baseStart_5857214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857286 : List Nat := [6, 2, 1, 2, 1, 2, 2, 1, 1, 1, 4]
def baseStart_5857286 : Nat := 118140960795 + 5857286 * 2 ^ 59
def prefixEnd_5857286 : Nat := 4983230072969 + 3 ^ 40 * 5857286 * 2
def baseEnd_5857286 : Nat := 3007603048850875575287839

theorem tailTrace_5857286 : CollatzResearch.WordTrace tailWord_5857286 prefixEnd_5857286 3007603048850875575287839 := by
  unfold tailWord_5857286
  simp only [CollatzResearch.WordTrace]
  refine ⟨6676024095564395051637241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 142421847372040427768261141 6676024095564395051637241)
  ·
    refine ⟨5007018071673296288727931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6676024095564395051637241 5007018071673296288727931)
    ·
      refine ⟨7510527107509944433091897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5007018071673296288727931 7510527107509944433091897)
      ·
        refine ⟨5632895330632458324818923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7510527107509944433091897 5632895330632458324818923)
        ·
          refine ⟨8449342995948687487228385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5632895330632458324818923 8449342995948687487228385)
          ·
            refine ⟨6337007246961515615421289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8449342995948687487228385 6337007246961515615421289)
            ·
              refine ⟨4752755435221136711565967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6337007246961515615421289 4752755435221136711565967)
              ·
                refine ⟨7129133152831705067348951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4752755435221136711565967 7129133152831705067348951)
                ·
                  refine ⟨10693699729247557601023427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7129133152831705067348951 10693699729247557601023427)
                  ·
                    refine ⟨16040549593871336401535141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10693699729247557601023427 16040549593871336401535141)
                    ·
                      refine ⟨3007603048850875575287839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16040549593871336401535141 3007603048850875575287839)
                      ·
                        rfl

theorem cell23_5857286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_5857286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857286 prefixEnd_5857286 := by exact prefixLift 5857286
  have htrace : WordTrace (prefixWord ++ tailWord_5857286) baseStart_5857286 baseEnd_5857286 := by
    simpa [prefixWord, tailWord_5857286, baseEnd_5857286] using wordTrace_append hprefix tailTrace_5857286
  have hstable : (prefixWord ++ tailWord_5857286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857286).length < 2 ^ (prefixWord ++ tailWord_5857286).sum := by decide
  have hdescent : baseEnd_5857286 < baseStart_5857286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857291 : List Nat := [1, 1, 1, 1, 6, 1, 1, 4, 1, 4, 2]
def baseStart_5857291 : Nat := 118140960795 + 5857291 * 2 ^ 59
def prefixEnd_5857291 : Nat := 4983230072969 + 3 ^ 40 * 5857291 * 2
def baseEnd_5857291 : Nat := 3007605616254148055725315

theorem tailTrace_5857291 : CollatzResearch.WordTrace tailWord_5857291 prefixEnd_5857291 3007605616254148055725315 := by
  unfold tailWord_5857291
  simp only [CollatzResearch.WordTrace]
  refine ⟨213632953423042527506323727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142421968948695018337549151 213632953423042527506323727)
  ·
    refine ⟨320449430134563791259485591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213632953423042527506323727 320449430134563791259485591)
    ·
      refine ⟨480674145201845686889228387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320449430134563791259485591 480674145201845686889228387)
      ·
        refine ⟨721011217802768530333842581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480674145201845686889228387 721011217802768530333842581)
        ·
          refine ⟨33797400834504774859398871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 721011217802768530333842581 33797400834504774859398871)
          ·
            refine ⟨50696101251757162289098307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33797400834504774859398871 50696101251757162289098307)
            ·
              refine ⟨76044151877635743433647461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50696101251757162289098307 76044151877635743433647461)
              ·
                refine ⟨14258278477056701893808899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76044151877635743433647461 14258278477056701893808899)
                ·
                  refine ⟨21387417715585052840713349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14258278477056701893808899 21387417715585052840713349)
                  ·
                    refine ⟨4010140821672197407633753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21387417715585052840713349 4010140821672197407633753)
                    ·
                      refine ⟨3007605616254148055725315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4010140821672197407633753 3007605616254148055725315)
                      ·
                        rfl

theorem cell23_5857291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 4, 2].length) (baseStart_5857291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857291 prefixEnd_5857291 := by exact prefixLift 5857291
  have htrace : WordTrace (prefixWord ++ tailWord_5857291) baseStart_5857291 baseEnd_5857291 := by
    simpa [prefixWord, tailWord_5857291, baseEnd_5857291] using wordTrace_append hprefix tailTrace_5857291
  have hstable : (prefixWord ++ tailWord_5857291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857291).length < 2 ^ (prefixWord ++ tailWord_5857291).sum := by decide
  have hdescent : baseEnd_5857291 < baseStart_5857291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857294 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5]
def baseStart_5857294 : Nat := 118140960795 + 5857294 * 2 ^ 59
def prefixEnd_5857294 : Nat := 4983230072969 + 3 ^ 40 * 5857294 * 2
def baseEnd_5857294 : Nat := 3007607156696111543987801

theorem tailTrace_5857294 : CollatzResearch.WordTrace tailWord_5857294 prefixEnd_5857294 3007607156696111543987801 := by
  unfold tailWord_5857294
  simp only [CollatzResearch.WordTrace]
  refine ⟨26704132855253957377335367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142422041894687772679121957 26704132855253957377335367)
  ·
    refine ⟨40056199282880936066003051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26704132855253957377335367 40056199282880936066003051)
    ·
      refine ⟨60084298924321404099004577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40056199282880936066003051 60084298924321404099004577)
      ·
        refine ⟨45063224193241053074253433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60084298924321404099004577 45063224193241053074253433)
        ·
          refine ⟨33797418144930789805690075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45063224193241053074253433 33797418144930789805690075)
          ·
            refine ⟨50696127217396184708535113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33797418144930789805690075 50696127217396184708535113)
            ·
              refine ⟨38022095413047138531401335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50696127217396184708535113 38022095413047138531401335)
              ·
                refine ⟨57033143119570707797102003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38022095413047138531401335 57033143119570707797102003)
                ·
                  refine ⟨85549714679356061695653005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57033143119570707797102003 85549714679356061695653005)
                  ·
                    refine ⟨32081143004758523135869877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85549714679356061695653005 32081143004758523135869877)
                    ·
                      refine ⟨3007607156696111543987801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32081143004758523135869877 3007607156696111543987801)
                      ·
                        rfl

theorem cell23_5857294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_5857294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857294 prefixEnd_5857294 := by exact prefixLift 5857294
  have htrace : WordTrace (prefixWord ++ tailWord_5857294) baseStart_5857294 baseEnd_5857294 := by
    simpa [prefixWord, tailWord_5857294, baseEnd_5857294] using wordTrace_append hprefix tailTrace_5857294
  have hstable : (prefixWord ++ tailWord_5857294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857294).length < 2 ^ (prefixWord ++ tailWord_5857294).sum := by decide
  have hdescent : baseEnd_5857294 < baseStart_5857294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857304 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 4, 2, 4]
def baseStart_5857304 : Nat := 118140960795 + 5857304 * 2 ^ 59
def prefixEnd_5857304 : Nat := 4983230072969 + 3 ^ 40 * 5857304 * 2
def baseEnd_5857304 : Nat := 3007612291502656504862755

theorem tailTrace_5857304 : CollatzResearch.WordTrace tailWord_5857304 prefixEnd_5857304 3007612291502656504862755 := by
  unfold tailWord_5857304
  simp only [CollatzResearch.WordTrace]
  refine ⟨106816713785997715363273483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142422285047996953817697977 106816713785997715363273483)
  ·
    refine ⟨160225070678996573044910225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106816713785997715363273483 160225070678996573044910225)
    ·
      refine ⟨120168803009247429783682669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160225070678996573044910225 120168803009247429783682669)
      ·
        refine ⟨45063301128467786168881001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120168803009247429783682669 45063301128467786168881001)
        ·
          refine ⟨33797475846350839626660751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45063301128467786168881001 33797475846350839626660751)
          ·
            refine ⟨50696213769526259439991127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33797475846350839626660751 50696213769526259439991127)
            ·
              refine ⟨76044320654289389159986691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50696213769526259439991127 76044320654289389159986691)
              ·
                refine ⟨114066480981434083739980037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76044320654289389159986691 114066480981434083739980037)
                ·
                  refine ⟨21387465184018890701246257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114066480981434083739980037 21387465184018890701246257)
                  ·
                    refine ⟨16040598888014168025934693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21387465184018890701246257 16040598888014168025934693)
                    ·
                      refine ⟨3007612291502656504862755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16040598888014168025934693 3007612291502656504862755)
                      ·
                        rfl

theorem cell23_5857304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_5857304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857304 prefixEnd_5857304 := by exact prefixLift 5857304
  have htrace : WordTrace (prefixWord ++ tailWord_5857304) baseStart_5857304 baseEnd_5857304 := by
    simpa [prefixWord, tailWord_5857304, baseEnd_5857304] using wordTrace_append hprefix tailTrace_5857304
  have hstable : (prefixWord ++ tailWord_5857304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857304).length < 2 ^ (prefixWord ++ tailWord_5857304).sum := by decide
  have hdescent : baseEnd_5857304 < baseStart_5857304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857307 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 9]
def baseStart_5857307 : Nat := 118140960795 + 5857307 * 2 ^ 59
def prefixEnd_5857307 : Nat := 4983230072969 + 3 ^ 40 * 5857307 * 2
def baseEnd_5857307 : Nat := 3007613831944619993125241

theorem tailTrace_5857307 : CollatzResearch.WordTrace tailWord_5857307 prefixEnd_5857307 3007613831944619993125241 := by
  unfold tailWord_5857307
  simp only [CollatzResearch.WordTrace]
  refine ⟨213633536990984562238906175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142422357993989708159270783 213633536990984562238906175)
  ·
    refine ⟨320450305486476843358359263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213633536990984562238906175 320450305486476843358359263)
    ·
      refine ⟨480675458229715265037538895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320450305486476843358359263 480675458229715265037538895)
      ·
        refine ⟨721013187344572897556308343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480675458229715265037538895 721013187344572897556308343)
        ·
          refine ⟨1081519781016859346334462515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 721013187344572897556308343 1081519781016859346334462515)
          ·
            refine ⟨1622279671525289019501693773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1081519781016859346334462515 1622279671525289019501693773)
            ·
              refine ⟨608354876821983382313135165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1622279671525289019501693773 608354876821983382313135165)
              ·
                refine ⟨228133078808243768367425687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 608354876821983382313135165 228133078808243768367425687)
                ·
                  refine ⟨342199618212365652551138531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 228133078808243768367425687 342199618212365652551138531)
                  ·
                    refine ⟨513299427318548478826707797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 342199618212365652551138531 513299427318548478826707797)
                    ·
                      refine ⟨3007613831944619993125241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 513299427318548478826707797 3007613831944619993125241)
                      ·
                        rfl

theorem cell23_5857307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 9].length) (baseStart_5857307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857307 prefixEnd_5857307 := by exact prefixLift 5857307
  have htrace : WordTrace (prefixWord ++ tailWord_5857307) baseStart_5857307 baseEnd_5857307 := by
    simpa [prefixWord, tailWord_5857307, baseEnd_5857307] using wordTrace_append hprefix tailTrace_5857307
  have hstable : (prefixWord ++ tailWord_5857307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857307).length < 2 ^ (prefixWord ++ tailWord_5857307).sum := by decide
  have hdescent : baseEnd_5857307 < baseStart_5857307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857324 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 3]
def baseStart_5857324 : Nat := 118140960795 + 5857324 * 2 ^ 59
def prefixEnd_5857324 : Nat := 4983230072969 + 3 ^ 40 * 5857324 * 2
def baseEnd_5857324 : Nat := 3007622561115746426612663

theorem tailTrace_5857324 : CollatzResearch.WordTrace tailWord_5857324 prefixEnd_5857324 3007622561115746426612663 := by
  unfold tailWord_5857324
  simp only [CollatzResearch.WordTrace]
  refine ⟨106817078515961487071137513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142422771354615316094850017 106817078515961487071137513)
  ·
    refine ⟨80112808886971115303353135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106817078515961487071137513 80112808886971115303353135)
    ·
      refine ⟨120169213330456672955029703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80112808886971115303353135 120169213330456672955029703)
      ·
        refine ⟨180253819995685009432544555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120169213330456672955029703 180253819995685009432544555)
        ·
          refine ⟨270380729993527514148816833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180253819995685009432544555 270380729993527514148816833)
          ·
            refine ⟨202785547495145635611612625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270380729993527514148816833 202785547495145635611612625)
            ·
              refine ⟨152089160621359226708709469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202785547495145635611612625 152089160621359226708709469)
              ·
                refine ⟨57033435233009710015766051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152089160621359226708709469 57033435233009710015766051)
                ·
                  refine ⟨85550152849514565023649077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57033435233009710015766051 85550152849514565023649077)
                  ·
                    refine ⟨8020326829641990470967101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85550152849514565023649077 8020326829641990470967101)
                    ·
                      refine ⟨3007622561115746426612663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8020326829641990470967101 3007622561115746426612663)
                      ·
                        rfl

theorem cell23_5857324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 3].length) (baseStart_5857324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857324 prefixEnd_5857324 := by exact prefixLift 5857324
  have htrace : WordTrace (prefixWord ++ tailWord_5857324) baseStart_5857324 baseEnd_5857324 := by
    simpa [prefixWord, tailWord_5857324, baseEnd_5857324] using wordTrace_append hprefix tailTrace_5857324
  have hstable : (prefixWord ++ tailWord_5857324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857324).length < 2 ^ (prefixWord ++ tailWord_5857324).sum := by decide
  have hdescent : baseEnd_5857324 < baseStart_5857324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857344 : List Nat := [2, 1, 1, 2, 2, 4, 2, 1, 1, 7]
def baseStart_5857344 : Nat := 118140960795 + 5857344 * 2 ^ 59
def prefixEnd_5857344 : Nat := 4983230072969 + 3 ^ 40 * 5857344 * 2
def baseEnd_5857344 : Nat := 1002544276909612116120857

theorem tailTrace_5857344 : CollatzResearch.WordTrace tailWord_5857344 prefixEnd_5857344 1002544276909612116120857 := by
  unfold tailWord_5857344
  simp only [CollatzResearch.WordTrace]
  refine ⟨106817443245925258779001543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142423257661233678372002057 106817443245925258779001543)
  ·
    refine ⟨160226164868887888168502315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106817443245925258779001543 160226164868887888168502315)
    ·
      refine ⟨240339247303331832252753473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160226164868887888168502315 240339247303331832252753473)
      ·
        refine ⟨180254435477498874189565105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240339247303331832252753473 180254435477498874189565105)
        ·
          refine ⟨135190826608124155642173829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180254435477498874189565105 135190826608124155642173829)
          ·
            refine ⟨25348279989023279182907593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135190826608124155642173829 25348279989023279182907593)
            ·
              refine ⟨19011209991767459387180695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25348279989023279182907593 19011209991767459387180695)
              ·
                refine ⟨28516814987651189080771043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19011209991767459387180695 28516814987651189080771043)
                ·
                  refine ⟨42775222481476783621156565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28516814987651189080771043 42775222481476783621156565)
                  ·
                    refine ⟨1002544276909612116120857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42775222481476783621156565 1002544276909612116120857)
                    ·
                      rfl

theorem cell23_5857344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 1, 7].length) (baseStart_5857344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857344 prefixEnd_5857344 := by exact prefixLift 5857344
  have htrace : WordTrace (prefixWord ++ tailWord_5857344) baseStart_5857344 baseEnd_5857344 := by
    simpa [prefixWord, tailWord_5857344, baseEnd_5857344] using wordTrace_append hprefix tailTrace_5857344
  have hstable : (prefixWord ++ tailWord_5857344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857344).length < 2 ^ (prefixWord ++ tailWord_5857344).sum := by decide
  have hdescent : baseEnd_5857344 < baseStart_5857344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857354 : List Nat := [3, 1, 2, 1, 1, 2, 1, 4, 1, 2, 5]
def baseStart_5857354 : Nat := 118140960795 + 5857354 * 2 ^ 59
def prefixEnd_5857354 : Nat := 4983230072969 + 3 ^ 40 * 5857354 * 2
def baseEnd_5857354 : Nat := 3007637965535381309237525

theorem tailTrace_5857354 : CollatzResearch.WordTrace tailWord_5857354 prefixEnd_5857354 3007637965535381309237525 := by
  unfold tailWord_5857354
  simp only [CollatzResearch.WordTrace]
  refine ⟨53408812805453572316466779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142423500814542859510578077 53408812805453572316466779)
  ·
    refine ⟨80113219208180358474700169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53408812805453572316466779 80113219208180358474700169)
    ·
      refine ⟨60084914406135268856025127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80113219208180358474700169 60084914406135268856025127)
      ·
        refine ⟨90127371609202903284037691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60084914406135268856025127 90127371609202903284037691)
        ·
          refine ⟨135191057413804354926056537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90127371609202903284037691 135191057413804354926056537)
          ·
            refine ⟨101393293060353266194542403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135191057413804354926056537 101393293060353266194542403)
            ·
              refine ⟨152089939590529899291813605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101393293060353266194542403 152089939590529899291813605)
              ·
                refine ⟨28516863673224356117215051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152089939590529899291813605 28516863673224356117215051)
                ·
                  refine ⟨42775295509836534175822577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28516863673224356117215051 42775295509836534175822577)
                  ·
                    refine ⟨32081471632377400631866933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42775295509836534175822577 32081471632377400631866933)
                    ·
                      refine ⟨3007637965535381309237525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32081471632377400631866933 3007637965535381309237525)
                      ·
                        rfl

theorem cell23_5857354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_5857354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857354 prefixEnd_5857354 := by exact prefixLift 5857354
  have htrace : WordTrace (prefixWord ++ tailWord_5857354) baseStart_5857354 baseEnd_5857354 := by
    simpa [prefixWord, tailWord_5857354, baseEnd_5857354] using wordTrace_append hprefix tailTrace_5857354
  have hstable : (prefixWord ++ tailWord_5857354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857354).length < 2 ^ (prefixWord ++ tailWord_5857354).sum := by decide
  have hdescent : baseEnd_5857354 < baseStart_5857354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857398 : List Nat := [5, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4]
def baseStart_5857398 : Nat := 118140960795 + 5857398 * 2 ^ 59
def prefixEnd_5857398 : Nat := 4983230072969 + 3 ^ 40 * 5857398 * 2
def baseEnd_5857398 : Nat := 3007660558684179137087323

theorem tailTrace_5857398 : CollatzResearch.WordTrace tailWord_5857398 prefixEnd_5857398 3007660558684179137087323 := by
  unfold tailWord_5857398
  simp only [CollatzResearch.WordTrace]
  refine ⟨13352303502103430298779303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142424570689103256520312565 13352303502103430298779303)
  ·
    refine ⟨20028455253155145448168955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13352303502103430298779303 20028455253155145448168955)
    ·
      refine ⟨30042682879732718172253433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20028455253155145448168955 30042682879732718172253433)
      ·
        refine ⟨22532012159799538629190075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30042682879732718172253433 22532012159799538629190075)
        ·
          refine ⟨33798018239699307943785113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22532012159799538629190075 33798018239699307943785113)
          ·
            refine ⟨25348513679774480957838835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33798018239699307943785113 25348513679774480957838835)
            ·
              refine ⟨38022770519661721436758253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25348513679774480957838835 38022770519661721436758253)
              ·
                refine ⟨14258538944873145538784345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38022770519661721436758253 14258538944873145538784345)
                ·
                  refine ⟨10693904208654859154088259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14258538944873145538784345 10693904208654859154088259)
                  ·
                    refine ⟨16040856312982288731132389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10693904208654859154088259 16040856312982288731132389)
                    ·
                      refine ⟨3007660558684179137087323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16040856312982288731132389 3007660558684179137087323)
                      ·
                        rfl

theorem cell23_5857398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_5857398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857398 prefixEnd_5857398 := by exact prefixLift 5857398
  have htrace : WordTrace (prefixWord ++ tailWord_5857398) baseStart_5857398 baseEnd_5857398 := by
    simpa [prefixWord, tailWord_5857398, baseEnd_5857398] using wordTrace_append hprefix tailTrace_5857398
  have hstable : (prefixWord ++ tailWord_5857398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857398).length < 2 ^ (prefixWord ++ tailWord_5857398).sum := by decide
  have hdescent : baseEnd_5857398 < baseStart_5857398 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857408 : List Nat := [2, 1, 1, 2, 1, 3, 1, 7, 1, 4]
def baseStart_5857408 : Nat := 118140960795 + 5857408 * 2 ^ 59
def prefixEnd_5857408 : Nat := 4983230072969 + 3 ^ 40 * 5857408 * 2
def baseEnd_5857408 : Nat := 1002555231163574699320759

theorem tailTrace_5857408 : CollatzResearch.WordTrace tailWord_5857408 prefixEnd_5857408 1002555231163574699320759 := by
  unfold tailWord_5857408
  simp only [CollatzResearch.WordTrace]
  refine ⟨106818610381809328244166439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142424813842412437658888585 106818610381809328244166439)
  ·
    refine ⟨160227915572713992366249659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106818610381809328244166439 160227915572713992366249659)
    ·
      refine ⟨240341873359070988549374489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160227915572713992366249659 240341873359070988549374489)
      ·
        refine ⟨180256405019303241412030867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240341873359070988549374489 180256405019303241412030867)
        ·
          refine ⟨270384607528954862118046301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180256405019303241412030867 270384607528954862118046301)
          ·
            refine ⟨101394227823358073294267363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 270384607528954862118046301 101394227823358073294267363)
            ·
              refine ⟨152091341735037109941401045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101394227823358073294267363 152091341735037109941401045)
              ·
                refine ⟨3564640821914932264251587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 152091341735037109941401045 3564640821914932264251587)
                ·
                  refine ⟨5346961232872398396377381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3564640821914932264251587 5346961232872398396377381)
                  ·
                    refine ⟨1002555231163574699320759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5346961232872398396377381 1002555231163574699320759)
                    ·
                      rfl

theorem cell23_5857408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 7, 1, 4].length) (baseStart_5857408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857408 prefixEnd_5857408 := by exact prefixLift 5857408
  have htrace : WordTrace (prefixWord ++ tailWord_5857408) baseStart_5857408 baseEnd_5857408 := by
    simpa [prefixWord, tailWord_5857408, baseEnd_5857408] using wordTrace_append hprefix tailTrace_5857408
  have hstable : (prefixWord ++ tailWord_5857408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857408).length < 2 ^ (prefixWord ++ tailWord_5857408).sum := by decide
  have hdescent : baseEnd_5857408 < baseStart_5857408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857418 : List Nat := [3, 1, 2, 3, 1, 2, 2, 2, 2, 2, 3]
def baseStart_5857418 : Nat := 118140960795 + 5857418 * 2 ^ 59
def prefixEnd_5857418 : Nat := 4983230072969 + 3 ^ 40 * 5857418 * 2
def baseEnd_5857418 : Nat := 3007670828297269058837231

theorem tailTrace_5857418 : CollatzResearch.WordTrace tailWord_5857418 prefixEnd_5857418 3007670828297269058837231 := by
  unfold tailWord_5857418
  simp only [CollatzResearch.WordTrace]
  refine ⟨53409396373395607049049227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142425056995721618797464605 53409396373395607049049227)
  ·
    refine ⟨80114094560093410573573841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53409396373395607049049227 80114094560093410573573841)
    ·
      refine ⟨60085570920070057930180381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80114094560093410573573841 60085570920070057930180381)
      ·
        refine ⟨22532089095026271723817643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60085570920070057930180381 22532089095026271723817643)
        ·
          refine ⟨33798133642539407585726465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22532089095026271723817643 33798133642539407585726465)
          ·
            refine ⟨25348600231904555689294849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33798133642539407585726465 25348600231904555689294849)
            ·
              refine ⟨19011450173928416766971137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25348600231904555689294849 19011450173928416766971137)
              ·
                refine ⟨14258587630446312575228353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19011450173928416766971137 14258587630446312575228353)
                ·
                  refine ⟨10693940722834734431421265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14258587630446312575228353 10693940722834734431421265)
                  ·
                    refine ⟨8020455542126050823565949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10693940722834734431421265 8020455542126050823565949)
                    ·
                      refine ⟨3007670828297269058837231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8020455542126050823565949 3007670828297269058837231)
                      ·
                        rfl

theorem cell23_5857418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_5857418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857418 prefixEnd_5857418 := by exact prefixLift 5857418
  have htrace : WordTrace (prefixWord ++ tailWord_5857418) baseStart_5857418 baseEnd_5857418 := by
    simpa [prefixWord, tailWord_5857418, baseEnd_5857418] using wordTrace_append hprefix tailTrace_5857418
  have hstable : (prefixWord ++ tailWord_5857418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857418).length < 2 ^ (prefixWord ++ tailWord_5857418).sum := by decide
  have hdescent : baseEnd_5857418 < baseStart_5857418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857424 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 6]
def baseStart_5857424 : Nat := 118140960795 + 5857424 * 2 ^ 59
def prefixEnd_5857424 : Nat := 4983230072969 + 3 ^ 40 * 5857424 * 2
def baseEnd_5857424 : Nat := 3007673909181196035362203

theorem tailTrace_5857424 : CollatzResearch.WordTrace tailWord_5857424 prefixEnd_5857424 3007673909181196035362203 := by
  unfold tailWord_5857424
  simp only [CollatzResearch.WordTrace]
  refine ⟨106818902165780345610457663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142425202887707127480610217 106818902165780345610457663)
  ·
    refine ⟨160228353248670518415686495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106818902165780345610457663 160228353248670518415686495)
    ·
      refine ⟨240342529873005777623529743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160228353248670518415686495 240342529873005777623529743)
      ·
        refine ⟨360513794809508666435294615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240342529873005777623529743 360513794809508666435294615)
        ·
          refine ⟨540770692214262999652941923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360513794809508666435294615 540770692214262999652941923)
          ·
            refine ⟨811156038321394499479412885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540770692214262999652941923 811156038321394499479412885)
            ·
              refine ⟨38022939296315367163097479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 811156038321394499479412885 38022939296315367163097479)
              ·
                refine ⟨57034408944473050744646219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38022939296315367163097479 57034408944473050744646219)
                ·
                  refine ⟨85551613416709576116969329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57034408944473050744646219 85551613416709576116969329)
                  ·
                    refine ⟨64163710062532182087726997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 85551613416709576116969329 64163710062532182087726997)
                    ·
                      refine ⟨3007673909181196035362203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64163710062532182087726997 3007673909181196035362203)
                      ·
                        rfl

theorem cell23_5857424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 6].length) (baseStart_5857424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857424 prefixEnd_5857424 := by exact prefixLift 5857424
  have htrace : WordTrace (prefixWord ++ tailWord_5857424) baseStart_5857424 baseEnd_5857424 := by
    simpa [prefixWord, tailWord_5857424, baseEnd_5857424] using wordTrace_append hprefix tailTrace_5857424
  have hstable : (prefixWord ++ tailWord_5857424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857424).length < 2 ^ (prefixWord ++ tailWord_5857424).sum := by decide
  have hdescent : baseEnd_5857424 < baseStart_5857424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857458 : List Nat := [3, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2]
def baseStart_5857458 : Nat := 118140960795 + 5857458 * 2 ^ 59
def prefixEnd_5857458 : Nat := 4983230072969 + 3 ^ 40 * 5857458 * 2
def baseEnd_5857458 : Nat := 3007691367523448902337047

theorem tailTrace_5857458 : CollatzResearch.WordTrace tailWord_5857458 prefixEnd_5857458 3007691367523448902337047 := by
  unfold tailWord_5857458
  simp only [CollatzResearch.WordTrace]
  refine ⟨53409761103359378756913257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142426029608958343351768685 53409761103359378756913257)
  ·
    refine ⟨40057320827519534067684943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53409761103359378756913257 40057320827519534067684943)
    ·
      refine ⟨60085981241279301101527415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40057320827519534067684943 60085981241279301101527415)
      ·
        refine ⟨90128971861918951652291123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60085981241279301101527415 90128971861918951652291123)
        ·
          refine ⟨135193457792878427478436685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90128971861918951652291123 135193457792878427478436685)
          ·
            refine ⟨50697546672329410304413757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135193457792878427478436685 50697546672329410304413757)
            ·
              refine ⟨19011580002123528864155159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50697546672329410304413757 19011580002123528864155159)
              ·
                refine ⟨28517370003185293296232739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19011580002123528864155159 28517370003185293296232739)
                ·
                  refine ⟨42776055004777939944349109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28517370003185293296232739 42776055004777939944349109)
                  ·
                    refine ⟨4010255156697931869782729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42776055004777939944349109 4010255156697931869782729)
                    ·
                      refine ⟨3007691367523448902337047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4010255156697931869782729 3007691367523448902337047)
                      ·
                        rfl

theorem cell23_5857458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2].length) (baseStart_5857458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857458 prefixEnd_5857458 := by exact prefixLift 5857458
  have htrace : WordTrace (prefixWord ++ tailWord_5857458) baseStart_5857458 baseEnd_5857458 := by
    simpa [prefixWord, tailWord_5857458, baseEnd_5857458] using wordTrace_append hprefix tailTrace_5857458
  have hstable : (prefixWord ++ tailWord_5857458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857458).length < 2 ^ (prefixWord ++ tailWord_5857458).sum := by decide
  have hdescent : baseEnd_5857458 < baseStart_5857458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857498 : List Nat := [3, 1, 1, 2, 2, 1, 2, 5, 2, 4]
def baseStart_5857498 : Nat := 118140960795 + 5857498 * 2 ^ 59
def prefixEnd_5857498 : Nat := 4983230072969 + 3 ^ 40 * 5857498 * 2
def baseEnd_5857498 : Nat := 1002570635583209581945621

theorem tailTrace_5857498 : CollatzResearch.WordTrace tailWord_5857498 prefixEnd_5857498 1002570635583209581945621 := by
  unfold tailWord_5857498
  simp only [CollatzResearch.WordTrace]
  refine ⟨53410125833323150464777287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142427002222195067906072765 53410125833323150464777287)
  ·
    refine ⟨80115188749984725697165931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53410125833323150464777287 80115188749984725697165931)
    ·
      refine ⟨120172783124977088545748897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80115188749984725697165931 120172783124977088545748897)
      ·
        refine ⟨90129587343732816409311673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120172783124977088545748897 90129587343732816409311673)
        ·
          refine ⟨67597190507799612306983755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90129587343732816409311673 67597190507799612306983755)
          ·
            refine ⟨101395785761699418460475633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67597190507799612306983755 101395785761699418460475633)
            ·
              refine ⟨76046839321274563845356725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101395785761699418460475633 76046839321274563845356725)
              ·
                refine ⟨7129391186369490360502193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76046839321274563845356725 7129391186369490360502193)
                ·
                  refine ⟨5347043389777117770376645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7129391186369490360502193 5347043389777117770376645)
                  ·
                    refine ⟨1002570635583209581945621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5347043389777117770376645 1002570635583209581945621)
                    ·
                      rfl

theorem cell23_5857498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 2, 4].length) (baseStart_5857498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857498 prefixEnd_5857498 := by exact prefixLift 5857498
  have htrace : WordTrace (prefixWord ++ tailWord_5857498) baseStart_5857498 baseEnd_5857498 := by
    simpa [prefixWord, tailWord_5857498, baseEnd_5857498] using wordTrace_append hprefix tailTrace_5857498
  have hstable : (prefixWord ++ tailWord_5857498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857498).length < 2 ^ (prefixWord ++ tailWord_5857498).sum := by decide
  have hdescent : baseEnd_5857498 < baseStart_5857498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857505 : List Nat := [1, 2, 3, 1, 3, 1, 1, 4, 3, 2, 2]
def baseStart_5857505 : Nat := 118140960795 + 5857505 * 2 ^ 59
def prefixEnd_5857505 : Nat := 4983230072969 + 3 ^ 40 * 5857505 * 2
def baseEnd_5857505 : Nat := 3007715501114210218449331

theorem tailTrace_5857505 : CollatzResearch.WordTrace tailWord_5857505 prefixEnd_5857505 3007715501114210218449331 := by
  unfold tailWord_5857505
  simp only [CollatzResearch.WordTrace]
  refine ⟨213640758644267242054613969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142427172429511494703075979 213640758644267242054613969)
  ·
    refine ⟨160230568983200431540960477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213640758644267242054613969 160230568983200431540960477)
    ·
      refine ⟨60086463368700161827860179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160230568983200431540960477 60086463368700161827860179)
      ·
        refine ⟨90129695053050242741790269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60086463368700161827860179 90129695053050242741790269)
        ·
          refine ⟨33798635644893841028171351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90129695053050242741790269 33798635644893841028171351)
          ·
            refine ⟨50697953467340761542257027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33798635644893841028171351 50697953467340761542257027)
            ·
              refine ⟨76046930201011142313385541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50697953467340761542257027 76046930201011142313385541)
              ·
                refine ⟨14258799412689589183759789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76046930201011142313385541 14258799412689589183759789)
                ·
                  refine ⟨5347049779758595943909921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14258799412689589183759789 5347049779758595943909921)
                  ·
                    refine ⟨4010287334818946957932441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5347049779758595943909921 4010287334818946957932441)
                    ·
                      refine ⟨3007715501114210218449331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4010287334818946957932441 3007715501114210218449331)
                      ·
                        rfl

theorem cell23_5857505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 3, 2, 2].length) (baseStart_5857505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857505 prefixEnd_5857505 := by exact prefixLift 5857505
  have htrace : WordTrace (prefixWord ++ tailWord_5857505) baseStart_5857505 baseEnd_5857505 := by
    simpa [prefixWord, tailWord_5857505, baseEnd_5857505] using wordTrace_append hprefix tailTrace_5857505
  have hstable : (prefixWord ++ tailWord_5857505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857505).length < 2 ^ (prefixWord ++ tailWord_5857505).sum := by decide
  have hdescent : baseEnd_5857505 < baseStart_5857505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857539 : List Nat := [1, 1, 1, 3, 2, 3, 5, 2, 1, 2, 2]
def baseStart_5857539 : Nat := 118140960795 + 5857539 * 2 ^ 59
def prefixEnd_5857539 : Nat := 4983230072969 + 3 ^ 40 * 5857539 * 2
def baseEnd_5857539 : Nat := 3007732959456463085424175

theorem tailTrace_5857539 : CollatzResearch.WordTrace tailWord_5857539 prefixEnd_5857539 3007732959456463085424175 := by
  unfold tailWord_5857539
  simp only [CollatzResearch.WordTrace]
  refine ⟨213641998726144065861351671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142427999150762710574234447 213641998726144065861351671)
  ·
    refine ⟨320462998089216098792027507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213641998726144065861351671 320462998089216098792027507)
    ·
      refine ⟨480694497133824148188041261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320462998089216098792027507 480694497133824148188041261)
      ·
        refine ⟨180260436425184055570515473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 480694497133824148188041261 180260436425184055570515473)
        ·
          refine ⟨135195327318888041677886605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180260436425184055570515473 135195327318888041677886605)
          ·
            refine ⟨50698247744583015629207477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135195327318888041677886605 50698247744583015629207477)
            ·
              refine ⟨4752960726054657715238201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50698247744583015629207477 4752960726054657715238201)
              ·
                refine ⟨3564720544540993286428651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4752960726054657715238201 3564720544540993286428651)
                ·
                  refine ⟨5347080816811489929642977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3564720544540993286428651 5347080816811489929642977)
                  ·
                    refine ⟨4010310612608617447232233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5347080816811489929642977 4010310612608617447232233)
                    ·
                      refine ⟨3007732959456463085424175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4010310612608617447232233 3007732959456463085424175)
                      ·
                        rfl

theorem cell23_5857539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 2, 1, 2, 2].length) (baseStart_5857539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857539 prefixEnd_5857539 := by exact prefixLift 5857539
  have htrace : WordTrace (prefixWord ++ tailWord_5857539) baseStart_5857539 baseEnd_5857539 := by
    simpa [prefixWord, tailWord_5857539, baseEnd_5857539] using wordTrace_append hprefix tailTrace_5857539
  have hstable : (prefixWord ++ tailWord_5857539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857539).length < 2 ^ (prefixWord ++ tailWord_5857539).sum := by decide
  have hdescent : baseEnd_5857539 < baseStart_5857539 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857591 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 4]
def baseStart_5857591 : Nat := 118140960795 + 5857591 * 2 ^ 59
def prefixEnd_5857591 : Nat := 4983230072969 + 3 ^ 40 * 5857591 * 2
def baseEnd_5857591 : Nat := 3007759660450496881973935

theorem tailTrace_5857591 : CollatzResearch.WordTrace tailWord_5857591 prefixEnd_5857591 3007759660450496881973935 := by
  unfold tailWord_5857591
  simp only [CollatzResearch.WordTrace]
  refine ⟨213643895321955678742244627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142429263547970452494829751 213643895321955678742244627)
  ·
    refine ⟨320465842982933518113366941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213643895321955678742244627 320465842982933518113366941)
    ·
      refine ⟨120174691118600069292512603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 320465842982933518113366941 120174691118600069292512603)
      ·
        refine ⟨180262036677900103938768905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120174691118600069292512603 180262036677900103938768905)
        ·
          refine ⟨135196527508425077954076679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180262036677900103938768905 135196527508425077954076679)
          ·
            refine ⟨202794791262637616931115019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135196527508425077954076679 202794791262637616931115019)
            ·
              refine ⟨304192186893956425396672529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202794791262637616931115019 304192186893956425396672529)
              ·
                refine ⟨228144140170467319047504397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304192186893956425396672529 228144140170467319047504397)
                ·
                  refine ⟨85554052563925244642814149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 228144140170467319047504397 85554052563925244642814149)
                  ·
                    refine ⟨16041384855735983370527653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85554052563925244642814149 16041384855735983370527653)
                    ·
                      refine ⟨3007759660450496881973935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16041384855735983370527653 3007759660450496881973935)
                      ·
                        rfl

theorem cell23_5857591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_5857591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857591 prefixEnd_5857591 := by exact prefixLift 5857591
  have htrace : WordTrace (prefixWord ++ tailWord_5857591) baseStart_5857591 baseEnd_5857591 := by
    simpa [prefixWord, tailWord_5857591, baseEnd_5857591] using wordTrace_append hprefix tailTrace_5857591
  have hstable : (prefixWord ++ tailWord_5857591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857591).length < 2 ^ (prefixWord ++ tailWord_5857591).sum := by decide
  have hdescent : baseEnd_5857591 < baseStart_5857591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857612 : List Nat := [2, 2, 1, 3, 2, 1, 1, 5, 2, 2, 2]
def baseStart_5857612 : Nat := 118140960795 + 5857612 * 2 ^ 59
def prefixEnd_5857612 : Nat := 4983230072969 + 3 ^ 40 * 5857612 * 2
def baseEnd_5857612 : Nat := 3007770443544241299811339

theorem tailTrace_5857612 : CollatzResearch.WordTrace tailWord_5857612 prefixEnd_5857612 3007770443544241299811339 := by
  unfold tailWord_5857612
  simp only [CollatzResearch.WordTrace]
  refine ⟨106822330627439799664379545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142429774169919732885839393 106822330627439799664379545)
  ·
    refine ⟨80116747970579849748284659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106822330627439799664379545 80116747970579849748284659)
    ·
      refine ⟨120175121955869774622426989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80116747970579849748284659 120175121955869774622426989)
      ·
        refine ⟨45065670733451165483410121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120175121955869774622426989 45065670733451165483410121)
        ·
          refine ⟨33799253050088374112557591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45065670733451165483410121 33799253050088374112557591)
          ·
            refine ⟨50698879575132561168836387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33799253050088374112557591 50698879575132561168836387)
            ·
              refine ⟨76048319362698841753254581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50698879575132561168836387 76048319362698841753254581)
              ·
                refine ⟨7129529940253016414367617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76048319362698841753254581 7129529940253016414367617)
                ·
                  refine ⟨5347147455189762310775713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7129529940253016414367617 5347147455189762310775713)
                  ·
                    refine ⟨4010360591392321733081785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5347147455189762310775713 4010360591392321733081785)
                    ·
                      refine ⟨3007770443544241299811339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4010360591392321733081785 3007770443544241299811339)
                      ·
                        rfl

theorem cell23_5857612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_5857612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857612 prefixEnd_5857612 := by exact prefixLift 5857612
  have htrace : WordTrace (prefixWord ++ tailWord_5857612) baseStart_5857612 baseEnd_5857612 := by
    simpa [prefixWord, tailWord_5857612, baseEnd_5857612] using wordTrace_append hprefix tailTrace_5857612
  have hstable : (prefixWord ++ tailWord_5857612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857612).length < 2 ^ (prefixWord ++ tailWord_5857612).sum := by decide
  have hdescent : baseEnd_5857612 < baseStart_5857612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857635 : List Nat := [1, 1, 1, 5, 2, 1, 4, 3, 5]
def baseStart_5857635 : Nat := 118140960795 + 5857635 * 2 ^ 59
def prefixEnd_5857635 : Nat := 4983230072969 + 3 ^ 40 * 5857635 * 2
def baseEnd_5857635 : Nat := 334198028177699412202637

theorem tailTrace_5857635 : CollatzResearch.WordTrace tailWord_5857635 prefixEnd_5857635 334198028177699412202637 := by
  unfold tailWord_5857635
  simp only [CollatzResearch.WordTrace]
  refine ⟨213645500133796274256846359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142430333422530849504564239 213645500133796274256846359)
  ·
    refine ⟨320468250200694411385269539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213645500133796274256846359 320468250200694411385269539)
    ·
      refine ⟨480702375301041617077904309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320468250200694411385269539 480702375301041617077904309)
      ·
        refine ⟨45065847684472651601053529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 480702375301041617077904309 45065847684472651601053529)
        ·
          refine ⟨33799385763354488700790147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45065847684472651601053529 33799385763354488700790147)
          ·
            refine ⟨50699078645031733051185221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33799385763354488700790147 50699078645031733051185221)
            ·
              refine ⟨9506077245943449947097229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50699078645031733051185221 9506077245943449947097229)
              ·
                refine ⟨3564778967228793730161461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9506077245943449947097229 3564778967228793730161461)
                ·
                  refine ⟨334198028177699412202637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3564778967228793730161461 334198028177699412202637)
                  ·
                    rfl

theorem cell23_5857635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 3, 5].length) (baseStart_5857635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857635 prefixEnd_5857635 := by exact prefixLift 5857635
  have htrace : WordTrace (prefixWord ++ tailWord_5857635) baseStart_5857635 baseEnd_5857635 := by
    simpa [prefixWord, tailWord_5857635, baseEnd_5857635] using wordTrace_append hprefix tailTrace_5857635
  have hstable : (prefixWord ++ tailWord_5857635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857635).length < 2 ^ (prefixWord ++ tailWord_5857635).sum := by decide
  have hdescent : baseEnd_5857635 < baseStart_5857635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857668 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 3, 3, 4]
def baseStart_5857668 : Nat := 118140960795 + 5857668 * 2 ^ 59
def prefixEnd_5857668 : Nat := 4983230072969 + 3 ^ 40 * 5857668 * 2
def baseEnd_5857668 : Nat := 3007799198460893080711081

theorem tailTrace_5857668 : CollatzResearch.WordTrace tailWord_5857668 prefixEnd_5857668 3007799198460893080711081 := by
  unfold tailWord_5857668
  simp only [CollatzResearch.WordTrace]
  refine ⟨106823351871338360446398829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142431135828451147261865105 106823351871338360446398829)
  ·
    refine ⟨40058756951751885167399561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106823351871338360446398829 40058756951751885167399561)
    ·
      refine ⟨30044067713813913875549671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40058756951751885167399561 30044067713813913875549671)
      ·
        refine ⟨45066101570720870813324507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30044067713813913875549671 45066101570720870813324507)
        ·
          refine ⟨67599152356081306219986761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45066101570720870813324507 67599152356081306219986761)
          ·
            refine ⟨50699364267060979664990071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67599152356081306219986761 50699364267060979664990071)
            ·
              refine ⟨76049046400591469497485107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50699364267060979664990071 76049046400591469497485107)
              ·
                refine ⟨114073569600887204246227661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76049046400591469497485107 114073569600887204246227661)
                ·
                  refine ⟨42777588600332701592335373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114073569600887204246227661 42777588600332701592335373)
                  ·
                    refine ⟨16041595725124763097125765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42777588600332701592335373 16041595725124763097125765)
                    ·
                      refine ⟨3007799198460893080711081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16041595725124763097125765 3007799198460893080711081)
                      ·
                        rfl

theorem cell23_5857668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_5857668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857668 prefixEnd_5857668 := by exact prefixLift 5857668
  have htrace : WordTrace (prefixWord ++ tailWord_5857668) baseStart_5857668 baseEnd_5857668 := by
    simpa [prefixWord, tailWord_5857668, baseEnd_5857668] using wordTrace_append hprefix tailTrace_5857668
  have hstable : (prefixWord ++ tailWord_5857668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857668).length < 2 ^ (prefixWord ++ tailWord_5857668).sum := by decide
  have hdescent : baseEnd_5857668 < baseStart_5857668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857708 : List Nat := [2, 2, 1, 1, 1, 1, 3, 6, 6]
def baseStart_5857708 : Nat := 118140960795 + 5857708 * 2 ^ 59
def prefixEnd_5857708 : Nat := 4983230072969 + 3 ^ 40 * 5857708 * 2
def baseEnd_5857708 : Nat := 334202193076341436023433

theorem tailTrace_5857708 : CollatzResearch.WordTrace tailWord_5857708 prefixEnd_5857708 334202193076341436023433 := by
  unfold tailWord_5857708
  simp only [CollatzResearch.WordTrace]
  refine ⟨106824081331265903862126889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142432108441687871816169185 106824081331265903862126889)
  ·
    refine ⟨80118060998449427896595167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106824081331265903862126889 80118060998449427896595167)
    ·
      refine ⟨120177091497674141844892751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80118060998449427896595167 120177091497674141844892751)
      ·
        refine ⟨180265637246511212767339127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120177091497674141844892751 180265637246511212767339127)
        ·
          refine ⟨270398455869766819151008691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180265637246511212767339127 270398455869766819151008691)
          ·
            refine ⟨405597683804650228726513037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270398455869766819151008691 405597683804650228726513037)
            ·
              refine ⟨152099131426743835772442389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 405597683804650228726513037 152099131426743835772442389)
              ·
                refine ⟨7129646785628617301833237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 152099131426743835772442389 7129646785628617301833237)
                ·
                  refine ⟨334202193076341436023433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7129646785628617301833237 334202193076341436023433)
                  ·
                    rfl

theorem cell23_5857708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 6].length) (baseStart_5857708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857708 prefixEnd_5857708 := by exact prefixLift 5857708
  have htrace : WordTrace (prefixWord ++ tailWord_5857708) baseStart_5857708 baseEnd_5857708 := by
    simpa [prefixWord, tailWord_5857708, baseEnd_5857708] using wordTrace_append hprefix tailTrace_5857708
  have hstable : (prefixWord ++ tailWord_5857708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857708).length < 2 ^ (prefixWord ++ tailWord_5857708).sum := by decide
  have hdescent : baseEnd_5857708 < baseStart_5857708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857725 : List Nat := [1, 4, 1, 2, 2, 3, 1, 3, 6]
def baseStart_5857725 : Nat := 118140960795 + 5857725 * 2 ^ 59
def prefixEnd_5857725 : Nat := 4983230072969 + 3 ^ 40 * 5857725 * 2
def baseEnd_5857725 : Nat := 334203162984244373077591

theorem tailTrace_5857725 : CollatzResearch.WordTrace tailWord_5857725 prefixEnd_5857725 334203162984244373077591 := by
  unfold tailWord_5857725
  simp only [CollatzResearch.WordTrace]
  refine ⟨213648782703470219627622629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142432521802313479751748419 213648782703470219627622629)
  ·
    refine ⟨40059146756900666180179243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213648782703470219627622629 40059146756900666180179243)
    ·
      refine ⟨60088720135350999270268865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40059146756900666180179243 60088720135350999270268865)
      ·
        refine ⟨45066540101513249452701649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60088720135350999270268865 45066540101513249452701649)
        ·
          refine ⟨33799905076134937089526237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45066540101513249452701649 33799905076134937089526237)
          ·
            refine ⟨12674964403550601408572339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33799905076134937089526237 12674964403550601408572339)
            ·
              refine ⟨19012446605325902112858509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12674964403550601408572339 19012446605325902112858509)
              ·
                refine ⟨7129667476997213292321941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19012446605325902112858509 7129667476997213292321941)
                ·
                  refine ⟨334203162984244373077591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7129667476997213292321941 334203162984244373077591)
                  ·
                    rfl

theorem cell23_5857725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 6].length) (baseStart_5857725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857725 prefixEnd_5857725 := by exact prefixLift 5857725
  have htrace : WordTrace (prefixWord ++ tailWord_5857725) baseStart_5857725 baseEnd_5857725 := by
    simpa [prefixWord, tailWord_5857725, baseEnd_5857725] using wordTrace_append hprefix tailTrace_5857725
  have hstable : (prefixWord ++ tailWord_5857725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857725).length < 2 ^ (prefixWord ++ tailWord_5857725).sum := by decide
  have hdescent : baseEnd_5857725 < baseStart_5857725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857745 : List Nat := [1, 2, 2, 1, 2, 1, 1, 5, 1, 5, 2]
def baseStart_5857745 : Nat := 118140960795 + 5857745 * 2 ^ 59
def prefixEnd_5857745 : Nat := 4983230072969 + 3 ^ 40 * 5857745 * 2
def baseEnd_5857745 : Nat := 3007838736471289279448227

theorem tailTrace_5857745 : CollatzResearch.WordTrace tailWord_5857745 prefixEnd_5857745 3007838736471289279448227 := by
  unfold tailWord_5857745
  simp only [CollatzResearch.WordTrace]
  refine ⟨213649512163397763043350689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142433008108931842028900459 213649512163397763043350689)
  ·
    refine ⟨160237134122548322282513017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213649512163397763043350689 160237134122548322282513017)
    ·
      refine ⟨120177850591911241711884763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160237134122548322282513017 120177850591911241711884763)
      ·
        refine ⟨180266775887866862567827145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120177850591911241711884763 180266775887866862567827145)
        ·
          refine ⟨135200081915900146925870359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180266775887866862567827145 135200081915900146925870359)
          ·
            refine ⟨202800122873850220388805539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135200081915900146925870359 202800122873850220388805539)
            ·
              refine ⟨304200184310775330583208309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202800122873850220388805539 304200184310775330583208309)
              ·
                refine ⟨28518767279135187242175779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 304200184310775330583208309 28518767279135187242175779)
                ·
                  refine ⟨42778150918702780863263669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28518767279135187242175779 42778150918702780863263669)
                  ·
                    refine ⟨4010451648628385705930969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42778150918702780863263669 4010451648628385705930969)
                    ·
                      refine ⟨3007838736471289279448227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4010451648628385705930969 3007838736471289279448227)
                      ·
                        rfl

theorem cell23_5857745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 5, 2].length) (baseStart_5857745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857745 prefixEnd_5857745 := by exact prefixLift 5857745
  have htrace : WordTrace (prefixWord ++ tailWord_5857745) baseStart_5857745 baseEnd_5857745 := by
    simpa [prefixWord, tailWord_5857745, baseEnd_5857745] using wordTrace_append hprefix tailTrace_5857745
  have hstable : (prefixWord ++ tailWord_5857745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857745).length < 2 ^ (prefixWord ++ tailWord_5857745).sum := by decide
  have hdescent : baseEnd_5857745 < baseStart_5857745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857763 : List Nat := [1, 1, 1, 6, 4, 1, 2, 2, 1, 4]
def baseStart_5857763 : Nat := 118140960795 + 5857763 * 2 ^ 59
def prefixEnd_5857763 : Nat := 4983230072969 + 3 ^ 40 * 5857763 * 2
def baseEnd_5857763 : Nat := 1002615993041023403007715

theorem tailTrace_5857763 : CollatzResearch.WordTrace tailWord_5857763 prefixEnd_5857763 1002615993041023403007715 := by
  unfold tailWord_5857763
  simp only [CollatzResearch.WordTrace]
  refine ⟨213650168677332552117505943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142433445784888368078337295 213650168677332552117505943)
  ·
    refine ⟨320475253015998828176258915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213650168677332552117505943 320475253015998828176258915)
    ·
      refine ⟨480712879523998242264388373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320475253015998828176258915 480712879523998242264388373)
      ·
        refine ⟨22533416227687417606143205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 480712879523998242264388373 22533416227687417606143205)
        ·
          refine ⟨4225015542691390801151851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22533416227687417606143205 4225015542691390801151851)
          ·
            refine ⟨6337523314037086201727777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4225015542691390801151851 6337523314037086201727777)
            ·
              refine ⟨4753142485527814651295833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6337523314037086201727777 4753142485527814651295833)
              ·
                refine ⟨3564856864145860988471875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4753142485527814651295833 3564856864145860988471875)
                ·
                  refine ⟨5347285296218791482707813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3564856864145860988471875 5347285296218791482707813)
                  ·
                    refine ⟨1002615993041023403007715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5347285296218791482707813 1002615993041023403007715)
                    ·
                      rfl

theorem cell23_5857763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 2, 1, 4].length) (baseStart_5857763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857763 prefixEnd_5857763 := by exact prefixLift 5857763
  have htrace : WordTrace (prefixWord ++ tailWord_5857763) baseStart_5857763 baseEnd_5857763 := by
    simpa [prefixWord, tailWord_5857763, baseEnd_5857763] using wordTrace_append hprefix tailTrace_5857763
  have hstable : (prefixWord ++ tailWord_5857763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857763).length < 2 ^ (prefixWord ++ tailWord_5857763).sum := by decide
  have hdescent : baseEnd_5857763 < baseStart_5857763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857775 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 2, 6, 2]
def baseStart_5857775 : Nat := 118140960795 + 5857775 * 2 ^ 59
def prefixEnd_5857775 : Nat := 4983230072969 + 3 ^ 40 * 5857775 * 2
def baseEnd_5857775 : Nat := 3007854140890924162073089

theorem tailTrace_5857775 : CollatzResearch.WordTrace tailWord_5857775 prefixEnd_5857775 3007854140890924162073089 := by
  unfold tailWord_5857775
  simp only [CollatzResearch.WordTrace]
  refine ⟨213650606353289078166942779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142433737568859385444628519 213650606353289078166942779)
  ·
    refine ⟨320475909529933617250414169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213650606353289078166942779 320475909529933617250414169)
    ·
      refine ⟨240356932147450212937810627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320475909529933617250414169 240356932147450212937810627)
      ·
        refine ⟨360535398221175319406715941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240356932147450212937810627 360535398221175319406715941)
        ·
          refine ⟨67600387166470372388759239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 360535398221175319406715941 67600387166470372388759239)
          ·
            refine ⟨101400580749705558583138859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67600387166470372388759239 101400580749705558583138859)
            ·
              refine ⟨152100871124558337874708289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101400580749705558583138859 152100871124558337874708289)
              ·
                refine ⟨114075653343418753406031217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152100871124558337874708289 114075653343418753406031217)
                ·
                  refine ⟨85556740007564065054523413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114075653343418753406031217 85556740007564065054523413)
                  ·
                    refine ⟨4010472187854565549430785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85556740007564065054523413 4010472187854565549430785)
                    ·
                      refine ⟨3007854140890924162073089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4010472187854565549430785 3007854140890924162073089)
                      ·
                        rfl

theorem cell23_5857775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 6, 2].length) (baseStart_5857775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857775 prefixEnd_5857775 := by exact prefixLift 5857775
  have htrace : WordTrace (prefixWord ++ tailWord_5857775) baseStart_5857775 baseEnd_5857775 := by
    simpa [prefixWord, tailWord_5857775, baseEnd_5857775] using wordTrace_append hprefix tailTrace_5857775
  have hstable : (prefixWord ++ tailWord_5857775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857775).length < 2 ^ (prefixWord ++ tailWord_5857775).sum := by decide
  have hdescent : baseEnd_5857775 < baseStart_5857775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857795 : List Nat := [1, 1, 1, 3, 2, 1, 3, 3, 3, 2, 3]
def baseStart_5857795 : Nat := 118140960795 + 5857795 * 2 ^ 59
def prefixEnd_5857795 : Nat := 4983230072969 + 3 ^ 40 * 5857795 * 2
def baseEnd_5857795 : Nat := 3007864410504014083822997

theorem tailTrace_5857795 : CollatzResearch.WordTrace tailWord_5857795 prefixEnd_5857795 3007864410504014083822997 := by
  unfold tailWord_5857795
  simp only [CollatzResearch.WordTrace]
  refine ⟨213651335813216621582670839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142434223875477747721780559 213651335813216621582670839)
  ·
    refine ⟨320477003719824932374006259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213651335813216621582670839 320477003719824932374006259)
    ·
      refine ⟨480715505579737398561009389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320477003719824932374006259 480715505579737398561009389)
      ·
        refine ⟨180268314592401524460378521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 480715505579737398561009389 180268314592401524460378521)
        ·
          refine ⟨135201235944301143345283891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180268314592401524460378521 135201235944301143345283891)
          ·
            refine ⟨202801853916451715017925837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135201235944301143345283891 202801853916451715017925837)
            ·
              refine ⟨76050695218669393131722189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202801853916451715017925837 76050695218669393131722189)
              ·
                refine ⟨28519010707001022424395821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76050695218669393131722189 28519010707001022424395821)
                ·
                  refine ⟨10694629015125383409148433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28519010707001022424395821 10694629015125383409148433)
                  ·
                    refine ⟨8020971761344037556861325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10694629015125383409148433 8020971761344037556861325)
                    ·
                      refine ⟨3007864410504014083822997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8020971761344037556861325 3007864410504014083822997)
                      ·
                        rfl

theorem cell23_5857795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 2, 3].length) (baseStart_5857795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857795 prefixEnd_5857795 := by exact prefixLift 5857795
  have htrace : WordTrace (prefixWord ++ tailWord_5857795) baseStart_5857795 baseEnd_5857795 := by
    simpa [prefixWord, tailWord_5857795, baseEnd_5857795] using wordTrace_append hprefix tailTrace_5857795
  have hstable : (prefixWord ++ tailWord_5857795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857795).length < 2 ^ (prefixWord ++ tailWord_5857795).sum := by decide
  have hdescent : baseEnd_5857795 < baseStart_5857795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857796 : List Nat := [2, 3, 2, 3, 1, 3, 1, 1, 2, 3, 2]
def baseStart_5857796 : Nat := 118140960795 + 5857796 * 2 ^ 59
def prefixEnd_5857796 : Nat := 4983230072969 + 3 ^ 40 * 5857796 * 2
def baseEnd_5857796 : Nat := 3007864923984668579910493

theorem tailTrace_5857796 : CollatzResearch.WordTrace tailWord_5857796 prefixEnd_5857796 3007864923984668579910493 := by
  unfold tailWord_5857796
  simp only [CollatzResearch.WordTrace]
  refine ⟨106825686143106499376728621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142434248190808665835638161 106825686143106499376728621)
  ·
    refine ⟨40059632303664937266273233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106825686143106499376728621 40059632303664937266273233)
    ·
      refine ⟨30044724227748702949704925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40059632303664937266273233 30044724227748702949704925)
      ·
        refine ⟨11266771585405763606139347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30044724227748702949704925 11266771585405763606139347)
        ·
          refine ⟨16900157378108645409209021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11266771585405763606139347 16900157378108645409209021)
          ·
            refine ⟨6337559016790742028453383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16900157378108645409209021 6337559016790742028453383)
            ·
              refine ⟨9506338525186113042680075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6337559016790742028453383 9506338525186113042680075)
              ·
                refine ⟨14259507787779169564020113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9506338525186113042680075 14259507787779169564020113)
                ·
                  refine ⟨10694630840834377173015085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14259507787779169564020113 10694630840834377173015085)
                  ·
                    refine ⟨4010486565312891439880657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10694630840834377173015085 4010486565312891439880657)
                    ·
                      refine ⟨3007864923984668579910493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4010486565312891439880657 3007864923984668579910493)
                      ·
                        rfl

theorem cell23_5857796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_5857796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857796 prefixEnd_5857796 := by exact prefixLift 5857796
  have htrace : WordTrace (prefixWord ++ tailWord_5857796) baseStart_5857796 baseEnd_5857796 := by
    simpa [prefixWord, tailWord_5857796, baseEnd_5857796] using wordTrace_append hprefix tailTrace_5857796
  have hstable : (prefixWord ++ tailWord_5857796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857796).length < 2 ^ (prefixWord ++ tailWord_5857796).sum := by decide
  have hdescent : baseEnd_5857796 < baseStart_5857796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857842 : List Nat := [3, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3]
def baseStart_5857842 : Nat := 118140960795 + 5857842 * 2 ^ 59
def prefixEnd_5857842 : Nat := 4983230072969 + 3 ^ 40 * 5857842 * 2
def baseEnd_5857842 : Nat := 3007888544094775399935281

theorem tailTrace_5857842 : CollatzResearch.WordTrace tailWord_5857842 prefixEnd_5857842 3007888544094775399935281 := by
  unfold tailWord_5857842
  simp only [CollatzResearch.WordTrace]
  refine ⟨53413262511011587152407945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142435366696030899073087853 53413262511011587152407945)
  ·
    refine ⟨40059946883258690364305959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53413262511011587152407945 40059946883258690364305959)
    ·
      refine ⟨60089920324888035546458939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40059946883258690364305959 60089920324888035546458939)
      ·
        refine ⟨90134880487332053319688409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60089920324888035546458939 90134880487332053319688409)
        ·
          refine ⟨67601160365499039989766307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90134880487332053319688409 67601160365499039989766307)
          ·
            refine ⟨101401740548248559984649461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67601160365499039989766307 101401740548248559984649461)
            ·
              refine ⟨9506413176398302498560887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101401740548248559984649461 9506413176398302498560887)
              ·
                refine ⟨14259619764597453747841331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9506413176398302498560887 14259619764597453747841331)
                ·
                  refine ⟨21389429646896180621761997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14259619764597453747841331 21389429646896180621761997)
                  ·
                    refine ⟨8021036117586067733160749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21389429646896180621761997 8021036117586067733160749)
                    ·
                      refine ⟨3007888544094775399935281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8021036117586067733160749 3007888544094775399935281)
                      ·
                        rfl

theorem cell23_5857842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_5857842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857842 prefixEnd_5857842 := by exact prefixLift 5857842
  have htrace : WordTrace (prefixWord ++ tailWord_5857842) baseStart_5857842 baseEnd_5857842 := by
    simpa [prefixWord, tailWord_5857842, baseEnd_5857842] using wordTrace_append hprefix tailTrace_5857842
  have hstable : (prefixWord ++ tailWord_5857842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857842).length < 2 ^ (prefixWord ++ tailWord_5857842).sum := by decide
  have hdescent : baseEnd_5857842 < baseStart_5857842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857846 : List Nat := [5, 1, 2, 1, 2, 2, 2, 2, 1, 2, 3]
def baseStart_5857846 : Nat := 118140960795 + 5857846 * 2 ^ 59
def prefixEnd_5857846 : Nat := 4983230072969 + 3 ^ 40 * 5857846 * 2
def baseEnd_5857846 : Nat := 3007890598017393384285263

theorem tailTrace_5857846 : CollatzResearch.WordTrace tailWord_5857846 prefixEnd_5857846 3007890598017393384285263 := by
  unfold tailWord_5857846
  simp only [CollatzResearch.WordTrace]
  refine ⟨13353324746001991080798587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142435463957354571528518261 13353324746001991080798587)
  ·
    refine ⟨20029987119002986621197881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13353324746001991080798587 20029987119002986621197881)
    ·
      refine ⟨15022490339252239965898411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20029987119002986621197881 15022490339252239965898411)
      ·
        refine ⟨22533735508878359948847617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15022490339252239965898411 22533735508878359948847617)
        ·
          refine ⟨16900301631658769961635713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22533735508878359948847617 16900301631658769961635713)
          ·
            refine ⟨12675226223744077471226785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16900301631658769961635713 12675226223744077471226785)
            ·
              refine ⟨9506419667808058103420089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12675226223744077471226785 9506419667808058103420089)
              ·
                refine ⟨7129814750856043577565067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9506419667808058103420089 7129814750856043577565067)
                ·
                  refine ⟨10694722126284065366347601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7129814750856043577565067 10694722126284065366347601)
                  ·
                    refine ⟨8021041594713049024760701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10694722126284065366347601 8021041594713049024760701)
                    ·
                      refine ⟨3007890598017393384285263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8021041594713049024760701 3007890598017393384285263)
                      ·
                        rfl

theorem cell23_5857846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_5857846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857846 prefixEnd_5857846 := by exact prefixLift 5857846
  have htrace : WordTrace (prefixWord ++ tailWord_5857846) baseStart_5857846 baseEnd_5857846 := by
    simpa [prefixWord, tailWord_5857846, baseEnd_5857846] using wordTrace_append hprefix tailTrace_5857846
  have hstable : (prefixWord ++ tailWord_5857846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857846).length < 2 ^ (prefixWord ++ tailWord_5857846).sum := by decide
  have hdescent : baseEnd_5857846 < baseStart_5857846 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857893 : List Nat := [1, 3, 1, 3, 4, 2, 2, 1, 2, 1, 3]
def baseStart_5857893 : Nat := 118140960795 + 5857893 * 2 ^ 59
def prefixEnd_5857893 : Nat := 4983230072969 + 3 ^ 40 * 5857893 * 2
def baseEnd_5857893 : Nat := 3007914731608154700397547

theorem tailTrace_5857893 : CollatzResearch.WordTrace tailWord_5857893 prefixEnd_5857893 3007914731608154700397547 := by
  unfold tailWord_5857893
  simp only [CollatzResearch.WordTrace]
  refine ⟨213654910166861584319738333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142436606777907722879825555 213654910166861584319738333)
  ·
    refine ⟨80120591312573094119901875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213654910166861584319738333 80120591312573094119901875)
    ·
      refine ⟨120180886968859641179852813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80120591312573094119901875 120180886968859641179852813)
      ·
        refine ⟨45067832613322365442444805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120180886968859641179852813 45067832613322365442444805)
        ·
          refine ⟨8450218614997943520458401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45067832613322365442444805 8450218614997943520458401)
          ·
            refine ⟨6337663961248457640343801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8450218614997943520458401 6337663961248457640343801)
            ·
              refine ⟨4753247970936343230257851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6337663961248457640343801 4753247970936343230257851)
              ·
                refine ⟨7129871956404514845386777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4753247970936343230257851 7129871956404514845386777)
                ·
                  refine ⟨5347403967303386134040083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7129871956404514845386777 5347403967303386134040083)
                  ·
                    refine ⟨8021105950955079201060125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5347403967303386134040083 8021105950955079201060125)
                    ·
                      refine ⟨3007914731608154700397547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8021105950955079201060125 3007914731608154700397547)
                      ·
                        rfl

theorem cell23_5857893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_5857893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857893 prefixEnd_5857893 := by exact prefixLift 5857893
  have htrace : WordTrace (prefixWord ++ tailWord_5857893) baseStart_5857893 baseEnd_5857893 := by
    simpa [prefixWord, tailWord_5857893, baseEnd_5857893] using wordTrace_append hprefix tailTrace_5857893
  have hstable : (prefixWord ++ tailWord_5857893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857893).length < 2 ^ (prefixWord ++ tailWord_5857893).sum := by decide
  have hdescent : baseEnd_5857893 < baseStart_5857893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857895 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 4]
def baseStart_5857895 : Nat := 118140960795 + 5857895 * 2 ^ 59
def prefixEnd_5857895 : Nat := 4983230072969 + 3 ^ 40 * 5857895 * 2
def baseEnd_5857895 : Nat := 3007915758569463692572537

theorem tailTrace_5857895 : CollatzResearch.WordTrace tailWord_5857895 prefixEnd_5857895 3007915758569463692572537 := by
  unfold tailWord_5857895
  simp only [CollatzResearch.WordTrace]
  refine ⟨213654983112854338661311139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142436655408569559107540759 213654983112854338661311139)
  ·
    refine ⟨320482474669281507991966709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213654983112854338661311139 320482474669281507991966709)
    ·
      refine ⟨30045232000245141374246879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 320482474669281507991966709 30045232000245141374246879)
      ·
        refine ⟨45067848000367712061370319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30045232000245141374246879 45067848000367712061370319)
        ·
          refine ⟨67601772000551568092055479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45067848000367712061370319 67601772000551568092055479)
          ·
            refine ⟨101402658000827352138083219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67601772000551568092055479 101402658000827352138083219)
            ·
              refine ⟨152103987001241028207124829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101402658000827352138083219 152103987001241028207124829)
              ·
                refine ⟨57038995125465385577671811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152103987001241028207124829 57038995125465385577671811)
                ·
                  refine ⟨85558492688198078366507717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57038995125465385577671811 85558492688198078366507717)
                  ·
                    refine ⟨16042217379037139693720197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85558492688198078366507717 16042217379037139693720197)
                    ·
                      refine ⟨3007915758569463692572537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16042217379037139693720197 3007915758569463692572537)
                      ·
                        rfl

theorem cell23_5857895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_5857895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857895 prefixEnd_5857895 := by exact prefixLift 5857895
  have htrace : WordTrace (prefixWord ++ tailWord_5857895) baseStart_5857895 baseEnd_5857895 := by
    simpa [prefixWord, tailWord_5857895, baseEnd_5857895] using wordTrace_append hprefix tailTrace_5857895
  have hstable : (prefixWord ++ tailWord_5857895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857895).length < 2 ^ (prefixWord ++ tailWord_5857895).sum := by decide
  have hdescent : baseEnd_5857895 < baseStart_5857895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857902 : List Nat := [4, 1, 2, 2, 2, 1, 1, 2, 2, 1, 5]
def baseStart_5857902 : Nat := 118140960795 + 5857902 * 2 ^ 59
def prefixEnd_5857902 : Nat := 4983230072969 + 3 ^ 40 * 5857902 * 2
def baseEnd_5857902 : Nat := 3007919352934045165185005

theorem tailTrace_5857902 : CollatzResearch.WordTrace tailWord_5857902 prefixEnd_5857902 3007919352934045165185005 := by
  unfold tailWord_5857902
  simp only [CollatzResearch.WordTrace]
  refine ⟨26706904802978622357101995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142436825615885985904543973 26706904802978622357101995)
  ·
    refine ⟨40060357204467933535652993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26706904802978622357101995 40060357204467933535652993)
    ·
      refine ⟨30045267903350950151739745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40060357204467933535652993 30045267903350950151739745)
      ·
        refine ⟨22533950927513212613804809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30045267903350950151739745 22533950927513212613804809)
        ·
          refine ⟨16900463195634909460353607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22533950927513212613804809 16900463195634909460353607)
          ·
            refine ⟨25350694793452364190530411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16900463195634909460353607 25350694793452364190530411)
            ·
              refine ⟨38026042190178546285795617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25350694793452364190530411 38026042190178546285795617)
              ·
                refine ⟨28519531642633909714346713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38026042190178546285795617 28519531642633909714346713)
                ·
                  refine ⟨21389648731975432285760035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28519531642633909714346713 21389648731975432285760035)
                  ·
                    refine ⟨32084473097963148428640053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21389648731975432285760035 32084473097963148428640053)
                    ·
                      refine ⟨3007919352934045165185005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32084473097963148428640053 3007919352934045165185005)
                      ·
                        rfl

theorem cell23_5857902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_5857902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857902 prefixEnd_5857902 := by exact prefixLift 5857902
  have htrace : WordTrace (prefixWord ++ tailWord_5857902) baseStart_5857902 baseEnd_5857902 := by
    simpa [prefixWord, tailWord_5857902, baseEnd_5857902] using wordTrace_append hprefix tailTrace_5857902
  have hstable : (prefixWord ++ tailWord_5857902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857902).length < 2 ^ (prefixWord ++ tailWord_5857902).sum := by decide
  have hdescent : baseEnd_5857902 < baseStart_5857902 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857915 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 3, 5, 3]
def baseStart_5857915 : Nat := 118140960795 + 5857915 * 2 ^ 59
def prefixEnd_5857915 : Nat := 4983230072969 + 3 ^ 40 * 5857915 * 2
def baseEnd_5857915 : Nat := 3007926028182553614322445

theorem tailTrace_5857915 : CollatzResearch.WordTrace tailWord_5857915 prefixEnd_5857915 3007926028182553614322445 := by
  unfold tailWord_5857915
  simp only [CollatzResearch.WordTrace]
  refine ⟨213655712572781882077039199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142437141715187921384692799 213655712572781882077039199)
  ·
    refine ⟨320483568859172823115558799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213655712572781882077039199 320483568859172823115558799)
    ·
      refine ⟨480725353288759234673338199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320483568859172823115558799 480725353288759234673338199)
      ·
        refine ⟨721088029933138852010007299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480725353288759234673338199 721088029933138852010007299)
        ·
          refine ⟨1081632044899708278015010949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 721088029933138852010007299 1081632044899708278015010949)
          ·
            refine ⟨202806008418695302127814553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1081632044899708278015010949 202806008418695302127814553)
            ·
              refine ⟨152104506314021476595860915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202806008418695302127814553 152104506314021476595860915)
              ·
                refine ⟨228156759471032214893791373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152104506314021476595860915 228156759471032214893791373)
                ·
                  refine ⟨85558784801637080585171765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 228156759471032214893791373 85558784801637080585171765)
                  ·
                    refine ⟨8021136075153476304859853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85558784801637080585171765 8021136075153476304859853)
                    ·
                      refine ⟨3007926028182553614322445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8021136075153476304859853 3007926028182553614322445)
                      ·
                        rfl

theorem cell23_5857915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 5, 3].length) (baseStart_5857915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857915 prefixEnd_5857915 := by exact prefixLift 5857915
  have htrace : WordTrace (prefixWord ++ tailWord_5857915) baseStart_5857915 baseEnd_5857915 := by
    simpa [prefixWord, tailWord_5857915, baseEnd_5857915] using wordTrace_append hprefix tailTrace_5857915
  have hstable : (prefixWord ++ tailWord_5857915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857915).length < 2 ^ (prefixWord ++ tailWord_5857915).sum := by decide
  have hdescent : baseEnd_5857915 < baseStart_5857915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857945 : List Nat := [1, 2, 1, 2, 1, 2, 3, 3, 1, 2, 5]
def baseStart_5857945 : Nat := 118140960795 + 5857945 * 2 ^ 59
def prefixEnd_5857945 : Nat := 4983230072969 + 3 ^ 40 * 5857945 * 2
def baseEnd_5857945 : Nat := 3007941432602188496947307

theorem tailTrace_5857945 : CollatzResearch.WordTrace tailWord_5857945 prefixEnd_5857945 3007941432602188496947307 := by
  unfold tailWord_5857945
  simp only [CollatzResearch.WordTrace]
  refine ⟨213656806762673197200631289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142437871175115464800420859 213656806762673197200631289)
  ·
    refine ⟨160242605072004897900473467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213656806762673197200631289 160242605072004897900473467)
    ·
      refine ⟨240363907608007346850710201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160242605072004897900473467 240363907608007346850710201)
      ·
        refine ⟨180272930706005510138032651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240363907608007346850710201 180272930706005510138032651)
        ·
          refine ⟨270409396059008265207048977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180272930706005510138032651 270409396059008265207048977)
          ·
            refine ⟨202807047044256198905286733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270409396059008265207048977 202807047044256198905286733)
            ·
              refine ⟨76052642641596074589482525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202807047044256198905286733 76052642641596074589482525)
              ·
                refine ⟨28519740990598527971055947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76052642641596074589482525 28519740990598527971055947)
                ·
                  refine ⟨42779611485897791956583921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28519740990598527971055947 42779611485897791956583921)
                  ·
                    refine ⟨32084708614423343967437941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42779611485897791956583921 32084708614423343967437941)
                    ·
                      refine ⟨3007941432602188496947307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32084708614423343967437941 3007941432602188496947307)
                      ·
                        rfl

theorem cell23_5857945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_5857945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857945 prefixEnd_5857945 := by exact prefixLift 5857945
  have htrace : WordTrace (prefixWord ++ tailWord_5857945) baseStart_5857945 baseEnd_5857945 := by
    simpa [prefixWord, tailWord_5857945, baseEnd_5857945] using wordTrace_append hprefix tailTrace_5857945
  have hstable : (prefixWord ++ tailWord_5857945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857945).length < 2 ^ (prefixWord ++ tailWord_5857945).sum := by decide
  have hdescent : baseEnd_5857945 < baseStart_5857945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5857969 : List Nat := [1, 2, 2, 6, 1, 1, 1, 1, 1, 7]
def baseStart_5857969 : Nat := 118140960795 + 5857969 * 2 ^ 59
def prefixEnd_5857969 : Nat := 4983230072969 + 3 ^ 40 * 5857969 * 2
def baseEnd_5857969 : Nat := 1002651252045965467682399

theorem tailTrace_5857969 : CollatzResearch.WordTrace tailWord_5857969 prefixEnd_5857969 1002651252045965467682399 := by
  unfold tailWord_5857969
  simp only [CollatzResearch.WordTrace]
  refine ⟨213657682114586249299504961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142438454743057499533003307 213657682114586249299504961)
  ·
    refine ⟨160243261585939686974628721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213657682114586249299504961 160243261585939686974628721)
    ·
      refine ⟨120182446189454765230971541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160243261585939686974628721 120182446189454765230971541)
      ·
        refine ⟨5633552165130692120201791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 120182446189454765230971541 5633552165130692120201791)
        ·
          refine ⟨8450328247696038180302687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5633552165130692120201791 8450328247696038180302687)
          ·
            refine ⟨12675492371544057270454031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8450328247696038180302687 12675492371544057270454031)
            ·
              refine ⟨19013238557316085905681047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12675492371544057270454031 19013238557316085905681047)
              ·
                refine ⟨28519857835974128858521571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19013238557316085905681047 28519857835974128858521571)
                ·
                  refine ⟨42779786753961193287782357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28519857835974128858521571 42779786753961193287782357)
                  ·
                    refine ⟨1002651252045965467682399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42779786753961193287782357 1002651252045965467682399)
                    ·
                      rfl

theorem cell23_5857969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 7].length) (baseStart_5857969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5857969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5857969 prefixEnd_5857969 := by exact prefixLift 5857969
  have htrace : WordTrace (prefixWord ++ tailWord_5857969) baseStart_5857969 baseEnd_5857969 := by
    simpa [prefixWord, tailWord_5857969, baseEnd_5857969] using wordTrace_append hprefix tailTrace_5857969
  have hstable : (prefixWord ++ tailWord_5857969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5857969).length < 2 ^ (prefixWord ++ tailWord_5857969).sum := by decide
  have hdescent : baseEnd_5857969 < baseStart_5857969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5857969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858050 : List Nat := [3, 4, 1, 1, 1, 3, 3, 2, 1, 4]
def baseStart_5858050 : Nat := 118140960795 + 5858050 * 2 ^ 59
def prefixEnd_5858050 : Nat := 4983230072969 + 3 ^ 40 * 5858050 * 2
def baseEnd_5858050 : Nat := 1002665116023636862044775

theorem tailTrace_5858050 : CollatzResearch.WordTrace tailWord_5858050 prefixEnd_5858050 1002665116023636862044775 := by
  unfold tailWord_5858050
  simp only [CollatzResearch.WordTrace]
  refine ⟨53415159106823200033300901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142440424284861866755469069 53415159106823200033300901)
  ·
    refine ⟨10015342332529350006243919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53415159106823200033300901 10015342332529350006243919)
    ·
      refine ⟨15023013498794025009365879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10015342332529350006243919 15023013498794025009365879)
      ·
        refine ⟨22534520248191037514048819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15023013498794025009365879 22534520248191037514048819)
        ·
          refine ⟨33801780372286556271073229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22534520248191037514048819 33801780372286556271073229)
          ·
            refine ⟨12675667639607458601652461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33801780372286556271073229 12675667639607458601652461)
            ·
              refine ⟨4753375364852796975619673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12675667639607458601652461 4753375364852796975619673)
              ·
                refine ⟨3565031523639597731714755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4753375364852796975619673 3565031523639597731714755)
                ·
                  refine ⟨5347547285459396597572133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3565031523639597731714755 5347547285459396597572133)
                  ·
                    refine ⟨1002665116023636862044775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5347547285459396597572133 1002665116023636862044775)
                    ·
                      rfl

theorem cell23_5858050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_5858050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858050 prefixEnd_5858050 := by exact prefixLift 5858050
  have htrace : WordTrace (prefixWord ++ tailWord_5858050) baseStart_5858050 baseEnd_5858050 := by
    simpa [prefixWord, tailWord_5858050, baseEnd_5858050] using wordTrace_append hprefix tailTrace_5858050
  have hstable : (prefixWord ++ tailWord_5858050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858050).length < 2 ^ (prefixWord ++ tailWord_5858050).sum := by decide
  have hdescent : baseEnd_5858050 < baseStart_5858050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858056 : List Nat := [2, 1, 3, 2, 2, 2, 3, 1, 3, 1, 3]
def baseStart_5858056 : Nat := 118140960795 + 5858056 * 2 ^ 59
def prefixEnd_5858056 : Nat := 4983230072969 + 3 ^ 40 * 5858056 * 2
def baseEnd_5858056 : Nat := 3007998428954837562659297

theorem tailTrace_5858056 : CollatzResearch.WordTrace tailWord_5858056 prefixEnd_5858056 3007998428954837562659297 := by
  unfold tailWord_5858056
  simp only [CollatzResearch.WordTrace]
  refine ⟨106830427632635531578961011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142440570176847375438614681 106830427632635531578961011)
  ·
    refine ⟨160245641448953297368441517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106830427632635531578961011 160245641448953297368441517)
    ·
      refine ⟨60092115543357486513165569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160245641448953297368441517 60092115543357486513165569)
      ·
        refine ⟨45069086657518114884874177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60092115543357486513165569 45069086657518114884874177)
        ·
          refine ⟨33801814993138586163655633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45069086657518114884874177 33801814993138586163655633)
          ·
            refine ⟨25351361244853939622741725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33801814993138586163655633 25351361244853939622741725)
            ·
              refine ⟨9506760466820227358528147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25351361244853939622741725 9506760466820227358528147)
              ·
                refine ⟨14260140700230341037792221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9506760466820227358528147 14260140700230341037792221)
                ·
                  refine ⟨5347552762586377889172083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14260140700230341037792221 5347552762586377889172083)
                  ·
                    refine ⟨8021329143879566833758125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5347552762586377889172083 8021329143879566833758125)
                    ·
                      refine ⟨3007998428954837562659297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8021329143879566833758125 3007998428954837562659297)
                      ·
                        rfl

theorem cell23_5858056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_5858056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858056 prefixEnd_5858056 := by exact prefixLift 5858056
  have htrace : WordTrace (prefixWord ++ tailWord_5858056) baseStart_5858056 baseEnd_5858056 := by
    simpa [prefixWord, tailWord_5858056, baseEnd_5858056] using wordTrace_append hprefix tailTrace_5858056
  have hstable : (prefixWord ++ tailWord_5858056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858056).length < 2 ^ (prefixWord ++ tailWord_5858056).sum := by decide
  have hdescent : baseEnd_5858056 < baseStart_5858056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858062 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4]
def baseStart_5858062 : Nat := 118140960795 + 5858062 * 2 ^ 59
def prefixEnd_5858062 : Nat := 4983230072969 + 3 ^ 40 * 5858062 * 2
def baseEnd_5858062 : Nat := 3008001509838764539184269

theorem tailTrace_5858062 : CollatzResearch.WordTrace tailWord_5858062 prefixEnd_5858062 3008001509838764539184269 := by
  unfold tailWord_5858062
  simp only [CollatzResearch.WordTrace]
  refine ⟨26707634262906165772830055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142440716068832884121760293 26707634262906165772830055)
  ·
    refine ⟨40061451394359248659245083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26707634262906165772830055 40061451394359248659245083)
    ·
      refine ⟨60092177091538872988867625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40061451394359248659245083 60092177091538872988867625)
      ·
        refine ⟨45069132818654154741650719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60092177091538872988867625 45069132818654154741650719)
        ·
          refine ⟨67603699227981232112476079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45069132818654154741650719 67603699227981232112476079)
          ·
            refine ⟨101405548841971848168714119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67603699227981232112476079 101405548841971848168714119)
            ·
              refine ⟨152108323262957772253071179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101405548841971848168714119 152108323262957772253071179)
              ·
                refine ⟨228162484894436658379606769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152108323262957772253071179 228162484894436658379606769)
                ·
                  refine ⟨171121863670827493784705077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 228162484894436658379606769 171121863670827493784705077)
                  ·
                    refine ⟨16042674719140077542316101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 171121863670827493784705077 16042674719140077542316101)
                    ·
                      refine ⟨3008001509838764539184269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16042674719140077542316101 3008001509838764539184269)
                      ·
                        rfl

theorem cell23_5858062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_5858062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858062 prefixEnd_5858062 := by exact prefixLift 5858062
  have htrace : WordTrace (prefixWord ++ tailWord_5858062) baseStart_5858062 baseEnd_5858062 := by
    simpa [prefixWord, tailWord_5858062, baseEnd_5858062] using wordTrace_append hprefix tailTrace_5858062
  have hstable : (prefixWord ++ tailWord_5858062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858062).length < 2 ^ (prefixWord ++ tailWord_5858062).sum := by decide
  have hdescent : baseEnd_5858062 < baseStart_5858062 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858072 : List Nat := [2, 1, 2, 3, 1, 1, 1, 5, 1, 6]
def baseStart_5858072 : Nat := 118140960795 + 5858072 * 2 ^ 59
def prefixEnd_5858072 : Nat := 4983230072969 + 3 ^ 40 * 5858072 * 2
def baseEnd_5858072 : Nat := 1002668881548436500019741

theorem tailTrace_5858072 : CollatzResearch.WordTrace tailWord_5858072 prefixEnd_5858072 1002668881548436500019741 := by
  unfold tailWord_5858072
  simp only [CollatzResearch.WordTrace]
  refine ⟨106830719416606548945252235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142440959222142065260336313 106830719416606548945252235)
  ·
    refine ⟨160246079124909823417878353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106830719416606548945252235 160246079124909823417878353)
    ·
      refine ⟨120184559343682367563408765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160246079124909823417878353 120184559343682367563408765)
      ·
        refine ⟨45069209753880887836278287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120184559343682367563408765 45069209753880887836278287)
        ·
          refine ⟨67603814630821331754417431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45069209753880887836278287 67603814630821331754417431)
          ·
            refine ⟨101405721946231997631626147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67603814630821331754417431 101405721946231997631626147)
            ·
              refine ⟨152108582919347996447439221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101405721946231997631626147 152108582919347996447439221)
              ·
                refine ⟨14260179648688874666947427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152108582919347996447439221 14260179648688874666947427)
                ·
                  refine ⟨21390269473033312000421141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14260179648688874666947427 21390269473033312000421141)
                  ·
                    refine ⟨1002668881548436500019741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21390269473033312000421141 1002668881548436500019741)
                    ·
                      rfl

theorem cell23_5858072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 1, 6].length) (baseStart_5858072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858072 prefixEnd_5858072 := by exact prefixLift 5858072
  have htrace : WordTrace (prefixWord ++ tailWord_5858072) baseStart_5858072 baseEnd_5858072 := by
    simpa [prefixWord, tailWord_5858072, baseEnd_5858072] using wordTrace_append hprefix tailTrace_5858072
  have hstable : (prefixWord ++ tailWord_5858072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858072).length < 2 ^ (prefixWord ++ tailWord_5858072).sum := by decide
  have hdescent : baseEnd_5858072 < baseStart_5858072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858076 : List Nat := [2, 2, 3, 1, 1, 5, 1, 2, 1, 5]
def baseStart_5858076 : Nat := 118140960795 + 5858076 * 2 ^ 59
def prefixEnd_5858076 : Nat := 4983230072969 + 3 ^ 40 * 5858076 * 2
def baseEnd_5858076 : Nat := 1002669566189309161469735

theorem tailTrace_5858076 : CollatzResearch.WordTrace tailWord_5858076 prefixEnd_5858076 1002669566189309161469735 := by
  unfold tailWord_5858076
  simp only [CollatzResearch.WordTrace]
  refine ⟨106830792362599303286825041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142441056483465737715766721 106830792362599303286825041)
  ·
    refine ⟨80123094271949477465118781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106830792362599303286825041 80123094271949477465118781)
    ·
      refine ⟨30046160351981054049419543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80123094271949477465118781 30046160351981054049419543)
      ·
        refine ⟨45069240527971581074129315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30046160351981054049419543 45069240527971581074129315)
        ·
          refine ⟨67603860791957371611193973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45069240527971581074129315 67603860791957371611193973)
          ·
            refine ⟨6337861949246003588549435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67603860791957371611193973 6337861949246003588549435)
            ·
              refine ⟨9506792923869005382824153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6337861949246003588549435 9506792923869005382824153)
              ·
                refine ⟨7130094692901754037118115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9506792923869005382824153 7130094692901754037118115)
                ·
                  refine ⟨10695142039352631055677173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7130094692901754037118115 10695142039352631055677173)
                  ·
                    refine ⟨1002669566189309161469735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10695142039352631055677173 1002669566189309161469735)
                    ·
                      rfl

theorem cell23_5858076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_5858076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858076 prefixEnd_5858076 := by exact prefixLift 5858076
  have htrace : WordTrace (prefixWord ++ tailWord_5858076) baseStart_5858076 baseEnd_5858076 := by
    simpa [prefixWord, tailWord_5858076, baseEnd_5858076] using wordTrace_append hprefix tailTrace_5858076
  have hstable : (prefixWord ++ tailWord_5858076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858076).length < 2 ^ (prefixWord ++ tailWord_5858076).sum := by decide
  have hdescent : baseEnd_5858076 < baseStart_5858076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858079 : List Nat := [1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 4]
def baseStart_5858079 : Nat := 118140960795 + 5858079 * 2 ^ 59
def prefixEnd_5858079 : Nat := 4983230072969 + 3 ^ 40 * 5858079 * 2
def baseEnd_5858079 : Nat := 3008010239009890972671691

theorem tailTrace_5858079 : CollatzResearch.WordTrace tailWord_5858079 prefixEnd_5858079 3008010239009890972671691 := by
  unfold tailWord_5858079
  simp only [CollatzResearch.WordTrace]
  refine ⟨213661694144187738086009291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142441129429458492057339527 213661694144187738086009291)
  ·
    refine ⟨320492541216281607129013937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213661694144187738086009291 320492541216281607129013937)
    ·
      refine ⟨240369405912211205346760453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320492541216281607129013937 240369405912211205346760453)
      ·
        refine ⟨45069263608539601002517585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 240369405912211205346760453 45069263608539601002517585)
        ·
          refine ⟨33801947706404700751888189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45069263608539601002517585 33801947706404700751888189)
          ·
            refine ⟨12675730389901762781958071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33801947706404700751888189 12675730389901762781958071)
            ·
              refine ⟨19013595584852644172937107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12675730389901762781958071 19013595584852644172937107)
              ·
                refine ⟨28520393377278966259405661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19013595584852644172937107 28520393377278966259405661)
                ·
                  refine ⟨10695147516479612347277123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28520393377278966259405661 10695147516479612347277123)
                  ·
                    refine ⟨16042721274719418520915685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10695147516479612347277123 16042721274719418520915685)
                    ·
                      refine ⟨3008010239009890972671691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16042721274719418520915685 3008010239009890972671691)
                      ·
                        rfl

theorem cell23_5858079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_5858079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858079 prefixEnd_5858079 := by exact prefixLift 5858079
  have htrace : WordTrace (prefixWord ++ tailWord_5858079) baseStart_5858079 baseEnd_5858079 := by
    simpa [prefixWord, tailWord_5858079, baseEnd_5858079] using wordTrace_append hprefix tailTrace_5858079
  have hstable : (prefixWord ++ tailWord_5858079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858079).length < 2 ^ (prefixWord ++ tailWord_5858079).sum := by decide
  have hdescent : baseEnd_5858079 < baseStart_5858079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858099 : List Nat := [1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 5]
def baseStart_5858099 : Nat := 118140960795 + 5858099 * 2 ^ 59
def prefixEnd_5858099 : Nat := 4983230072969 + 3 ^ 40 * 5858099 * 2
def baseEnd_5858099 : Nat := 3008020508622980894421599

theorem tailTrace_5858099 : CollatzResearch.WordTrace tailWord_5858099 prefixEnd_5858099 3008020508622980894421599 := by
  unfold tailWord_5858099
  simp only [CollatzResearch.WordTrace]
  refine ⟨213662423604115281501737351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142441615736076854334491567 213662423604115281501737351)
  ·
    refine ⟨320493635406172922252606027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213662423604115281501737351 320493635406172922252606027)
    ·
      refine ⟨480740453109259383378909041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320493635406172922252606027 480740453109259383378909041)
      ·
        refine ⟨360555339831944537534181781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 480740453109259383378909041 360555339831944537534181781)
        ·
          refine ⟨16901031554622400196914771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 360555339831944537534181781 16901031554622400196914771)
          ·
            refine ⟨25351547331933600295372157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16901031554622400196914771 25351547331933600295372157)
            ·
              refine ⟨9506830249475100110764559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25351547331933600295372157 9506830249475100110764559)
              ·
                refine ⟨14260245374212650166146839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9506830249475100110764559 14260245374212650166146839)
                ·
                  refine ⟨21390368061318975249220259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14260245374212650166146839 21390368061318975249220259)
                  ·
                    refine ⟨32085552091978462873830389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21390368061318975249220259 32085552091978462873830389)
                    ·
                      refine ⟨3008020508622980894421599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32085552091978462873830389 3008020508622980894421599)
                      ·
                        rfl

theorem cell23_5858099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 5].length) (baseStart_5858099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858099 prefixEnd_5858099 := by exact prefixLift 5858099
  have htrace : WordTrace (prefixWord ++ tailWord_5858099) baseStart_5858099 baseEnd_5858099 := by
    simpa [prefixWord, tailWord_5858099, baseEnd_5858099] using wordTrace_append hprefix tailTrace_5858099
  have hstable : (prefixWord ++ tailWord_5858099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858099).length < 2 ^ (prefixWord ++ tailWord_5858099).sum := by decide
  have hdescent : baseEnd_5858099 < baseStart_5858099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858277 : List Nat := [1, 3, 1, 6, 1, 2, 2, 2, 5]
def baseStart_5858277 : Nat := 118140960795 + 5858277 * 2 ^ 59
def prefixEnd_5858277 : Nat := 4983230072969 + 3 ^ 40 * 5858277 * 2
def baseEnd_5858277 : Nat := 334234656464386799777309

theorem tailTrace_5858277 : CollatzResearch.WordTrace tailWord_5858277 prefixEnd_5858277 334234656464386799777309 := by
  unfold tailWord_5858277
  simp only [CollatzResearch.WordTrace]
  refine ⟨213668915797470417901717085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142445943864980278601144723 213668915797470417901717085)
  ·
    refine ⟨80125843424051406713143907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213668915797470417901717085 80125843424051406713143907)
    ·
      refine ⟨120188765136077110069715861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80125843424051406713143907 120188765136077110069715861)
      ·
        refine ⟨5633848365753614534517931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 120188765136077110069715861 5633848365753614534517931)
        ·
          refine ⟨8450772548630421801776897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5633848365753614534517931 8450772548630421801776897)
          ·
            refine ⟨6338079411472816351332673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8450772548630421801776897 6338079411472816351332673)
            ·
              refine ⟨4753559558604612263499505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6338079411472816351332673 4753559558604612263499505)
              ·
                refine ⟨3565169668953459197624629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4753559558604612263499505 3565169668953459197624629)
                ·
                  refine ⟨334234656464386799777309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3565169668953459197624629 334234656464386799777309)
                  ·
                    rfl

theorem cell23_5858277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 2, 5].length) (baseStart_5858277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858277 prefixEnd_5858277 := by exact prefixLift 5858277
  have htrace : WordTrace (prefixWord ++ tailWord_5858277) baseStart_5858277 baseEnd_5858277 := by
    simpa [prefixWord, tailWord_5858277, baseEnd_5858277] using wordTrace_append hprefix tailTrace_5858277
  have hstable : (prefixWord ++ tailWord_5858277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858277).length < 2 ^ (prefixWord ++ tailWord_5858277).sum := by decide
  have hdescent : baseEnd_5858277 < baseStart_5858277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858376 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 6, 4]
def baseStart_5858376 : Nat := 118140960795 + 5858376 * 2 ^ 59
def prefixEnd_5858376 : Nat := 4983230072969 + 3 ^ 40 * 5858376 * 2
def baseEnd_5858376 : Nat := 1002720914254758770219275

theorem tailTrace_5858376 : CollatzResearch.WordTrace tailWord_5858376 prefixEnd_5858376 1002720914254758770219275 := by
  unfold tailWord_5858376
  simp only [CollatzResearch.WordTrace]
  refine ⟨106836263312055878904785491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142448351082741171873047321 106836263312055878904785491)
  ·
    refine ⟨160254394968083818357178237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106836263312055878904785491 160254394968083818357178237)
    ·
      refine ⟨60095398113031431883941839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160254394968083818357178237 60095398113031431883941839)
      ·
        refine ⟨90143097169547147825912759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60095398113031431883941839 90143097169547147825912759)
        ·
          refine ⟨135214645754320721738869139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90143097169547147825912759 135214645754320721738869139)
          ·
            refine ⟨202821968631481082608303709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135214645754320721738869139 202821968631481082608303709)
            ·
              refine ⟨76058238236805405978113891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202821968631481082608303709 76058238236805405978113891)
              ·
                refine ⟨114087357355208108967170837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76058238236805405978113891 114087357355208108967170837)
                ·
                  refine ⟨5347844876025380107836133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 114087357355208108967170837 5347844876025380107836133)
                  ·
                    refine ⟨1002720914254758770219275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5347844876025380107836133 1002720914254758770219275)
                    ·
                      rfl

theorem cell23_5858376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_5858376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858376 prefixEnd_5858376 := by exact prefixLift 5858376
  have htrace : WordTrace (prefixWord ++ tailWord_5858376) baseStart_5858376 baseEnd_5858376 := by
    simpa [prefixWord, tailWord_5858376, baseEnd_5858376] using wordTrace_append hprefix tailTrace_5858376
  have hstable : (prefixWord ++ tailWord_5858376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858376).length < 2 ^ (prefixWord ++ tailWord_5858376).sum := by decide
  have hdescent : baseEnd_5858376 < baseStart_5858376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858379 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 6]
def baseStart_5858379 : Nat := 118140960795 + 5858379 * 2 ^ 59
def prefixEnd_5858379 : Nat := 4983230072969 + 3 ^ 40 * 5858379 * 2
def baseEnd_5858379 : Nat := 3008164283206239798920311

theorem tailTrace_5858379 : CollatzResearch.WordTrace tailWord_5858379 prefixEnd_5858379 3008164283206239798920311 := by
  unfold tailWord_5858379
  simp only [CollatzResearch.WordTrace]
  refine ⟨213672636043100889321930191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142448424028733926214620127 213672636043100889321930191)
  ·
    refine ⟨320508954064651333982895287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213672636043100889321930191 320508954064651333982895287)
    ·
      refine ⟨480763431096977000974342931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320508954064651333982895287 480763431096977000974342931)
      ·
        refine ⟨721145146645465501461514397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480763431096977000974342931 721145146645465501461514397)
        ·
          refine ⟨270429429992049563048067899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 721145146645465501461514397 270429429992049563048067899)
          ·
            refine ⟨405644144988074344572101849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270429429992049563048067899 405644144988074344572101849)
            ·
              refine ⟨304233108741055758429076387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 405644144988074344572101849 304233108741055758429076387)
              ·
                refine ⟨456349663111583637643614581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304233108741055758429076387 456349663111583637643614581)
                ·
                  refine ⟨42782780916710966029088867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 456349663111583637643614581 42782780916710966029088867)
                  ·
                    refine ⟨64174171375066449043633301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42782780916710966029088867 64174171375066449043633301)
                    ·
                      refine ⟨3008164283206239798920311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64174171375066449043633301 3008164283206239798920311)
                      ·
                        rfl

theorem cell23_5858379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 6].length) (baseStart_5858379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858379 prefixEnd_5858379 := by exact prefixLift 5858379
  have htrace : WordTrace (prefixWord ++ tailWord_5858379) baseStart_5858379 baseEnd_5858379 := by
    simpa [prefixWord, tailWord_5858379, baseEnd_5858379] using wordTrace_append hprefix tailTrace_5858379
  have hstable : (prefixWord ++ tailWord_5858379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858379).length < 2 ^ (prefixWord ++ tailWord_5858379).sum := by decide
  have hdescent : baseEnd_5858379 < baseStart_5858379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858396 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_5858396 : Nat := 118140960795 + 5858396 * 2 ^ 59
def prefixEnd_5858396 : Nat := 4983230072969 + 3 ^ 40 * 5858396 * 2
def baseEnd_5858396 : Nat := 3008173012377366232407733

theorem tailTrace_5858396 : CollatzResearch.WordTrace tailWord_5858396 prefixEnd_5858396 3008173012377366232407733 := by
  unfold tailWord_5858396
  simp only [CollatzResearch.WordTrace]
  refine ⟨106836628042019650612649521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142448837389359534150199361 106836628042019650612649521)
  ·
    refine ⟨80127471031514737959487141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106836628042019650612649521 80127471031514737959487141)
    ·
      refine ⟨15023900818409013367403839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80127471031514737959487141 15023900818409013367403839)
      ·
        refine ⟨22535851227613520051105759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15023900818409013367403839 22535851227613520051105759)
        ·
          refine ⟨33803776841420280076658639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22535851227613520051105759 33803776841420280076658639)
          ·
            refine ⟨50705665262130420114987959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33803776841420280076658639 50705665262130420114987959)
            ·
              refine ⟨76058497893195630172481939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50705665262130420114987959 76058497893195630172481939)
              ·
                refine ⟨114087746839793445258722909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76058497893195630172481939 114087746839793445258722909)
                ·
                  refine ⟨42782905064922541972021091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114087746839793445258722909 42782905064922541972021091)
                  ·
                    refine ⟨64174357597383812958031637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42782905064922541972021091 64174357597383812958031637)
                    ·
                      refine ⟨3008173012377366232407733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64174357597383812958031637 3008173012377366232407733)
                      ·
                        rfl

theorem cell23_5858396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_5858396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858396 prefixEnd_5858396 := by exact prefixLift 5858396
  have htrace : WordTrace (prefixWord ++ tailWord_5858396) baseStart_5858396 baseEnd_5858396 := by
    simpa [prefixWord, tailWord_5858396, baseEnd_5858396] using wordTrace_append hprefix tailTrace_5858396
  have hstable : (prefixWord ++ tailWord_5858396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858396).length < 2 ^ (prefixWord ++ tailWord_5858396).sum := by decide
  have hdescent : baseEnd_5858396 < baseStart_5858396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858410 : List Nat := [3, 1, 3, 2, 2, 2, 1, 3, 2, 4]
def baseStart_5858410 : Nat := 118140960795 + 5858410 * 2 ^ 59
def prefixEnd_5858410 : Nat := 4983230072969 + 3 ^ 40 * 5858410 * 2
def baseEnd_5858410 : Nat := 1002726733702176392544223

theorem tailTrace_5858410 : CollatzResearch.WordTrace tailWord_5858410 prefixEnd_5858410 1002726733702176392544223 := by
  unfold tailWord_5858410
  simp only [CollatzResearch.WordTrace]
  refine ⟨53418441676497145404077171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142449177803992387744205789 53418441676497145404077171)
  ·
    refine ⟨80127662514745718106115757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53418441676497145404077171 80127662514745718106115757)
    ·
      refine ⟨30047873443029644289793409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80127662514745718106115757 30047873443029644289793409)
      ·
        refine ⟨22535905082272233217345057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30047873443029644289793409 22535905082272233217345057)
        ·
          refine ⟨16901928811704174913008793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22535905082272233217345057 16901928811704174913008793)
          ·
            refine ⟨12676446608778131184756595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16901928811704174913008793 12676446608778131184756595)
            ·
              refine ⟨19014669913167196777134893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12676446608778131184756595 19014669913167196777134893)
              ·
                refine ⟨7130501217437698791425585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19014669913167196777134893 7130501217437698791425585)
                ·
                  refine ⟨5347875913078274093569189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7130501217437698791425585 5347875913078274093569189)
                  ·
                    refine ⟨1002726733702176392544223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5347875913078274093569189 1002726733702176392544223)
                    ·
                      rfl

theorem cell23_5858410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_5858410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858410 prefixEnd_5858410 := by exact prefixLift 5858410
  have htrace : WordTrace (prefixWord ++ tailWord_5858410) baseStart_5858410 baseEnd_5858410 := by
    simpa [prefixWord, tailWord_5858410, baseEnd_5858410] using wordTrace_append hprefix tailTrace_5858410
  have hstable : (prefixWord ++ tailWord_5858410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858410).length < 2 ^ (prefixWord ++ tailWord_5858410).sum := by decide
  have hdescent : baseEnd_5858410 < baseStart_5858410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858433 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 3, 3, 3]
def baseStart_5858433 : Nat := 118140960795 + 5858433 * 2 ^ 59
def prefixEnd_5858433 : Nat := 4983230072969 + 3 ^ 40 * 5858433 * 2
def baseEnd_5858433 : Nat := 3008192011161582587645063

theorem tailTrace_5858433 : CollatzResearch.WordTrace tailWord_5858433 prefixEnd_5858433 3008192011161582587645063 := by
  unfold tailWord_5858433
  simp only [CollatzResearch.WordTrace]
  refine ⟨213674605584905256544395953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142449737056603504362930635 213674605584905256544395953)
  ·
    refine ⟨160255954188678942408296965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213674605584905256544395953 160255954188678942408296965)
    ·
      refine ⟨30047991410377301701555681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160255954188678942408296965 30047991410377301701555681)
      ·
        refine ⟨22535993557782976276166761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30047991410377301701555681 22535993557782976276166761)
        ·
          refine ⟨16901995168337232207125071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22535993557782976276166761 16901995168337232207125071)
          ·
            refine ⟨25352992752505848310687607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16901995168337232207125071 25352992752505848310687607)
            ·
              refine ⟨38029489128758772466031411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25352992752505848310687607 38029489128758772466031411)
              ·
                refine ⟨57044233693138158699047117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38029489128758772466031411 57044233693138158699047117)
                ·
                  refine ⟨21391587634926809512142669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57044233693138158699047117 21391587634926809512142669)
                  ·
                    refine ⟨8021845363097553567053501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21391587634926809512142669 8021845363097553567053501)
                    ·
                      refine ⟨3008192011161582587645063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8021845363097553567053501 3008192011161582587645063)
                      ·
                        rfl

theorem cell23_5858433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_5858433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858433 prefixEnd_5858433 := by exact prefixLift 5858433
  have htrace : WordTrace (prefixWord ++ tailWord_5858433) baseStart_5858433 baseEnd_5858433 := by
    simpa [prefixWord, tailWord_5858433, baseEnd_5858433] using wordTrace_append hprefix tailTrace_5858433
  have hstable : (prefixWord ++ tailWord_5858433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858433).length < 2 ^ (prefixWord ++ tailWord_5858433).sum := by decide
  have hdescent : baseEnd_5858433 < baseStart_5858433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858437 : List Nat := [1, 3, 1, 1, 6, 1, 3, 1, 1, 2, 3]
def baseStart_5858437 : Nat := 118140960795 + 5858437 * 2 ^ 59
def prefixEnd_5858437 : Nat := 4983230072969 + 3 ^ 40 * 5858437 * 2
def baseEnd_5858437 : Nat := 3008194065084200571995045

theorem tailTrace_5858437 : CollatzResearch.WordTrace tailWord_5858437 prefixEnd_5858437 3008194065084200571995045 := by
  unfold tailWord_5858437
  simp only [CollatzResearch.WordTrace]
  refine ⟨213674751476890765227541565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142449834317927176818361043 213674751476890765227541565)
  ·
    refine ⟨80128031803834036960328087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213674751476890765227541565 80128031803834036960328087)
    ·
      refine ⟨120192047705751055440492131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80128031803834036960328087 120192047705751055440492131)
      ·
        refine ⟨180288071558626583160738197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120192047705751055440492131 180288071558626583160738197)
        ·
          refine ⟨8451003354310621085659603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 180288071558626583160738197 8451003354310621085659603)
          ·
            refine ⟨12676505031465931628489405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8451003354310621085659603 12676505031465931628489405)
            ·
              refine ⟨4753689386799724360683527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12676505031465931628489405 4753689386799724360683527)
              ·
                refine ⟨7130534080199586541025291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4753689386799724360683527 7130534080199586541025291)
                ·
                  refine ⟨10695801120299379811537937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7130534080199586541025291 10695801120299379811537937)
                  ·
                    refine ⟨8021850840224534858653453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10695801120299379811537937 8021850840224534858653453)
                    ·
                      refine ⟨3008194065084200571995045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8021850840224534858653453 3008194065084200571995045)
                      ·
                        rfl

theorem cell23_5858437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 1, 2, 3].length) (baseStart_5858437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858437 prefixEnd_5858437 := by exact prefixLift 5858437
  have htrace : WordTrace (prefixWord ++ tailWord_5858437) baseStart_5858437 baseEnd_5858437 := by
    simpa [prefixWord, tailWord_5858437, baseEnd_5858437] using wordTrace_append hprefix tailTrace_5858437
  have hstable : (prefixWord ++ tailWord_5858437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858437).length < 2 ^ (prefixWord ++ tailWord_5858437).sum := by decide
  have hdescent : baseEnd_5858437 < baseStart_5858437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858460 : List Nat := [2, 2, 3, 2, 1, 2, 1, 2, 3, 3, 2]
def baseStart_5858460 : Nat := 118140960795 + 5858460 * 2 ^ 59
def prefixEnd_5858460 : Nat := 4983230072969 + 3 ^ 40 * 5858460 * 2
def baseEnd_5858460 : Nat := 3008205875139253982007439

theorem tailTrace_5858460 : CollatzResearch.WordTrace tailWord_5858460 prefixEnd_5858460 3008205875139253982007439 := by
  unfold tailWord_5858460
  simp only [CollatzResearch.WordTrace]
  refine ⟨106837795177903720077814417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142450393570538293437085889 106837795177903720077814417)
  ·
    refine ⟨80128346383427790058360813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106837795177903720077814417 80128346383427790058360813)
    ·
      refine ⟨30048129893785421271885305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80128346383427790058360813 30048129893785421271885305)
      ·
        refine ⟨22536097420339065953913979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30048129893785421271885305 22536097420339065953913979)
        ·
          refine ⟨33804146130508598930870969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22536097420339065953913979 33804146130508598930870969)
          ·
            refine ⟨25353109597881449198153227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33804146130508598930870969 25353109597881449198153227)
            ·
              refine ⟨38029664396822173797229841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25353109597881449198153227 38029664396822173797229841)
              ·
                refine ⟨28522248297616630347922381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38029664396822173797229841 28522248297616630347922381)
                ·
                  refine ⟨10695843111606236380470893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28522248297616630347922381 10695843111606236380470893)
                  ·
                    refine ⟨4010941166852338642676585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10695843111606236380470893 4010941166852338642676585)
                    ·
                      refine ⟨3008205875139253982007439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4010941166852338642676585 3008205875139253982007439)
                      ·
                        rfl

theorem cell23_5858460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_5858460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858460 prefixEnd_5858460 := by exact prefixLift 5858460
  have htrace : WordTrace (prefixWord ++ tailWord_5858460) baseStart_5858460 baseEnd_5858460 := by
    simpa [prefixWord, tailWord_5858460, baseEnd_5858460] using wordTrace_append hprefix tailTrace_5858460
  have hstable : (prefixWord ++ tailWord_5858460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858460).length < 2 ^ (prefixWord ++ tailWord_5858460).sum := by decide
  have hdescent : baseEnd_5858460 < baseStart_5858460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858476 : List Nat := [2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 5]
def baseStart_5858476 : Nat := 118140960795 + 5858476 * 2 ^ 59
def prefixEnd_5858476 : Nat := 4983230072969 + 3 ^ 40 * 5858476 * 2
def baseEnd_5858476 : Nat := 3008214090829725919407365

theorem tailTrace_5858476 : CollatzResearch.WordTrace tailWord_5858476 prefixEnd_5858476 3008214090829725919407365 := by
  unfold tailWord_5858476
  simp only [CollatzResearch.WordTrace]
  refine ⟨106838086961874737444105641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142450782615832983258807521 106838086961874737444105641)
  ·
    refine ⟨80128565221406053083079231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106838086961874737444105641 80128565221406053083079231)
    ·
      refine ⟨120192847832109079624618847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80128565221406053083079231 120192847832109079624618847)
      ·
        refine ⟨180289271748163619436928271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120192847832109079624618847 180289271748163619436928271)
        ·
          refine ⟨270433907622245429155392407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180289271748163619436928271 270433907622245429155392407)
          ·
            refine ⟨405650861433368143733088611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270433907622245429155392407 405650861433368143733088611)
            ·
              refine ⟨608476292150052215599632917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 405650861433368143733088611 608476292150052215599632917)
              ·
                refine ⟨28522326194533697606232793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 608476292150052215599632917 28522326194533697606232793)
                ·
                  refine ⟨21391744645900273204674595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28522326194533697606232793 21391744645900273204674595)
                  ·
                    refine ⟨32087616968850409807011893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21391744645900273204674595 32087616968850409807011893)
                    ·
                      refine ⟨3008214090829725919407365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32087616968850409807011893 3008214090829725919407365)
                      ·
                        rfl

theorem cell23_5858476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_5858476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858476 prefixEnd_5858476 := by exact prefixLift 5858476
  have htrace : WordTrace (prefixWord ++ tailWord_5858476) baseStart_5858476 baseEnd_5858476 := by
    simpa [prefixWord, tailWord_5858476, baseEnd_5858476] using wordTrace_append hprefix tailTrace_5858476
  have hstable : (prefixWord ++ tailWord_5858476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858476).length < 2 ^ (prefixWord ++ tailWord_5858476).sum := by decide
  have hdescent : baseEnd_5858476 < baseStart_5858476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858490 : List Nat := [3, 1, 1, 1, 2, 2, 1, 4, 4, 2, 2]
def baseStart_5858490 : Nat := 118140960795 + 5858490 * 2 ^ 59
def prefixEnd_5858490 : Nat := 4983230072969 + 3 ^ 40 * 5858490 * 2
def baseEnd_5858490 : Nat := 3008221279558888864632301

theorem tailTrace_5858490 : CollatzResearch.WordTrace tailWord_5858490 prefixEnd_5858490 3008221279558888864632301 := by
  unfold tailWord_5858490
  simp only [CollatzResearch.WordTrace]
  refine ⟨53419171136424688819805231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142451123030465836852813949 53419171136424688819805231)
  ·
    refine ⟨80128756704637033229707847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53419171136424688819805231 80128756704637033229707847)
    ·
      refine ⟨120193135056955549844561771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80128756704637033229707847 120193135056955549844561771)
      ·
        refine ⟨180289702585433324766842657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120193135056955549844561771 180289702585433324766842657)
        ·
          refine ⟨135217276939074993575131993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180289702585433324766842657 135217276939074993575131993)
          ·
            refine ⟨101412957704306245181348995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135217276939074993575131993 101412957704306245181348995)
            ·
              refine ⟨152119436556459367772023493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101412957704306245181348995 152119436556459367772023493)
              ·
                refine ⟨28522394354336131457254405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152119436556459367772023493 28522394354336131457254405)
                ·
                  refine ⟨5347948941438024648235201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28522394354336131457254405 5347948941438024648235201)
                  ·
                    refine ⟨4010961706078518486176401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5347948941438024648235201 4010961706078518486176401)
                    ·
                      refine ⟨3008221279558888864632301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4010961706078518486176401 3008221279558888864632301)
                      ·
                        rfl

theorem cell23_5858490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 4, 2, 2].length) (baseStart_5858490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858490 prefixEnd_5858490 := by exact prefixLift 5858490
  have htrace : WordTrace (prefixWord ++ tailWord_5858490) baseStart_5858490 baseEnd_5858490 := by
    simpa [prefixWord, tailWord_5858490, baseEnd_5858490] using wordTrace_append hprefix tailTrace_5858490
  have hstable : (prefixWord ++ tailWord_5858490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858490).length < 2 ^ (prefixWord ++ tailWord_5858490).sum := by decide
  have hdescent : baseEnd_5858490 < baseStart_5858490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858494 : List Nat := [4, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2]
def baseStart_5858494 : Nat := 118140960795 + 5858494 * 2 ^ 59
def prefixEnd_5858494 : Nat := 4983230072969 + 3 ^ 40 * 5858494 * 2
def baseEnd_5858494 : Nat := 3008223333481506848982283

theorem tailTrace_5858494 : CollatzResearch.WordTrace tailWord_5858494 prefixEnd_5858494 3008223333481506848982283 := by
  unfold tailWord_5858494
  simp only [CollatzResearch.WordTrace]
  refine ⟨26709603804710532995295817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142451220291789509308244357 26709603804710532995295817)
  ·
    refine ⟨20032202853532899746471863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26709603804710532995295817 20032202853532899746471863)
    ·
      refine ⟨30048304280299349619707795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20032202853532899746471863 30048304280299349619707795)
      ·
        refine ⟨45072456420449024429561693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30048304280299349619707795 45072456420449024429561693)
        ·
          refine ⟨16902171157668384161085635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45072456420449024429561693 16902171157668384161085635)
          ·
            refine ⟨25353256736502576241628453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16902171157668384161085635 25353256736502576241628453)
            ·
              refine ⟨4753735638094233045305335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25353256736502576241628453 4753735638094233045305335)
              ·
                refine ⟨7130603457141349567958003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4753735638094233045305335 7130603457141349567958003)
                ·
                  refine ⟨10695905185712024351937005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7130603457141349567958003 10695905185712024351937005)
                  ·
                    refine ⟨4010964444642009131976377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10695905185712024351937005 4010964444642009131976377)
                    ·
                      refine ⟨3008223333481506848982283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4010964444642009131976377 3008223333481506848982283)
                      ·
                        rfl

theorem cell23_5858494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_5858494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858494 prefixEnd_5858494 := by exact prefixLift 5858494
  have htrace : WordTrace (prefixWord ++ tailWord_5858494) baseStart_5858494 baseEnd_5858494 := by
    simpa [prefixWord, tailWord_5858494, baseEnd_5858494] using wordTrace_append hprefix tailTrace_5858494
  have hstable : (prefixWord ++ tailWord_5858494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858494).length < 2 ^ (prefixWord ++ tailWord_5858494).sum := by decide
  have hdescent : baseEnd_5858494 < baseStart_5858494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858550 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2]
def baseStart_5858550 : Nat := 118140960795 + 5858550 * 2 ^ 59
def prefixEnd_5858550 : Nat := 4983230072969 + 3 ^ 40 * 5858550 * 2
def baseEnd_5858550 : Nat := 3008252088398158629882025

theorem tailTrace_5858550 : CollatzResearch.WordTrace tailWord_5858550 prefixEnd_5858550 3008252088398158629882025 := by
  unfold tailWord_5858550
  simp only [CollatzResearch.WordTrace]
  refine ⟨13354929557842586595400319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142452581950320923684270069 13354929557842586595400319)
  ·
    refine ⟨20032394336763879893100479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13354929557842586595400319 20032394336763879893100479)
    ·
      refine ⟨30048591505145819839650719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20032394336763879893100479 30048591505145819839650719)
      ·
        refine ⟨45072887257718729759476079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30048591505145819839650719 45072887257718729759476079)
        ·
          refine ⟨67609330886578094639214119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45072887257718729759476079 67609330886578094639214119)
          ·
            refine ⟨101413996329867141958821179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67609330886578094639214119 101413996329867141958821179)
            ·
              refine ⟨152120994494800712938231769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101413996329867141958821179 152120994494800712938231769)
              ·
                refine ⟨114090745871100534703673827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152120994494800712938231769 114090745871100534703673827)
                ·
                  refine ⟨171136118806650802055510741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114090745871100534703673827 171136118806650802055510741)
                  ·
                    refine ⟨4011002784530878173176033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 171136118806650802055510741 4011002784530878173176033)
                    ·
                      refine ⟨3008252088398158629882025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4011002784530878173176033 3008252088398158629882025)
                      ·
                        rfl

theorem cell23_5858550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_5858550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858550 prefixEnd_5858550 := by exact prefixLift 5858550
  have htrace : WordTrace (prefixWord ++ tailWord_5858550) baseStart_5858550 baseEnd_5858550 := by
    simpa [prefixWord, tailWord_5858550, baseEnd_5858550] using wordTrace_append hprefix tailTrace_5858550
  have hstable : (prefixWord ++ tailWord_5858550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858550).length < 2 ^ (prefixWord ++ tailWord_5858550).sum := by decide
  have hdescent : baseEnd_5858550 < baseStart_5858550 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858563 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 4]
def baseStart_5858563 : Nat := 118140960795 + 5858563 * 2 ^ 59
def prefixEnd_5858563 : Nat := 4983230072969 + 3 ^ 40 * 5858563 * 2
def baseEnd_5858563 : Nat := 3008258763646667079019465

theorem tailTrace_5858563 : CollatzResearch.WordTrace tailWord_5858563 prefixEnd_5858563 3008258763646667079019465 := by
  unfold tailWord_5858563
  simp only [CollatzResearch.WordTrace]
  refine ⟨213679347074434288746628343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142452898049622859164418895 213679347074434288746628343)
  ·
    refine ⟨320519020611651433119942515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213679347074434288746628343 320519020611651433119942515)
    ·
      refine ⟨480778530917477149679913773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320519020611651433119942515 480778530917477149679913773)
      ·
        refine ⟨180291949094053931129967665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 480778530917477149679913773 180291949094053931129967665)
        ·
          refine ⟨135218961820540448347475749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180291949094053931129967665 135218961820540448347475749)
          ·
            refine ⟨25353555341351334065151703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135218961820540448347475749 25353555341351334065151703)
            ·
              refine ⟨38030333012027001097727555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25353555341351334065151703 38030333012027001097727555)
              ·
                refine ⟨57045499518040501646591333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38030333012027001097727555 57045499518040501646591333)
                ·
                  refine ⟨10696031159632594058735875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57045499518040501646591333 10696031159632594058735875)
                  ·
                    refine ⟨16044046739448891088103813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10696031159632594058735875 16044046739448891088103813)
                    ·
                      refine ⟨3008258763646667079019465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16044046739448891088103813 3008258763646667079019465)
                      ·
                        rfl

theorem cell23_5858563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 4].length) (baseStart_5858563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858563 prefixEnd_5858563 := by exact prefixLift 5858563
  have htrace : WordTrace (prefixWord ++ tailWord_5858563) baseStart_5858563 baseEnd_5858563 := by
    simpa [prefixWord, tailWord_5858563, baseEnd_5858563] using wordTrace_append hprefix tailTrace_5858563
  have hstable : (prefixWord ++ tailWord_5858563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858563).length < 2 ^ (prefixWord ++ tailWord_5858563).sum := by decide
  have hdescent : baseEnd_5858563 < baseStart_5858563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858576 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 6]
def baseStart_5858576 : Nat := 118140960795 + 5858576 * 2 ^ 59
def prefixEnd_5858576 : Nat := 4983230072969 + 3 ^ 40 * 5858576 * 2
def baseEnd_5858576 : Nat := 3008265438895175528156905

theorem tailTrace_5858576 : CollatzResearch.WordTrace tailWord_5858576 prefixEnd_5858576 3008265438895175528156905 := by
  unfold tailWord_5858576
  simp only [CollatzResearch.WordTrace]
  refine ⟨106839910611693595983425791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142453214148924794644567721 106839910611693595983425791)
  ·
    refine ⟨160259865917540393975138687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106839910611693595983425791 160259865917540393975138687)
    ·
      refine ⟨240389798876310590962708031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160259865917540393975138687 240389798876310590962708031)
      ·
        refine ⟨360584698314465886444062047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240389798876310590962708031 360584698314465886444062047)
        ·
          refine ⟨540877047471698829666093071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360584698314465886444062047 540877047471698829666093071)
          ·
            refine ⟨811315571207548244499139607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540877047471698829666093071 811315571207548244499139607)
            ·
              refine ⟨1216973356811322366748709411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 811315571207548244499139607 1216973356811322366748709411)
              ·
                refine ⟨1825460035216983550123064117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1216973356811322366748709411 1825460035216983550123064117)
                ·
                  refine ⟨171136878301592207824037261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1825460035216983550123064117 171136878301592207824037261)
                  ·
                    refine ⟨64176329363097077934013973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 171136878301592207824037261 64176329363097077934013973)
                    ·
                      refine ⟨3008265438895175528156905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64176329363097077934013973 3008265438895175528156905)
                      ·
                        rfl

theorem cell23_5858576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 6].length) (baseStart_5858576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858576 prefixEnd_5858576 := by exact prefixLift 5858576
  have htrace : WordTrace (prefixWord ++ tailWord_5858576) baseStart_5858576 baseEnd_5858576 := by
    simpa [prefixWord, tailWord_5858576, baseEnd_5858576] using wordTrace_append hprefix tailTrace_5858576
  have hstable : (prefixWord ++ tailWord_5858576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858576).length < 2 ^ (prefixWord ++ tailWord_5858576).sum := by decide
  have hdescent : baseEnd_5858576 < baseStart_5858576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858620 : List Nat := [2, 2, 2, 2, 1, 4, 2, 2, 6]
def baseStart_5858620 : Nat := 118140960795 + 5858620 * 2 ^ 59
def prefixEnd_5858620 : Nat := 4983230072969 + 3 ^ 40 * 5858620 * 2
def baseEnd_5858620 : Nat := 334254225782663706222967

theorem tailTrace_5858620 : CollatzResearch.WordTrace tailWord_5858620 prefixEnd_5858620 334254225782663706222967 := by
  unfold tailWord_5858620
  simp only [CollatzResearch.WordTrace]
  refine ⟨106840713017613893740726657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142454284023485191654302209 106840713017613893740726657)
  ·
    refine ⟨80130534763210420305544993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106840713017613893740726657 80130534763210420305544993)
    ·
      refine ⟨60097901072407815229158745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80130534763210420305544993 60097901072407815229158745)
      ·
        refine ⟨45073425804305861421869059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60097901072407815229158745 45073425804305861421869059)
        ·
          refine ⟨67610138706458792132803589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45073425804305861421869059 67610138706458792132803589)
          ·
            refine ⟨12676901007461023524900673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67610138706458792132803589 12676901007461023524900673)
            ·
              refine ⟨9507675755595767643675505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12676901007461023524900673 9507675755595767643675505)
              ·
                refine ⟨7130756816696825732756629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9507675755595767643675505 7130756816696825732756629)
                ·
                  refine ⟨334254225782663706222967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7130756816696825732756629 334254225782663706222967)
                  ·
                    rfl

theorem cell23_5858620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 6].length) (baseStart_5858620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858620 prefixEnd_5858620 := by exact prefixLift 5858620
  have htrace : WordTrace (prefixWord ++ tailWord_5858620) baseStart_5858620 baseEnd_5858620 := by
    simpa [prefixWord, tailWord_5858620, baseEnd_5858620] using wordTrace_append hprefix tailTrace_5858620
  have hstable : (prefixWord ++ tailWord_5858620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858620).length < 2 ^ (prefixWord ++ tailWord_5858620).sum := by decide
  have hdescent : baseEnd_5858620 < baseStart_5858620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858633 : List Nat := [1, 2, 1, 1, 2, 3, 3, 2, 3, 5]
def baseStart_5858633 : Nat := 118140960795 + 5858633 * 2 ^ 59
def prefixEnd_5858633 : Nat := 4983230072969 + 3 ^ 40 * 5858633 * 2
def baseEnd_5858633 : Nat := 1002764902430827268381381

theorem tailTrace_5858633 : CollatzResearch.WordTrace tailWord_5858633 prefixEnd_5858633 1002764902430827268381381 := by
  unfold tailWord_5858633
  simp only [CollatzResearch.WordTrace]
  refine ⟨213681900184180690701676553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142454600122787127134451035 213681900184180690701676553)
  ·
    refine ⟨160261425138135518026257415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213681900184180690701676553 160261425138135518026257415)
    ·
      refine ⟨240392137707203277039386123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160261425138135518026257415 240392137707203277039386123)
      ·
        refine ⟨360588206560804915559079185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240392137707203277039386123 360588206560804915559079185)
        ·
          refine ⟨270441154920603686669309389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360588206560804915559079185 270441154920603686669309389)
          ·
            refine ⟨101415433095226382500991021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 270441154920603686669309389 101415433095226382500991021)
            ·
              refine ⟨38030787410709893437871633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101415433095226382500991021 38030787410709893437871633)
              ·
                refine ⟨28523090558032420078403725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38030787410709893437871633 28523090558032420078403725)
                ·
                  refine ⟨10696158959262157529401397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28523090558032420078403725 10696158959262157529401397)
                  ·
                    refine ⟨1002764902430827268381381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10696158959262157529401397 1002764902430827268381381)
                    ·
                      rfl

theorem cell23_5858633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 5].length) (baseStart_5858633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858633 prefixEnd_5858633 := by exact prefixLift 5858633
  have htrace : WordTrace (prefixWord ++ tailWord_5858633) baseStart_5858633 baseEnd_5858633 := by
    simpa [prefixWord, tailWord_5858633, baseEnd_5858633] using wordTrace_append hprefix tailTrace_5858633
  have hstable : (prefixWord ++ tailWord_5858633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858633).length < 2 ^ (prefixWord ++ tailWord_5858633).sum := by decide
  have hdescent : baseEnd_5858633 < baseStart_5858633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858640 : List Nat := [2, 1, 1, 1, 1, 5, 2, 2, 1, 5, 2]
def baseStart_5858640 : Nat := 118140960795 + 5858640 * 2 ^ 59
def prefixEnd_5858640 : Nat := 4983230072969 + 3 ^ 40 * 5858640 * 2
def baseEnd_5858640 : Nat := 3008298301657063277756611

theorem tailTrace_5858640 : CollatzResearch.WordTrace tailWord_5858640 prefixEnd_5858640 3008298301657063277756611 := by
  unfold tailWord_5858640
  simp only [CollatzResearch.WordTrace]
  refine ⟨106841077747577665448590687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142454770330103553931454249 106841077747577665448590687)
  ·
    refine ⟨160261616621366498172886031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106841077747577665448590687 160261616621366498172886031)
    ·
      refine ⟨240392424932049747259329047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160261616621366498172886031 240392424932049747259329047)
      ·
        refine ⟨360588637398074620888993571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240392424932049747259329047 360588637398074620888993571)
        ·
          refine ⟨540882956097111931333490357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360588637398074620888993571 540882956097111931333490357)
          ·
            refine ⟨50707777134104243562514721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 540882956097111931333490357 50707777134104243562514721)
            ·
              refine ⟨38030832850578182671886041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50707777134104243562514721 38030832850578182671886041)
              ·
                refine ⟨28523124637933637003914531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38030832850578182671886041 28523124637933637003914531)
                ·
                  refine ⟨42784686956900455505871797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28523124637933637003914531 42784686956900455505871797)
                  ·
                    refine ⟨4011064402209417703675481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42784686956900455505871797 4011064402209417703675481)
                    ·
                      refine ⟨3008298301657063277756611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4011064402209417703675481 3008298301657063277756611)
                      ·
                        rfl

theorem cell23_5858640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 1, 5, 2].length) (baseStart_5858640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858640 prefixEnd_5858640 := by exact prefixLift 5858640
  have htrace : WordTrace (prefixWord ++ tailWord_5858640) baseStart_5858640 baseEnd_5858640 := by
    simpa [prefixWord, tailWord_5858640, baseEnd_5858640] using wordTrace_append hprefix tailTrace_5858640
  have hstable : (prefixWord ++ tailWord_5858640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858640).length < 2 ^ (prefixWord ++ tailWord_5858640).sum := by decide
  have hdescent : baseEnd_5858640 < baseStart_5858640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858647 : List Nat := [1, 1, 3, 2, 3, 3, 1, 2, 3, 1, 3]
def baseStart_5858647 : Nat := 118140960795 + 5858647 * 2 ^ 59
def prefixEnd_5858647 : Nat := 4983230072969 + 3 ^ 40 * 5858647 * 2
def baseEnd_5858647 : Nat := 3008301896021644750369079

theorem tailTrace_5858647 : CollatzResearch.WordTrace tailWord_5858647 prefixEnd_5858647 3008301896021644750369079 := by
  unfold tailWord_5858647
  simp only [CollatzResearch.WordTrace]
  refine ⟨213682410806129971092686195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142454940537419980728457463 213682410806129971092686195)
  ·
    refine ⟨320523616209194956639029293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213682410806129971092686195 320523616209194956639029293)
    ·
      refine ⟨120196356078448108739635985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 320523616209194956639029293 120196356078448108739635985)
      ·
        refine ⟨90147267058836081554726989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120196356078448108739635985 90147267058836081554726989)
        ·
          refine ⟨33805225147063530583022621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90147267058836081554726989 33805225147063530583022621)
          ·
            refine ⟨12676959430148823968633483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33805225147063530583022621 12676959430148823968633483)
            ·
              refine ⟨19015439145223235952950225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12676959430148823968633483 19015439145223235952950225)
              ·
                refine ⟨14261579358917426964712669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19015439145223235952950225 14261579358917426964712669)
                ·
                  refine ⟨5348092259594035111767251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14261579358917426964712669 5348092259594035111767251)
                  ·
                    refine ⟨8022138389391052667650877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5348092259594035111767251 8022138389391052667650877)
                    ·
                      refine ⟨3008301896021644750369079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8022138389391052667650877 3008301896021644750369079)
                      ·
                        rfl

theorem cell23_5858647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 3, 1, 3].length) (baseStart_5858647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858647 prefixEnd_5858647 := by exact prefixLift 5858647
  have htrace : WordTrace (prefixWord ++ tailWord_5858647) baseStart_5858647 baseEnd_5858647 := by
    simpa [prefixWord, tailWord_5858647, baseEnd_5858647] using wordTrace_append hprefix tailTrace_5858647
  have hstable : (prefixWord ++ tailWord_5858647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858647).length < 2 ^ (prefixWord ++ tailWord_5858647).sum := by decide
  have hdescent : baseEnd_5858647 < baseStart_5858647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858683 : List Nat := [1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 6]
def baseStart_5858683 : Nat := 118140960795 + 5858683 * 2 ^ 59
def prefixEnd_5858683 : Nat := 4983230072969 + 3 ^ 40 * 5858683 * 2
def baseEnd_5858683 : Nat := 3008320381325206609518913

theorem tailTrace_5858683 : CollatzResearch.WordTrace tailWord_5858683 prefixEnd_5858683 3008320381325206609518913 := by
  unfold tailWord_5858683
  simp only [CollatzResearch.WordTrace]
  refine ⟨213683723833999549240996703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142455815889333032827331135 213683723833999549240996703)
  ·
    refine ⟨320525585750999323861495055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213683723833999549240996703 320525585750999323861495055)
    ·
      refine ⟨480788378626498985792242583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320525585750999323861495055 480788378626498985792242583)
      ·
        refine ⟨721182567939748478688363875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480788378626498985792242583 721182567939748478688363875)
        ·
          refine ⟨1081773851909622718032545813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 721182567939748478688363875 1081773851909622718032545813)
          ·
            refine ⟨50708149308263564907775585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1081773851909622718032545813 50708149308263564907775585)
            ·
              refine ⟨38031111981197673680831689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50708149308263564907775585 38031111981197673680831689)
              ·
                refine ⟨28523333985898255260623767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38031111981197673680831689 28523333985898255260623767)
                ·
                  refine ⟨42785000978847382890935651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28523333985898255260623767 42785000978847382890935651)
                  ·
                    refine ⟨64177501468271074336403477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42785000978847382890935651 64177501468271074336403477)
                    ·
                      refine ⟨3008320381325206609518913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64177501468271074336403477 3008320381325206609518913)
                      ·
                        rfl

theorem cell23_5858683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 6].length) (baseStart_5858683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858683 prefixEnd_5858683 := by exact prefixLift 5858683
  have htrace : WordTrace (prefixWord ++ tailWord_5858683) baseStart_5858683 baseEnd_5858683 := by
    simpa [prefixWord, tailWord_5858683, baseEnd_5858683] using wordTrace_append hprefix tailTrace_5858683
  have hstable : (prefixWord ++ tailWord_5858683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858683).length < 2 ^ (prefixWord ++ tailWord_5858683).sum := by decide
  have hdescent : baseEnd_5858683 < baseStart_5858683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858697 : List Nat := [1, 2, 1, 1, 7, 2, 1, 1, 1, 6]
def baseStart_5858697 : Nat := 118140960795 + 5858697 * 2 ^ 59
def prefixEnd_5858697 : Nat := 4983230072969 + 3 ^ 40 * 5858697 * 2
def baseEnd_5858697 : Nat := 1002775856684789851581283

theorem tailTrace_5858697 : CollatzResearch.WordTrace tailWord_5858697 prefixEnd_5858697 1002775856684789851581283 := by
  unfold tailWord_5858697
  simp only [CollatzResearch.WordTrace]
  refine ⟨213684234455948829632006345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142456156303965886421337563 213684234455948829632006345)
  ·
    refine ⟨160263175841961622224004759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213684234455948829632006345 160263175841961622224004759)
    ·
      refine ⟨240394763762942433336007139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160263175841961622224004759 240394763762942433336007139)
      ·
        refine ⟨360592145644413650004010709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240394763762942433336007139 360592145644413650004010709)
        ·
          refine ⟨8451378413540944921969001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 360592145644413650004010709 8451378413540944921969001)
          ·
            refine ⟨6338533810155708691476751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8451378413540944921969001 6338533810155708691476751)
            ·
              refine ⟨9507800715233563037215127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6338533810155708691476751 9507800715233563037215127)
              ·
                refine ⟨14261701072850344555822691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9507800715233563037215127 14261701072850344555822691)
                ·
                  refine ⟨21392551609275516833734037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14261701072850344555822691 21392551609275516833734037)
                  ·
                    refine ⟨1002775856684789851581283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21392551609275516833734037 1002775856684789851581283)
                    ·
                      rfl

theorem cell23_5858697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 6].length) (baseStart_5858697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858697 prefixEnd_5858697 := by exact prefixLift 5858697
  have htrace : WordTrace (prefixWord ++ tailWord_5858697) baseStart_5858697 baseEnd_5858697 := by
    simpa [prefixWord, tailWord_5858697, baseEnd_5858697] using wordTrace_append hprefix tailTrace_5858697
  have hstable : (prefixWord ++ tailWord_5858697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858697).length < 2 ^ (prefixWord ++ tailWord_5858697).sum := by decide
  have hdescent : baseEnd_5858697 < baseStart_5858697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858720 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 3]
def baseStart_5858720 : Nat := 118140960795 + 5858720 * 2 ^ 59
def prefixEnd_5858720 : Nat := 4983230072969 + 3 ^ 40 * 5858720 * 2
def baseEnd_5858720 : Nat := 3008339380109422964756243

theorem tailTrace_5858720 : CollatzResearch.WordTrace tailWord_5858720 prefixEnd_5858720 3008339380109422964756243 := by
  unfold tailWord_5858720
  simp only [CollatzResearch.WordTrace]
  refine ⟨106842536667432752280046807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142456715556577003040062409 106842536667432752280046807)
  ·
    refine ⟨160263805001149128420070211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106842536667432752280046807 160263805001149128420070211)
    ·
      refine ⟨240395707501723692630105317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160263805001149128420070211 240395707501723692630105317)
      ·
        refine ⟨45074195156573192368144747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 240395707501723692630105317 45074195156573192368144747)
        ·
          refine ⟨67611292734859788552217121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45074195156573192368144747 67611292734859788552217121)
          ·
            refine ⟨50708469551144841414162841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67611292734859788552217121 50708469551144841414162841)
            ·
              refine ⟨38031352163358631060622131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50708469551144841414162841 38031352163358631060622131)
              ·
                refine ⟨57047028245037946590933197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38031352163358631060622131 57047028245037946590933197)
                ·
                  refine ⟨21392635591889229971599949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57047028245037946590933197 21392635591889229971599949)
                  ·
                    refine ⟨8022238346958461239349981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21392635591889229971599949 8022238346958461239349981)
                    ·
                      refine ⟨3008339380109422964756243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8022238346958461239349981 3008339380109422964756243)
                      ·
                        rfl

theorem cell23_5858720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_5858720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858720 prefixEnd_5858720 := by exact prefixLift 5858720
  have htrace : WordTrace (prefixWord ++ tailWord_5858720) baseStart_5858720 baseEnd_5858720 := by
    simpa [prefixWord, tailWord_5858720, baseEnd_5858720] using wordTrace_append hprefix tailTrace_5858720
  have hstable : (prefixWord ++ tailWord_5858720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858720).length < 2 ^ (prefixWord ++ tailWord_5858720).sum := by decide
  have hdescent : baseEnd_5858720 < baseStart_5858720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858737 : List Nat := [1, 2, 2, 4, 1, 1, 1, 3, 4, 1, 3]
def baseStart_5858737 : Nat := 118140960795 + 5858737 * 2 ^ 59
def prefixEnd_5858737 : Nat := 4983230072969 + 3 ^ 40 * 5858737 * 2
def baseEnd_5858737 : Nat := 3008348109280549398243665

theorem tailTrace_5858737 : CollatzResearch.WordTrace tailWord_5858737 prefixEnd_5858737 3008348109280549398243665 := by
  unfold tailWord_5858737
  simp only [CollatzResearch.WordTrace]
  refine ⟨213685693375803916463462465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142457128917202610975641643 213685693375803916463462465)
  ·
    refine ⟨160264270031852937347596849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213685693375803916463462465 160264270031852937347596849)
    ·
      refine ⟨120198202523889703010697637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160264270031852937347596849 120198202523889703010697637)
      ·
        refine ⟨22537162973229319314505807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120198202523889703010697637 22537162973229319314505807)
        ·
          refine ⟨33805744459843978971758711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22537162973229319314505807 33805744459843978971758711)
          ·
            refine ⟨50708616689765968457638067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33805744459843978971758711 50708616689765968457638067)
            ·
              refine ⟨76062925034648952686457101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50708616689765968457638067 76062925034648952686457101)
              ·
                refine ⟨28523596887993357257421413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76062925034648952686457101 28523596887993357257421413)
                ·
                  refine ⟨5348174416498754485766515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28523596887993357257421413 5348174416498754485766515)
                  ·
                    refine ⟨8022261624748131728649773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5348174416498754485766515 8022261624748131728649773)
                    ·
                      refine ⟨3008348109280549398243665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8022261624748131728649773 3008348109280549398243665)
                      ·
                        rfl

theorem cell23_5858737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_5858737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858737 prefixEnd_5858737 := by exact prefixLift 5858737
  have htrace : WordTrace (prefixWord ++ tailWord_5858737) baseStart_5858737 baseEnd_5858737 := by
    simpa [prefixWord, tailWord_5858737, baseEnd_5858737] using wordTrace_append hprefix tailTrace_5858737
  have hstable : (prefixWord ++ tailWord_5858737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858737).length < 2 ^ (prefixWord ++ tailWord_5858737).sum := by decide
  have hdescent : baseEnd_5858737 < baseStart_5858737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858748 : List Nat := [2, 2, 2, 4, 3, 1, 2, 1, 2, 4]
def baseStart_5858748 : Nat := 118140960795 + 5858748 * 2 ^ 59
def prefixEnd_5858748 : Nat := 4983230072969 + 3 ^ 40 * 5858748 * 2
def baseEnd_5858748 : Nat := 1002784585855916285068705

theorem tailTrace_5858748 : CollatzResearch.WordTrace tailWord_5858748 prefixEnd_5858748 1002784585855916285068705 := by
  unfold tailWord_5858748
  simp only [CollatzResearch.WordTrace]
  refine ⟨106843047289382032671056449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142457396385842710228075265 106843047289382032671056449)
  ·
    refine ⟨80132285467036524503292337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106843047289382032671056449 80132285467036524503292337)
    ·
      refine ⟨60099214100277393377469253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80132285467036524503292337 60099214100277393377469253)
      ·
        refine ⟨11268602643802011258275485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60099214100277393377469253 11268602643802011258275485)
        ·
          refine ⟨4225725991425754221853307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11268602643802011258275485 4225725991425754221853307)
          ·
            refine ⟨6338588987138631332779961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4225725991425754221853307 6338588987138631332779961)
            ·
              refine ⟨4753941740353973499584971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6338588987138631332779961 4753941740353973499584971)
              ·
                refine ⟨7130912610530960249377457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4753941740353973499584971 7130912610530960249377457)
                ·
                  refine ⟨5348184457898220187033093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7130912610530960249377457 5348184457898220187033093)
                  ·
                    refine ⟨1002784585855916285068705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5348184457898220187033093 1002784585855916285068705)
                    ·
                      rfl

theorem cell23_5858748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 2, 4].length) (baseStart_5858748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858748 prefixEnd_5858748 := by exact prefixLift 5858748
  have htrace : WordTrace (prefixWord ++ tailWord_5858748) baseStart_5858748 baseEnd_5858748 := by
    simpa [prefixWord, tailWord_5858748, baseEnd_5858748] using wordTrace_append hprefix tailTrace_5858748
  have hstable : (prefixWord ++ tailWord_5858748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858748).length < 2 ^ (prefixWord ++ tailWord_5858748).sum := by decide
  have hdescent : baseEnd_5858748 < baseStart_5858748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858764 : List Nat := [2, 2, 1, 4, 2, 2, 1, 1, 3, 3, 2]
def baseStart_5858764 : Nat := 118140960795 + 5858764 * 2 ^ 59
def prefixEnd_5858764 : Nat := 4983230072969 + 3 ^ 40 * 5858764 * 2
def baseEnd_5858764 : Nat := 3008361973258220792606041

theorem tailTrace_5858764 : CollatzResearch.WordTrace tailWord_5858764 prefixEnd_5858764 3008361973258220792606041 := by
  unfold tailWord_5858764
  simp only [CollatzResearch.WordTrace]
  refine ⟨106843339073353050037347673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142457785431137400049796897 106843339073353050037347673)
  ·
    refine ⟨80132504305014787528010755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106843339073353050037347673 80132504305014787528010755)
    ·
      refine ⟨120198756457522181292016133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80132504305014787528010755 120198756457522181292016133)
      ·
        refine ⟨22537266835785408992253025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120198756457522181292016133 22537266835785408992253025)
        ·
          refine ⟨16902950126839056744189769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22537266835785408992253025 16902950126839056744189769)
          ·
            refine ⟨12677212595129292558142327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16902950126839056744189769 12677212595129292558142327)
            ·
              refine ⟨19015818892693938837213491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12677212595129292558142327 19015818892693938837213491)
              ·
                refine ⟨28523728339040908255820237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19015818892693938837213491 28523728339040908255820237)
                ·
                  refine ⟨10696398127140340595932589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28523728339040908255820237 10696398127140340595932589)
                  ·
                    refine ⟨4011149297677627723474721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10696398127140340595932589 4011149297677627723474721)
                    ·
                      refine ⟨3008361973258220792606041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4011149297677627723474721 3008361973258220792606041)
                      ·
                        rfl

theorem cell23_5858764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_5858764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858764 prefixEnd_5858764 := by exact prefixLift 5858764
  have htrace : WordTrace (prefixWord ++ tailWord_5858764) baseStart_5858764 baseEnd_5858764 := by
    simpa [prefixWord, tailWord_5858764, baseEnd_5858764] using wordTrace_append hprefix tailTrace_5858764
  have hstable : (prefixWord ++ tailWord_5858764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858764).length < 2 ^ (prefixWord ++ tailWord_5858764).sum := by decide
  have hdescent : baseEnd_5858764 < baseStart_5858764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858777 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 3, 4, 2]
def baseStart_5858777 : Nat := 118140960795 + 5858777 * 2 ^ 59
def prefixEnd_5858777 : Nat := 4983230072969 + 3 ^ 40 * 5858777 * 2
def baseEnd_5858777 : Nat := 3008368648506729241743481

theorem tailTrace_5858777 : CollatzResearch.WordTrace tailWord_5858777 prefixEnd_5858777 3008368648506729241743481 := by
  unfold tailWord_5858777
  simp only [CollatzResearch.WordTrace]
  refine ⟨213687152295659003294918585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142458101530439335529945723 213687152295659003294918585)
  ·
    refine ⟨160265364221744252471188939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213687152295659003294918585 160265364221744252471188939)
    ·
      refine ⟨240398046332616378706783409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160265364221744252471188939 240398046332616378706783409)
      ·
        refine ⟨180298534749462284030087557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240398046332616378706783409 180298534749462284030087557)
        ·
          refine ⟨33805975265524178255641417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180298534749462284030087557 33805975265524178255641417)
          ·
            refine ⟨25354481449143133691731063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33805975265524178255641417 25354481449143133691731063)
            ·
              refine ⟨38031722173714700537596595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25354481449143133691731063 38031722173714700537596595)
              ·
                refine ⟨57047583260572050806394893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38031722173714700537596595 57047583260572050806394893)
                ·
                  refine ⟨21392843722714519052398085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57047583260572050806394893 21392843722714519052398085)
                  ·
                    refine ⟨4011158198008972322324641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21392843722714519052398085 4011158198008972322324641)
                    ·
                      refine ⟨3008368648506729241743481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4011158198008972322324641 3008368648506729241743481)
                      ·
                        rfl

theorem cell23_5858777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 4, 2].length) (baseStart_5858777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858777 prefixEnd_5858777 := by exact prefixLift 5858777
  have htrace : WordTrace (prefixWord ++ tailWord_5858777) baseStart_5858777 baseEnd_5858777 := by
    simpa [prefixWord, tailWord_5858777, baseEnd_5858777] using wordTrace_append hprefix tailTrace_5858777
  have hstable : (prefixWord ++ tailWord_5858777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858777).length < 2 ^ (prefixWord ++ tailWord_5858777).sum := by decide
  have hdescent : baseEnd_5858777 < baseStart_5858777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858817 : List Nat := [1, 2, 4, 1, 4, 1, 1, 2, 7]
def baseStart_5858817 : Nat := 118140960795 + 5858817 * 2 ^ 59
def prefixEnd_5858817 : Nat := 4983230072969 + 3 ^ 40 * 5858817 * 2
def baseEnd_5858817 : Nat := 334265465303656565027033

theorem tailTrace_5858817 : CollatzResearch.WordTrace tailWord_5858817 prefixEnd_5858817 334265465303656565027033 := by
  unfold tailWord_5858817
  simp only [CollatzResearch.WordTrace]
  refine ⟨213688611215514090126374705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142459074143676060084249803 213688611215514090126374705)
  ·
    refine ⟨160266458411635567594781029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213688611215514090126374705 160266458411635567594781029)
    ·
      refine ⟨30049960952181668924021443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160266458411635567594781029 30049960952181668924021443)
      ·
        refine ⟨45074941428272503386032165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30049960952181668924021443 45074941428272503386032165)
        ·
          refine ⟨8451551517801094384881031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45074941428272503386032165 8451551517801094384881031)
          ·
            refine ⟨12677327276701641577321547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8451551517801094384881031 12677327276701641577321547)
            ·
              refine ⟨19015990915052462365982321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12677327276701641577321547 19015990915052462365982321)
              ·
                refine ⟨14261993186289346774486741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19015990915052462365982321 14261993186289346774486741)
                ·
                  refine ⟨334265465303656565027033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14261993186289346774486741 334265465303656565027033)
                  ·
                    rfl

theorem cell23_5858817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 7].length) (baseStart_5858817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858817 prefixEnd_5858817 := by exact prefixLift 5858817
  have htrace : WordTrace (prefixWord ++ tailWord_5858817) baseStart_5858817 baseEnd_5858817 := by
    simpa [prefixWord, tailWord_5858817, baseEnd_5858817] using wordTrace_append hprefix tailTrace_5858817
  have hstable : (prefixWord ++ tailWord_5858817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858817).length < 2 ^ (prefixWord ++ tailWord_5858817).sum := by decide
  have hdescent : baseEnd_5858817 < baseStart_5858817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858880 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 4]
def baseStart_5858880 : Nat := 118140960795 + 5858880 * 2 ^ 59
def prefixEnd_5858880 : Nat := 4983230072969 + 3 ^ 40 * 5858880 * 2
def baseEnd_5858880 : Nat := 3008421537014142338755507

theorem tailTrace_5858880 : CollatzResearch.WordTrace tailWord_5858880 prefixEnd_5858880 3008421537014142338755507 := by
  unfold tailWord_5858880
  simp only [CollatzResearch.WordTrace]
  refine ⟨106845454507142925942959047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142460606009523901257278729 106845454507142925942959047)
  ·
    refine ⟨160268181760714388914438571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106845454507142925942959047 160268181760714388914438571)
    ·
      refine ⟨240402272641071583371657857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160268181760714388914438571 240402272641071583371657857)
      ·
        refine ⟨180301704480803687528743393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240402272641071583371657857 180301704480803687528743393)
        ·
          refine ⟨135226278360602765646557545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180301704480803687528743393 135226278360602765646557545)
          ·
            refine ⟨101419708770452074234918159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135226278360602765646557545 101419708770452074234918159)
            ·
              refine ⟨152129563155678111352377239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101419708770452074234918159 152129563155678111352377239)
              ·
                refine ⟨228194344733517167028565859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152129563155678111352377239 228194344733517167028565859)
                ·
                  refine ⟨342291517100275750542848789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 228194344733517167028565859 342291517100275750542848789)
                  ·
                    refine ⟨16044914864075425806696037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 342291517100275750542848789 16044914864075425806696037)
                    ·
                      refine ⟨3008421537014142338755507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16044914864075425806696037 3008421537014142338755507)
                      ·
                        rfl

theorem cell23_5858880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_5858880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858880 prefixEnd_5858880 := by exact prefixLift 5858880
  have htrace : WordTrace (prefixWord ++ tailWord_5858880) baseStart_5858880 baseEnd_5858880 := by
    simpa [prefixWord, tailWord_5858880, baseEnd_5858880] using wordTrace_append hprefix tailTrace_5858880
  have hstable : (prefixWord ++ tailWord_5858880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858880).length < 2 ^ (prefixWord ++ tailWord_5858880).sum := by decide
  have hdescent : baseEnd_5858880 < baseStart_5858880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858890 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 10]
def baseStart_5858890 : Nat := 118140960795 + 5858890 * 2 ^ 59
def prefixEnd_5858890 : Nat := 4983230072969 + 3 ^ 40 * 5858890 * 2
def baseEnd_5858890 : Nat := 334269630202298588847829

theorem tailTrace_5858890 : CollatzResearch.WordTrace tailWord_5858890 prefixEnd_5858890 334269630202298588847829 := by
  unfold tailWord_5858890
  simp only [CollatzResearch.WordTrace]
  refine ⟨53422818436062405898445531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142460849162833082395854749 53422818436062405898445531)
  ·
    refine ⟨80134227654093608847668297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53422818436062405898445531 80134227654093608847668297)
    ·
      refine ⟨60100670740570206635751223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80134227654093608847668297 60100670740570206635751223)
      ·
        refine ⟨90151006110855309953626835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60100670740570206635751223 90151006110855309953626835)
        ·
          refine ⟨135226509166282964930440253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90151006110855309953626835 135226509166282964930440253)
          ·
            refine ⟨50709940937356111848915095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135226509166282964930440253 50709940937356111848915095)
            ·
              refine ⟨76064911406034167773372643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50709940937356111848915095 76064911406034167773372643)
              ·
                refine ⟨114097367109051251660058965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76064911406034167773372643 114097367109051251660058965)
                ·
                  refine ⟨334269630202298588847829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 114097367109051251660058965 334269630202298588847829)
                  ·
                    rfl

theorem cell23_5858890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 10].length) (baseStart_5858890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858890 prefixEnd_5858890 := by exact prefixLift 5858890
  have htrace : WordTrace (prefixWord ++ tailWord_5858890) baseStart_5858890 baseEnd_5858890 := by
    simpa [prefixWord, tailWord_5858890, baseEnd_5858890] using wordTrace_append hprefix tailTrace_5858890
  have hstable : (prefixWord ++ tailWord_5858890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858890).length < 2 ^ (prefixWord ++ tailWord_5858890).sum := by decide
  have hdescent : baseEnd_5858890 < baseStart_5858890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858937 : List Nat := [1, 2, 1, 3, 3, 1, 3, 1, 3, 5]
def baseStart_5858937 : Nat := 118140960795 + 5858937 * 2 ^ 59
def prefixEnd_5858937 : Nat := 4983230072969 + 3 ^ 40 * 5858937 * 2
def baseEnd_5858937 : Nat := 1002816935137149538580915

theorem tailTrace_5858937 : CollatzResearch.WordTrace tailWord_5858937 prefixEnd_5858937 1002816935137149538580915 := by
  unfold tailWord_5858937
  simp only [CollatzResearch.WordTrace]
  refine ⟨213692987975079350620743065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142461991983386233747162043 213692987975079350620743065)
  ·
    refine ⟨160269740981309512965557299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213692987975079350620743065 160269740981309512965557299)
    ·
      refine ⟨240404611471964269448335949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160269740981309512965557299 240404611471964269448335949)
      ·
        refine ⟨90151729301986601043125981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240404611471964269448335949 90151729301986601043125981)
        ·
          refine ⟨33806898488244975391172243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90151729301986601043125981 33806898488244975391172243)
          ·
            refine ⟨50710347732367463086758365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33806898488244975391172243 50710347732367463086758365)
            ·
              refine ⟨19016380399637798657534387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50710347732367463086758365 19016380399637798657534387)
              ·
                refine ⟨28524570599456697986301581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19016380399637798657534387 28524570599456697986301581)
                ·
                  refine ⟨10696713974796261744863093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28524570599456697986301581 10696713974796261744863093)
                  ·
                    refine ⟨1002816935137149538580915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10696713974796261744863093 1002816935137149538580915)
                    ·
                      rfl

theorem cell23_5858937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 5].length) (baseStart_5858937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858937 prefixEnd_5858937 := by exact prefixLift 5858937
  have htrace : WordTrace (prefixWord ++ tailWord_5858937) baseStart_5858937 baseEnd_5858937 := by
    simpa [prefixWord, tailWord_5858937, baseEnd_5858937] using wordTrace_append hprefix tailTrace_5858937
  have hstable : (prefixWord ++ tailWord_5858937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858937).length < 2 ^ (prefixWord ++ tailWord_5858937).sum := by decide
  have hdescent : baseEnd_5858937 < baseStart_5858937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858962 : List Nat := [3, 2, 3, 1, 4, 1, 2, 2, 1, 4]
def baseStart_5858962 : Nat := 118140960795 + 5858962 * 2 ^ 59
def prefixEnd_5858962 : Nat := 4983230072969 + 3 ^ 40 * 5858962 * 2
def baseEnd_5858962 : Nat := 1002821214142603672643377

theorem tailTrace_5858962 : CollatzResearch.WordTrace tailWord_5858962 prefixEnd_5858962 1002821214142603672643377 := by
  unfold tailWord_5858962
  simp only [CollatzResearch.WordTrace]
  refine ⟨53423474949997194972600785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142462599866659186593602093 53423474949997194972600785)
  ·
    refine ⟨40067606212497896229450589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53423474949997194972600785 40067606212497896229450589)
    ·
      refine ⟨15025352329686711086043971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40067606212497896229450589 15025352329686711086043971)
      ·
        refine ⟨22538028494530066629065957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15025352329686711086043971 22538028494530066629065957)
        ·
          refine ⟨4225880342724387492949867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22538028494530066629065957 4225880342724387492949867)
          ·
            refine ⟨6338820514086581239424801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4225880342724387492949867 6338820514086581239424801)
            ·
              refine ⟨4754115385564935929568601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6338820514086581239424801 4754115385564935929568601)
              ·
                refine ⟨3565586539173701947176451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4754115385564935929568601 3565586539173701947176451)
                ·
                  refine ⟨5348379808760552920764677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3565586539173701947176451 5348379808760552920764677)
                  ·
                    refine ⟨1002821214142603672643377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5348379808760552920764677 1002821214142603672643377)
                    ·
                      rfl

theorem cell23_5858962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_5858962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858962 prefixEnd_5858962 := by exact prefixLift 5858962
  have htrace : WordTrace (prefixWord ++ tailWord_5858962) baseStart_5858962 baseEnd_5858962 := by
    simpa [prefixWord, tailWord_5858962, baseEnd_5858962] using wordTrace_append hprefix tailTrace_5858962
  have hstable : (prefixWord ++ tailWord_5858962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858962).length < 2 ^ (prefixWord ++ tailWord_5858962).sum := by decide
  have hdescent : baseEnd_5858962 < baseStart_5858962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858968 : List Nat := [2, 1, 2, 4, 1, 3, 1, 4, 1, 1, 3]
def baseStart_5858968 : Nat := 118140960795 + 5858968 * 2 ^ 59
def prefixEnd_5858968 : Nat := 4983230072969 + 3 ^ 40 * 5858968 * 2
def baseEnd_5858968 : Nat := 3008466723311737994455103

theorem tailTrace_5858968 : CollatzResearch.WordTrace tailWord_5858968 prefixEnd_5858968 3008466723311737994455103 := by
  unfold tailWord_5858968
  simp only [CollatzResearch.WordTrace]
  refine ⟨106847059318983521457560779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142462745758644695276747705 106847059318983521457560779)
  ·
    refine ⟨160270588978475282186341169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106847059318983521457560779 160270588978475282186341169)
    ·
      refine ⟨120202941733856461639755877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160270588978475282186341169 120202941733856461639755877)
      ·
        refine ⟨22538051575098086557454227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120202941733856461639755877 22538051575098086557454227)
        ·
          refine ⟨33807077362647129836181341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22538051575098086557454227 33807077362647129836181341)
          ·
            refine ⟨12677654010992673688568003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33807077362647129836181341 12677654010992673688568003)
            ·
              refine ⟨19016481016489010532852005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12677654010992673688568003 19016481016489010532852005)
              ·
                refine ⟨3565590190591689474909751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19016481016489010532852005 3565590190591689474909751)
                ·
                  refine ⟨5348385285887534212364627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3565590190591689474909751 5348385285887534212364627)
                  ·
                    refine ⟨8022577928831301318546941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5348385285887534212364627 8022577928831301318546941)
                    ·
                      refine ⟨3008466723311737994455103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8022577928831301318546941 3008466723311737994455103)
                      ·
                        rfl

theorem cell23_5858968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_5858968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858968 prefixEnd_5858968 := by exact prefixLift 5858968
  have htrace : WordTrace (prefixWord ++ tailWord_5858968) baseStart_5858968 baseEnd_5858968 := by
    simpa [prefixWord, tailWord_5858968, baseEnd_5858968] using wordTrace_append hprefix tailTrace_5858968
  have hstable : (prefixWord ++ tailWord_5858968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858968).length < 2 ^ (prefixWord ++ tailWord_5858968).sum := by decide
  have hdescent : baseEnd_5858968 < baseStart_5858968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858991 : List Nat := [1, 1, 2, 1, 2, 4, 3, 2, 3, 2, 2]
def baseStart_5858991 : Nat := 118140960795 + 5858991 * 2 ^ 59
def prefixEnd_5858991 : Nat := 4983230072969 + 3 ^ 40 * 5858991 * 2
def baseEnd_5858991 : Nat := 3008478533366791404467497

theorem tailTrace_5858991 : CollatzResearch.WordTrace tailWord_5858991 prefixEnd_5858991 3008478533366791404467497 := by
  unfold tailWord_5858991
  simp only [CollatzResearch.WordTrace]
  refine ⟨213694957516883717843208827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142463305011255811895472551 213694957516883717843208827)
  ·
    refine ⟨320542436275325576764813241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213694957516883717843208827 320542436275325576764813241)
    ·
      refine ⟨240406827206494182573609931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320542436275325576764813241 240406827206494182573609931)
      ·
        refine ⟨360610240809741273860414897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240406827206494182573609931 360610240809741273860414897)
        ·
          refine ⟨270457680607305955395311173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360610240809741273860414897 270457680607305955395311173)
          ·
            refine ⟨50710815113869866636620845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 270457680607305955395311173 50710815113869866636620845)
            ·
              refine ⟨19016555667701199988732817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50710815113869866636620845 19016555667701199988732817)
              ·
                refine ⟨14262416750775899991549613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19016555667701199988732817 14262416750775899991549613)
                ·
                  refine ⟨5348406281540962496831105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14262416750775899991549613 5348406281540962496831105)
                  ·
                    refine ⟨4011304711155721872623329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5348406281540962496831105 4011304711155721872623329)
                    ·
                      refine ⟨3008478533366791404467497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4011304711155721872623329 3008478533366791404467497)
                      ·
                        rfl

theorem cell23_5858991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 3, 2, 2].length) (baseStart_5858991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858991 prefixEnd_5858991 := by exact prefixLift 5858991
  have htrace : WordTrace (prefixWord ++ tailWord_5858991) baseStart_5858991 baseEnd_5858991 := by
    simpa [prefixWord, tailWord_5858991, baseEnd_5858991] using wordTrace_append hprefix tailTrace_5858991
  have hstable : (prefixWord ++ tailWord_5858991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858991).length < 2 ^ (prefixWord ++ tailWord_5858991).sum := by decide
  have hdescent : baseEnd_5858991 < baseStart_5858991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5858994 : List Nat := [3, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3]
def baseStart_5858994 : Nat := 118140960795 + 5858994 * 2 ^ 59
def prefixEnd_5858994 : Nat := 4983230072969 + 3 ^ 40 * 5858994 * 2
def baseEnd_5858994 : Nat := 3008480073808754892729983

theorem tailTrace_5858994 : CollatzResearch.WordTrace tailWord_5858994 prefixEnd_5858994 3008480073808754892729983 := by
  unfold tailWord_5858994
  simp only [CollatzResearch.WordTrace]
  refine ⟨53423766733968212338892009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142463377957248566237045357 53423766733968212338892009)
  ·
    refine ⟨40067825050476159254169007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53423766733968212338892009 40067825050476159254169007)
    ·
      refine ⟨60101737575714238881253511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40067825050476159254169007 60101737575714238881253511)
      ·
        refine ⟨90152606363571358321880267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60101737575714238881253511 90152606363571358321880267)
        ·
          refine ⟨135228909545357037482820401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90152606363571358321880267 135228909545357037482820401)
          ·
            refine ⟨101421682159017778112115301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135228909545357037482820401 101421682159017778112115301)
            ·
              refine ⟨19016565404815833396021619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101421682159017778112115301 19016565404815833396021619)
              ·
                refine ⟨28524848107223750094032429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19016565404815833396021619 28524848107223750094032429)
                ·
                  refine ⟨10696818040208906285262161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28524848107223750094032429 10696818040208906285262161)
                  ·
                    refine ⟨8022613530156679713946621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10696818040208906285262161 8022613530156679713946621)
                    ·
                      refine ⟨3008480073808754892729983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8022613530156679713946621 3008480073808754892729983)
                      ·
                        rfl

theorem cell23_5858994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_5858994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5858994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5858994 prefixEnd_5858994 := by exact prefixLift 5858994
  have htrace : WordTrace (prefixWord ++ tailWord_5858994) baseStart_5858994 baseEnd_5858994 := by
    simpa [prefixWord, tailWord_5858994, baseEnd_5858994] using wordTrace_append hprefix tailTrace_5858994
  have hstable : (prefixWord ++ tailWord_5858994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5858994).length < 2 ^ (prefixWord ++ tailWord_5858994).sum := by decide
  have hdescent : baseEnd_5858994 < baseStart_5858994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5858994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859004 : List Nat := [2, 2, 2, 3, 1, 2, 2, 2, 1, 2, 4]
def baseStart_5859004 : Nat := 118140960795 + 5859004 * 2 ^ 59
def prefixEnd_5859004 : Nat := 4983230072969 + 3 ^ 40 * 5859004 * 2
def baseEnd_5859004 : Nat := 3008485208615299853604937

theorem tailTrace_5859004 : CollatzResearch.WordTrace tailWord_5859004 prefixEnd_5859004 3008485208615299853604937 := by
  unfold tailWord_5859004
  simp only [CollatzResearch.WordTrace]
  refine ⟨106847715832918310531716033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142463621110557747375621377 106847715832918310531716033)
  ·
    refine ⟨80135786874688732898787025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106847715832918310531716033 80135786874688732898787025)
    ·
      refine ⟨60101840156016549674090269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80135786874688732898787025 60101840156016549674090269)
      ·
        refine ⟨22538190058506206127783851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60101840156016549674090269 22538190058506206127783851)
        ·
          refine ⟨33807285087759309191675777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22538190058506206127783851 33807285087759309191675777)
          ·
            refine ⟨25355463815819481893756833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33807285087759309191675777 25355463815819481893756833)
            ·
              refine ⟨19016597861864611420317625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25355463815819481893756833 19016597861864611420317625)
              ·
                refine ⟨14262448396398458565238219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19016597861864611420317625 14262448396398458565238219)
                ·
                  refine ⟨21393672594597687847857329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14262448396398458565238219 21393672594597687847857329)
                  ·
                    refine ⟨16045254445948265885892997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21393672594597687847857329 16045254445948265885892997)
                    ·
                      refine ⟨3008485208615299853604937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16045254445948265885892997 3008485208615299853604937)
                      ·
                        rfl

theorem cell23_5859004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_5859004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859004 prefixEnd_5859004 := by exact prefixLift 5859004
  have htrace : WordTrace (prefixWord ++ tailWord_5859004) baseStart_5859004 baseEnd_5859004 := by
    simpa [prefixWord, tailWord_5859004, baseEnd_5859004] using wordTrace_append hprefix tailTrace_5859004
  have hstable : (prefixWord ++ tailWord_5859004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859004).length < 2 ^ (prefixWord ++ tailWord_5859004).sum := by decide
  have hdescent : baseEnd_5859004 < baseStart_5859004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859018 : List Nat := [3, 1, 2, 1, 5, 2, 1, 2, 2, 4]
def baseStart_5859018 : Nat := 118140960795 + 5859018 * 2 ^ 59
def prefixEnd_5859018 : Nat := 4983230072969 + 3 ^ 40 * 5859018 * 2
def baseEnd_5859018 : Nat := 1002830799114820932943291

theorem tailTrace_5859018 : CollatzResearch.WordTrace tailWord_5859018 prefixEnd_5859018 1002830799114820932943291 := by
  unfold tailWord_5859018
  simp only [CollatzResearch.WordTrace]
  refine ⟨53423985571946475363610427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142463961525190600969627805 53423985571946475363610427)
  ·
    refine ⟨80135978357919713045415641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53423985571946475363610427 80135978357919713045415641)
    ·
      refine ⟨60101983768439784784061731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80135978357919713045415641 60101983768439784784061731)
      ·
        refine ⟨90152975652659677176092597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60101983768439784784061731 90152975652659677176092597)
        ·
          refine ⟨8451841467436844735258681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90152975652659677176092597 8451841467436844735258681)
          ·
            refine ⟨6338881100577633551444011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8451841467436844735258681 6338881100577633551444011)
            ·
              refine ⟨9508321650866450327166017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6338881100577633551444011 9508321650866450327166017)
              ·
                refine ⟨7131241238149837745374513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9508321650866450327166017 7131241238149837745374513)
                ·
                  refine ⟨5348430928612378309030885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7131241238149837745374513 5348430928612378309030885)
                  ·
                    refine ⟨1002830799114820932943291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5348430928612378309030885 1002830799114820932943291)
                    ·
                      rfl

theorem cell23_5859018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_5859018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859018 prefixEnd_5859018 := by exact prefixLift 5859018
  have htrace : WordTrace (prefixWord ++ tailWord_5859018) baseStart_5859018 baseEnd_5859018 := by
    simpa [prefixWord, tailWord_5859018, baseEnd_5859018] using wordTrace_append hprefix tailTrace_5859018
  have hstable : (prefixWord ++ tailWord_5859018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859018).length < 2 ^ (prefixWord ++ tailWord_5859018).sum := by decide
  have hdescent : baseEnd_5859018 < baseStart_5859018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859051 : List Nat := [1, 1, 1, 1, 2, 4, 3, 4, 1, 3, 2]
def baseStart_5859051 : Nat := 118140960795 + 5859051 * 2 ^ 59
def prefixEnd_5859051 : Nat := 4983230072969 + 3 ^ 40 * 5859051 * 2
def baseEnd_5859051 : Nat := 3008509342206061169717221

theorem tailTrace_5859051 : CollatzResearch.WordTrace tailWord_5859051 prefixEnd_5859051 3008509342206061169717221 := by
  unfold tailWord_5859051
  simp only [CollatzResearch.WordTrace]
  refine ⟨213697145896666348090393007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142464763931110898726928671 213697145896666348090393007)
  ·
    refine ⟨320545718844999522135589511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213697145896666348090393007 320545718844999522135589511)
    ·
      refine ⟨480818578267499283203384267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320545718844999522135589511 480818578267499283203384267)
      ·
        refine ⟨721227867401248924805076401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480818578267499283203384267 721227867401248924805076401)
        ·
          refine ⟨540920900550936693603807301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 721227867401248924805076401 540920900550936693603807301)
          ·
            refine ⟨101422668853300630050713869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 540920900550936693603807301 101422668853300630050713869)
            ·
              refine ⟨38033500819987736269017701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101422668853300630050713869 38033500819987736269017701)
              ·
                refine ⟨7131281403747700550440819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38033500819987736269017701 7131281403747700550440819)
                ·
                  refine ⟨10696922105621550825661229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7131281403747700550440819 10696922105621550825661229)
                  ·
                    refine ⟨4011345789608081559622961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10696922105621550825661229 4011345789608081559622961)
                    ·
                      refine ⟨3008509342206061169717221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4011345789608081559622961 3008509342206061169717221)
                      ·
                        rfl

theorem cell23_5859051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 3, 2].length) (baseStart_5859051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859051 prefixEnd_5859051 := by exact prefixLift 5859051
  have htrace : WordTrace (prefixWord ++ tailWord_5859051) baseStart_5859051 baseEnd_5859051 := by
    simpa [prefixWord, tailWord_5859051, baseEnd_5859051] using wordTrace_append hprefix tailTrace_5859051
  have hstable : (prefixWord ++ tailWord_5859051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859051).length < 2 ^ (prefixWord ++ tailWord_5859051).sum := by decide
  have hdescent : baseEnd_5859051 < baseStart_5859051 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859087 : List Nat := [1, 1, 2, 1, 1, 1, 4, 5, 7]
def baseStart_5859087 : Nat := 118140960795 + 5859087 * 2 ^ 59
def prefixEnd_5859087 : Nat := 4983230072969 + 3 ^ 40 * 5859087 * 2
def baseEnd_5859087 : Nat := 334280869723291447651895

theorem tailTrace_5859087 : CollatzResearch.WordTrace tailWord_5859087 prefixEnd_5859087 334280869723291447651895 := by
  unfold tailWord_5859087
  simp only [CollatzResearch.WordTrace]
  refine ⟨213698458924535926238703515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142465639283023950825802343 213698458924535926238703515)
  ·
    refine ⟨320547688386803889358055273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213698458924535926238703515 320547688386803889358055273)
    ·
      refine ⟨240410766290102917018541455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320547688386803889358055273 240410766290102917018541455)
      ·
        refine ⟨360616149435154375527812183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240410766290102917018541455 360616149435154375527812183)
        ·
          refine ⟨540924224152731563291718275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360616149435154375527812183 540924224152731563291718275)
          ·
            refine ⟨811386336229097344937577413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540924224152731563291718275 811386336229097344937577413)
            ·
              refine ⟨152134938042955752175795765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 811386336229097344937577413 152134938042955752175795765)
              ·
                refine ⟨14262650441527101766480853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152134938042955752175795765 14262650441527101766480853)
                ·
                  refine ⟨334280869723291447651895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14262650441527101766480853 334280869723291447651895)
                  ·
                    rfl

theorem cell23_5859087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 7].length) (baseStart_5859087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859087 prefixEnd_5859087 := by exact prefixLift 5859087
  have htrace : WordTrace (prefixWord ++ tailWord_5859087) baseStart_5859087 baseEnd_5859087 := by
    simpa [prefixWord, tailWord_5859087, baseEnd_5859087] using wordTrace_append hprefix tailTrace_5859087
  have hstable : (prefixWord ++ tailWord_5859087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859087).length < 2 ^ (prefixWord ++ tailWord_5859087).sum := by decide
  have hdescent : baseEnd_5859087 < baseStart_5859087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859102 : List Nat := [4, 3, 2, 2, 1, 1, 1, 1, 3, 3, 2]
def baseStart_5859102 : Nat := 118140960795 + 5859102 * 2 ^ 59
def prefixEnd_5859102 : Nat := 4983230072969 + 3 ^ 40 * 5859102 * 2
def baseEnd_5859102 : Nat := 3008535529719440470179487

theorem tailTrace_5859102 : CollatzResearch.WordTrace tailWord_5859102 prefixEnd_5859102 3008535529719440470179487 := by
  unfold tailWord_5859102
  simp only [CollatzResearch.WordTrace]
  refine ⟨26712375752435197975062445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142466004012987722533666373 26712375752435197975062445)
  ·
    refine ⟨10017140907163199240648417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26712375752435197975062445 10017140907163199240648417)
    ·
      refine ⟨7512855680372399430486313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10017140907163199240648417 7512855680372399430486313)
      ·
        refine ⟨5634641760279299572864735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7512855680372399430486313 5634641760279299572864735)
        ·
          refine ⟨8451962640418949359297103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5634641760279299572864735 8451962640418949359297103)
          ·
            refine ⟨12677943960628424038945655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8451962640418949359297103 12677943960628424038945655)
            ·
              refine ⟨19016915940942636058418483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12677943960628424038945655 19016915940942636058418483)
              ·
                refine ⟨28525373911413954087627725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19016915940942636058418483 28525373911413954087627725)
                ·
                  refine ⟨10697015216780232782860397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28525373911413954087627725 10697015216780232782860397)
                  ·
                    refine ⟨4011380706292587293572649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10697015216780232782860397 4011380706292587293572649)
                    ·
                      refine ⟨3008535529719440470179487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4011380706292587293572649 3008535529719440470179487)
                      ·
                        rfl

theorem cell23_5859102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_5859102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859102 prefixEnd_5859102 := by exact prefixLift 5859102
  have htrace : WordTrace (prefixWord ++ tailWord_5859102) baseStart_5859102 baseEnd_5859102 := by
    simpa [prefixWord, tailWord_5859102, baseEnd_5859102] using wordTrace_append hprefix tailTrace_5859102
  have hstable : (prefixWord ++ tailWord_5859102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859102).length < 2 ^ (prefixWord ++ tailWord_5859102).sum := by decide
  have hdescent : baseEnd_5859102 < baseStart_5859102 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859144 : List Nat := [2, 1, 3, 1, 1, 4, 2, 1, 1, 2, 5]
def baseStart_5859144 : Nat := 118140960795 + 5859144 * 2 ^ 59
def prefixEnd_5859144 : Nat := 4983230072969 + 3 ^ 40 * 5859144 * 2
def baseEnd_5859144 : Nat := 3008557095906929305854293

theorem tailTrace_5859144 : CollatzResearch.WordTrace tailWord_5859144 prefixEnd_5859144 3008557095906929305854293 := by
  unfold tailWord_5859144
  simp only [CollatzResearch.WordTrace]
  refine ⟨106850268942664712486764243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142467025256886283315685657 106850268942664712486764243)
  ·
    refine ⟨160275403413997068730146365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106850268942664712486764243 160275403413997068730146365)
    ·
      refine ⟨60103276280248900773804887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160275403413997068730146365 60103276280248900773804887)
      ·
        refine ⟨90154914420373351160707331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60103276280248900773804887 90154914420373351160707331)
        ·
          refine ⟨135232371630560026741060997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90154914420373351160707331 135232371630560026741060997)
          ·
            refine ⟨25356069680730005013948937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135232371630560026741060997 25356069680730005013948937)
            ·
              refine ⟨19017052260547503760461703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25356069680730005013948937 19017052260547503760461703)
              ·
                refine ⟨28525578390821255640692555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19017052260547503760461703 28525578390821255640692555)
                ·
                  refine ⟨42788367586231883461038833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28525578390821255640692555 42788367586231883461038833)
                  ·
                    refine ⟨32091275689673912595779125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42788367586231883461038833 32091275689673912595779125)
                    ·
                      refine ⟨3008557095906929305854293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32091275689673912595779125 3008557095906929305854293)
                      ·
                        rfl

theorem cell23_5859144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_5859144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859144 prefixEnd_5859144 := by exact prefixLift 5859144
  have htrace : WordTrace (prefixWord ++ tailWord_5859144) baseStart_5859144 baseEnd_5859144 := by
    simpa [prefixWord, tailWord_5859144, baseEnd_5859144] using wordTrace_append hprefix tailTrace_5859144
  have hstable : (prefixWord ++ tailWord_5859144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859144).length < 2 ^ (prefixWord ++ tailWord_5859144).sum := by decide
  have hdescent : baseEnd_5859144 < baseStart_5859144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859171 : List Nat := [1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 4]
def baseStart_5859171 : Nat := 118140960795 + 5859171 * 2 ^ 59
def prefixEnd_5859171 : Nat := 4983230072969 + 3 ^ 40 * 5859171 * 2
def baseEnd_5859171 : Nat := 3008570959884600700216669

theorem tailTrace_5859171 : CollatzResearch.WordTrace tailWord_5859171 prefixEnd_5859171 3008570959884600700216669 := by
  unfold tailWord_5859171
  simp only [CollatzResearch.WordTrace]
  refine ⟨213701522656231608584761367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142467681770821072389840911 213701522656231608584761367)
  ·
    refine ⟨320552283984347412877142051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213701522656231608584761367 320552283984347412877142051)
    ·
      refine ⟨480828425976521119315713077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320552283984347412877142051 480828425976521119315713077)
      ·
        refine ⟨45077664935298854935848101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 480828425976521119315713077 45077664935298854935848101)
        ·
          refine ⟨8452062175368535300471519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45077664935298854935848101 8452062175368535300471519)
          ·
            refine ⟨12678093263052802950707279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8452062175368535300471519 12678093263052802950707279)
            ·
              refine ⟨19017139894579204426060919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12678093263052802950707279 19017139894579204426060919)
              ·
                refine ⟨28525709841868806639091379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19017139894579204426060919 28525709841868806639091379)
                ·
                  refine ⟨42788564762803209958637069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28525709841868806639091379 42788564762803209958637069)
                  ·
                    refine ⟨16045711786051203734488901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42788564762803209958637069 16045711786051203734488901)
                    ·
                      refine ⟨3008570959884600700216669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16045711786051203734488901 3008570959884600700216669)
                      ·
                        rfl

theorem cell23_5859171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_5859171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859171 prefixEnd_5859171 := by exact prefixLift 5859171
  have htrace : WordTrace (prefixWord ++ tailWord_5859171) baseStart_5859171 baseEnd_5859171 := by
    simpa [prefixWord, tailWord_5859171, baseEnd_5859171] using wordTrace_append hprefix tailTrace_5859171
  have hstable : (prefixWord ++ tailWord_5859171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859171).length < 2 ^ (prefixWord ++ tailWord_5859171).sum := by decide
  have hdescent : baseEnd_5859171 < baseStart_5859171 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859282 : List Nat := [3, 2, 2, 3, 2, 1, 2, 1, 2, 3, 2]
def baseStart_5859282 : Nat := 118140960795 + 5859282 * 2 ^ 59
def prefixEnd_5859282 : Nat := 4983230072969 + 3 ^ 40 * 5859282 * 2
def baseEnd_5859282 : Nat := 3008627956237249765928659

theorem tailTrace_5859282 : CollatzResearch.WordTrace tailWord_5859282 prefixEnd_5859282 3008627956237249765928659 := by
  unfold tailWord_5859282
  simp only [CollatzResearch.WordTrace]
  refine ⟨53426392789707368635513025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142470380772552983028034733 53426392789707368635513025)
  ·
    refine ⟨40069794592280526476634769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53426392789707368635513025 40069794592280526476634769)
    ·
      refine ⟨30052345944210394857476077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40069794592280526476634769 30052345944210394857476077)
      ·
        refine ⟨11269629729078898071553529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30052345944210394857476077 11269629729078898071553529)
        ·
          refine ⟨8452222296809173553665147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11269629729078898071553529 8452222296809173553665147)
          ·
            refine ⟨12678333445213760330497721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8452222296809173553665147 12678333445213760330497721)
            ·
              refine ⟨9508750083910320247873291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12678333445213760330497721 9508750083910320247873291)
              ·
                refine ⟨14263125125865480371809937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9508750083910320247873291 14263125125865480371809937)
                ·
                  refine ⟨10697343844399110278857453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14263125125865480371809937 10697343844399110278857453)
                  ·
                    refine ⟨4011503941649666354571545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10697343844399110278857453 4011503941649666354571545)
                    ·
                      refine ⟨3008627956237249765928659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4011503941649666354571545 3008627956237249765928659)
                      ·
                        rfl

theorem cell23_5859282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_5859282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859282 prefixEnd_5859282 := by exact prefixLift 5859282
  have htrace : WordTrace (prefixWord ++ tailWord_5859282) baseStart_5859282 baseEnd_5859282 := by
    simpa [prefixWord, tailWord_5859282, baseEnd_5859282] using wordTrace_append hprefix tailTrace_5859282
  have hstable : (prefixWord ++ tailWord_5859282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859282).length < 2 ^ (prefixWord ++ tailWord_5859282).sum := by decide
  have hdescent : baseEnd_5859282 < baseStart_5859282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859295 : List Nat := [1, 1, 2, 3, 4, 2, 3, 1, 1, 1, 4]
def baseStart_5859295 : Nat := 118140960795 + 5859295 * 2 ^ 59
def prefixEnd_5859295 : Nat := 4983230072969 + 3 ^ 40 * 5859295 * 2
def baseEnd_5859295 : Nat := 3008634631485758215066099

theorem tailTrace_5859295 : CollatzResearch.WordTrace tailWord_5859295 prefixEnd_5859295 3008634631485758215066099 := by
  unfold tailWord_5859295
  simp only [CollatzResearch.WordTrace]
  refine ⟨213706045307782377762275339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142470696871854918508183559 213706045307782377762275339)
  ·
    refine ⟨320559067961673566643413009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213706045307782377762275339 320559067961673566643413009)
    ·
      refine ⟨240419300971255174982559757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320559067961673566643413009 240419300971255174982559757)
      ·
        refine ⟨90157237864220690618459909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240419300971255174982559757 90157237864220690618459909)
        ·
          refine ⟨16904482099541379490961233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90157237864220690618459909 16904482099541379490961233)
          ·
            refine ⟨12678361574656034618220925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16904482099541379490961233 12678361574656034618220925)
            ·
              refine ⟨4754385590496012981832847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12678361574656034618220925 4754385590496012981832847)
              ·
                refine ⟨7131578385744019472749271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4754385590496012981832847 7131578385744019472749271)
                ·
                  refine ⟨10697367578616029209123907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7131578385744019472749271 10697367578616029209123907)
                  ·
                    refine ⟨16046051367924043813685861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10697367578616029209123907 16046051367924043813685861)
                    ·
                      refine ⟨3008634631485758215066099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16046051367924043813685861 3008634631485758215066099)
                      ·
                        rfl

theorem cell23_5859295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 1, 1, 4].length) (baseStart_5859295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859295 prefixEnd_5859295 := by exact prefixLift 5859295
  have htrace : WordTrace (prefixWord ++ tailWord_5859295) baseStart_5859295 baseEnd_5859295 := by
    simpa [prefixWord, tailWord_5859295, baseEnd_5859295] using wordTrace_append hprefix tailTrace_5859295
  have hstable : (prefixWord ++ tailWord_5859295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859295).length < 2 ^ (prefixWord ++ tailWord_5859295).sum := by decide
  have hdescent : baseEnd_5859295 < baseStart_5859295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859311 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 3, 3, 3]
def baseStart_5859311 : Nat := 118140960795 + 5859311 * 2 ^ 59
def prefixEnd_5859311 : Nat := 4983230072969 + 3 ^ 40 * 5859311 * 2
def baseEnd_5859311 : Nat := 3008642847176230152466025

theorem tailTrace_5859311 : CollatzResearch.WordTrace tailWord_5859311 prefixEnd_5859311 3008642847176230152466025 := by
  unfold tailWord_5859311
  simp only [CollatzResearch.WordTrace]
  refine ⟨213706628875724412494857787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142471085917149608329905191 213706628875724412494857787)
  ·
    refine ⟨320559943313586618742286681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213706628875724412494857787 320559943313586618742286681)
    ·
      refine ⟨240419957485189964056715011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320559943313586618742286681 240419957485189964056715011)
      ·
        refine ⟨360629936227784946085072517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240419957485189964056715011 360629936227784946085072517)
        ·
          refine ⟨67618113042709677390951097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 360629936227784946085072517 67618113042709677390951097)
          ·
            refine ⟨50713584782032258043213323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67618113042709677390951097 50713584782032258043213323)
            ·
              refine ⟨76070377173048387064819985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50713584782032258043213323 76070377173048387064819985)
              ·
                refine ⟨57052782879786290298614989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76070377173048387064819985 57052782879786290298614989)
                ·
                  refine ⟨21394793579919858861980621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57052782879786290298614989 21394793579919858861980621)
                  ·
                    refine ⟨8023047592469947073242733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21394793579919858861980621 8023047592469947073242733)
                    ·
                      refine ⟨3008642847176230152466025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8023047592469947073242733 3008642847176230152466025)
                      ·
                        rfl

theorem cell23_5859311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 3, 3].length) (baseStart_5859311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859311 prefixEnd_5859311 := by exact prefixLift 5859311
  have htrace : WordTrace (prefixWord ++ tailWord_5859311) baseStart_5859311 baseEnd_5859311 := by
    simpa [prefixWord, tailWord_5859311, baseEnd_5859311] using wordTrace_append hprefix tailTrace_5859311
  have hstable : (prefixWord ++ tailWord_5859311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859311).length < 2 ^ (prefixWord ++ tailWord_5859311).sum := by decide
  have hdescent : baseEnd_5859311 < baseStart_5859311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859349 : List Nat := [1, 3, 2, 1, 6, 1, 2, 1, 1, 2, 3]
def baseStart_5859349 : Nat := 118140960795 + 5859349 * 2 ^ 59
def prefixEnd_5859349 : Nat := 4983230072969 + 3 ^ 40 * 5859349 * 2
def baseEnd_5859349 : Nat := 3008662359441101003790851

theorem tailTrace_5859349 : CollatzResearch.WordTrace tailWord_5859349 prefixEnd_5859349 3008662359441101003790851 := by
  unfold tailWord_5859349
  simp only [CollatzResearch.WordTrace]
  refine ⟨213708014849586744984741101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142472009899724496656494067 213708014849586744984741101)
  ·
    refine ⟨80140505568595029369277913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213708014849586744984741101 80140505568595029369277913)
    ·
      refine ⟨60105379176446272026958435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80140505568595029369277913 60105379176446272026958435)
      ·
        refine ⟨90158068764669408040437653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60105379176446272026958435 90158068764669408040437653)
        ·
          refine ⟨4226159473343878501895515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 90158068764669408040437653 4226159473343878501895515)
          ·
            refine ⟨6339239210015817752843273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4226159473343878501895515 6339239210015817752843273)
            ·
              refine ⟨4754429407511863314632455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6339239210015817752843273 4754429407511863314632455)
              ·
                refine ⟨7131644111267794971948683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4754429407511863314632455 7131644111267794971948683)
                ·
                  refine ⟨10697466166901692457923025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7131644111267794971948683 10697466166901692457923025)
                  ·
                    refine ⟨8023099625176269343442269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10697466166901692457923025 8023099625176269343442269)
                    ·
                      refine ⟨3008662359441101003790851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8023099625176269343442269 3008662359441101003790851)
                      ·
                        rfl

theorem cell23_5859349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 1, 2, 3].length) (baseStart_5859349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859349 prefixEnd_5859349 := by exact prefixLift 5859349
  have htrace : WordTrace (prefixWord ++ tailWord_5859349) baseStart_5859349 baseEnd_5859349 := by
    simpa [prefixWord, tailWord_5859349, baseEnd_5859349] using wordTrace_append hprefix tailTrace_5859349
  have hstable : (prefixWord ++ tailWord_5859349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859349).length < 2 ^ (prefixWord ++ tailWord_5859349).sum := by decide
  have hdescent : baseEnd_5859349 < baseStart_5859349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859371 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 2, 4, 3]
def baseStart_5859371 : Nat := 118140960795 + 5859371 * 2 ^ 59
def prefixEnd_5859371 : Nat := 4983230072969 + 3 ^ 40 * 5859371 * 2
def baseEnd_5859371 : Nat := 3008673656015499917715749

theorem tailTrace_5859371 : CollatzResearch.WordTrace tailWord_5859371 prefixEnd_5859371 3008673656015499917715749 := by
  unfold tailWord_5859371
  simp only [CollatzResearch.WordTrace]
  refine ⟨213708817255507042742041967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142472544837004695161361311 213708817255507042742041967)
  ·
    refine ⟨320563225883260564113062951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213708817255507042742041967 320563225883260564113062951)
    ·
      refine ⟨480844838824890846169594427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320563225883260564113062951 480844838824890846169594427)
      ·
        refine ⟨721267258237336269254391641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480844838824890846169594427 721267258237336269254391641)
        ·
          refine ⟨540950443678002201940793731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 721267258237336269254391641 540950443678002201940793731)
          ·
            refine ⟨811425665517003302911190597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540950443678002201940793731 811425665517003302911190597)
            ·
              refine ⟨152142312284438119295848237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 811425665517003302911190597 152142312284438119295848237)
              ·
                refine ⟨57053367106664294735943089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152142312284438119295848237 57053367106664294735943089)
                ·
                  refine ⟨42790025329998221051957317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57053367106664294735943089 42790025329998221051957317)
                  ·
                    refine ⟨8023129749374666447241997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42790025329998221051957317 8023129749374666447241997)
                    ·
                      refine ⟨3008673656015499917715749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8023129749374666447241997 3008673656015499917715749)
                      ·
                        rfl

theorem cell23_5859371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 4, 3].length) (baseStart_5859371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859371 prefixEnd_5859371 := by exact prefixLift 5859371
  have htrace : WordTrace (prefixWord ++ tailWord_5859371) baseStart_5859371 baseEnd_5859371 := by
    simpa [prefixWord, tailWord_5859371, baseEnd_5859371] using wordTrace_append hprefix tailTrace_5859371
  have hstable : (prefixWord ++ tailWord_5859371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859371).length < 2 ^ (prefixWord ++ tailWord_5859371).sum := by decide
  have hdescent : baseEnd_5859371 < baseStart_5859371 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859391 : List Nat := [1, 1, 2, 2, 3, 1, 4, 2, 7]
def baseStart_5859391 : Nat := 118140960795 + 5859391 * 2 ^ 59
def prefixEnd_5859391 : Nat := 4983230072969 + 3 ^ 40 * 5859391 * 2
def baseEnd_5859391 : Nat := 334298213958732204385073

theorem tailTrace_5859391 : CollatzResearch.WordTrace tailWord_5859391 prefixEnd_5859391 334298213958732204385073 := by
  unfold tailWord_5859391
  simp only [CollatzResearch.WordTrace]
  refine ⟨213709546715434586157770027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142473031143623057438513351 213709546715434586157770027)
  ·
    refine ⟨320564320073151879236655041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213709546715434586157770027 320564320073151879236655041)
    ·
      refine ⟨240423240054863909427491281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320564320073151879236655041 240423240054863909427491281)
      ·
        refine ⟨180317430041147932070618461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240423240054863909427491281 180317430041147932070618461)
        ·
          refine ⟨67619036265430474526481923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180317430041147932070618461 67619036265430474526481923)
          ·
            refine ⟨101428554398145711789722885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67619036265430474526481923 101428554398145711789722885)
            ·
              refine ⟨19017853949652320960573041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101428554398145711789722885 19017853949652320960573041)
              ·
                refine ⟨14263390462239240720429781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19017853949652320960573041 14263390462239240720429781)
                ·
                  refine ⟨334298213958732204385073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14263390462239240720429781 334298213958732204385073)
                  ·
                    rfl

theorem cell23_5859391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 7].length) (baseStart_5859391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859391 prefixEnd_5859391 := by exact prefixLift 5859391
  have htrace : WordTrace (prefixWord ++ tailWord_5859391) baseStart_5859391 baseEnd_5859391 := by
    simpa [prefixWord, tailWord_5859391, baseEnd_5859391] using wordTrace_append hprefix tailTrace_5859391
  have hstable : (prefixWord ++ tailWord_5859391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859391).length < 2 ^ (prefixWord ++ tailWord_5859391).sum := by decide
  have hdescent : baseEnd_5859391 < baseStart_5859391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859438 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 4, 5]
def baseStart_5859438 : Nat := 118140960795 + 5859438 * 2 ^ 59
def prefixEnd_5859438 : Nat := 4983230072969 + 3 ^ 40 * 5859438 * 2
def baseEnd_5859438 : Nat := 1002902686406450385192647

theorem tailTrace_5859438 : CollatzResearch.WordTrace tailWord_5859438 prefixEnd_5859438 1002902686406450385192647 := by
  unfold tailWord_5859438
  simp only [CollatzResearch.WordTrace]
  refine ⟨26713907618283039148091371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142474173964176208789820645 26713907618283039148091371)
  ·
    refine ⟨40070861427424558722137057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26713907618283039148091371 40070861427424558722137057)
    ·
      refine ⟨30053146070568419041602793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40070861427424558722137057 30053146070568419041602793)
      ·
        refine ⟨22539859552926314281202095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30053146070568419041602793 22539859552926314281202095)
        ·
          refine ⟨33809789329389471421803143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22539859552926314281202095 33809789329389471421803143)
          ·
            refine ⟨50714683994084207132704715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33809789329389471421803143 50714683994084207132704715)
            ·
              refine ⟨76072025991126310699057073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50714683994084207132704715 76072025991126310699057073)
              ·
                refine ⟨57054019493344733024292805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76072025991126310699057073 57054019493344733024292805)
                ·
                  refine ⟨10697628655002137442054901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57054019493344733024292805 10697628655002137442054901)
                  ·
                    refine ⟨1002902686406450385192647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10697628655002137442054901 1002902686406450385192647)
                    ·
                      rfl

theorem cell23_5859438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_5859438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859438 prefixEnd_5859438 := by exact prefixLift 5859438
  have htrace : WordTrace (prefixWord ++ tailWord_5859438) baseStart_5859438 baseEnd_5859438 := by
    simpa [prefixWord, tailWord_5859438, baseEnd_5859438] using wordTrace_append hprefix tailTrace_5859438
  have hstable : (prefixWord ++ tailWord_5859438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859438).length < 2 ^ (prefixWord ++ tailWord_5859438).sum := by decide
  have hdescent : baseEnd_5859438 < baseStart_5859438 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859476 : List Nat := [2, 4, 2, 3, 1, 2, 2, 2, 5]
def baseStart_5859476 : Nat := 118140960795 + 5859476 * 2 ^ 59
def prefixEnd_5859476 : Nat := 4983230072969 + 3 ^ 40 * 5859476 * 2
def baseEnd_5859476 : Nat := 334303063498246889655863

theorem tailTrace_5859476 : CollatzResearch.WordTrace tailWord_5859476 prefixEnd_5859476 334303063498246889655863 := by
  unfold tailWord_5859476
  simp only [CollatzResearch.WordTrace]
  refine ⟨106856323460063322837307141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142475097946751097116409521 106856323460063322837307141)
  ·
    refine ⟨20035560648761873031995089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106856323460063322837307141 20035560648761873031995089)
    ·
      refine ⟨15026670486571404773996317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20035560648761873031995089 15026670486571404773996317)
      ·
        refine ⟨5635001432464276790248619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15026670486571404773996317 5635001432464276790248619)
        ·
          refine ⟨8452502148696415185372929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5635001432464276790248619 8452502148696415185372929)
          ·
            refine ⟨6339376611522311389029697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8452502148696415185372929 6339376611522311389029697)
            ·
              refine ⟨4754532458641733541772273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6339376611522311389029697 4754532458641733541772273)
              ·
                refine ⟨3565899343981300156329205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4754532458641733541772273 3565899343981300156329205)
                ·
                  refine ⟨334303063498246889655863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3565899343981300156329205 334303063498246889655863)
                  ·
                    rfl

theorem cell23_5859476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_5859476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859476 prefixEnd_5859476 := by exact prefixLift 5859476
  have htrace : WordTrace (prefixWord ++ tailWord_5859476) baseStart_5859476 baseEnd_5859476 := by
    simpa [prefixWord, tailWord_5859476, baseEnd_5859476] using wordTrace_append hprefix tailTrace_5859476
  have hstable : (prefixWord ++ tailWord_5859476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859476).length < 2 ^ (prefixWord ++ tailWord_5859476).sum := by decide
  have hdescent : baseEnd_5859476 < baseStart_5859476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859481 : List Nat := [1, 2, 1, 2, 1, 2, 1, 5, 8]
def baseStart_5859481 : Nat := 118140960795 + 5859481 * 2 ^ 59
def prefixEnd_5859481 : Nat := 4983230072969 + 3 ^ 40 * 5859481 * 2
def baseEnd_5859481 : Nat := 334303348765277165260027

theorem tailTrace_5859481 : CollatzResearch.WordTrace tailWord_5859481 prefixEnd_5859481 334303348765277165260027 := by
  unfold tailWord_5859481
  simp only [CollatzResearch.WordTrace]
  refine ⟨213712829285108531528546297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142475219523405687685697531 213712829285108531528546297)
  ·
    refine ⟨160284621963831398646409723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213712829285108531528546297 160284621963831398646409723)
    ·
      refine ⟨240426932945747097969614585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160284621963831398646409723 240426932945747097969614585)
      ·
        refine ⟨180320199709310323477210939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240426932945747097969614585 180320199709310323477210939)
        ·
          refine ⟨270480299563965485215816409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180320199709310323477210939 270480299563965485215816409)
          ·
            refine ⟨202860224672974113911862307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270480299563965485215816409 202860224672974113911862307)
            ·
              refine ⟨304290337009461170867793461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202860224672974113911862307 304290337009461170867793461)
              ·
                refine ⟨28527219094636984768855637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 304290337009461170867793461 28527219094636984768855637)
                ·
                  refine ⟨334303348765277165260027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28527219094636984768855637 334303348765277165260027)
                  ·
                    rfl

theorem cell23_5859481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 8].length) (baseStart_5859481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859481 prefixEnd_5859481 := by exact prefixLift 5859481
  have htrace : WordTrace (prefixWord ++ tailWord_5859481) baseStart_5859481 baseEnd_5859481 := by
    simpa [prefixWord, tailWord_5859481, baseEnd_5859481] using wordTrace_append hprefix tailTrace_5859481
  have hstable : (prefixWord ++ tailWord_5859481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859481).length < 2 ^ (prefixWord ++ tailWord_5859481).sum := by decide
  have hdescent : baseEnd_5859481 < baseStart_5859481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859492 : List Nat := [2, 3, 1, 2, 4, 1, 1, 1, 2, 4, 2]
def baseStart_5859492 : Nat := 118140960795 + 5859492 * 2 ^ 59
def prefixEnd_5859492 : Nat := 4983230072969 + 3 ^ 40 * 5859492 * 2
def baseEnd_5859492 : Nat := 3008735787174693944302693

theorem tailTrace_5859492 : CollatzResearch.WordTrace tailWord_5859492 prefixEnd_5859492 3008735787174693944302693 := by
  unfold tailWord_5859492
  simp only [CollatzResearch.WordTrace]
  refine ⟨106856615244034340203598365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142475486992045786938131153 106856615244034340203598365)
  ·
    refine ⟨40071230716512877576349387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106856615244034340203598365 40071230716512877576349387)
    ·
      refine ⟨60106846074769316364524081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40071230716512877576349387 60106846074769316364524081)
      ·
        refine ⟨45080134556076987273393061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60106846074769316364524081 45080134556076987273393061)
        ·
          refine ⟨8452525229264435113761199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45080134556076987273393061 8452525229264435113761199)
          ·
            refine ⟨12678787843896652670641799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8452525229264435113761199 12678787843896652670641799)
            ·
              refine ⟨19018181765844979005962699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12678787843896652670641799 19018181765844979005962699)
              ·
                refine ⟨28527272648767468508944049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19018181765844979005962699 28527272648767468508944049)
                ·
                  refine ⟨21395454486575601381708037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28527272648767468508944049 21395454486575601381708037)
                  ·
                    refine ⟨4011647716232925259070257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21395454486575601381708037 4011647716232925259070257)
                    ·
                      refine ⟨3008735787174693944302693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4011647716232925259070257 3008735787174693944302693)
                      ·
                        rfl

theorem cell23_5859492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_5859492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859492 prefixEnd_5859492 := by exact prefixLift 5859492
  have htrace : WordTrace (prefixWord ++ tailWord_5859492) baseStart_5859492 baseEnd_5859492 := by
    simpa [prefixWord, tailWord_5859492, baseEnd_5859492] using wordTrace_append hprefix tailTrace_5859492
  have hstable : (prefixWord ++ tailWord_5859492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859492).length < 2 ^ (prefixWord ++ tailWord_5859492).sum := by decide
  have hdescent : baseEnd_5859492 < baseStart_5859492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859509 : List Nat := [1, 3, 3, 4, 1, 2, 1, 1, 2, 1, 4]
def baseStart_5859509 : Nat := 118140960795 + 5859509 * 2 ^ 59
def prefixEnd_5859509 : Nat := 4983230072969 + 3 ^ 40 * 5859509 * 2
def baseEnd_5859509 : Nat := 3008744516345820377790115

theorem tailTrace_5859509 : CollatzResearch.WordTrace tailWord_5859509 prefixEnd_5859509 3008744516345820377790115 := by
  unfold tailWord_5859509
  simp only [CollatzResearch.WordTrace]
  refine ⟨213713850529007092310565581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142475900352671394873710387 213713850529007092310565581)
  ·
    refine ⟨80142693948377659616462093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213713850529007092310565581 80142693948377659616462093)
    ·
      refine ⟨30053510230641622356173285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80142693948377659616462093 30053510230641622356173285)
      ·
        refine ⟨5635033168245304191782491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30053510230641622356173285 5635033168245304191782491)
        ·
          refine ⟨8452549752367956287673737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5635033168245304191782491 8452549752367956287673737)
          ·
            refine ⟨6339412314275967215755303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8452549752367956287673737 6339412314275967215755303)
            ·
              refine ⟨9509118471413950823632955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6339412314275967215755303 9509118471413950823632955)
              ·
                refine ⟨14263677707120926235449433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9509118471413950823632955 14263677707120926235449433)
                ·
                  refine ⟨10697758280340694676587075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14263677707120926235449433 10697758280340694676587075)
                  ·
                    refine ⟨16046637420511042014880613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10697758280340694676587075 16046637420511042014880613)
                    ·
                      refine ⟨3008744516345820377790115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16046637420511042014880613 3008744516345820377790115)
                      ·
                        rfl

theorem cell23_5859509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_5859509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859509 prefixEnd_5859509 := by exact prefixLift 5859509
  have htrace : WordTrace (prefixWord ++ tailWord_5859509) baseStart_5859509 baseEnd_5859509 := by
    simpa [prefixWord, tailWord_5859509, baseEnd_5859509] using wordTrace_append hprefix tailTrace_5859509
  have hstable : (prefixWord ++ tailWord_5859509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859509).length < 2 ^ (prefixWord ++ tailWord_5859509).sum := by decide
  have hdescent : baseEnd_5859509 < baseStart_5859509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859522 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_5859522 : Nat := 118140960795 + 5859522 * 2 ^ 59
def prefixEnd_5859522 : Nat := 4983230072969 + 3 ^ 40 * 5859522 * 2
def baseEnd_5859522 : Nat := 3008751191594328826927555

theorem tailTrace_5859522 : CollatzResearch.WordTrace tailWord_5859522 prefixEnd_5859522 3008751191594328826927555 := by
  unfold tailWord_5859522
  simp only [CollatzResearch.WordTrace]
  refine ⟨53428581169489998882697205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142476216451973330353859213 53428581169489998882697205)
  ·
    refine ⟨5008929484639687395252863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53428581169489998882697205 5008929484639687395252863)
    ·
      refine ⟨7513394226959531092879295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5008929484639687395252863 7513394226959531092879295)
      ·
        refine ⟨11270091340439296639318943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7513394226959531092879295 11270091340439296639318943)
        ·
          refine ⟨16905137010658944958978415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11270091340439296639318943 16905137010658944958978415)
          ·
            refine ⟨25357705515988417438467623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16905137010658944958978415 25357705515988417438467623)
            ·
              refine ⟨38036558273982626157701435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25357705515988417438467623 38036558273982626157701435)
              ·
                refine ⟨57054837410973939236552153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38036558273982626157701435 57054837410973939236552153)
                ·
                  refine ⟨42791128058230454427414115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57054837410973939236552153 42791128058230454427414115)
                  ·
                    refine ⟨64186692087345681641121173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42791128058230454427414115 64186692087345681641121173)
                    ·
                      refine ⟨3008751191594328826927555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64186692087345681641121173 3008751191594328826927555)
                      ·
                        rfl

theorem cell23_5859522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_5859522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859522 prefixEnd_5859522 := by exact prefixLift 5859522
  have htrace : WordTrace (prefixWord ++ tailWord_5859522) baseStart_5859522 baseEnd_5859522 := by
    simpa [prefixWord, tailWord_5859522, baseEnd_5859522] using wordTrace_append hprefix tailTrace_5859522
  have hstable : (prefixWord ++ tailWord_5859522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859522).length < 2 ^ (prefixWord ++ tailWord_5859522).sum := by decide
  have hdescent : baseEnd_5859522 < baseStart_5859522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859535 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 4, 3, 2]
def baseStart_5859535 : Nat := 118140960795 + 5859535 * 2 ^ 59
def prefixEnd_5859535 : Nat := 4983230072969 + 3 ^ 40 * 5859535 * 2
def baseEnd_5859535 : Nat := 3008757866842837276064995

theorem tailTrace_5859535 : CollatzResearch.WordTrace tailWord_5859535 prefixEnd_5859535 3008757866842837276064995 := by
  unfold tailWord_5859535
  simp only [CollatzResearch.WordTrace]
  refine ⟨213714798826912898751012059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142476532551275265834008039 213714798826912898751012059)
  ·
    refine ⟨320572198240369348126518089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213714798826912898751012059 320572198240369348126518089)
    ·
      refine ⟨240429148680277011094888567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320572198240369348126518089 240429148680277011094888567)
      ·
        refine ⟨360643723020415516642332851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240429148680277011094888567 360643723020415516642332851)
        ·
          refine ⟨540965584530623274963499277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360643723020415516642332851 540965584530623274963499277)
          ·
            refine ⟨202862094198983728111312229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 540965584530623274963499277 202862094198983728111312229)
            ·
              refine ⟨38036642662309449020871043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 202862094198983728111312229 38036642662309449020871043)
              ·
                refine ⟨57054963993464173531306565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38036642662309449020871043 57054963993464173531306565)
                ·
                  refine ⟨10697805748774532537119981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57054963993464173531306565 10697805748774532537119981)
                  ·
                    refine ⟨4011677155790449701419993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10697805748774532537119981 4011677155790449701419993)
                    ·
                      refine ⟨3008757866842837276064995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4011677155790449701419993 3008757866842837276064995)
                      ·
                        rfl

theorem cell23_5859535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 3, 2].length) (baseStart_5859535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859535 prefixEnd_5859535 := by exact prefixLift 5859535
  have htrace : WordTrace (prefixWord ++ tailWord_5859535) baseStart_5859535 baseEnd_5859535 := by
    simpa [prefixWord, tailWord_5859535, baseEnd_5859535] using wordTrace_append hprefix tailTrace_5859535
  have hstable : (prefixWord ++ tailWord_5859535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859535).length < 2 ^ (prefixWord ++ tailWord_5859535).sum := by decide
  have hdescent : baseEnd_5859535 < baseStart_5859535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859568 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 3]
def baseStart_5859568 : Nat := 118140960795 + 5859568 * 2 ^ 59
def prefixEnd_5859568 : Nat := 4983230072969 + 3 ^ 40 * 5859568 * 2
def baseEnd_5859568 : Nat := 3008774811704435646952343

theorem tailTrace_5859568 : CollatzResearch.WordTrace tailWord_5859568 prefixEnd_5859568 3008774811704435646952343 := by
  unfold tailWord_5859568
  simp only [CollatzResearch.WordTrace]
  refine ⟨106858001217896672693481679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142477334957195563591308905 106858001217896672693481679)
  ·
    refine ⟨160287001826845009040222519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106858001217896672693481679 160287001826845009040222519)
    ·
      refine ⟨240430502740267513560333779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160287001826845009040222519 240430502740267513560333779)
      ·
        refine ⟨360645754110401270340500669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240430502740267513560333779 360645754110401270340500669)
        ·
          refine ⟨135242157791400476377687751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 360645754110401270340500669 135242157791400476377687751)
          ·
            refine ⟨202863236687100714566531627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135242157791400476377687751 202863236687100714566531627)
            ·
              refine ⟨304294855030651071849797441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202863236687100714566531627 304294855030651071849797441)
              ·
                refine ⟨228221141272988303887348081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304294855030651071849797441 228221141272988303887348081)
                ·
                  refine ⟨171165855954741227915511061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 228221141272988303887348081 171165855954741227915511061)
                  ·
                    refine ⟨8023399497878495058539581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 171165855954741227915511061 8023399497878495058539581)
                    ·
                      refine ⟨3008774811704435646952343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8023399497878495058539581 3008774811704435646952343)
                      ·
                        rfl

theorem cell23_5859568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 3].length) (baseStart_5859568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859568 prefixEnd_5859568 := by exact prefixLift 5859568
  have htrace : WordTrace (prefixWord ++ tailWord_5859568) baseStart_5859568 baseEnd_5859568 := by
    simpa [prefixWord, tailWord_5859568, baseEnd_5859568] using wordTrace_append hprefix tailTrace_5859568
  have hstable : (prefixWord ++ tailWord_5859568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859568).length < 2 ^ (prefixWord ++ tailWord_5859568).sum := by decide
  have hdescent : baseEnd_5859568 < baseStart_5859568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859582 : List Nat := [4, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4]
def baseStart_5859582 : Nat := 118140960795 + 5859582 * 2 ^ 59
def prefixEnd_5859582 : Nat := 4983230072969 + 3 ^ 40 * 5859582 * 2
def baseEnd_5859582 : Nat := 3008782000433598592177279

theorem tailTrace_5859582 : CollatzResearch.WordTrace tailWord_5859582 prefixEnd_5859582 3008782000433598592177279 := by
  unfold tailWord_5859582
  simp only [CollatzResearch.WordTrace]
  refine ⟨26714564132217828222246625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142477675371828417185315333 26714564132217828222246625)
  ·
    refine ⟨20035923099163371166684969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26714564132217828222246625 20035923099163371166684969)
    ·
      refine ⟨15026942324372528375013727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20035923099163371166684969 15026942324372528375013727)
      ·
        refine ⟨22540413486558792562520591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15026942324372528375013727 22540413486558792562520591)
        ·
          refine ⟨33810620229838188843780887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22540413486558792562520591 33810620229838188843780887)
          ·
            refine ⟨50715930344757283265671331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33810620229838188843780887 50715930344757283265671331)
            ·
              refine ⟨76073895517135924898506997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50715930344757283265671331 76073895517135924898506997)
              ·
                refine ⟨7131927704731492959235031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76073895517135924898506997 7131927704731492959235031)
                ·
                  refine ⟨10697891557097239438852547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7131927704731492959235031 10697891557097239438852547)
                  ·
                    refine ⟨16046837335645859158278821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10697891557097239438852547 16046837335645859158278821)
                    ·
                      refine ⟨3008782000433598592177279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16046837335645859158278821 3008782000433598592177279)
                      ·
                        rfl

theorem cell23_5859582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_5859582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859582 prefixEnd_5859582 := by exact prefixLift 5859582
  have htrace : WordTrace (prefixWord ++ tailWord_5859582) baseStart_5859582 baseEnd_5859582 := by
    simpa [prefixWord, tailWord_5859582, baseEnd_5859582] using wordTrace_append hprefix tailTrace_5859582
  have hstable : (prefixWord ++ tailWord_5859582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859582).length < 2 ^ (prefixWord ++ tailWord_5859582).sum := by decide
  have hdescent : baseEnd_5859582 < baseStart_5859582 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859585 : List Nat := [1, 2, 4, 1, 1, 2, 4, 1, 1, 1, 5]
def baseStart_5859585 : Nat := 118140960795 + 5859585 * 2 ^ 59
def prefixEnd_5859585 : Nat := 4983230072969 + 3 ^ 40 * 5859585 * 2
def baseEnd_5859585 : Nat := 3008783540875562080439765

theorem tailTrace_5859585 : CollatzResearch.WordTrace tailWord_5859585 prefixEnd_5859585 3008783540875562080439765 := by
  unfold tailWord_5859585
  simp only [CollatzResearch.WordTrace]
  refine ⟨213716622476731757290332209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142477748317821171526888139 213716622476731757290332209)
  ·
    refine ⟨160287466857548817967749157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213716622476731757290332209 160287466857548817967749157)
    ·
      refine ⟨30053900035790403368952967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160287466857548817967749157 30053900035790403368952967)
      ·
        refine ⟨45080850053685605053429451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30053900035790403368952967 45080850053685605053429451)
        ·
          refine ⟨67621275080528407580144177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45080850053685605053429451 67621275080528407580144177)
          ·
            refine ⟨50715956310396305685108133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67621275080528407580144177 50715956310396305685108133)
            ·
              refine ⟨9509241808199307315957775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50715956310396305685108133 9509241808199307315957775)
              ·
                refine ⟨14263862712298960973936663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9509241808199307315957775 14263862712298960973936663)
                ·
                  refine ⟨21395794068448441460904995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14263862712298960973936663 21395794068448441460904995)
                  ·
                    refine ⟨32093691102672662191357493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21395794068448441460904995 32093691102672662191357493)
                    ·
                      refine ⟨3008783540875562080439765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32093691102672662191357493 3008783540875562080439765)
                      ·
                        rfl

theorem cell23_5859585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_5859585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859585 prefixEnd_5859585 := by exact prefixLift 5859585
  have htrace : WordTrace (prefixWord ++ tailWord_5859585) baseStart_5859585 baseEnd_5859585 := by
    simpa [prefixWord, tailWord_5859585, baseEnd_5859585] using wordTrace_append hprefix tailTrace_5859585
  have hstable : (prefixWord ++ tailWord_5859585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859585).length < 2 ^ (prefixWord ++ tailWord_5859585).sum := by decide
  have hdescent : baseEnd_5859585 < baseStart_5859585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859599 : List Nat := [1, 1, 2, 1, 1, 1, 3, 8, 1, 2, 2]
def baseStart_5859599 : Nat := 118140960795 + 5859599 * 2 ^ 59
def prefixEnd_5859599 : Nat := 4983230072969 + 3 ^ 40 * 5859599 * 2
def baseEnd_5859599 : Nat := 3008790729604725025664701

theorem tailTrace_5859599 : CollatzResearch.WordTrace tailWord_5859599 prefixEnd_5859599 3008790729604725025664701 := by
  unfold tailWord_5859599
  simp only [CollatzResearch.WordTrace]
  refine ⟨213717133098681037681341851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142478088732454025120894567 213717133098681037681341851)
  ·
    refine ⟨320575699648021556522012777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213717133098681037681341851 320575699648021556522012777)
    ·
      refine ⟨240431774736016167391509583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320575699648021556522012777 240431774736016167391509583)
      ·
        refine ⟨360647662104024251087264375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240431774736016167391509583 360647662104024251087264375)
        ·
          refine ⟨540971493156036376630896563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360647662104024251087264375 540971493156036376630896563)
          ·
            refine ⟨811457239734054564946344845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540971493156036376630896563 811457239734054564946344845)
            ·
              refine ⟨304296464900270461854879317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 811457239734054564946344845 304296464900270461854879317)
              ·
                refine ⟨3565974198050044474861867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 304296464900270461854879317 3565974198050044474861867)
                ·
                  refine ⟨5348961297075066712292801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3565974198050044474861867 5348961297075066712292801)
                  ·
                    refine ⟨4011720972806300034219601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5348961297075066712292801 4011720972806300034219601)
                    ·
                      refine ⟨3008790729604725025664701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4011720972806300034219601 3008790729604725025664701)
                      ·
                        rfl

theorem cell23_5859599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 8, 1, 2, 2].length) (baseStart_5859599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859599 prefixEnd_5859599 := by exact prefixLift 5859599
  have htrace : WordTrace (prefixWord ++ tailWord_5859599) baseStart_5859599 baseEnd_5859599 := by
    simpa [prefixWord, tailWord_5859599, baseEnd_5859599] using wordTrace_append hprefix tailTrace_5859599
  have hstable : (prefixWord ++ tailWord_5859599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859599).length < 2 ^ (prefixWord ++ tailWord_5859599).sum := by decide
  have hdescent : baseEnd_5859599 < baseStart_5859599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859608 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 2, 2, 6]
def baseStart_5859608 : Nat := 118140960795 + 5859608 * 2 ^ 59
def prefixEnd_5859608 : Nat := 4983230072969 + 3 ^ 40 * 5859608 * 2
def baseEnd_5859608 : Nat := 3008795350930615490452159

theorem tailTrace_5859608 : CollatzResearch.WordTrace tailWord_5859608 prefixEnd_5859608 3008795350930615490452159 := by
  unfold tailWord_5859608
  simp only [CollatzResearch.WordTrace]
  refine ⟨106858730677824216109209739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142478307570432288145612985 106858730677824216109209739)
  ·
    refine ⟨160288096016736324163814609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106858730677824216109209739 160288096016736324163814609)
    ·
      refine ⟨120216072012552243122860957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160288096016736324163814609 120216072012552243122860957)
      ·
        refine ⟨45081027004707091171072859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120216072012552243122860957 45081027004707091171072859)
        ·
          refine ⟨67621540507060636756609289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45081027004707091171072859 67621540507060636756609289)
          ·
            refine ⟨50716155380295477567456967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67621540507060636756609289 50716155380295477567456967)
            ·
              refine ⟨76074233070443216351185451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50716155380295477567456967 76074233070443216351185451)
              ·
                refine ⟨114111349605664824526778177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76074233070443216351185451 114111349605664824526778177)
                ·
                  refine ⟨85583512204248618395083633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114111349605664824526778177 85583512204248618395083633)
                  ·
                    refine ⟨64187634153186463796312725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 85583512204248618395083633 64187634153186463796312725)
                    ·
                      refine ⟨3008795350930615490452159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64187634153186463796312725 3008795350930615490452159)
                      ·
                        rfl

theorem cell23_5859608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_5859608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859608 prefixEnd_5859608 := by exact prefixLift 5859608
  have htrace : WordTrace (prefixWord ++ tailWord_5859608) baseStart_5859608 baseEnd_5859608 := by
    simpa [prefixWord, tailWord_5859608, baseEnd_5859608] using wordTrace_append hprefix tailTrace_5859608
  have hstable : (prefixWord ++ tailWord_5859608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859608).length < 2 ^ (prefixWord ++ tailWord_5859608).sum := by decide
  have hdescent : baseEnd_5859608 < baseStart_5859608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859628 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 5]
def baseStart_5859628 : Nat := 118140960795 + 5859628 * 2 ^ 59
def prefixEnd_5859628 : Nat := 4983230072969 + 3 ^ 40 * 5859628 * 2
def baseEnd_5859628 : Nat := 3008805620543705412202067

theorem tailTrace_5859628 : CollatzResearch.WordTrace tailWord_5859628 prefixEnd_5859628 3008805620543705412202067 := by
  unfold tailWord_5859628
  simp only [CollatzResearch.WordTrace]
  refine ⟨106859095407787987817073769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142478793877050650422765025 106859095407787987817073769)
  ·
    refine ⟨80144321555840990862805327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106859095407787987817073769 80144321555840990862805327)
    ·
      refine ⟨120216482333761486294207991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80144321555840990862805327 120216482333761486294207991)
      ·
        refine ⟨180324723500642229441311987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120216482333761486294207991 180324723500642229441311987)
        ·
          refine ⟨270487085250963344161967981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180324723500642229441311987 270487085250963344161967981)
          ·
            refine ⟨101432656969111254060737993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 270487085250963344161967981 101432656969111254060737993)
            ·
              refine ⟨76074492726833440545553495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101432656969111254060737993 76074492726833440545553495)
              ·
                refine ⟨114111739090250160818330243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76074492726833440545553495 114111739090250160818330243)
                ·
                  refine ⟨171167608635375241227495365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114111739090250160818330243 171167608635375241227495365)
                  ·
                    refine ⟨32093926619132857730155381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 171167608635375241227495365 32093926619132857730155381)
                    ·
                      refine ⟨3008805620543705412202067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32093926619132857730155381 3008805620543705412202067)
                      ·
                        rfl

theorem cell23_5859628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_5859628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859628 prefixEnd_5859628 := by exact prefixLift 5859628
  have htrace : WordTrace (prefixWord ++ tailWord_5859628) baseStart_5859628 baseEnd_5859628 := by
    simpa [prefixWord, tailWord_5859628, baseEnd_5859628] using wordTrace_append hprefix tailTrace_5859628
  have hstable : (prefixWord ++ tailWord_5859628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859628).length < 2 ^ (prefixWord ++ tailWord_5859628).sum := by decide
  have hdescent : baseEnd_5859628 < baseStart_5859628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859629 : List Nat := [1, 5, 3, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_5859629 : Nat := 118140960795 + 5859629 * 2 ^ 59
def prefixEnd_5859629 : Nat := 4983230072969 + 3 ^ 40 * 5859629 * 2
def baseEnd_5859629 : Nat := 3008806134024359908289563

theorem tailTrace_5859629 : CollatzResearch.WordTrace tailWord_5859629 prefixEnd_5859629 3008806134024359908289563 := by
  unfold tailWord_5859629
  simp only [CollatzResearch.WordTrace]
  refine ⟨213718227288572352804933941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142478818192381568536622627 213718227288572352804933941)
  ·
    refine ⟨20036083808303658075462557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 213718227288572352804933941 20036083808303658075462557)
    ·
      refine ⟨7513531428113871778298459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20036083808303658075462557 7513531428113871778298459)
      ·
        refine ⟨11270297142170807667447689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7513531428113871778298459 11270297142170807667447689)
        ·
          refine ⟨8452722856628105750585767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11270297142170807667447689 8452722856628105750585767)
          ·
            refine ⟨12679084284942158625878651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8452722856628105750585767 12679084284942158625878651)
            ·
              refine ⟨19018626427413237938817977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12679084284942158625878651 19018626427413237938817977)
              ·
                refine ⟨14263969820559928454113483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19018626427413237938817977 14263969820559928454113483)
                ·
                  refine ⟨21395954730839892681170225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14263969820559928454113483 21395954730839892681170225)
                  ·
                    refine ⟨16046966048129919510877669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21395954730839892681170225 16046966048129919510877669)
                    ·
                      refine ⟨3008806134024359908289563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16046966048129919510877669 3008806134024359908289563)
                      ·
                        rfl

theorem cell23_5859629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_5859629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859629 prefixEnd_5859629 := by exact prefixLift 5859629
  have htrace : WordTrace (prefixWord ++ tailWord_5859629) baseStart_5859629 baseEnd_5859629 := by
    simpa [prefixWord, tailWord_5859629, baseEnd_5859629] using wordTrace_append hprefix tailTrace_5859629
  have hstable : (prefixWord ++ tailWord_5859629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859629).length < 2 ^ (prefixWord ++ tailWord_5859629).sum := by decide
  have hdescent : baseEnd_5859629 < baseStart_5859629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859636 : List Nat := [2, 5, 1, 1, 1, 3, 3, 1, 1, 2, 3]
def baseStart_5859636 : Nat := 118140960795 + 5859636 * 2 ^ 59
def prefixEnd_5859636 : Nat := 4983230072969 + 3 ^ 40 * 5859636 * 2
def baseEnd_5859636 : Nat := 3008809728388941380902031

theorem tailTrace_5859636 : CollatzResearch.WordTrace tailWord_5859636 prefixEnd_5859636 3008809728388941380902031 := by
  unfold tailWord_5859636
  simp only [CollatzResearch.WordTrace]
  refine ⟨106859241299773496500219381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142478988399697995333625841 106859241299773496500219381)
  ·
    refine ⟨10018053871853765296895567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106859241299773496500219381 10018053871853765296895567)
    ·
      refine ⟨15027080807780647945343351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10018053871853765296895567 15027080807780647945343351)
      ·
        refine ⟨22540621211670971918015027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15027080807780647945343351 22540621211670971918015027)
        ·
          refine ⟨33810931817506457877022541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22540621211670971918015027 33810931817506457877022541)
          ·
            refine ⟨12679099431564921703883453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33810931817506457877022541 12679099431564921703883453)
            ·
              refine ⟨4754662286836845638956295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12679099431564921703883453 4754662286836845638956295)
              ·
                refine ⟨7131993430255268458434443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4754662286836845638956295 7131993430255268458434443)
                ·
                  refine ⟨10697990145382902687651665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7131993430255268458434443 10697990145382902687651665)
                  ·
                    refine ⟨8023492609037177015738749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10697990145382902687651665 8023492609037177015738749)
                    ·
                      refine ⟨3008809728388941380902031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8023492609037177015738749 3008809728388941380902031)
                      ·
                        rfl

theorem cell23_5859636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_5859636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859636 prefixEnd_5859636 := by exact prefixLift 5859636
  have htrace : WordTrace (prefixWord ++ tailWord_5859636) baseStart_5859636 baseEnd_5859636 := by
    simpa [prefixWord, tailWord_5859636, baseEnd_5859636] using wordTrace_append hprefix tailTrace_5859636
  have hstable : (prefixWord ++ tailWord_5859636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859636).length < 2 ^ (prefixWord ++ tailWord_5859636).sum := by decide
  have hdescent : baseEnd_5859636 < baseStart_5859636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859665 : List Nat := [1, 2, 2, 1, 4, 3, 1, 1, 2, 6]
def baseStart_5859665 : Nat := 118140960795 + 5859665 * 2 ^ 59
def prefixEnd_5859665 : Nat := 4983230072969 + 3 ^ 40 * 5859665 * 2
def baseEnd_5859665 : Nat := 1002941539775973922479799

theorem tailTrace_5859665 : CollatzResearch.WordTrace tailWord_5859665 prefixEnd_5859665 1002941539775973922479799 := by
  unfold tailWord_5859665
  simp only [CollatzResearch.WordTrace]
  refine ⟨213719540316441930953244449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142479693544294620635496299 213719540316441930953244449)
  ·
    refine ⟨160289655237331448214933337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213719540316441930953244449 160289655237331448214933337)
    ·
      refine ⟨120217241427998586161200003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160289655237331448214933337 120217241427998586161200003)
      ·
        refine ⟨180325862141997879241800005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120217241427998586161200003 180325862141997879241800005)
        ·
          refine ⟨33811099151624602357837501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180325862141997879241800005 33811099151624602357837501)
          ·
            refine ⟨12679162181859225884189063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33811099151624602357837501 12679162181859225884189063)
            ·
              refine ⟨19018743272788838826283595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12679162181859225884189063 19018743272788838826283595)
              ·
                refine ⟨28528114909183258239425393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19018743272788838826283595 28528114909183258239425393)
                ·
                  refine ⟨21396086181887443679569045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28528114909183258239425393 21396086181887443679569045)
                  ·
                    refine ⟨1002941539775973922479799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21396086181887443679569045 1002941539775973922479799)
                    ·
                      rfl

theorem cell23_5859665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 6].length) (baseStart_5859665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859665 prefixEnd_5859665 := by exact prefixLift 5859665
  have htrace : WordTrace (prefixWord ++ tailWord_5859665) baseStart_5859665 baseEnd_5859665 := by
    simpa [prefixWord, tailWord_5859665, baseEnd_5859665] using wordTrace_append hprefix tailTrace_5859665
  have hstable : (prefixWord ++ tailWord_5859665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859665).length < 2 ^ (prefixWord ++ tailWord_5859665).sum := by decide
  have hdescent : baseEnd_5859665 < baseStart_5859665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859762 : List Nat := [3, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4]
def baseStart_5859762 : Nat := 118140960795 + 5859762 * 2 ^ 59
def prefixEnd_5859762 : Nat := 4983230072969 + 3 ^ 40 * 5859762 * 2
def baseEnd_5859762 : Nat := 3008874426951407887926451

theorem tailTrace_5859762 : CollatzResearch.WordTrace tailWord_5859762 prefixEnd_5859762 3008874426951407887926451 := by
  unfold tailWord_5859762
  simp only [CollatzResearch.WordTrace]
  refine ⟨53430769549272629129881385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142482052131393677679683693 53430769549272629129881385)
  ·
    refine ⟨40073077161954471847411039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53430769549272629129881385 40073077161954471847411039)
    ·
      refine ⟨60109615742931707771116559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40073077161954471847411039 60109615742931707771116559)
      ·
        refine ⟨90164423614397561656674839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60109615742931707771116559 90164423614397561656674839)
        ·
          refine ⟨135246635421596342485012259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90164423614397561656674839 135246635421596342485012259)
          ·
            refine ⟨202869953132394513727518389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135246635421596342485012259 202869953132394513727518389)
            ·
              refine ⟨19019058106161985661954849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 202869953132394513727518389 19019058106161985661954849)
              ·
                refine ⟨14264293579621489246466137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19019058106161985661954849 14264293579621489246466137)
                ·
                  refine ⟨10698220184716116934849603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14264293579621489246466137 10698220184716116934849603)
                  ·
                    refine ⟨16047330277074175402274405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10698220184716116934849603 16047330277074175402274405)
                    ·
                      refine ⟨3008874426951407887926451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16047330277074175402274405 3008874426951407887926451)
                      ·
                        rfl

theorem cell23_5859762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_5859762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859762 prefixEnd_5859762 := by exact prefixLift 5859762
  have htrace : WordTrace (prefixWord ++ tailWord_5859762) baseStart_5859762 baseEnd_5859762 := by
    simpa [prefixWord, tailWord_5859762, baseEnd_5859762] using wordTrace_append hprefix tailTrace_5859762
  have hstable : (prefixWord ++ tailWord_5859762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859762).length < 2 ^ (prefixWord ++ tailWord_5859762).sum := by decide
  have hdescent : baseEnd_5859762 < baseStart_5859762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859835 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 4]
def baseStart_5859835 : Nat := 118140960795 + 5859835 * 2 ^ 59
def prefixEnd_5859835 : Nat := 4983230072969 + 3 ^ 40 * 5859835 * 2
def baseEnd_5859835 : Nat := 3008911911039186102313615

theorem tailTrace_5859835 : CollatzResearch.WordTrace tailWord_5859835 prefixEnd_5859835 3008911911039186102313615 := by
  unfold tailWord_5859835
  simp only [CollatzResearch.WordTrace]
  refine ⟨213725740725826049986932959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142483827150550699991288639 213725740725826049986932959)
  ·
    refine ⟨320588611088739074980399439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213725740725826049986932959 320588611088739074980399439)
    ·
      refine ⟨480882916633108612470599159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320588611088739074980399439 480882916633108612470599159)
      ·
        refine ⟨721324374949662918705898739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480882916633108612470599159 721324374949662918705898739)
        ·
          refine ⟨1081986562424494378058848109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 721324374949662918705898739 1081986562424494378058848109)
          ·
            refine ⟨405744960909185391772068041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1081986562424494378058848109 405744960909185391772068041)
            ·
              refine ⟨304308720681889043829051031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 405744960909185391772068041 304308720681889043829051031)
              ·
                refine ⟨456463081022833565743576547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304308720681889043829051031 456463081022833565743576547)
                ·
                  refine ⟨684694621534250348615364821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 456463081022833565743576547 684694621534250348615364821)
                  ·
                    refine ⟨16047530192208992545672613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 684694621534250348615364821 16047530192208992545672613)
                    ·
                      refine ⟨3008911911039186102313615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16047530192208992545672613 3008911911039186102313615)
                      ·
                        rfl

theorem cell23_5859835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 7, 4].length) (baseStart_5859835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859835 prefixEnd_5859835 := by exact prefixLift 5859835
  have htrace : WordTrace (prefixWord ++ tailWord_5859835) baseStart_5859835 baseEnd_5859835 := by
    simpa [prefixWord, tailWord_5859835, baseEnd_5859835] using wordTrace_append hprefix tailTrace_5859835
  have hstable : (prefixWord ++ tailWord_5859835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859835).length < 2 ^ (prefixWord ++ tailWord_5859835).sum := by decide
  have hdescent : baseEnd_5859835 < baseStart_5859835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859896 : List Nat := [2, 1, 2, 1, 4, 1, 5, 1, 2, 4]
def baseStart_5859896 : Nat := 118140960795 + 5859896 * 2 ^ 59
def prefixEnd_5859896 : Nat := 4983230072969 + 3 ^ 40 * 5859896 * 2
def baseEnd_5859896 : Nat := 1002981077786370121216945

theorem tailTrace_5859896 : CollatzResearch.WordTrace tailWord_5859896 prefixEnd_5859896 1002981077786370121216945 := by
  unfold tailWord_5859896
  simp only [CollatzResearch.WordTrace]
  refine ⟨106863982789302528702451771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142485310385736704936602361 106863982789302528702451771)
  ·
    refine ⟨160295974183953793053677657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106863982789302528702451771 160295974183953793053677657)
    ·
      refine ⟨120221980637965344790258243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160295974183953793053677657 120221980637965344790258243)
      ·
        refine ⟨180332970956948017185387365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120221980637965344790258243 180332970956948017185387365)
        ·
          refine ⟨33812432054427753222260131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180332970956948017185387365 33812432054427753222260131)
          ·
            refine ⟨50718648081641629833390197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33812432054427753222260131 50718648081641629833390197)
            ·
              refine ⟨4754873257653902796880331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50718648081641629833390197 4754873257653902796880331)
              ·
                refine ⟨7132309886480854195320497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4754873257653902796880331 7132309886480854195320497)
                ·
                  refine ⟨5349232414860640646490373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7132309886480854195320497 5349232414860640646490373)
                  ·
                    refine ⟨1002981077786370121216945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5349232414860640646490373 1002981077786370121216945)
                    ·
                      rfl

theorem cell23_5859896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 2, 4].length) (baseStart_5859896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859896 prefixEnd_5859896 := by exact prefixLift 5859896
  have htrace : WordTrace (prefixWord ++ tailWord_5859896) baseStart_5859896 baseEnd_5859896 := by
    simpa [prefixWord, tailWord_5859896, baseEnd_5859896] using wordTrace_append hprefix tailTrace_5859896
  have hstable : (prefixWord ++ tailWord_5859896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859896).length < 2 ^ (prefixWord ++ tailWord_5859896).sum := by decide
  have hdescent : baseEnd_5859896 < baseStart_5859896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859909 : List Nat := [1, 3, 1, 1, 1, 7, 2, 7]
def baseStart_5859909 : Nat := 118140960795 + 5859909 * 2 ^ 59
def prefixEnd_5859909 : Nat := 4983230072969 + 3 ^ 40 * 5859909 * 2
def baseEnd_5859909 : Nat := 111442589207689585658825

theorem tailTrace_5859909 : CollatzResearch.WordTrace tailWord_5859909 prefixEnd_5859909 111442589207689585658825 := by
  unfold tailWord_5859909
  simp only [CollatzResearch.WordTrace]
  refine ⟨213728439727557960625126781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142485626485038640416751187 213728439727557960625126781)
  ·
    refine ⟨80148164897834235234422543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213728439727557960625126781 80148164897834235234422543)
    ·
      refine ⟨120222247346751352851633815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80148164897834235234422543 120222247346751352851633815)
      ·
        refine ⟨180333371020127029277450723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120222247346751352851633815 180333371020127029277450723)
        ·
          refine ⟨270500056530190543916176085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180333371020127029277450723 270500056530190543916176085)
          ·
            refine ⟨6339845074926340873035377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 270500056530190543916176085 6339845074926340873035377)
            ·
              refine ⟨4754883806194755654776533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6339845074926340873035377 4754883806194755654776533)
              ·
                refine ⟨111442589207689585658825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4754883806194755654776533 111442589207689585658825)
                ·
                  rfl

theorem cell23_5859909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 7].length) (baseStart_5859909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859909 prefixEnd_5859909 := by exact prefixLift 5859909
  have htrace : WordTrace (prefixWord ++ tailWord_5859909) baseStart_5859909 baseEnd_5859909 := by
    simpa [prefixWord, tailWord_5859909, baseEnd_5859909] using wordTrace_append hprefix tailTrace_5859909
  have hstable : (prefixWord ++ tailWord_5859909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859909).length < 2 ^ (prefixWord ++ tailWord_5859909).sum := by decide
  have hdescent : baseEnd_5859909 < baseStart_5859909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859919 : List Nat := [1, 1, 2, 1, 1, 2, 5, 2, 4, 1, 3]
def baseStart_5859919 : Nat := 118140960795 + 5859919 * 2 ^ 59
def prefixEnd_5859919 : Nat := 4983230072969 + 3 ^ 40 * 5859919 * 2
def baseEnd_5859919 : Nat := 3008955043414163773663229

theorem tailTrace_5859919 : CollatzResearch.WordTrace tailWord_5859919 prefixEnd_5859919 3008955043414163773663229 := by
  unfold tailWord_5859919
  simp only [CollatzResearch.WordTrace]
  refine ⟨213728804457521732332990811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142485869638347821555327207 213728804457521732332990811)
  ·
    refine ⟨320593206686282598499486217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213728804457521732332990811 320593206686282598499486217)
    ·
      refine ⟨240444905014711948874614663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320593206686282598499486217 240444905014711948874614663)
      ·
        refine ⟨360667357522067923311921995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240444905014711948874614663 360667357522067923311921995)
        ·
          refine ⟨541001036283101884967882993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360667357522067923311921995 541001036283101884967882993)
          ·
            refine ⟨405750777212326413725912245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 541001036283101884967882993 405750777212326413725912245)
            ·
              refine ⟨38039135363655601286804273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 405750777212326413725912245 38039135363655601286804273)
              ·
                refine ⟨28529351522741700965103205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38039135363655601286804273 28529351522741700965103205)
                ·
                  refine ⟨5349253410514068930956851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28529351522741700965103205 5349253410514068930956851)
                  ·
                    refine ⟨8023880115771103396435277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5349253410514068930956851 8023880115771103396435277)
                    ·
                      refine ⟨3008955043414163773663229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8023880115771103396435277 3008955043414163773663229)
                      ·
                        rfl

theorem cell23_5859919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 4, 1, 3].length) (baseStart_5859919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859919 prefixEnd_5859919 := by exact prefixLift 5859919
  have htrace : WordTrace (prefixWord ++ tailWord_5859919) baseStart_5859919 baseEnd_5859919 := by
    simpa [prefixWord, tailWord_5859919, baseEnd_5859919] using wordTrace_append hprefix tailTrace_5859919
  have hstable : (prefixWord ++ tailWord_5859919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859919).length < 2 ^ (prefixWord ++ tailWord_5859919).sum := by decide
  have hdescent : baseEnd_5859919 < baseStart_5859919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859929 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 7, 3, 2]
def baseStart_5859929 : Nat := 118140960795 + 5859929 * 2 ^ 59
def prefixEnd_5859929 : Nat := 4983230072969 + 3 ^ 40 * 5859929 * 2
def baseEnd_5859929 : Nat := 3008960178220708734538183

theorem tailTrace_5859929 : CollatzResearch.WordTrace tailWord_5859929 prefixEnd_5859929 3008960178220708734538183 := by
  unfold tailWord_5859929
  simp only [CollatzResearch.WordTrace]
  refine ⟨213729169187485504040854841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142486112791657002693903227 213729169187485504040854841)
  ·
    refine ⟨160296876890614128030641131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213729169187485504040854841 160296876890614128030641131)
    ·
      refine ⟨240445315335921192045961697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160296876890614128030641131 240445315335921192045961697)
      ·
        refine ⟨180333986501940894034471273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240445315335921192045961697 180333986501940894034471273)
        ·
          refine ⟨135250489876455670525853455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180333986501940894034471273 135250489876455670525853455)
          ·
            refine ⟨202875734814683505788780183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135250489876455670525853455 202875734814683505788780183)
            ·
              refine ⟨304313602222025258683170275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202875734814683505788780183 304313602222025258683170275)
              ·
                refine ⟨456470403333037888024755413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304313602222025258683170275 456470403333037888024755413)
                ·
                  refine ⟨10698525078118075500580205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 456470403333037888024755413 10698525078118075500580205)
                  ·
                    refine ⟨4011946904294278312717577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10698525078118075500580205 4011946904294278312717577)
                    ·
                      refine ⟨3008960178220708734538183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4011946904294278312717577 3008960178220708734538183)
                      ·
                        rfl

theorem cell23_5859929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 3, 2].length) (baseStart_5859929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859929 prefixEnd_5859929 := by exact prefixLift 5859929
  have htrace : WordTrace (prefixWord ++ tailWord_5859929) baseStart_5859929 baseEnd_5859929 := by
    simpa [prefixWord, tailWord_5859929, baseEnd_5859929] using wordTrace_append hprefix tailTrace_5859929
  have hstable : (prefixWord ++ tailWord_5859929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859929).length < 2 ^ (prefixWord ++ tailWord_5859929).sum := by decide
  have hdescent : baseEnd_5859929 < baseStart_5859929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859946 : List Nat := [3, 1, 3, 2, 1, 1, 2, 2, 3, 3, 2]
def baseStart_5859946 : Nat := 118140960795 + 5859946 * 2 ^ 59
def prefixEnd_5859946 : Nat := 4983230072969 + 3 ^ 40 * 5859946 * 2
def baseEnd_5859946 : Nat := 3008968907391835168025605

theorem tailTrace_5859946 : CollatzResearch.WordTrace tailWord_5859946 prefixEnd_5859946 3008968907391835168025605 := by
  unfold tailWord_5859946
  simp only [CollatzResearch.WordTrace]
  refine ⟨53432447307105978986055923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142486526152282610629482461 53432447307105978986055923)
  ·
    refine ⟨80148670960658968479083885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53432447307105978986055923 80148670960658968479083885)
    ·
      refine ⟨30055751610247113179656457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80148670960658968479083885 30055751610247113179656457)
      ·
        refine ⟨22541813707685334884742343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30055751610247113179656457 22541813707685334884742343)
        ·
          refine ⟨33812720561528002327113515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22541813707685334884742343 33812720561528002327113515)
          ·
            refine ⟨50719080842292003490670273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33812720561528002327113515 50719080842292003490670273)
            ·
              refine ⟨38039310631719002618002705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50719080842292003490670273 38039310631719002618002705)
              ·
                refine ⟨28529482973789251963502029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38039310631719002618002705 28529482973789251963502029)
                ·
                  refine ⟨10698556115170969486313261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28529482973789251963502029 10698556115170969486313261)
                  ·
                    refine ⟨4011958543189113557367473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10698556115170969486313261 4011958543189113557367473)
                    ·
                      refine ⟨3008968907391835168025605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4011958543189113557367473 3008968907391835168025605)
                      ·
                        rfl

theorem cell23_5859946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_5859946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859946 prefixEnd_5859946 := by exact prefixLift 5859946
  have htrace : WordTrace (prefixWord ++ tailWord_5859946) baseStart_5859946 baseEnd_5859946 := by
    simpa [prefixWord, tailWord_5859946, baseEnd_5859946] using wordTrace_append hprefix tailTrace_5859946
  have hstable : (prefixWord ++ tailWord_5859946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859946).length < 2 ^ (prefixWord ++ tailWord_5859946).sum := by decide
  have hdescent : baseEnd_5859946 < baseStart_5859946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5859993 : List Nat := [1, 2, 1, 2, 1, 2, 6, 2, 2, 2, 2]
def baseStart_5859993 : Nat := 118140960795 + 5859993 * 2 ^ 59
def prefixEnd_5859993 : Nat := 4983230072969 + 3 ^ 40 * 5859993 * 2
def baseEnd_5859993 : Nat := 3008993040982596484137889

theorem tailTrace_5859993 : CollatzResearch.WordTrace tailWord_5859993 prefixEnd_5859993 3008993040982596484137889 := by
  unfold tailWord_5859993
  simp only [CollatzResearch.WordTrace]
  refine ⟨213731503459253642971184633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142487668972835761980789755 213731503459253642971184633)
  ·
    refine ⟨160298627594440232228388475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213731503459253642971184633 160298627594440232228388475)
    ·
      refine ⟨240447941391660348342582713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160298627594440232228388475 240447941391660348342582713)
      ·
        refine ⟨180335956043745261256937035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240447941391660348342582713 180335956043745261256937035)
        ·
          refine ⟨270503934065617891885405553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180335956043745261256937035 270503934065617891885405553)
          ·
            refine ⟨202877950549213418914054165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270503934065617891885405553 202877950549213418914054165)
            ·
              refine ⟨9509903931994379011596289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 202877950549213418914054165 9509903931994379011596289)
              ·
                refine ⟨7132427948995784258697217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9509903931994379011596289 7132427948995784258697217)
                ·
                  refine ⟨5349320961746838194022913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7132427948995784258697217 5349320961746838194022913)
                  ·
                    refine ⟨4011990721310128645517185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5349320961746838194022913 4011990721310128645517185)
                    ·
                      refine ⟨3008993040982596484137889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4011990721310128645517185 3008993040982596484137889)
                      ·
                        rfl

theorem cell23_5859993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 2, 2, 2].length) (baseStart_5859993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5859993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5859993 prefixEnd_5859993 := by exact prefixLift 5859993
  have htrace : WordTrace (prefixWord ++ tailWord_5859993) baseStart_5859993 baseEnd_5859993 := by
    simpa [prefixWord, tailWord_5859993, baseEnd_5859993] using wordTrace_append hprefix tailTrace_5859993
  have hstable : (prefixWord ++ tailWord_5859993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5859993).length < 2 ^ (prefixWord ++ tailWord_5859993).sum := by decide
  have hdescent : baseEnd_5859993 < baseStart_5859993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5859993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860029 : List Nat := [1, 4, 1, 2, 1, 4, 1, 1, 1, 7]
def baseStart_5860029 : Nat := 118140960795 + 5860029 * 2 ^ 59
def prefixEnd_5860029 : Nat := 4983230072969 + 3 ^ 40 * 5860029 * 2
def baseEnd_5860029 : Nat := 1003003842095386114429241

theorem tailTrace_5860029 : CollatzResearch.WordTrace tailWord_5860029 prefixEnd_5860029 1003003842095386114429241 := by
  unfold tailWord_5860029
  simp only [CollatzResearch.WordTrace]
  refine ⟨213732816487123221119495141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142488544324748814079663427 213732816487123221119495141)
  ·
    refine ⟨40074903091335603959905339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213732816487123221119495141 40074903091335603959905339)
    ·
      refine ⟨60112354637003405939858009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40074903091335603959905339 60112354637003405939858009)
      ·
        refine ⟨45084265977752554454893507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60112354637003405939858009 45084265977752554454893507)
        ·
          refine ⟨67626398966628831682340261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45084265977752554454893507 67626398966628831682340261)
          ·
            refine ⟨12679949806242905940438799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67626398966628831682340261 12679949806242905940438799)
            ·
              refine ⟨19019924709364358910658199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12679949806242905940438799 19019924709364358910658199)
              ·
                refine ⟨28529887064046538365987299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19019924709364358910658199 28529887064046538365987299)
                ·
                  refine ⟨42794830596069807548980949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28529887064046538365987299 42794830596069807548980949)
                  ·
                    refine ⟨1003003842095386114429241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42794830596069807548980949 1003003842095386114429241)
                    ·
                      rfl

theorem cell23_5860029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_5860029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860029 prefixEnd_5860029 := by exact prefixLift 5860029
  have htrace : WordTrace (prefixWord ++ tailWord_5860029) baseStart_5860029 baseEnd_5860029 := by
    simpa [prefixWord, tailWord_5860029, baseEnd_5860029] using wordTrace_append hprefix tailTrace_5860029
  have hstable : (prefixWord ++ tailWord_5860029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860029).length < 2 ^ (prefixWord ++ tailWord_5860029).sum := by decide
  have hdescent : baseEnd_5860029 < baseStart_5860029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860049 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 4, 1, 4]
def baseStart_5860049 : Nat := 118140960795 + 5860049 * 2 ^ 59
def prefixEnd_5860049 : Nat := 4983230072969 + 3 ^ 40 * 5860049 * 2
def baseEnd_5860049 : Nat := 3009021795899248265037631

theorem tailTrace_5860049 : CollatzResearch.WordTrace tailWord_5860049 prefixEnd_5860049 3009021795899248265037631 := by
  unfold tailWord_5860049
  simp only [CollatzResearch.WordTrace]
  refine ⟨213733545947050764535223201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142489030631367176356815467 213733545947050764535223201)
  ·
    refine ⟨160300159460288073401417401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213733545947050764535223201 160300159460288073401417401)
    ·
      refine ⟨120225119595216055051063051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160300159460288073401417401 120225119595216055051063051)
      ·
        refine ⟨180337679392824082576594577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120225119595216055051063051 180337679392824082576594577)
        ·
          refine ⟨135253259544618061932445933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180337679392824082576594577 135253259544618061932445933)
          ·
            refine ⟨50719972329231773224667225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135253259544618061932445933 50719972329231773224667225)
            ·
              refine ⟨38039979246923829918500419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50719972329231773224667225 38039979246923829918500419)
              ·
                refine ⟨57059968870385744877750629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38039979246923829918500419 57059968870385744877750629)
                ·
                  refine ⟨10698744163197327164578243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57059968870385744877750629 10698744163197327164578243)
                  ·
                    refine ⟨16048116244795990746867365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10698744163197327164578243 16048116244795990746867365)
                    ·
                      refine ⟨3009021795899248265037631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16048116244795990746867365 3009021795899248265037631)
                      ·
                        rfl

theorem cell23_5860049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 1, 4].length) (baseStart_5860049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860049 prefixEnd_5860049 := by exact prefixLift 5860049
  have htrace : WordTrace (prefixWord ++ tailWord_5860049) baseStart_5860049 baseEnd_5860049 := by
    simpa [prefixWord, tailWord_5860049, baseEnd_5860049] using wordTrace_append hprefix tailTrace_5860049
  have hstable : (prefixWord ++ tailWord_5860049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860049).length < 2 ^ (prefixWord ++ tailWord_5860049).sum := by decide
  have hdescent : baseEnd_5860049 < baseStart_5860049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860084 : List Nat := [2, 6, 1, 1, 3, 1, 1, 3, 5]
def baseStart_5860084 : Nat := 118140960795 + 5860084 * 2 ^ 59
def prefixEnd_5860084 : Nat := 4983230072969 + 3 ^ 40 * 5860084 * 2
def baseEnd_5860084 : Nat := 334337751969128403122219

theorem tailTrace_5860084 : CollatzResearch.WordTrace tailWord_5860084 prefixEnd_5860084 334337751969128403122219 := by
  unfold tailWord_5860084
  simp only [CollatzResearch.WordTrace]
  refine ⟨106867411250961982756373653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142489881667949310341831537 106867411250961982756373653)
  ·
    refine ⟨5009409902388842941705015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 106867411250961982756373653 5009409902388842941705015)
    ·
      refine ⟨7514114853583264412557523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5009409902388842941705015 7514114853583264412557523)
      ·
        refine ⟨11271172280374896618836285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7514114853583264412557523 11271172280374896618836285)
        ·
          refine ⟨4226689605140586232063607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11271172280374896618836285 4226689605140586232063607)
          ·
            refine ⟨6340034407710879348095411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4226689605140586232063607 6340034407710879348095411)
            ·
              refine ⟨9510051611566319022143117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6340034407710879348095411 9510051611566319022143117)
              ·
                refine ⟨3566269354337369633303669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9510051611566319022143117 3566269354337369633303669)
                ·
                  refine ⟨334337751969128403122219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3566269354337369633303669 334337751969128403122219)
                  ·
                    rfl

theorem cell23_5860084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_5860084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860084 prefixEnd_5860084 := by exact prefixLift 5860084
  have htrace : WordTrace (prefixWord ++ tailWord_5860084) baseStart_5860084 baseEnd_5860084 := by
    simpa [prefixWord, tailWord_5860084, baseEnd_5860084] using wordTrace_append hprefix tailTrace_5860084
  have hstable : (prefixWord ++ tailWord_5860084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860084).length < 2 ^ (prefixWord ++ tailWord_5860084).sum := by decide
  have hdescent : baseEnd_5860084 < baseStart_5860084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860086 : List Nat := [5, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3]
def baseStart_5860086 : Nat := 118140960795 + 5860086 * 2 ^ 59
def prefixEnd_5860086 : Nat := 4983230072969 + 3 ^ 40 * 5860086 * 2
def baseEnd_5860086 : Nat := 3009040794683464620274961

theorem tailTrace_5860086 : CollatzResearch.WordTrace tailWord_5860086 prefixEnd_5860086 3009040794683464620274961 := by
  unfold tailWord_5860086
  simp only [CollatzResearch.WordTrace]
  refine ⟨13358430965494794990895007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142489930298611146569546741 13358430965494794990895007)
  ·
    refine ⟨20037646448242192486342511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13358430965494794990895007 20037646448242192486342511)
    ·
      refine ⟨30056469672363288729513767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20037646448242192486342511 30056469672363288729513767)
      ·
        refine ⟨45084704508544933094270651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30056469672363288729513767 45084704508544933094270651)
        ·
          refine ⟨67627056762817399641405977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45084704508544933094270651 67627056762817399641405977)
          ·
            refine ⟨50720292572113049731054483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67627056762817399641405977 50720292572113049731054483)
            ·
              refine ⟨76080438858169574596581725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50720292572113049731054483 76080438858169574596581725)
              ·
                refine ⟨28530164571813590473718147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76080438858169574596581725 28530164571813590473718147)
                ·
                  refine ⟨42795246857720385710577221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28530164571813590473718147 42795246857720385710577221)
                  ·
                    refine ⟨8024108785822572320733229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42795246857720385710577221 8024108785822572320733229)
                    ·
                      refine ⟨3009040794683464620274961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8024108785822572320733229 3009040794683464620274961)
                      ·
                        rfl

theorem cell23_5860086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_5860086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860086 prefixEnd_5860086 := by exact prefixLift 5860086
  have htrace : WordTrace (prefixWord ++ tailWord_5860086) baseStart_5860086 baseEnd_5860086 := by
    simpa [prefixWord, tailWord_5860086, baseEnd_5860086] using wordTrace_append hprefix tailTrace_5860086
  have hstable : (prefixWord ++ tailWord_5860086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860086).length < 2 ^ (prefixWord ++ tailWord_5860086).sum := by decide
  have hdescent : baseEnd_5860086 < baseStart_5860086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860103 : List Nat := [1, 1, 4, 4, 1, 2, 1, 2, 2, 2, 3]
def baseStart_5860103 : Nat := 118140960795 + 5860103 * 2 ^ 59
def prefixEnd_5860103 : Nat := 4983230072969 + 3 ^ 40 * 5860103 * 2
def baseEnd_5860103 : Nat := 3009049523854591053762383

theorem tailTrace_5860103 : CollatzResearch.WordTrace tailWord_5860103 prefixEnd_5860103 3009049523854591053762383 := by
  unfold tailWord_5860103
  simp only [CollatzResearch.WordTrace]
  refine ⟨213735515488855131757688963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142490343659236754505125975 213735515488855131757688963)
  ·
    refine ⟨320603273233282697636533445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213735515488855131757688963 320603273233282697636533445)
    ·
      refine ⟨60113113731240505806850021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 320603273233282697636533445 60113113731240505806850021)
      ·
        refine ⟨11271208824607594838784379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60113113731240505806850021 11271208824607594838784379)
        ·
          refine ⟨16906813236911392258176569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11271208824607594838784379 16906813236911392258176569)
          ·
            refine ⟨12680109927683544193632427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16906813236911392258176569 12680109927683544193632427)
            ·
              refine ⟨19020164891525316290448641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12680109927683544193632427 19020164891525316290448641)
              ·
                refine ⟨14265123668643987217836481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19020164891525316290448641 14265123668643987217836481)
                ·
                  refine ⟨10698842751482990413377361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14265123668643987217836481 10698842751482990413377361)
                  ·
                    refine ⟨8024132063612242810033021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10698842751482990413377361 8024132063612242810033021)
                    ·
                      refine ⟨3009049523854591053762383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8024132063612242810033021 3009049523854591053762383)
                      ·
                        rfl

theorem cell23_5860103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_5860103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860103 prefixEnd_5860103 := by exact prefixLift 5860103
  have htrace : WordTrace (prefixWord ++ tailWord_5860103) baseStart_5860103 baseEnd_5860103 := by
    simpa [prefixWord, tailWord_5860103, baseEnd_5860103] using wordTrace_append hprefix tailTrace_5860103
  have hstable : (prefixWord ++ tailWord_5860103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860103).length < 2 ^ (prefixWord ++ tailWord_5860103).sum := by decide
  have hdescent : baseEnd_5860103 < baseStart_5860103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860136 : List Nat := [2, 1, 5, 1, 1, 1, 3, 1, 3, 5]
def baseStart_5860136 : Nat := 118140960795 + 5860136 * 2 ^ 59
def prefixEnd_5860136 : Nat := 4983230072969 + 3 ^ 40 * 5860136 * 2
def baseEnd_5860136 : Nat := 1003022156238729808216577

theorem tailTrace_5860136 : CollatzResearch.WordTrace tailWord_5860136 prefixEnd_5860136 1003022156238729808216577 := by
  unfold tailWord_5860136
  simp only [CollatzResearch.WordTrace]
  refine ⟨106868359548867789196820131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142491146065157052262426841 106868359548867789196820131)
  ·
    refine ⟨160302539323301683795230197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106868359548867789196820131 160302539323301683795230197)
    ·
      refine ⟨15028363061559532855802831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 160302539323301683795230197 15028363061559532855802831)
      ·
        refine ⟨22542544592339299283704247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15028363061559532855802831 22542544592339299283704247)
        ·
          refine ⟨33813816888508948925556371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22542544592339299283704247 33813816888508948925556371)
          ·
            refine ⟨50720725332763423388334557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33813816888508948925556371 50720725332763423388334557)
            ·
              refine ⟨19020271999786283770625459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50720725332763423388334557 19020271999786283770625459)
              ·
                refine ⟨28530407999679425655938189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19020271999786283770625459 28530407999679425655938189)
                ·
                  refine ⟨10698902999879784620976821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28530407999679425655938189 10698902999879784620976821)
                  ·
                    refine ⟨1003022156238729808216577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10698902999879784620976821 1003022156238729808216577)
                    ·
                      rfl

theorem cell23_5860136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_5860136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860136 prefixEnd_5860136 := by exact prefixLift 5860136
  have htrace : WordTrace (prefixWord ++ tailWord_5860136) baseStart_5860136 baseEnd_5860136 := by
    simpa [prefixWord, tailWord_5860136, baseEnd_5860136] using wordTrace_append hprefix tailTrace_5860136
  have hstable : (prefixWord ++ tailWord_5860136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860136).length < 2 ^ (prefixWord ++ tailWord_5860136).sum := by decide
  have hdescent : baseEnd_5860136 < baseStart_5860136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860161 : List Nat := [1, 2, 5, 3, 2, 1, 2, 2, 1, 4]
def baseStart_5860161 : Nat := 118140960795 + 5860161 * 2 ^ 59
def prefixEnd_5860161 : Nat := 4983230072969 + 3 ^ 40 * 5860161 * 2
def baseEnd_5860161 : Nat := 1003026435244183942279039

theorem tailTrace_5860161 : CollatzResearch.WordTrace tailWord_5860161 prefixEnd_5860161 1003026435244183942279039 := by
  unfold tailWord_5860161
  simp only [CollatzResearch.WordTrace]
  refine ⟨213737630922645007663300337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142491753948430005108866891 213737630922645007663300337)
  ·
    refine ⟨160303223191983755747475253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213737630922645007663300337 160303223191983755747475253)
    ·
      refine ⟨15028427174248477101325805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 160303223191983755747475253 15028427174248477101325805)
      ·
        refine ⟨5635660190343178912997177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15028427174248477101325805 5635660190343178912997177)
        ·
          refine ⟨4226745142757384184747883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5635660190343178912997177 4226745142757384184747883)
          ·
            refine ⟨6340117714136076277121825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4226745142757384184747883 6340117714136076277121825)
            ·
              refine ⟨4755088285602057207841369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6340117714136076277121825 4755088285602057207841369)
              ·
                refine ⟨3566316214201542905881027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4755088285602057207841369 3566316214201542905881027)
                ·
                  refine ⟨5349474321302314358821541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3566316214201542905881027 5349474321302314358821541)
                  ·
                    refine ⟨1003026435244183942279039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5349474321302314358821541 1003026435244183942279039)
                    ·
                      rfl

theorem cell23_5860161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_5860161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860161 prefixEnd_5860161 := by exact prefixLift 5860161
  have htrace : WordTrace (prefixWord ++ tailWord_5860161) baseStart_5860161 baseEnd_5860161 := by
    simpa [prefixWord, tailWord_5860161, baseEnd_5860161] using wordTrace_append hprefix tailTrace_5860161
  have hstable : (prefixWord ++ tailWord_5860161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860161).length < 2 ^ (prefixWord ++ tailWord_5860161).sum := by decide
  have hdescent : baseEnd_5860161 < baseStart_5860161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860176 : List Nat := [2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 3]
def baseStart_5860176 : Nat := 118140960795 + 5860176 * 2 ^ 59
def prefixEnd_5860176 : Nat := 4983230072969 + 3 ^ 40 * 5860176 * 2
def baseEnd_5860176 : Nat := 3009087007942369268149547

theorem tailTrace_5860176 : CollatzResearch.WordTrace tailWord_5860176 prefixEnd_5860176 3009087007942369268149547 := by
  unfold tailWord_5860176
  simp only [CollatzResearch.WordTrace]
  refine ⟨106869089008795332612548191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142492118678393776816730921 106869089008795332612548191)
  ·
    refine ⟨160303633513192998918822287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106869089008795332612548191 160303633513192998918822287)
    ·
      refine ⟨240455450269789498378233431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160303633513192998918822287 240455450269789498378233431)
      ·
        refine ⟨360683175404684247567350147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240455450269789498378233431 360683175404684247567350147)
        ·
          refine ⟨541024763107026371351025221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360683175404684247567350147 541024763107026371351025221)
          ·
            refine ⟨101442143082567444628317229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 541024763107026371351025221 101442143082567444628317229)
            ·
              refine ⟨38040803655962791735618961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101442143082567444628317229 38040803655962791735618961)
              ·
                refine ⟨28530602741972093801714221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38040803655962791735618961 28530602741972093801714221)
                ·
                  refine ⟨10698976028239535175642833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28530602741972093801714221 10698976028239535175642833)
                  ·
                    refine ⟨8024232021179651381732125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10698976028239535175642833 8024232021179651381732125)
                    ·
                      refine ⟨3009087007942369268149547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8024232021179651381732125 3009087007942369268149547)
                      ·
                        rfl

theorem cell23_5860176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 3].length) (baseStart_5860176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860176 prefixEnd_5860176 := by exact prefixLift 5860176
  have htrace : WordTrace (prefixWord ++ tailWord_5860176) baseStart_5860176 baseEnd_5860176 := by
    simpa [prefixWord, tailWord_5860176, baseEnd_5860176] using wordTrace_append hprefix tailTrace_5860176
  have hstable : (prefixWord ++ tailWord_5860176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860176).length < 2 ^ (prefixWord ++ tailWord_5860176).sum := by decide
  have hdescent : baseEnd_5860176 < baseStart_5860176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860183 : List Nat := [1, 1, 3, 2, 4, 1, 2, 3, 2, 4]
def baseStart_5860183 : Nat := 118140960795 + 5860183 * 2 ^ 59
def prefixEnd_5860183 : Nat := 4983230072969 + 3 ^ 40 * 5860183 * 2
def baseEnd_5860183 : Nat := 1003030200768983580254005

theorem tailTrace_5860183 : CollatzResearch.WordTrace tailWord_5860183 prefixEnd_5860183 1003030200768983580254005 := by
  unfold tailWord_5860183
  simp only [CollatzResearch.WordTrace]
  refine ⟨213738433328565305420601203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142492288885710203613734135 213738433328565305420601203)
  ·
    refine ⟨320607649992847958130901805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213738433328565305420601203 320607649992847958130901805)
    ·
      refine ⟨120227868747317984299088177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 320607649992847958130901805 120227868747317984299088177)
      ·
        refine ⟨90170901560488488224316133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120227868747317984299088177 90170901560488488224316133)
        ·
          refine ⟨16907044042591591542059275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90170901560488488224316133 16907044042591591542059275)
          ·
            refine ⟨25360566063887387313088913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16907044042591591542059275 25360566063887387313088913)
            ·
              refine ⟨19020424547915540484816685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25360566063887387313088913 19020424547915540484816685)
              ·
                refine ⟨7132659205468327681806257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19020424547915540484816685 7132659205468327681806257)
                ·
                  refine ⟨5349494404101245761354693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7132659205468327681806257 5349494404101245761354693)
                  ·
                    refine ⟨1003030200768983580254005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5349494404101245761354693 1003030200768983580254005)
                    ·
                      rfl

theorem cell23_5860183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 2, 4].length) (baseStart_5860183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860183 prefixEnd_5860183 := by exact prefixLift 5860183
  have htrace : WordTrace (prefixWord ++ tailWord_5860183) baseStart_5860183 baseEnd_5860183 := by
    simpa [prefixWord, tailWord_5860183, baseEnd_5860183] using wordTrace_append hprefix tailTrace_5860183
  have hstable : (prefixWord ++ tailWord_5860183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860183).length < 2 ^ (prefixWord ++ tailWord_5860183).sum := by decide
  have hdescent : baseEnd_5860183 < baseStart_5860183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860186 : List Nat := [3, 1, 1, 2, 1, 4, 1, 3, 1, 2, 4]
def baseStart_5860186 : Nat := 118140960795 + 5860186 * 2 ^ 59
def prefixEnd_5860186 : Nat := 4983230072969 + 3 ^ 40 * 5860186 * 2
def baseEnd_5860186 : Nat := 3009092142748914229024501

theorem tailTrace_5860186 : CollatzResearch.WordTrace tailWord_5860186 prefixEnd_5860186 3009092142748914229024501 := by
  unfold tailWord_5860186
  simp only [CollatzResearch.WordTrace]
  refine ⟨53434635686888609233240103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142492361831702957955306941 53434635686888609233240103)
  ·
    refine ⟨80151953530332913849860155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53434635686888609233240103 80151953530332913849860155)
    ·
      refine ⟨120227930295499370774790233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80151953530332913849860155 120227930295499370774790233)
      ·
        refine ⟨90170947721624528081092675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120227930295499370774790233 90170947721624528081092675)
        ·
          refine ⟨135256421582436792121639013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90170947721624528081092675 135256421582436792121639013)
          ·
            refine ⟨25360579046706898522807315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135256421582436792121639013 25360579046706898522807315)
            ·
              refine ⟨38040868570060347784210973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25360579046706898522807315 38040868570060347784210973)
              ·
                refine ⟨14265325713772630419079115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38040868570060347784210973 14265325713772630419079115)
                ·
                  refine ⟨21397988570658945628618673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14265325713772630419079115 21397988570658945628618673)
                  ·
                    refine ⟨16048491427994209221464005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21397988570658945628618673 16048491427994209221464005)
                    ·
                      refine ⟨3009092142748914229024501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16048491427994209221464005 3009092142748914229024501)
                      ·
                        rfl

theorem cell23_5860186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_5860186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860186 prefixEnd_5860186 := by exact prefixLift 5860186
  have htrace : WordTrace (prefixWord ++ tailWord_5860186) baseStart_5860186 baseEnd_5860186 := by
    simpa [prefixWord, tailWord_5860186, baseEnd_5860186] using wordTrace_append hprefix tailTrace_5860186
  have hstable : (prefixWord ++ tailWord_5860186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860186).length < 2 ^ (prefixWord ++ tailWord_5860186).sum := by decide
  have hdescent : baseEnd_5860186 < baseStart_5860186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860194 : List Nat := [3, 3, 2, 1, 4, 1, 1, 1, 2, 3, 2]
def baseStart_5860194 : Nat := 118140960795 + 5860194 * 2 ^ 59
def prefixEnd_5860194 : Nat := 4983230072969 + 3 ^ 40 * 5860194 * 2
def baseEnd_5860194 : Nat := 3009096250594150197724465

theorem tailTrace_5860194 : CollatzResearch.WordTrace tailWord_5860194 prefixEnd_5860194 3009096250594150197724465 := by
  unfold tailWord_5860194
  simp only [CollatzResearch.WordTrace]
  refine ⟨53434708632881363574812909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142492556354350302866167757 53434708632881363574812909)
  ·
    refine ⟨20038015737330511340554841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53434708632881363574812909 20038015737330511340554841)
    ·
      refine ⟨15028511802997883505416131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20038015737330511340554841 15028511802997883505416131)
      ·
        refine ⟨22542767704496825258124197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15028511802997883505416131 22542767704496825258124197)
        ·
          refine ⟨4226768944593154735898287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22542767704496825258124197 4226768944593154735898287)
          ·
            refine ⟨6340153416889732103847431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4226768944593154735898287 6340153416889732103847431)
            ·
              refine ⟨9510230125334598155771147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6340153416889732103847431 9510230125334598155771147)
              ·
                refine ⟨14265345188001897233656721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9510230125334598155771147 14265345188001897233656721)
                ·
                  refine ⟨10699008891001422925242541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14265345188001897233656721 10699008891001422925242541)
                  ·
                    refine ⟨4012128334125533596965953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10699008891001422925242541 4012128334125533596965953)
                    ·
                      refine ⟨3009096250594150197724465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4012128334125533596965953 3009096250594150197724465)
                      ·
                        rfl

theorem cell23_5860194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_5860194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860194 prefixEnd_5860194 := by exact prefixLift 5860194
  have htrace : WordTrace (prefixWord ++ tailWord_5860194) baseStart_5860194 baseEnd_5860194 := by
    simpa [prefixWord, tailWord_5860194, baseEnd_5860194] using wordTrace_append hprefix tailTrace_5860194
  have hstable : (prefixWord ++ tailWord_5860194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860194).length < 2 ^ (prefixWord ++ tailWord_5860194).sum := by decide
  have hdescent : baseEnd_5860194 < baseStart_5860194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860210 : List Nat := [3, 2, 1, 2, 1, 1, 6, 1, 1, 2, 3]
def baseStart_5860210 : Nat := 118140960795 + 5860210 * 2 ^ 59
def prefixEnd_5860210 : Nat := 4983230072969 + 3 ^ 40 * 5860210 * 2
def baseEnd_5860210 : Nat := 3009104466284622135124391

theorem tailTrace_5860210 : CollatzResearch.WordTrace tailWord_5860210 prefixEnd_5860210 3009104466284622135124391 := by
  unfold tailWord_5860210
  simp only [CollatzResearch.WordTrace]
  refine ⟨53434854524866872257958521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142492945399644992687889389 53434854524866872257958521)
  ·
    refine ⟨40076140893650154193468891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53434854524866872257958521 40076140893650154193468891)
    ·
      refine ⟨60114211340475231290203337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40076140893650154193468891 60114211340475231290203337)
      ·
        refine ⟨45085658505356423467652503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60114211340475231290203337 45085658505356423467652503)
        ·
          refine ⟨67628487758034635201478755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45085658505356423467652503 67628487758034635201478755)
          ·
            refine ⟨101442731637051952802218133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67628487758034635201478755 101442731637051952802218133)
            ·
              refine ⟨4755128045486810287603975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 101442731637051952802218133 4755128045486810287603975)
              ·
                refine ⟨7132692068230215431405963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4755128045486810287603975 7132692068230215431405963)
                ·
                  refine ⟨10699038102345323147108945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7132692068230215431405963 10699038102345323147108945)
                  ·
                    refine ⟨8024278576758992360331709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10699038102345323147108945 8024278576758992360331709)
                    ·
                      refine ⟨3009104466284622135124391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8024278576758992360331709 3009104466284622135124391)
                      ·
                        rfl

theorem cell23_5860210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_5860210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860210 prefixEnd_5860210 := by exact prefixLift 5860210
  have htrace : WordTrace (prefixWord ++ tailWord_5860210) baseStart_5860210 baseEnd_5860210 := by
    simpa [prefixWord, tailWord_5860210, baseEnd_5860210] using wordTrace_append hprefix tailTrace_5860210
  have hstable : (prefixWord ++ tailWord_5860210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860210).length < 2 ^ (prefixWord ++ tailWord_5860210).sum := by decide
  have hdescent : baseEnd_5860210 < baseStart_5860210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860280 : List Nat := [2, 1, 2, 1, 2, 4, 2, 1, 4, 2, 2]
def baseStart_5860280 : Nat := 118140960795 + 5860280 * 2 ^ 59
def prefixEnd_5860280 : Nat := 4983230072969 + 3 ^ 40 * 5860280 * 2
def baseEnd_5860280 : Nat := 3009140409930436861249069

theorem tailTrace_5860280 : CollatzResearch.WordTrace tailWord_5860280 prefixEnd_5860280 3009140409930436861249069 := by
  unfold tailWord_5860280
  simp only [CollatzResearch.WordTrace]
  refine ⟨106870985604606945493441147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142494647472809260657921529 106870985604606945493441147)
  ·
    refine ⟨160306478406910418240161721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106870985604606945493441147 160306478406910418240161721)
    ·
      refine ⟨120229858805182813680121291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160306478406910418240161721 120229858805182813680121291)
      ·
        refine ⟨180344788207774220520181937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120229858805182813680121291 180344788207774220520181937)
        ·
          refine ⟨135258591155830665390136453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180344788207774220520181937 135258591155830665390136453)
          ·
            refine ⟨25360985841718249760650585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135258591155830665390136453 25360985841718249760650585)
            ·
              refine ⟨19020739381288687320487939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25360985841718249760650585 19020739381288687320487939)
              ·
                refine ⟨28531109071933030980731909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19020739381288687320487939 28531109071933030980731909)
                ·
                  refine ⟨5349582950987443308887233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28531109071933030980731909 5349582950987443308887233)
                  ·
                    refine ⟨4012187213240582481665425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5349582950987443308887233 4012187213240582481665425)
                    ·
                      refine ⟨3009140409930436861249069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4012187213240582481665425 3009140409930436861249069)
                      ·
                        rfl

theorem cell23_5860280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 4, 2, 2].length) (baseStart_5860280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860280 prefixEnd_5860280 := by exact prefixLift 5860280
  have htrace : WordTrace (prefixWord ++ tailWord_5860280) baseStart_5860280 baseEnd_5860280 := by
    simpa [prefixWord, tailWord_5860280, baseEnd_5860280] using wordTrace_append hprefix tailTrace_5860280
  have hstable : (prefixWord ++ tailWord_5860280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860280).length < 2 ^ (prefixWord ++ tailWord_5860280).sum := by decide
  have hdescent : baseEnd_5860280 < baseStart_5860280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860301 : List Nat := [1, 6, 3, 1, 1, 1, 1, 1, 3, 3, 2]
def baseStart_5860301 : Nat := 118140960795 + 5860301 * 2 ^ 59
def prefixEnd_5860301 : Nat := 4983230072969 + 3 ^ 40 * 5860301 * 2
def baseEnd_5860301 : Nat := 3009151193024181279086473

theorem tailTrace_5860301 : CollatzResearch.WordTrace tailWord_5860301 prefixEnd_5860301 3009151193024181279086473 := by
  unfold tailWord_5860301
  simp only [CollatzResearch.WordTrace]
  refine ⟨213742737142137811573396757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142495158094758541048931171 213742737142137811573396757)
  ·
    refine ⟨10019190803537709917502973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 213742737142137811573396757 10019190803537709917502973)
    ·
      refine ⟨3757196551326641219063615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10019190803537709917502973 3757196551326641219063615)
      ·
        refine ⟨5635794826989961828595423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3757196551326641219063615 5635794826989961828595423)
        ·
          refine ⟨8453692240484942742893135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5635794826989961828595423 8453692240484942742893135)
          ·
            refine ⟨12680538360727414114339703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8453692240484942742893135 12680538360727414114339703)
            ·
              refine ⟨19020807541091121171509555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12680538360727414114339703 19020807541091121171509555)
              ·
                refine ⟨28531211311636681757264333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19020807541091121171509555 28531211311636681757264333)
                ·
                  refine ⟨10699204241863755658974125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28531211311636681757264333 10699204241863755658974125)
                  ·
                    refine ⟨4012201590698908372115297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10699204241863755658974125 4012201590698908372115297)
                    ·
                      refine ⟨3009151193024181279086473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4012201590698908372115297 3009151193024181279086473)
                      ·
                        rfl

theorem cell23_5860301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_5860301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860301 prefixEnd_5860301 := by exact prefixLift 5860301
  have htrace : WordTrace (prefixWord ++ tailWord_5860301) baseStart_5860301 baseEnd_5860301 := by
    simpa [prefixWord, tailWord_5860301, baseEnd_5860301] using wordTrace_append hprefix tailTrace_5860301
  have hstable : (prefixWord ++ tailWord_5860301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860301).length < 2 ^ (prefixWord ++ tailWord_5860301).sum := by decide
  have hdescent : baseEnd_5860301 < baseStart_5860301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860336 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 4]
def baseStart_5860336 : Nat := 118140960795 + 5860336 * 2 ^ 59
def prefixEnd_5860336 : Nat := 4983230072969 + 3 ^ 40 * 5860336 * 2
def baseEnd_5860336 : Nat := 3009169164847088642148811

theorem tailTrace_5860336 : CollatzResearch.WordTrace tailWord_5860336 prefixEnd_5860336 3009169164847088642148811 := by
  unfold tailWord_5860336
  simp only [CollatzResearch.WordTrace]
  refine ⟨106872006848505506275460431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142496009131340675033947241 106872006848505506275460431)
  ·
    refine ⟨160308010272758259413190647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106872006848505506275460431 160308010272758259413190647)
    ·
      refine ⟨240462015409137389119785971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160308010272758259413190647 240462015409137389119785971)
      ·
        refine ⟨360693023113706083679678957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240462015409137389119785971 360693023113706083679678957)
        ·
          refine ⟨135259883667639781379879609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 360693023113706083679678957 135259883667639781379879609)
          ·
            refine ⟨101444912750729836034909707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135259883667639781379879609 101444912750729836034909707)
            ·
              refine ⟨152167369126094754052364561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101444912750729836034909707 152167369126094754052364561)
              ·
                refine ⟨114125526844571065539273421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152167369126094754052364561 114125526844571065539273421)
                ·
                  refine ⟨42797072566714149577227533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114125526844571065539273421 42797072566714149577227533)
                  ·
                    refine ⟨16048902212517806091460325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42797072566714149577227533 16048902212517806091460325)
                    ·
                      refine ⟨3009169164847088642148811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16048902212517806091460325 3009169164847088642148811)
                      ·
                        rfl

theorem cell23_5860336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 4].length) (baseStart_5860336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860336 prefixEnd_5860336 := by exact prefixLift 5860336
  have htrace : WordTrace (prefixWord ++ tailWord_5860336) baseStart_5860336 baseEnd_5860336 := by
    simpa [prefixWord, tailWord_5860336, baseEnd_5860336] using wordTrace_append hprefix tailTrace_5860336
  have hstable : (prefixWord ++ tailWord_5860336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860336).length < 2 ^ (prefixWord ++ tailWord_5860336).sum := by decide
  have hdescent : baseEnd_5860336 < baseStart_5860336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860337 : List Nat := [1, 2, 2, 2, 4, 3, 2, 2, 5]
def baseStart_5860337 : Nat := 118140960795 + 5860337 * 2 ^ 59
def prefixEnd_5860337 : Nat := 4983230072969 + 3 ^ 40 * 5860337 * 2
def baseEnd_5860337 : Nat := 334352186480860348692923

theorem tailTrace_5860337 : CollatzResearch.WordTrace tailWord_5860337 prefixEnd_5860337 334352186480860348692923 := by
  unfold tailWord_5860337
  simp only [CollatzResearch.WordTrace]
  refine ⟨213744050170007389721707265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142496033446671593147804843 213744050170007389721707265)
  ·
    refine ⟨160308037627505542291280449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213744050170007389721707265 160308037627505542291280449)
    ·
      refine ⟨120231028220629156718460337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160308037627505542291280449 120231028220629156718460337)
      ·
        refine ⟨90173271165471867538845253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120231028220629156718460337 90173271165471867538845253)
        ·
          refine ⟨16907488343525975163533485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90173271165471867538845253 16907488343525975163533485)
          ·
            refine ⟨6340308128822240686325057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16907488343525975163533485 6340308128822240686325057)
            ·
              refine ⟨4755231096616680514743793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6340308128822240686325057 4755231096616680514743793)
              ·
                refine ⟨3566423322462510386057845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4755231096616680514743793 3566423322462510386057845)
                ·
                  refine ⟨334352186480860348692923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3566423322462510386057845 334352186480860348692923)
                  ·
                    rfl

theorem cell23_5860337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 2, 5].length) (baseStart_5860337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860337 prefixEnd_5860337 := by exact prefixLift 5860337
  have htrace : WordTrace (prefixWord ++ tailWord_5860337) baseStart_5860337 baseEnd_5860337 := by
    simpa [prefixWord, tailWord_5860337, baseEnd_5860337] using wordTrace_append hprefix tailTrace_5860337
  have hstable : (prefixWord ++ tailWord_5860337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860337).length < 2 ^ (prefixWord ++ tailWord_5860337).sum := by decide
  have hdescent : baseEnd_5860337 < baseStart_5860337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860363 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 5, 4]
def baseStart_5860363 : Nat := 118140960795 + 5860363 * 2 ^ 59
def prefixEnd_5860363 : Nat := 4983230072969 + 3 ^ 40 * 5860363 * 2
def baseEnd_5860363 : Nat := 1003061009608253345503729

theorem tailTrace_5860363 : CollatzResearch.WordTrace tailWord_5860363 prefixEnd_5860363 1003061009608253345503729 := by
  unfold tailWord_5860363
  simp only [CollatzResearch.WordTrace]
  refine ⟨213744998467913196162153743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142496665645275464108102495 213744998467913196162153743)
  ·
    refine ⟨320617497701869794243230615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213744998467913196162153743 320617497701869794243230615)
    ·
      refine ⟨480926246552804691364845923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320617497701869794243230615 480926246552804691364845923)
      ·
        refine ⟨721389369829207037047268885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480926246552804691364845923 721389369829207037047268885)
        ·
          refine ⟨33815126710744079861590729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 721389369829207037047268885 33815126710744079861590729)
          ·
            refine ⟨25361345033058059896193047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33815126710744079861590729 25361345033058059896193047)
            ·
              refine ⟨38042017549587089844289571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25361345033058059896193047 38042017549587089844289571)
              ·
                refine ⟨57063026324380634766434357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38042017549587089844289571 57063026324380634766434357)
                ·
                  refine ⟨5349658717910684509353221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57063026324380634766434357 5349658717910684509353221)
                  ·
                    refine ⟨1003061009608253345503729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5349658717910684509353221 1003061009608253345503729)
                    ·
                      rfl

theorem cell23_5860363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 5, 4].length) (baseStart_5860363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860363 prefixEnd_5860363 := by exact prefixLift 5860363
  have htrace : WordTrace (prefixWord ++ tailWord_5860363) baseStart_5860363 baseEnd_5860363 := by
    simpa [prefixWord, tailWord_5860363, baseEnd_5860363] using wordTrace_append hprefix tailTrace_5860363
  have hstable : (prefixWord ++ tailWord_5860363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860363).length < 2 ^ (prefixWord ++ tailWord_5860363).sum := by decide
  have hdescent : baseEnd_5860363 < baseStart_5860363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860396 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 8]
def baseStart_5860396 : Nat := 118140960795 + 5860396 * 2 ^ 59
def prefixEnd_5860396 : Nat := 4983230072969 + 3 ^ 40 * 5860396 * 2
def baseEnd_5860396 : Nat := 3009199973686358407398535

theorem tailTrace_5860396 : CollatzResearch.WordTrace tailWord_5860396 prefixEnd_5860396 3009199973686358407398535 := by
  unfold tailWord_5860396
  simp only [CollatzResearch.WordTrace]
  refine ⟨106873101038396821399052521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142497468051195761865403361 106873101038396821399052521)
  ·
    refine ⟨80154825778797616049289391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106873101038396821399052521 80154825778797616049289391)
    ·
      refine ⟨120232238668196424073934087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80154825778797616049289391 120232238668196424073934087)
      ·
        refine ⟨180348358002294636110901131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120232238668196424073934087 180348358002294636110901131)
        ·
          refine ⟨270522537003441954166351697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180348358002294636110901131 270522537003441954166351697)
          ·
            refine ⟨202891902752581465624763773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270522537003441954166351697 202891902752581465624763773)
            ·
              refine ⟨76084463532218049609286415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202891902752581465624763773 76084463532218049609286415)
              ·
                refine ⟨114126695298327074413929623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76084463532218049609286415 114126695298327074413929623)
                ·
                  refine ⟨171190042947490611620894435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114126695298327074413929623 171190042947490611620894435)
                  ·
                    refine ⟨256785064421235917431341653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 171190042947490611620894435 256785064421235917431341653)
                    ·
                      refine ⟨3009199973686358407398535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 256785064421235917431341653 3009199973686358407398535)
                      ·
                        rfl

theorem cell23_5860396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_5860396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860396 prefixEnd_5860396 := by exact prefixLift 5860396
  have htrace : WordTrace (prefixWord ++ tailWord_5860396) baseStart_5860396 baseEnd_5860396 := by
    simpa [prefixWord, tailWord_5860396, baseEnd_5860396] using wordTrace_append hprefix tailTrace_5860396
  have hstable : (prefixWord ++ tailWord_5860396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860396).length < 2 ^ (prefixWord ++ tailWord_5860396).sum := by decide
  have hdescent : baseEnd_5860396 < baseStart_5860396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860430 : List Nat := [4, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2]
def baseStart_5860430 : Nat := 118140960795 + 5860430 * 2 ^ 59
def prefixEnd_5860430 : Nat := 4983230072969 + 3 ^ 40 * 5860430 * 2
def baseEnd_5860430 : Nat := 3009217432028611274373379

theorem tailTrace_5860430 : CollatzResearch.WordTrace tailWord_5860430 prefixEnd_5860430 3009217432028611274373379 := by
  unfold tailWord_5860430
  simp only [CollatzResearch.WordTrace]
  refine ⟨26718430269833808325605343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142498294772446977736561829 26718430269833808325605343)
  ·
    refine ⟨40077645404750712488408015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26718430269833808325605343 40077645404750712488408015)
    ·
      refine ⟨60116468107126068732612023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40077645404750712488408015 60116468107126068732612023)
      ·
        refine ⟨90174702160689103098918035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60116468107126068732612023 90174702160689103098918035)
        ·
          refine ⟨135262053241033654648377053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90174702160689103098918035 135262053241033654648377053)
          ·
            refine ⟨50723269965387620493141395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135262053241033654648377053 50723269965387620493141395)
            ·
              refine ⟨76084904948081430739712093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50723269965387620493141395 76084904948081430739712093)
              ·
                refine ⟨28531839355530536527392035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76084904948081430739712093 28531839355530536527392035)
                ·
                  refine ⟨42797759033295804791088053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28531839355530536527392035 42797759033295804791088053)
                  ·
                    refine ⟨4012289909371481699164505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42797759033295804791088053 4012289909371481699164505)
                    ·
                      refine ⟨3009217432028611274373379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4012289909371481699164505 3009217432028611274373379)
                      ·
                        rfl

theorem cell23_5860430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2].length) (baseStart_5860430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860430 prefixEnd_5860430 := by exact prefixLift 5860430
  have htrace : WordTrace (prefixWord ++ tailWord_5860430) baseStart_5860430 baseEnd_5860430 := by
    simpa [prefixWord, tailWord_5860430, baseEnd_5860430] using wordTrace_append hprefix tailTrace_5860430
  have hstable : (prefixWord ++ tailWord_5860430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860430).length < 2 ^ (prefixWord ++ tailWord_5860430).sum := by decide
  have hdescent : baseEnd_5860430 < baseStart_5860430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860463 : List Nat := [1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 5]
def baseStart_5860463 : Nat := 118140960795 + 5860463 * 2 ^ 59
def prefixEnd_5860463 : Nat := 4983230072969 + 3 ^ 40 * 5860463 * 2
def baseEnd_5860463 : Nat := 3009234376890209645260727

theorem tailTrace_5860463 : CollatzResearch.WordTrace tailWord_5860463 prefixEnd_5860463 3009234376890209645260727 := by
  unfold tailWord_5860463
  simp only [CollatzResearch.WordTrace]
  refine ⟨213748645767550913240794043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142499097178367275493862695 213748645767550913240794043)
  ·
    refine ⟨320622968651326369861191065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213748645767550913240794043 320622968651326369861191065)
    ·
      refine ⟨240467226488494777395893299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320622968651326369861191065 240467226488494777395893299)
      ·
        refine ⟨360700839732742166093839949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240467226488494777395893299 360700839732742166093839949)
        ·
          refine ⟨135262814899778312285189981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 360700839732742166093839949 135262814899778312285189981)
          ·
            refine ⟨50723555587416867106946243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135262814899778312285189981 50723555587416867106946243)
            ·
              refine ⟨76085333381125300660419365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50723555587416867106946243 76085333381125300660419365)
              ·
                refine ⟨14266000008960993873828631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76085333381125300660419365 14266000008960993873828631)
                ·
                  refine ⟨21399000013441490810742947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14266000008960993873828631 21399000013441490810742947)
                  ·
                    refine ⟨32098500020162236216114421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21399000013441490810742947 32098500020162236216114421)
                    ·
                      refine ⟨3009234376890209645260727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32098500020162236216114421 3009234376890209645260727)
                      ·
                        rfl

theorem cell23_5860463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 5].length) (baseStart_5860463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860463 prefixEnd_5860463 := by exact prefixLift 5860463
  have htrace : WordTrace (prefixWord ++ tailWord_5860463) baseStart_5860463 baseEnd_5860463 := by
    simpa [prefixWord, tailWord_5860463, baseEnd_5860463] using wordTrace_append hprefix tailTrace_5860463
  have hstable : (prefixWord ++ tailWord_5860463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860463).length < 2 ^ (prefixWord ++ tailWord_5860463).sum := by decide
  have hdescent : baseEnd_5860463 < baseStart_5860463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860470 : List Nat := [5, 1, 1, 2, 1, 1, 2, 3, 1, 6]
def baseStart_5860470 : Nat := 118140960795 + 5860470 * 2 ^ 59
def prefixEnd_5860470 : Nat := 4983230072969 + 3 ^ 40 * 5860470 * 2
def baseEnd_5860470 : Nat := 1003079323751597039291065

theorem tailTrace_5860470 : CollatzResearch.WordTrace tailWord_5860470 prefixEnd_5860470 1003079323751597039291065 := by
  unfold tailWord_5860470
  simp only [CollatzResearch.WordTrace]
  refine ⟨13359306317407847089768679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142499267385683702290865909 13359306317407847089768679)
  ·
    refine ⟨20038959476111770634653019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13359306317407847089768679 20038959476111770634653019)
    ·
      refine ⟨30058439214167655951979529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20038959476111770634653019 30058439214167655951979529)
      ·
        refine ⟨22543829410625741963984647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30058439214167655951979529 22543829410625741963984647)
        ·
          refine ⟨33815744115938612945976971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22543829410625741963984647 33815744115938612945976971)
          ·
            refine ⟨50723616173907919418965457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33815744115938612945976971 50723616173907919418965457)
            ·
              refine ⟨38042712130430939564224093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50723616173907919418965457 38042712130430939564224093)
              ·
                refine ⟨14266017048911602336584035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38042712130430939564224093 14266017048911602336584035)
                ·
                  refine ⟨21399025573367403504876053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14266017048911602336584035 21399025573367403504876053)
                  ·
                    refine ⟨1003079323751597039291065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21399025573367403504876053 1003079323751597039291065)
                    ·
                      rfl

theorem cell23_5860470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_5860470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860470 prefixEnd_5860470 := by exact prefixLift 5860470
  have htrace : WordTrace (prefixWord ++ tailWord_5860470) baseStart_5860470 baseEnd_5860470 := by
    simpa [prefixWord, tailWord_5860470, baseEnd_5860470] using wordTrace_append hprefix tailTrace_5860470
  have hstable : (prefixWord ++ tailWord_5860470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860470).length < 2 ^ (prefixWord ++ tailWord_5860470).sum := by decide
  have hdescent : baseEnd_5860470 < baseStart_5860470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860477 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 5, 2, 2]
def baseStart_5860477 : Nat := 118140960795 + 5860477 * 2 ^ 59
def prefixEnd_5860477 : Nat := 4983230072969 + 3 ^ 40 * 5860477 * 2
def baseEnd_5860477 : Nat := 3009241565619372590485663

theorem tailTrace_5860477 : CollatzResearch.WordTrace tailWord_5860477 prefixEnd_5860477 3009241565619372590485663 := by
  unfold tailWord_5860477
  simp only [CollatzResearch.WordTrace]
  refine ⟨213749156389500193631803685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142499437593000129087869123 213749156389500193631803685)
  ·
    refine ⟨40077966823031286305963191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213749156389500193631803685 40077966823031286305963191)
    ·
      refine ⟨60116950234546929458944787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40077966823031286305963191 60116950234546929458944787)
      ·
        refine ⟨90175425351820394188417181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60116950234546929458944787 90175425351820394188417181)
        ·
          refine ⟨33815784506932647820656443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90175425351820394188417181 33815784506932647820656443)
          ·
            refine ⟨50723676760398971730984665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33815784506932647820656443 50723676760398971730984665)
            ·
              refine ⟨38042757570299228798238499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50723676760398971730984665 38042757570299228798238499)
              ·
                refine ⟨57064136355448843197357749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38042757570299228798238499 57064136355448843197357749)
                ·
                  refine ⟨5349762783323329049752289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57064136355448843197357749 5349762783323329049752289)
                  ·
                    refine ⟨4012322087492496787314217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5349762783323329049752289 4012322087492496787314217)
                    ·
                      refine ⟨3009241565619372590485663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4012322087492496787314217 3009241565619372590485663)
                      ·
                        rfl

theorem cell23_5860477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 5, 2, 2].length) (baseStart_5860477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860477 prefixEnd_5860477 := by exact prefixLift 5860477
  have htrace : WordTrace (prefixWord ++ tailWord_5860477) baseStart_5860477 baseEnd_5860477 := by
    simpa [prefixWord, tailWord_5860477, baseEnd_5860477] using wordTrace_append hprefix tailTrace_5860477
  have hstable : (prefixWord ++ tailWord_5860477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860477).length < 2 ^ (prefixWord ++ tailWord_5860477).sum := by decide
  have hdescent : baseEnd_5860477 < baseStart_5860477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860490 : List Nat := [3, 1, 2, 3, 1, 1, 3, 2, 1, 2, 4]
def baseStart_5860490 : Nat := 118140960795 + 5860490 * 2 ^ 59
def prefixEnd_5860490 : Nat := 4983230072969 + 3 ^ 40 * 5860490 * 2
def baseEnd_5860490 : Nat := 3009248240867881039623103

theorem tailTrace_5860490 : CollatzResearch.WordTrace tailWord_5860490 prefixEnd_5860490 3009248240867881039623103 := by
  unfold tailWord_5860490
  simp only [CollatzResearch.WordTrace]
  refine ⟨53437407634613274213006731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142499753692302064568017949 53437407634613274213006731)
  ·
    refine ⟨80156111451919911319510097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53437407634613274213006731 80156111451919911319510097)
    ·
      refine ⟨60117083588939933489632573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80156111451919911319510097 60117083588939933489632573)
      ·
        refine ⟨22543906345852475058612215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60117083588939933489632573 22543906345852475058612215)
        ·
          refine ⟨33815859518778712587918323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22543906345852475058612215 33815859518778712587918323)
          ·
            refine ⟨50723789278168068881877485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33815859518778712587918323 50723789278168068881877485)
            ·
              refine ⟨19021420979313025830704057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50723789278168068881877485 19021420979313025830704057)
              ·
                refine ⟨14266065734484769373028043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19021420979313025830704057 14266065734484769373028043)
                ·
                  refine ⟨21399098601727154059542065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14266065734484769373028043 21399098601727154059542065)
                  ·
                    refine ⟨16049323951295365544656549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21399098601727154059542065 16049323951295365544656549)
                    ·
                      refine ⟨3009248240867881039623103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16049323951295365544656549 3009248240867881039623103)
                      ·
                        rfl

theorem cell23_5860490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_5860490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860490 prefixEnd_5860490 := by exact prefixLift 5860490
  have htrace : WordTrace (prefixWord ++ tailWord_5860490) baseStart_5860490 baseEnd_5860490 := by
    simpa [prefixWord, tailWord_5860490, baseEnd_5860490] using wordTrace_append hprefix tailTrace_5860490
  have hstable : (prefixWord ++ tailWord_5860490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860490).length < 2 ^ (prefixWord ++ tailWord_5860490).sum := by decide
  have hdescent : baseEnd_5860490 < baseStart_5860490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860494 : List Nat := [4, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4]
def baseStart_5860494 : Nat := 118140960795 + 5860494 * 2 ^ 59
def prefixEnd_5860494 : Nat := 4983230072969 + 3 ^ 40 * 5860494 * 2
def baseEnd_5860494 : Nat := 3009250294790499023973085

theorem tailTrace_5860494 : CollatzResearch.WordTrace tailWord_5860494 prefixEnd_5860494 3009250294790499023973085 := by
  unfold tailWord_5860494
  simp only [CollatzResearch.WordTrace]
  refine ⟨26718722053804825691896567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142499850953625737023448357 26718722053804825691896567)
  ·
    refine ⟨40078083080707238537844851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26718722053804825691896567 40078083080707238537844851)
    ·
      refine ⟨60117124621060857806767277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40078083080707238537844851 60117124621060857806767277)
      ·
        refine ⟨22543921732897821677537729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60117124621060857806767277 22543921732897821677537729)
        ·
          refine ⟨16907941299673366258153297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22543921732897821677537729 16907941299673366258153297)
          ·
            refine ⟨12680955974755024693614973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16907941299673366258153297 12680955974755024693614973)
            ·
              refine ⟨4755358490533134260105615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12680955974755024693614973 4755358490533134260105615)
              ·
                refine ⟨7133037735799701390158423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4755358490533134260105615 7133037735799701390158423)
                ·
                  refine ⟨10699556603699552085237635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7133037735799701390158423 10699556603699552085237635)
                  ·
                    refine ⟨16049334905549328127856453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10699556603699552085237635 16049334905549328127856453)
                    ·
                      refine ⟨3009250294790499023973085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16049334905549328127856453 3009250294790499023973085)
                      ·
                        rfl

theorem cell23_5860494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_5860494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860494 prefixEnd_5860494 := by exact prefixLift 5860494
  have htrace : WordTrace (prefixWord ++ tailWord_5860494) baseStart_5860494 baseEnd_5860494 := by
    simpa [prefixWord, tailWord_5860494, baseEnd_5860494] using wordTrace_append hprefix tailTrace_5860494
  have hstable : (prefixWord ++ tailWord_5860494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860494).length < 2 ^ (prefixWord ++ tailWord_5860494).sum := by decide
  have hdescent : baseEnd_5860494 < baseStart_5860494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860513 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 1, 9]
def baseStart_5860513 : Nat := 118140960795 + 5860513 * 2 ^ 59
def prefixEnd_5860513 : Nat := 4983230072969 + 3 ^ 40 * 5860513 * 2
def baseEnd_5860513 : Nat := 1003086683640978149878499

theorem tailTrace_5860513 : CollatzResearch.WordTrace tailWord_5860513 prefixEnd_5860513 1003086683640978149878499 := by
  unfold tailWord_5860513
  simp only [CollatzResearch.WordTrace]
  refine ⟨213750469417369771780114193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142500312944913181186742795 213750469417369771780114193)
  ·
    refine ⟨160312852063027328835085645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213750469417369771780114193 160312852063027328835085645)
    ·
      refine ⟨60117319523635248313157117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160312852063027328835085645 60117319523635248313157117)
      ·
        refine ⟨22543994821363218117433919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60117319523635248313157117 22543994821363218117433919)
        ·
          refine ⟨33815992232044827176150879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22543994821363218117433919 33815992232044827176150879)
          ·
            refine ⟨50723988348067240764226319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33815992232044827176150879 50723988348067240764226319)
            ·
              refine ⟨76085982522100861146339479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50723988348067240764226319 76085982522100861146339479)
              ·
                refine ⟨114128973783151291719509219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76085982522100861146339479 114128973783151291719509219)
                ·
                  refine ⟨171193460674726937579263829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114128973783151291719509219 171193460674726937579263829)
                  ·
                    refine ⟨1003086683640978149878499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 171193460674726937579263829 1003086683640978149878499)
                    ·
                      rfl

theorem cell23_5860513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_5860513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860513 prefixEnd_5860513 := by exact prefixLift 5860513
  have htrace : WordTrace (prefixWord ++ tailWord_5860513) baseStart_5860513 baseEnd_5860513 := by
    simpa [prefixWord, tailWord_5860513, baseEnd_5860513] using wordTrace_append hprefix tailTrace_5860513
  have hstable : (prefixWord ++ tailWord_5860513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860513).length < 2 ^ (prefixWord ++ tailWord_5860513).sum := by decide
  have hdescent : baseEnd_5860513 < baseStart_5860513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860527 : List Nat := [1, 1, 2, 1, 2, 3, 4, 3, 2, 1, 3]
def baseStart_5860527 : Nat := 118140960795 + 5860527 * 2 ^ 59
def prefixEnd_5860527 : Nat := 4983230072969 + 3 ^ 40 * 5860527 * 2
def baseEnd_5860527 : Nat := 3009267239652097394860433

theorem tailTrace_5860527 : CollatzResearch.WordTrace tailWord_5860527 prefixEnd_5860527 3009267239652097394860433 := by
  unfold tailWord_5860527
  simp only [CollatzResearch.WordTrace]
  refine ⟨213750980039319052171123835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142500653359546034780749223 213750980039319052171123835)
  ·
    refine ⟨320626470058978578256685753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213750980039319052171123835 320626470058978578256685753)
    ·
      refine ⟨240469852544233933692514315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320626470058978578256685753 240469852544233933692514315)
      ·
        refine ⟨360704778816350900538771473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240469852544233933692514315 360704778816350900538771473)
        ·
          refine ⟨270528584112263175404078605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360704778816350900538771473 270528584112263175404078605)
          ·
            refine ⟨101448219042098690776529477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 270528584112263175404078605 101448219042098690776529477)
            ·
              refine ⟨19021541070393504520599277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101448219042098690776529477 19021541070393504520599277)
              ·
                refine ⟨7133077901397564195224729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19021541070393504520599277 7133077901397564195224729)
                ·
                  refine ⟨5349808426048173146418547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7133077901397564195224729 5349808426048173146418547)
                  ·
                    refine ⟨8024712639072259719627821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5349808426048173146418547 8024712639072259719627821)
                    ·
                      refine ⟨3009267239652097394860433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8024712639072259719627821 3009267239652097394860433)
                      ·
                        rfl

theorem cell23_5860527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 2, 1, 3].length) (baseStart_5860527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860527 prefixEnd_5860527 := by exact prefixLift 5860527
  have htrace : WordTrace (prefixWord ++ tailWord_5860527) baseStart_5860527 baseEnd_5860527 := by
    simpa [prefixWord, tailWord_5860527, baseEnd_5860527] using wordTrace_append hprefix tailTrace_5860527
  have hstable : (prefixWord ++ tailWord_5860527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860527).length < 2 ^ (prefixWord ++ tailWord_5860527).sum := by decide
  have hdescent : baseEnd_5860527 < baseStart_5860527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860537 : List Nat := [1, 2, 1, 4, 1, 3, 2, 1, 3, 3, 2]
def baseStart_5860537 : Nat := 118140960795 + 5860537 * 2 ^ 59
def prefixEnd_5860537 : Nat := 4983230072969 + 3 ^ 40 * 5860537 * 2
def baseEnd_5860537 : Nat := 3009272374458642355735387

theorem tailTrace_5860537 : CollatzResearch.WordTrace tailWord_5860537 prefixEnd_5860537 3009272374458642355735387 := by
  unfold tailWord_5860537
  simp only [CollatzResearch.WordTrace]
  refine ⟨213751344769282823878987865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142500896512855215919325243 213751344769282823878987865)
  ·
    refine ⟨160313508576962117909240899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213751344769282823878987865 160313508576962117909240899)
    ·
      refine ⟨240470262865443176863861349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160313508576962117909240899 240470262865443176863861349)
      ·
        refine ⟨45088174287270595661974003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 240470262865443176863861349 45088174287270595661974003)
        ·
          refine ⟨67632261430905893492961005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45088174287270595661974003 67632261430905893492961005)
          ·
            refine ⟨25362098036589710059860377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67632261430905893492961005 25362098036589710059860377)
            ·
              refine ⟨19021573527442282544895283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25362098036589710059860377 19021573527442282544895283)
              ·
                refine ⟨28532360291163423817342925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19021573527442282544895283 28532360291163423817342925)
                ·
                  refine ⟨10699635109186283931503597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28532360291163423817342925 10699635109186283931503597)
                  ·
                    refine ⟨4012363165944856474313849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10699635109186283931503597 4012363165944856474313849)
                    ·
                      refine ⟨3009272374458642355735387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4012363165944856474313849 3009272374458642355735387)
                      ·
                        rfl

theorem cell23_5860537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_5860537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860537 prefixEnd_5860537 := by exact prefixLift 5860537
  have htrace : WordTrace (prefixWord ++ tailWord_5860537) baseStart_5860537 baseEnd_5860537 := by
    simpa [prefixWord, tailWord_5860537, baseEnd_5860537] using wordTrace_append hprefix tailTrace_5860537
  have hstable : (prefixWord ++ tailWord_5860537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860537).length < 2 ^ (prefixWord ++ tailWord_5860537).sum := by decide
  have hdescent : baseEnd_5860537 < baseStart_5860537 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860548 : List Nat := [2, 3, 3, 1, 4, 1, 2, 1, 1, 2, 3]
def baseStart_5860548 : Nat := 118140960795 + 5860548 * 2 ^ 59
def prefixEnd_5860548 : Nat := 4983230072969 + 3 ^ 40 * 5860548 * 2
def baseEnd_5860548 : Nat := 3009278022745841812697837

theorem tailTrace_5860548 : CollatzResearch.WordTrace tailWord_5860548 prefixEnd_5860548 3009278022745841812697837 := by
  unfold tailWord_5860548
  simp only [CollatzResearch.WordTrace]
  refine ⟨106875872986121486378819149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142501163981495315171758865 106875872986121486378819149)
  ·
    refine ⟨40078452369795557392057181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106875872986121486378819149 40078452369795557392057181)
    ·
      refine ⟨15029419638673334022021443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40078452369795557392057181 15029419638673334022021443)
      ·
        refine ⟨22544129458010001033032165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15029419638673334022021443 22544129458010001033032165)
        ·
          refine ⟨4227024273376875193693531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22544129458010001033032165 4227024273376875193693531)
          ·
            refine ⟨6340536410065312790540297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4227024273376875193693531 6340536410065312790540297)
            ·
              refine ⟨4755402307548984592905223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6340536410065312790540297 4755402307548984592905223)
              ·
                refine ⟨7133103461323476889357835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4755402307548984592905223 7133103461323476889357835)
                ·
                  refine ⟨10699655191985215334036753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7133103461323476889357835 10699655191985215334036753)
                  ·
                    refine ⟨8024741393988911500527565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10699655191985215334036753 8024741393988911500527565)
                    ·
                      refine ⟨3009278022745841812697837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8024741393988911500527565 3009278022745841812697837)
                      ·
                        rfl

theorem cell23_5860548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_5860548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860548 prefixEnd_5860548 := by exact prefixLift 5860548
  have htrace : WordTrace (prefixWord ++ tailWord_5860548) baseStart_5860548 baseEnd_5860548 := by
    simpa [prefixWord, tailWord_5860548, baseEnd_5860548] using wordTrace_append hprefix tailTrace_5860548
  have hstable : (prefixWord ++ tailWord_5860548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860548).length < 2 ^ (prefixWord ++ tailWord_5860548).sum := by decide
  have hdescent : baseEnd_5860548 < baseStart_5860548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860553 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 6, 1, 5]
def baseStart_5860553 : Nat := 118140960795 + 5860553 * 2 ^ 59
def prefixEnd_5860553 : Nat := 4983230072969 + 3 ^ 40 * 5860553 * 2
def baseEnd_5860553 : Nat := 3009280590149114293135313

theorem tailTrace_5860553 : CollatzResearch.WordTrace tailWord_5860553 prefixEnd_5860553 3009280590149114293135313 := by
  unfold tailWord_5860553
  simp only [CollatzResearch.WordTrace]
  refine ⟨213751928337224858611570313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142501285558149905741046875 213751928337224858611570313)
  ·
    refine ⟨160313946252918643958677735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213751928337224858611570313 160313946252918643958677735)
    ·
      refine ⟨240470919379377965938016603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160313946252918643958677735 240470919379377965938016603)
      ·
        refine ⟨360706379069066948907024905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240470919379377965938016603 360706379069066948907024905)
        ·
          refine ⟨270529784301800211680268679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360706379069066948907024905 270529784301800211680268679)
          ·
            refine ⟨405794676452700317520403019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270529784301800211680268679 405794676452700317520403019)
            ·
              refine ⟨608692014679050476280604529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 405794676452700317520403019 608692014679050476280604529)
              ·
                refine ⟨456519011009287857210453397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 608692014679050476280604529 456519011009287857210453397)
                ·
                  refine ⟨21399328641060368306740003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 456519011009287857210453397 21399328641060368306740003)
                  ·
                    refine ⟨32098992961590552460110005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21399328641060368306740003 32098992961590552460110005)
                    ·
                      refine ⟨3009280590149114293135313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32098992961590552460110005 3009280590149114293135313)
                      ·
                        rfl

theorem cell23_5860553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 1, 5].length) (baseStart_5860553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860553 prefixEnd_5860553 := by exact prefixLift 5860553
  have htrace : WordTrace (prefixWord ++ tailWord_5860553) baseStart_5860553 baseEnd_5860553 := by
    simpa [prefixWord, tailWord_5860553, baseEnd_5860553] using wordTrace_append hprefix tailTrace_5860553
  have hstable : (prefixWord ++ tailWord_5860553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860553).length < 2 ^ (prefixWord ++ tailWord_5860553).sum := by decide
  have hdescent : baseEnd_5860553 < baseStart_5860553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860554 : List Nat := [3, 1, 2, 1, 3, 3, 1, 3, 1, 3, 2]
def baseStart_5860554 : Nat := 118140960795 + 5860554 * 2 ^ 59
def prefixEnd_5860554 : Nat := 4983230072969 + 3 ^ 40 * 5860554 * 2
def baseEnd_5860554 : Nat := 3009281103629768789222809

theorem tailTrace_5860554 : CollatzResearch.WordTrace tailWord_5860554 prefixEnd_5860554 3009281103629768789222809 := by
  unfold tailWord_5860554
  simp only [CollatzResearch.WordTrace]
  refine ⟨53437991202555308945589179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142501309873480823854904477 53437991202555308945589179)
  ·
    refine ⟨80156986803832963418383769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53437991202555308945589179 80156986803832963418383769)
    ·
      refine ⟨60117740102874722563787827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80156986803832963418383769 60117740102874722563787827)
      ·
        refine ⟨90176610154312083845681741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60117740102874722563787827 90176610154312083845681741)
        ·
          refine ⟨33816228807867031442130653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90176610154312083845681741 33816228807867031442130653)
          ·
            refine ⟨12681085802950136790798995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33816228807867031442130653 12681085802950136790798995)
            ·
              refine ⟨19021628704425205186198493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12681085802950136790798995 19021628704425205186198493)
              ·
                refine ⟨7133110764159451944824435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19021628704425205186198493 7133110764159451944824435)
                ·
                  refine ⟨10699666146239177917236653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7133110764159451944824435 10699666146239177917236653)
                  ·
                    refine ⟨4012374804839691718963745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10699666146239177917236653 4012374804839691718963745)
                    ·
                      refine ⟨3009281103629768789222809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4012374804839691718963745 3009281103629768789222809)
                      ·
                        rfl

theorem cell23_5860554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 1, 3, 2].length) (baseStart_5860554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860554 prefixEnd_5860554 := by exact prefixLift 5860554
  have htrace : WordTrace (prefixWord ++ tailWord_5860554) baseStart_5860554 baseEnd_5860554 := by
    simpa [prefixWord, tailWord_5860554, baseEnd_5860554] using wordTrace_append hprefix tailTrace_5860554
  have hstable : (prefixWord ++ tailWord_5860554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860554).length < 2 ^ (prefixWord ++ tailWord_5860554).sum := by decide
  have hdescent : baseEnd_5860554 < baseStart_5860554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860563 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 4]
def baseStart_5860563 : Nat := 118140960795 + 5860563 * 2 ^ 59
def prefixEnd_5860563 : Nat := 4983230072969 + 3 ^ 40 * 5860563 * 2
def baseEnd_5860563 : Nat := 3009285724955659254010267

theorem tailTrace_5860563 : CollatzResearch.WordTrace tailWord_5860563 prefixEnd_5860563 3009285724955659254010267 := by
  unfold tailWord_5860563
  simp only [CollatzResearch.WordTrace]
  refine ⟨213752293067188630319434343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142501528711459086879622895 213752293067188630319434343)
  ·
    refine ⟨320628439600782945479151515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213752293067188630319434343 320628439600782945479151515)
    ·
      refine ⟨480942659401174418218727273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320628439600782945479151515 480942659401174418218727273)
      ·
        refine ⟨360706994550880813664045455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 480942659401174418218727273 360706994550880813664045455)
        ·
          refine ⟨541060491826321220496068183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360706994550880813664045455 541060491826321220496068183)
          ·
            refine ⟨811590737739481830744102275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541060491826321220496068183 811590737739481830744102275)
            ·
              refine ⟨1217386106609222746116153413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 811590737739481830744102275 1217386106609222746116153413)
              ·
                refine ⟨228259894989229264896778765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1217386106609222746116153413 228259894989229264896778765)
                ·
                  refine ⟨85597460620960974336292037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 228259894989229264896778765 85597460620960974336292037)
                  ·
                    refine ⟨16049523866430182688054757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85597460620960974336292037 16049523866430182688054757)
                    ·
                      refine ⟨3009285724955659254010267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16049523866430182688054757 3009285724955659254010267)
                      ·
                        rfl

theorem cell23_5860563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 4].length) (baseStart_5860563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860563 prefixEnd_5860563 := by exact prefixLift 5860563
  have htrace : WordTrace (prefixWord ++ tailWord_5860563) baseStart_5860563 baseEnd_5860563 := by
    simpa [prefixWord, tailWord_5860563, baseEnd_5860563] using wordTrace_append hprefix tailTrace_5860563
  have hstable : (prefixWord ++ tailWord_5860563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860563).length < 2 ^ (prefixWord ++ tailWord_5860563).sum := by decide
  have hdescent : baseEnd_5860563 < baseStart_5860563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860580 : List Nat := [2, 3, 1, 1, 1, 2, 4, 1, 2, 2, 4]
def baseStart_5860580 : Nat := 118140960795 + 5860580 * 2 ^ 59
def prefixEnd_5860580 : Nat := 4983230072969 + 3 ^ 40 * 5860580 * 2
def baseEnd_5860580 : Nat := 3009294454126785687497689

theorem tailTrace_5860580 : CollatzResearch.WordTrace tailWord_5860580 prefixEnd_5860580 3009294454126785687497689 := by
  unfold tailWord_5860580
  simp only [CollatzResearch.WordTrace]
  refine ⟨106876456554063521111401597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142501942072084694815202129 106876456554063521111401597)
  ·
    refine ⟨40078671207773820416775599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106876456554063521111401597 40078671207773820416775599)
    ·
      refine ⟨60118006811660730625163399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40078671207773820416775599 60118006811660730625163399)
      ·
        refine ⟨90177010217491095937745099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60118006811660730625163399 90177010217491095937745099)
        ·
          refine ⟨135265515326236643906617649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90177010217491095937745099 135265515326236643906617649)
          ·
            refine ⟨101449136494677482929963237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135265515326236643906617649 101449136494677482929963237)
            ·
              refine ⟨19021713092752028049368107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101449136494677482929963237 19021713092752028049368107)
              ·
                refine ⟨28532569639128042074052161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19021713092752028049368107 28532569639128042074052161)
                ·
                  refine ⟨21399427229346031555539121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28532569639128042074052161 21399427229346031555539121)
                  ·
                    refine ⟨16049570422009523666654341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21399427229346031555539121 16049570422009523666654341)
                    ·
                      refine ⟨3009294454126785687497689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16049570422009523666654341 3009294454126785687497689)
                      ·
                        rfl

theorem cell23_5860580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_5860580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860580 prefixEnd_5860580 := by exact prefixLift 5860580
  have htrace : WordTrace (prefixWord ++ tailWord_5860580) baseStart_5860580 baseEnd_5860580 := by
    simpa [prefixWord, tailWord_5860580, baseEnd_5860580] using wordTrace_append hprefix tailTrace_5860580
  have hstable : (prefixWord ++ tailWord_5860580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860580).length < 2 ^ (prefixWord ++ tailWord_5860580).sum := by decide
  have hdescent : baseEnd_5860580 < baseStart_5860580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860590 : List Nat := [4, 1, 2, 1, 1, 1, 4, 2, 7]
def baseStart_5860590 : Nat := 118140960795 + 5860590 * 2 ^ 59
def prefixEnd_5860590 : Nat := 4983230072969 + 3 ^ 40 * 5860590 * 2
def baseEnd_5860590 : Nat := 334366620992592294263627

theorem tailTrace_5860590 : CollatzResearch.WordTrace tailWord_5860590 prefixEnd_5860590 334366620992592294263627 := by
  unfold tailWord_5860590
  simp only [CollatzResearch.WordTrace]
  refine ⟨26719159729761351741333403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142502185225393875953778149 26719159729761351741333403)
  ·
    refine ⟨40078739594642027612000105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26719159729761351741333403 40078739594642027612000105)
    ·
      refine ⟨30059054695981520709000079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40078739594642027612000105 30059054695981520709000079)
      ·
        refine ⟨45088582043972281063500119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30059054695981520709000079 45088582043972281063500119)
        ·
          refine ⟨67632873065958421595250179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45088582043972281063500119 67632873065958421595250179)
          ·
            refine ⟨101449309598937632392875269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67632873065958421595250179 101449309598937632392875269)
            ·
              refine ⟨19021745549800806073664113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101449309598937632392875269 19021745549800806073664113)
              ·
                refine ⟨14266309162350604555248085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19021745549800806073664113 14266309162350604555248085)
                ·
                  refine ⟨334366620992592294263627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14266309162350604555248085 334366620992592294263627)
                  ·
                    rfl

theorem cell23_5860590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 7].length) (baseStart_5860590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860590 prefixEnd_5860590 := by exact prefixLift 5860590
  have htrace : WordTrace (prefixWord ++ tailWord_5860590) baseStart_5860590 baseEnd_5860590 := by
    simpa [prefixWord, tailWord_5860590, baseEnd_5860590] using wordTrace_append hprefix tailTrace_5860590
  have hstable : (prefixWord ++ tailWord_5860590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860590).length < 2 ^ (prefixWord ++ tailWord_5860590).sum := by decide
  have hdescent : baseEnd_5860590 < baseStart_5860590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860607 : List Nat := [1, 1, 2, 2, 1, 5, 3, 3, 5]
def baseStart_5860607 : Nat := 118140960795 + 5860607 * 2 ^ 59
def prefixEnd_5860607 : Nat := 4983230072969 + 3 ^ 40 * 5860607 * 2
def baseEnd_5860607 : Nat := 334367590900495231317785

theorem tailTrace_5860607 : CollatzResearch.WordTrace tailWord_5860607 prefixEnd_5860607 334367590900495231317785 := by
  unfold tailWord_5860607
  simp only [CollatzResearch.WordTrace]
  refine ⟨213753897879029225834036075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142502598586019483889357383 213753897879029225834036075)
  ·
    refine ⟨320630846818543838751054113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213753897879029225834036075 320630846818543838751054113)
    ·
      refine ⟨240473135113907879063290585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320630846818543838751054113 240473135113907879063290585)
      ·
        refine ⟨180354851335430909297467939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240473135113907879063290585 180354851335430909297467939)
        ·
          refine ⟨270532277003146363946201909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180354851335430909297467939 270532277003146363946201909)
          ·
            refine ⟨25362400969044971619956429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 270532277003146363946201909 25362400969044971619956429)
            ·
              refine ⟨9510900363391864357483661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25362400969044971619956429 9510900363391864357483661)
              ·
                refine ⟨3566587636271949134056373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9510900363391864357483661 3566587636271949134056373)
                ·
                  refine ⟨334367590900495231317785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3566587636271949134056373 334367590900495231317785)
                  ·
                    rfl

theorem cell23_5860607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 3, 5].length) (baseStart_5860607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860607 prefixEnd_5860607 := by exact prefixLift 5860607
  have htrace : WordTrace (prefixWord ++ tailWord_5860607) baseStart_5860607 baseEnd_5860607 := by
    simpa [prefixWord, tailWord_5860607, baseEnd_5860607] using wordTrace_append hprefix tailTrace_5860607
  have hstable : (prefixWord ++ tailWord_5860607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860607).length < 2 ^ (prefixWord ++ tailWord_5860607).sum := by decide
  have hdescent : baseEnd_5860607 < baseStart_5860607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860620 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 4, 5]
def baseStart_5860620 : Nat := 118140960795 + 5860620 * 2 ^ 59
def prefixEnd_5860620 : Nat := 4983230072969 + 3 ^ 40 * 5860620 * 2
def baseEnd_5860620 : Nat := 1003104997784321843665835

theorem tailTrace_5860620 : CollatzResearch.WordTrace tailWord_5860620 prefixEnd_5860620 1003104997784321843665835 := by
  unfold tailWord_5860620
  simp only [CollatzResearch.WordTrace]
  refine ⟨106877186013991064527129657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142502914685321419369506209 106877186013991064527129657)
  ·
    refine ⟨80157889510493298395347243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106877186013991064527129657 80157889510493298395347243)
    ·
      refine ⟨120236834265739947593020865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80157889510493298395347243 120236834265739947593020865)
      ·
        refine ⟨90177625699304960694765649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120236834265739947593020865 90177625699304960694765649)
        ·
          refine ⟨67633219274478720521074237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90177625699304960694765649 67633219274478720521074237)
          ·
            refine ⟨25362457227929520195402839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67633219274478720521074237 25362457227929520195402839)
            ·
              refine ⟨38043685841894280293104259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25362457227929520195402839 38043685841894280293104259)
              ·
                refine ⟨57065528762841420439656389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38043685841894280293104259 57065528762841420439656389)
                ·
                  refine ⟨10699786643032766332435573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57065528762841420439656389 10699786643032766332435573)
                  ·
                    refine ⟨1003104997784321843665835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10699786643032766332435573 1003104997784321843665835)
                    ·
                      rfl

theorem cell23_5860620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 4, 5].length) (baseStart_5860620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860620 prefixEnd_5860620 := by exact prefixLift 5860620
  have htrace : WordTrace (prefixWord ++ tailWord_5860620) baseStart_5860620 baseEnd_5860620 := by
    simpa [prefixWord, tailWord_5860620, baseEnd_5860620] using wordTrace_append hprefix tailTrace_5860620
  have hstable : (prefixWord ++ tailWord_5860620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860620).length < 2 ^ (prefixWord ++ tailWord_5860620).sum := by decide
  have hdescent : baseEnd_5860620 < baseStart_5860620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860623 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 8]
def baseStart_5860623 : Nat := 118140960795 + 5860623 * 2 ^ 59
def prefixEnd_5860623 : Nat := 4983230072969 + 3 ^ 40 * 5860623 * 2
def baseEnd_5860623 : Nat := 3009316533794929019259991

theorem tailTrace_5860623 : CollatzResearch.WordTrace tailWord_5860623 prefixEnd_5860623 3009316533794929019259991 := by
  unfold tailWord_5860623
  simp only [CollatzResearch.WordTrace]
  refine ⟨213754481446971260566618523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142502987631314173711079015 213754481446971260566618523)
  ·
    refine ⟨320631722170456890849927785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213754481446971260566618523 320631722170456890849927785)
    ·
      refine ⟨240473791627842668137445839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320631722170456890849927785 240473791627842668137445839)
      ·
        refine ⟨360710687441764002206168759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240473791627842668137445839 360710687441764002206168759)
        ·
          refine ⟨541066031162646003309253139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360710687441764002206168759 541066031162646003309253139)
          ·
            refine ⟨811599046743969004963879709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541066031162646003309253139 811599046743969004963879709)
            ·
              refine ⟨304349642528988376861454891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 811599046743969004963879709 304349642528988376861454891)
              ·
                refine ⟨456524463793482565292182337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304349642528988376861454891 456524463793482565292182337)
                ·
                  refine ⟨342393347845111923969136753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 456524463793482565292182337 342393347845111923969136753)
                  ·
                    refine ⟨256795010883833942976852565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 342393347845111923969136753 256795010883833942976852565)
                    ·
                      refine ⟨3009316533794929019259991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 256795010883833942976852565 3009316533794929019259991)
                      ·
                        rfl

theorem cell23_5860623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 8].length) (baseStart_5860623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860623 prefixEnd_5860623 := by exact prefixLift 5860623
  have htrace : WordTrace (prefixWord ++ tailWord_5860623) baseStart_5860623 baseEnd_5860623 := by
    simpa [prefixWord, tailWord_5860623, baseEnd_5860623] using wordTrace_append hprefix tailTrace_5860623
  have hstable : (prefixWord ++ tailWord_5860623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860623).length < 2 ^ (prefixWord ++ tailWord_5860623).sum := by decide
  have hdescent : baseEnd_5860623 < baseStart_5860623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860657 : List Nat := [1, 2, 2, 3, 3, 1, 1, 3, 2, 1, 4]
def baseStart_5860657 : Nat := 118140960795 + 5860657 * 2 ^ 59
def prefixEnd_5860657 : Nat := 4983230072969 + 3 ^ 40 * 5860657 * 2
def baseEnd_5860657 : Nat := 3009333992137181886234835

theorem tailTrace_5860657 : CollatzResearch.WordTrace tailWord_5860657 prefixEnd_5860657 3009333992137181886234835 := by
  unfold tailWord_5860657
  simp only [CollatzResearch.WordTrace]
  refine ⟨213755721528848084373356225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142503814352565389582237483 213755721528848084373356225)
  ·
    refine ⟨160316791146636063280017169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213755721528848084373356225 160316791146636063280017169)
    ·
      refine ⟨120237593359977047460012877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160316791146636063280017169 120237593359977047460012877)
      ·
        refine ⟨45089097509991392797504829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120237593359977047460012877 45089097509991392797504829)
        ·
          refine ⟨16908411566246772299064311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45089097509991392797504829 16908411566246772299064311)
          ·
            refine ⟨25362617349370158448596467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16908411566246772299064311 25362617349370158448596467)
            ·
              refine ⟨38043926024055237672894701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25362617349370158448596467 38043926024055237672894701)
              ·
                refine ⟨14266472259020714127335513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38043926024055237672894701 14266472259020714127335513)
                ·
                  refine ⟨10699854194265535595501635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14266472259020714127335513 10699854194265535595501635)
                  ·
                    refine ⟨16049781291398303393252453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10699854194265535595501635 16049781291398303393252453)
                    ·
                      refine ⟨3009333992137181886234835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16049781291398303393252453 3009333992137181886234835)
                      ·
                        rfl

theorem cell23_5860657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_5860657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860657 prefixEnd_5860657 := by exact prefixLift 5860657
  have htrace : WordTrace (prefixWord ++ tailWord_5860657) baseStart_5860657 baseEnd_5860657 := by
    simpa [prefixWord, tailWord_5860657, baseEnd_5860657] using wordTrace_append hprefix tailTrace_5860657
  have hstable : (prefixWord ++ tailWord_5860657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860657).length < 2 ^ (prefixWord ++ tailWord_5860657).sum := by decide
  have hdescent : baseEnd_5860657 < baseStart_5860657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860711 : List Nat := [1, 1, 5, 1, 4, 2, 1, 1, 2, 2, 3]
def baseStart_5860711 : Nat := 118140960795 + 5860711 * 2 ^ 59
def prefixEnd_5860711 : Nat := 4983230072969 + 3 ^ 40 * 5860711 * 2
def baseEnd_5860711 : Nat := 3009361720092524674959587

theorem tailTrace_5860711 : CollatzResearch.WordTrace tailWord_5860711 prefixEnd_5860711 3009361720092524674959587 := by
  unfold tailWord_5860711
  simp only [CollatzResearch.WordTrace]
  refine ⟨213757691070652451595821987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142505127380434967730547991 213757691070652451595821987)
  ·
    refine ⟨320636536605978677393732981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213757691070652451595821987 320636536605978677393732981)
    ·
      refine ⟨30059675306810501005662467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 320636536605978677393732981 30059675306810501005662467)
      ·
        refine ⟨45089512960215751508493701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30059675306810501005662467 45089512960215751508493701)
        ·
          refine ⟨8454283680040453407842569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45089512960215751508493701 8454283680040453407842569)
          ·
            refine ⟨6340712760030340055881927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8454283680040453407842569 6340712760030340055881927)
            ·
              refine ⟨9511069140045510083822891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6340712760030340055881927 9511069140045510083822891)
              ·
                refine ⟨14266603710068265125734337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9511069140045510083822891 14266603710068265125734337)
                ·
                  refine ⟨10699952782551198844300753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14266603710068265125734337 10699952782551198844300753)
                  ·
                    refine ⟨8024964586913399133225565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10699952782551198844300753 8024964586913399133225565)
                    ·
                      refine ⟨3009361720092524674959587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8024964586913399133225565 3009361720092524674959587)
                      ·
                        rfl

theorem cell23_5860711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_5860711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860711 prefixEnd_5860711 := by exact prefixLift 5860711
  have htrace : WordTrace (prefixWord ++ tailWord_5860711) baseStart_5860711 baseEnd_5860711 := by
    simpa [prefixWord, tailWord_5860711, baseEnd_5860711] using wordTrace_append hprefix tailTrace_5860711
  have hstable : (prefixWord ++ tailWord_5860711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860711).length < 2 ^ (prefixWord ++ tailWord_5860711).sum := by decide
  have hdescent : baseEnd_5860711 < baseStart_5860711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860727 : List Nat := [1, 1, 3, 1, 1, 2, 5, 3, 1, 5]
def baseStart_5860727 : Nat := 118140960795 + 5860727 * 2 ^ 59
def prefixEnd_5860727 : Nat := 4983230072969 + 3 ^ 40 * 5860727 * 2
def baseEnd_5860727 : Nat := 1003123311927665537453171

theorem tailTrace_5860727 : CollatzResearch.WordTrace tailWord_5860727 prefixEnd_5860727 1003123311927665537453171 := by
  unfold tailWord_5860727
  simp only [CollatzResearch.WordTrace]
  refine ⟨213758274638594486328404435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142505516425729657552269623 213758274638594486328404435)
  ·
    refine ⟨320637411957891729492606653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213758274638594486328404435 320637411957891729492606653)
    ·
      refine ⟨120239029484209398559727495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 320637411957891729492606653 120239029484209398559727495)
      ·
        refine ⟨180358544226314097839591243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120239029484209398559727495 180358544226314097839591243)
        ·
          refine ⟨270537816339471146759386865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180358544226314097839591243 270537816339471146759386865)
          ·
            refine ⟨202903362254603360069540149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270537816339471146759386865 202903362254603360069540149)
            ·
              refine ⟨19022190211369065006519389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 202903362254603360069540149 19022190211369065006519389)
              ·
                refine ⟨7133321329263399377444771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19022190211369065006519389 7133321329263399377444771)
                ·
                  refine ⟨10699981993895099066167157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7133321329263399377444771 10699981993895099066167157)
                  ·
                    refine ⟨1003123311927665537453171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10699981993895099066167157 1003123311927665537453171)
                    ·
                      rfl

theorem cell23_5860727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 5].length) (baseStart_5860727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860727 prefixEnd_5860727 := by exact prefixLift 5860727
  have htrace : WordTrace (prefixWord ++ tailWord_5860727) baseStart_5860727 baseEnd_5860727 := by
    simpa [prefixWord, tailWord_5860727, baseEnd_5860727] using wordTrace_append hprefix tailTrace_5860727
  have hstable : (prefixWord ++ tailWord_5860727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860727).length < 2 ^ (prefixWord ++ tailWord_5860727).sum := by decide
  have hdescent : baseEnd_5860727 < baseStart_5860727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860741 : List Nat := [1, 3, 1, 1, 3, 1, 4, 4, 1, 1, 3]
def baseStart_5860741 : Nat := 118140960795 + 5860741 * 2 ^ 59
def prefixEnd_5860741 : Nat := 4983230072969 + 3 ^ 40 * 5860741 * 2
def baseEnd_5860741 : Nat := 3009377124512159557584449

theorem tailTrace_5860741 : CollatzResearch.WordTrace tailWord_5860741 prefixEnd_5860741 3009377124512159557584449 := by
  unfold tailWord_5860741
  simp only [CollatzResearch.WordTrace]
  refine ⟨213758785260543766719414077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142505856840362511146276051 213758785260543766719414077)
  ·
    refine ⟨80159544472703912519780279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213758785260543766719414077 80159544472703912519780279)
    ·
      refine ⟨120239316709055868779670419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80159544472703912519780279 120239316709055868779670419)
      ·
        refine ⟨180358975063583803169505629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120239316709055868779670419 180358975063583803169505629)
        ·
          refine ⟨67634615648843926188564611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180358975063583803169505629 67634615648843926188564611)
          ·
            refine ⟨101451923473265889282846917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67634615648843926188564611 101451923473265889282846917)
            ·
              refine ⟨19022235651237354240533797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101451923473265889282846917 19022235651237354240533797)
              ·
                refine ⟨3566669184607003920100087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19022235651237354240533797 3566669184607003920100087)
                ·
                  refine ⟨5350003776910505880150131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3566669184607003920100087 5350003776910505880150131)
                  ·
                    refine ⟨8025005665365758820225197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5350003776910505880150131 8025005665365758820225197)
                    ·
                      refine ⟨3009377124512159557584449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8025005665365758820225197 3009377124512159557584449)
                      ·
                        rfl

theorem cell23_5860741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 4, 1, 1, 3].length) (baseStart_5860741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860741 prefixEnd_5860741 := by exact prefixLift 5860741
  have htrace : WordTrace (prefixWord ++ tailWord_5860741) baseStart_5860741 baseEnd_5860741 := by
    simpa [prefixWord, tailWord_5860741, baseEnd_5860741] using wordTrace_append hprefix tailTrace_5860741
  have hstable : (prefixWord ++ tailWord_5860741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860741).length < 2 ^ (prefixWord ++ tailWord_5860741).sum := by decide
  have hdescent : baseEnd_5860741 < baseStart_5860741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860757 : List Nat := [1, 3, 2, 1, 1, 2, 5, 1, 1, 6]
def baseStart_5860757 : Nat := 118140960795 + 5860757 * 2 ^ 59
def prefixEnd_5860757 : Nat := 4983230072969 + 3 ^ 40 * 5860757 * 2
def baseEnd_5860757 : Nat := 1003128446734210498328125

theorem tailTrace_5860757 : CollatzResearch.WordTrace tailWord_5860757 prefixEnd_5860757 1003128446734210498328125 := by
  unfold tailWord_5860757
  simp only [CollatzResearch.WordTrace]
  refine ⟨213759368828485801451996525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142506245885657200967997683 213759368828485801451996525)
  ·
    refine ⟨80159763310682175544498697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213759368828485801451996525 80159763310682175544498697)
    ·
      refine ⟨60119822483011631658374023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80159763310682175544498697 60119822483011631658374023)
      ·
        refine ⟨90179733724517447487561035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60119822483011631658374023 90179733724517447487561035)
        ·
          refine ⟨135269600586776171231341553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90179733724517447487561035 135269600586776171231341553)
          ·
            refine ⟨101452200440082128423506165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135269600586776171231341553 101452200440082128423506165)
            ·
              refine ⟨9511143791257699539703703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101452200440082128423506165 9511143791257699539703703)
              ·
                refine ⟨14266715686886549309555555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9511143791257699539703703 14266715686886549309555555)
                ·
                  refine ⟨21400073530329823964333333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14266715686886549309555555 21400073530329823964333333)
                  ·
                    refine ⟨1003128446734210498328125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21400073530329823964333333 1003128446734210498328125)
                    ·
                      rfl

theorem cell23_5860757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_5860757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860757 prefixEnd_5860757 := by exact prefixLift 5860757
  have htrace : WordTrace (prefixWord ++ tailWord_5860757) baseStart_5860757 baseEnd_5860757 := by
    simpa [prefixWord, tailWord_5860757, baseEnd_5860757] using wordTrace_append hprefix tailTrace_5860757
  have hstable : (prefixWord ++ tailWord_5860757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860757).length < 2 ^ (prefixWord ++ tailWord_5860757).sum := by decide
  have hdescent : baseEnd_5860757 < baseStart_5860757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860781 : List Nat := [1, 5, 2, 2, 1, 1, 2, 3, 1, 1, 4]
def baseStart_5860781 : Nat := 118140960795 + 5860781 * 2 ^ 59
def prefixEnd_5860781 : Nat := 4983230072969 + 3 ^ 40 * 5860781 * 2
def baseEnd_5860781 : Nat := 3009397663738339401084265

theorem tailTrace_5860781 : CollatzResearch.WordTrace tailWord_5860781 prefixEnd_5860781 3009397663738339401084265 := by
  unfold tailWord_5860781
  simp only [CollatzResearch.WordTrace]
  refine ⟨213760244180398853550870197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142506829453599235700580131 213760244180398853550870197)
  ·
    refine ⟨20040022891912392520394081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 213760244180398853550870197 20040022891912392520394081)
    ·
      refine ⟨15030017168934294390295561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20040022891912392520394081 15030017168934294390295561)
      ·
        refine ⟨11272512876700720792721671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15030017168934294390295561 11272512876700720792721671)
        ·
          refine ⟨16908769315051081189082507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11272512876700720792721671 16908769315051081189082507)
          ·
            refine ⟨25363153972576621783623761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16908769315051081189082507 25363153972576621783623761)
            ·
              refine ⟨19022365479432466337717821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25363153972576621783623761 19022365479432466337717821)
              ·
                refine ⟨7133387054787174876644183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19022365479432466337717821 7133387054787174876644183)
                ·
                  refine ⟨10700080582180762314966275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7133387054787174876644183 10700080582180762314966275)
                  ·
                    refine ⟨16050120873271143472449413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10700080582180762314966275 16050120873271143472449413)
                    ·
                      refine ⟨3009397663738339401084265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16050120873271143472449413 3009397663738339401084265)
                      ·
                        rfl

theorem cell23_5860781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_5860781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860781 prefixEnd_5860781 := by exact prefixLift 5860781
  have htrace : WordTrace (prefixWord ++ tailWord_5860781) baseStart_5860781 baseEnd_5860781 := by
    simpa [prefixWord, tailWord_5860781, baseEnd_5860781] using wordTrace_append hprefix tailTrace_5860781
  have hstable : (prefixWord ++ tailWord_5860781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860781).length < 2 ^ (prefixWord ++ tailWord_5860781).sum := by decide
  have hdescent : baseEnd_5860781 < baseStart_5860781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860804 : List Nat := [2, 3, 3, 2, 1, 2, 2, 8]
def baseStart_5860804 : Nat := 118140960795 + 5860804 * 2 ^ 59
def prefixEnd_5860804 : Nat := 4983230072969 + 3 ^ 40 * 5860804 * 2
def baseEnd_5860804 : Nat := 111459610140496030040617

theorem tailTrace_5860804 : CollatzResearch.WordTrace tailWord_5860804 prefixEnd_5860804 111459610140496030040617 := by
  unfold tailWord_5860804
  simp only [CollatzResearch.WordTrace]
  refine ⟨106880541529657764239478733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142507388706210352319304977 106880541529657764239478733)
  ·
    refine ⟨40080203073621661589804525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106880541529657764239478733 40080203073621661589804525)
    ·
      refine ⟨15030076152608123096176697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40080203073621661589804525 15030076152608123096176697)
      ·
        refine ⟨11272557114456092322132523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15030076152608123096176697 11272557114456092322132523)
        ·
          refine ⟨16908835671684138483198785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11272557114456092322132523 16908835671684138483198785)
          ·
            refine ⟨12681626753763103862399089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16908835671684138483198785 12681626753763103862399089)
            ·
              refine ⟨9511220065322327896799317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12681626753763103862399089 9511220065322327896799317)
              ·
                refine ⟨111459610140496030040617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9511220065322327896799317 111459610140496030040617)
                ·
                  rfl

theorem cell23_5860804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 8].length) (baseStart_5860804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860804 prefixEnd_5860804 := by exact prefixLift 5860804
  have htrace : WordTrace (prefixWord ++ tailWord_5860804) baseStart_5860804 baseEnd_5860804 := by
    simpa [prefixWord, tailWord_5860804, baseEnd_5860804] using wordTrace_append hprefix tailTrace_5860804
  have hstable : (prefixWord ++ tailWord_5860804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860804).length < 2 ^ (prefixWord ++ tailWord_5860804).sum := by decide
  have hdescent : baseEnd_5860804 < baseStart_5860804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860854 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4]
def baseStart_5860854 : Nat := 118140960795 + 5860854 * 2 ^ 59
def prefixEnd_5860854 : Nat := 4983230072969 + 3 ^ 40 * 5860854 * 2
def baseEnd_5860854 : Nat := 3009435147826117615471429

theorem tailTrace_5860854 : CollatzResearch.WordTrace tailWord_5860854 prefixEnd_5860854 3009435147826117615471429 := by
  unfold tailWord_5860854
  simp only [CollatzResearch.WordTrace]
  refine ⟨13360181669320899188642351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142508604472756258012185077 13360181669320899188642351)
  ·
    refine ⟨20040272503981348782963527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13360181669320899188642351 20040272503981348782963527)
    ·
      refine ⟨30060408755972023174445291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20040272503981348782963527 30060408755972023174445291)
      ·
        refine ⟨45090613133958034761667937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30060408755972023174445291 45090613133958034761667937)
        ·
          refine ⟨33817959850468526071250953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45090613133958034761667937 33817959850468526071250953)
          ·
            refine ⟨25363469887851394553438215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33817959850468526071250953 25363469887851394553438215)
            ·
              refine ⟨38045204831777091830157323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25363469887851394553438215 38045204831777091830157323)
              ·
                refine ⟨57067807247665637745235985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38045204831777091830157323 57067807247665637745235985)
                ·
                  refine ⟨42800855435749228308926989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57067807247665637745235985 42800855435749228308926989)
                  ·
                    refine ⟨16050320788405960615847621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42800855435749228308926989 16050320788405960615847621)
                    ·
                      refine ⟨3009435147826117615471429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16050320788405960615847621 3009435147826117615471429)
                      ·
                        rfl

theorem cell23_5860854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_5860854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860854 prefixEnd_5860854 := by exact prefixLift 5860854
  have htrace : WordTrace (prefixWord ++ tailWord_5860854) baseStart_5860854 baseEnd_5860854 := by
    simpa [prefixWord, tailWord_5860854, baseEnd_5860854] using wordTrace_append hprefix tailTrace_5860854
  have hstable : (prefixWord ++ tailWord_5860854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860854).length < 2 ^ (prefixWord ++ tailWord_5860854).sum := by decide
  have hdescent : baseEnd_5860854 < baseStart_5860854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860871 : List Nat := [1, 1, 4, 3, 2, 1, 1, 3, 1, 4, 2]
def baseStart_5860871 : Nat := 118140960795 + 5860871 * 2 ^ 59
def prefixEnd_5860871 : Nat := 4983230072969 + 3 ^ 40 * 5860871 * 2
def baseEnd_5860871 : Nat := 3009443876997244048958851

theorem tailTrace_5860871 : CollatzResearch.WordTrace tailWord_5860871 prefixEnd_5860871 3009443876997244048958851 := by
  unfold tailWord_5860871
  simp only [CollatzResearch.WordTrace]
  refine ⟨213763526750072798921646467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142509017833381865947764311 213763526750072798921646467)
  ·
    refine ⟨320645290125109198382469701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213763526750072798921646467 320645290125109198382469701)
    ·
      refine ⟨60120991898457974696713069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 320645290125109198382469701 60120991898457974696713069)
      ·
        refine ⟨22545371961921740511267401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60120991898457974696713069 22545371961921740511267401)
        ·
          refine ⟨16909028971441305383450551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22545371961921740511267401 16909028971441305383450551)
          ·
            refine ⟨25363543457161958075175827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16909028971441305383450551 25363543457161958075175827)
            ·
              refine ⟨38045315185742937112763741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25363543457161958075175827 38045315185742937112763741)
              ·
                refine ⟨14266993194653601417286403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38045315185742937112763741 14266993194653601417286403)
                ·
                  refine ⟨21400489791980402125929605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14266993194653601417286403 21400489791980402125929605)
                  ·
                    refine ⟨4012591835996325398611801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21400489791980402125929605 4012591835996325398611801)
                    ·
                      refine ⟨3009443876997244048958851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4012591835996325398611801 3009443876997244048958851)
                      ·
                        rfl

theorem cell23_5860871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_5860871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860871 prefixEnd_5860871 := by exact prefixLift 5860871
  have htrace : WordTrace (prefixWord ++ tailWord_5860871) baseStart_5860871 baseEnd_5860871 := by
    simpa [prefixWord, tailWord_5860871, baseEnd_5860871] using wordTrace_append hprefix tailTrace_5860871
  have hstable : (prefixWord ++ tailWord_5860871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860871).length < 2 ^ (prefixWord ++ tailWord_5860871).sum := by decide
  have hdescent : baseEnd_5860871 < baseStart_5860871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5860944 : List Nat := [2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 4]
def baseStart_5860944 : Nat := 118140960795 + 5860944 * 2 ^ 59
def prefixEnd_5860944 : Nat := 4983230072969 + 3 ^ 40 * 5860944 * 2
def baseEnd_5860944 : Nat := 3009481361085022263346015

theorem tailTrace_5860944 : CollatzResearch.WordTrace tailWord_5860944 prefixEnd_5860944 3009481361085022263346015 := by
  unfold tailWord_5860944
  simp only [CollatzResearch.WordTrace]
  refine ⟨106883094639404166194526943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142510792852538888259369257 106883094639404166194526943)
  ·
    refine ⟨160324641959106249291790415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106883094639404166194526943 160324641959106249291790415)
    ·
      refine ⟨240486962938659373937685623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160324641959106249291790415 240486962938659373937685623)
      ·
        refine ⟨360730444407989060906528435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240486962938659373937685623 360730444407989060906528435)
        ·
          refine ⟨541095666611983591359792653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360730444407989060906528435 541095666611983591359792653)
          ·
            refine ⟨202910874979493846759922245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 541095666611983591359792653 202910874979493846759922245)
            ·
              refine ⟨38045789058655096267485421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 202910874979493846759922245 38045789058655096267485421)
              ·
                refine ⟨14267170896995661100307033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38045789058655096267485421 14267170896995661100307033)
                ·
                  refine ⟨10700378172746745825230275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14267170896995661100307033 10700378172746745825230275)
                  ·
                    refine ⟨16050567259120118737845413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10700378172746745825230275 16050567259120118737845413)
                    ·
                      refine ⟨3009481361085022263346015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16050567259120118737845413 3009481361085022263346015)
                      ·
                        rfl

theorem cell23_5860944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 4].length) (baseStart_5860944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860944 prefixEnd_5860944 := by exact prefixLift 5860944
  have htrace : WordTrace (prefixWord ++ tailWord_5860944) baseStart_5860944 baseEnd_5860944 := by
    simpa [prefixWord, tailWord_5860944, baseEnd_5860944] using wordTrace_append hprefix tailTrace_5860944
  have hstable : (prefixWord ++ tailWord_5860944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860944).length < 2 ^ (prefixWord ++ tailWord_5860944).sum := by decide
  have hdescent : baseEnd_5860944 < baseStart_5860944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
