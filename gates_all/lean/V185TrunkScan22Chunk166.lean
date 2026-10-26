import V185TrunkScan22Chunk165

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1482371 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 1, 7]
def baseStart_1482371 : Nat := 118140960795 + 1482371 * 2 ^ 59
def prefixEnd_1482371 : Nat := 4983230072969 + 3 ^ 40 * 1482371 * 2
def baseEnd_1482371 : Nat := 507445887524083300230137

theorem tailTrace_1482371 : CollatzResearch.WordTrace tailWord_1482371 prefixEnd_1482371 507445887524083300230137 := by
  unfold tailWord_1482371
  simp only [CollatzResearch.WordTrace]
  refine ⟨54066512112630510656110967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36044341408420340437407311 54066512112630510656110967)
  ·
    refine ⟨81099768168945765984166451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54066512112630510656110967 81099768168945765984166451)
    ·
      refine ⟨121649652253418648976249677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81099768168945765984166451 121649652253418648976249677)
      ·
        refine ⟨45618619595031993366093629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121649652253418648976249677 45618619595031993366093629)
        ·
          refine ⟨17106982348136997512285111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45618619595031993366093629 17106982348136997512285111)
          ·
            refine ⟨25660473522205496268427667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17106982348136997512285111 25660473522205496268427667)
            ·
              refine ⟨38490710283308244402641501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25660473522205496268427667 38490710283308244402641501)
              ·
                refine ⟨14434016356240591650990563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38490710283308244402641501 14434016356240591650990563)
                ·
                  refine ⟨21651024534360887476485845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14434016356240591650990563 21651024534360887476485845)
                  ·
                    refine ⟨507445887524083300230137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21651024534360887476485845 507445887524083300230137)
                    ·
                      rfl

theorem cell22_1482371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 7].length) (baseStart_1482371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1482371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1482371 prefixEnd_1482371 := by exact prefixLift 1482371
  have htrace : WordTrace (prefixWord ++ tailWord_1482371) baseStart_1482371 baseEnd_1482371 := by
    simpa [prefixWord, tailWord_1482371, baseEnd_1482371] using wordTrace_append hprefix tailTrace_1482371
  have hstable : (prefixWord ++ tailWord_1482371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482371).length < 2 ^ (prefixWord ++ tailWord_1482371).sum := by decide
  have hdescent : baseEnd_1482371 < baseStart_1482371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482373 : List Nat := [1, 3, 1, 1, 4, 1, 3, 3, 5]
def baseStart_1482373 : Nat := 118140960795 + 1482373 * 2 ^ 59
def prefixEnd_1482373 : Nat := 4983230072969 + 3 ^ 40 * 1482373 * 2
def baseEnd_1482373 : Nat := 169148857388318653893377

theorem tailTrace_1482373 : CollatzResearch.WordTrace tailWord_1482373 prefixEnd_1482373 169148857388318653893377 := by
  unfold tailWord_1482373
  simp only [CollatzResearch.WordTrace]
  refine ⟨54066585058623264997683773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36044390039082176665122515 54066585058623264997683773)
  ·
    refine ⟨20274969396983724374131415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54066585058623264997683773 20274969396983724374131415)
    ·
      refine ⟨30412454095475586561197123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20274969396983724374131415 30412454095475586561197123)
      ·
        refine ⟨45618681143213379841795685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30412454095475586561197123 45618681143213379841795685)
        ·
          refine ⟨8553502714352508720336691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45618681143213379841795685 8553502714352508720336691)
          ·
            refine ⟨12830254071528763080505037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8553502714352508720336691 12830254071528763080505037)
            ·
              refine ⟨4811345276823286155189389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12830254071528763080505037 4811345276823286155189389)
              ·
                refine ⟨1804254478808732308196021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4811345276823286155189389 1804254478808732308196021)
                ·
                  refine ⟨169148857388318653893377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1804254478808732308196021 169148857388318653893377)
                  ·
                    rfl

theorem cell22_1482373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 5].length) (baseStart_1482373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1482373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1482373 prefixEnd_1482373 := by exact prefixLift 1482373
  have htrace : WordTrace (prefixWord ++ tailWord_1482373) baseStart_1482373 baseEnd_1482373 := by
    simpa [prefixWord, tailWord_1482373, baseEnd_1482373] using wordTrace_append hprefix tailTrace_1482373
  have hstable : (prefixWord ++ tailWord_1482373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482373).length < 2 ^ (prefixWord ++ tailWord_1482373).sum := by decide
  have hdescent : baseEnd_1482373 < baseStart_1482373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482422 : List Nat := [5, 1, 3, 1, 1, 2, 1, 1, 2, 5]
def baseStart_1482422 : Nat := 118140960795 + 1482422 * 2 ^ 59
def prefixEnd_1482422 : Nat := 4983230072969 + 3 ^ 40 * 1482422 * 2
def baseEnd_1482422 : Nat := 507463345866336167204981

theorem tailTrace_1482422 : CollatzResearch.WordTrace tailWord_1482422 prefixEnd_1482422 507463345866336167204981 := by
  unfold tailWord_1482422
  simp only [CollatzResearch.WordTrace]
  refine ⟨3379273264715359147888595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36045581490297164244145013 3379273264715359147888595)
  ·
    refine ⟨5068909897073038721832893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3379273264715359147888595 5068909897073038721832893)
    ·
      refine ⟨1900841211402389520687335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5068909897073038721832893 1900841211402389520687335)
      ·
        refine ⟨2851261817103584281031003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1900841211402389520687335 2851261817103584281031003)
        ·
          refine ⟨4276892725655376421546505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2851261817103584281031003 4276892725655376421546505)
          ·
            refine ⟨3207669544241532316159879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4276892725655376421546505 3207669544241532316159879)
            ·
              refine ⟨4811504316362298474239819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3207669544241532316159879 4811504316362298474239819)
              ·
                refine ⟨7217256474543447711359729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4811504316362298474239819 7217256474543447711359729)
                ·
                  refine ⟨5412942355907585783519797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7217256474543447711359729 5412942355907585783519797)
                  ·
                    refine ⟨507463345866336167204981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5412942355907585783519797 507463345866336167204981)
                    ·
                      rfl

theorem cell22_1482422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_1482422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1482422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1482422 prefixEnd_1482422 := by exact prefixLift 1482422
  have htrace : WordTrace (prefixWord ++ tailWord_1482422) baseStart_1482422 baseEnd_1482422 := by
    simpa [prefixWord, tailWord_1482422, baseEnd_1482422] using wordTrace_append hprefix tailTrace_1482422
  have hstable : (prefixWord ++ tailWord_1482422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482422).length < 2 ^ (prefixWord ++ tailWord_1482422).sum := by decide
  have hdescent : baseEnd_1482422 < baseStart_1482422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482448 : List Nat := [2, 1, 1, 1, 1, 2, 1, 7, 2, 4]
def baseStart_1482448 : Nat := 118140960795 + 1482448 * 2 ^ 59
def prefixEnd_1482448 : Nat := 4983230072969 + 3 ^ 40 * 1482448 * 2
def baseEnd_1482448 : Nat := 507472246197680766054901

theorem tailTrace_1482448 : CollatzResearch.WordTrace tailWord_1482448 prefixEnd_1482448 507472246197680766054901 := by
  unfold tailWord_1482448
  simp only [CollatzResearch.WordTrace]
  refine ⟨27034660266675776403331999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36046213688901035204442665 27034660266675776403331999)
  ·
    refine ⟨40551990400013664604997999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27034660266675776403331999 40551990400013664604997999)
    ·
      refine ⟨60827985600020496907496999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40551990400013664604997999 60827985600020496907496999)
      ·
        refine ⟨91241978400030745361245499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60827985600020496907496999 91241978400030745361245499)
        ·
          refine ⟨136862967600046118041868249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91241978400030745361245499 136862967600046118041868249)
          ·
            refine ⟨102647225700034588531401187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136862967600046118041868249 102647225700034588531401187)
            ·
              refine ⟨153970838550051882797101781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102647225700034588531401187 153970838550051882797101781)
              ·
                refine ⟨3608691528516841003057073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 153970838550051882797101781 3608691528516841003057073)
                ·
                  refine ⟨2706518646387630752292805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3608691528516841003057073 2706518646387630752292805)
                  ·
                    refine ⟨507472246197680766054901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2706518646387630752292805 507472246197680766054901)
                    ·
                      rfl

theorem cell22_1482448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 2, 4].length) (baseStart_1482448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1482448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1482448 prefixEnd_1482448 := by exact prefixLift 1482448
  have htrace : WordTrace (prefixWord ++ tailWord_1482448) baseStart_1482448 baseEnd_1482448 := by
    simpa [prefixWord, tailWord_1482448, baseEnd_1482448] using wordTrace_append hprefix tailTrace_1482448
  have hstable : (prefixWord ++ tailWord_1482448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482448).length < 2 ^ (prefixWord ++ tailWord_1482448).sum := by decide
  have hdescent : baseEnd_1482448 < baseStart_1482448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482450 : List Nat := [3, 2, 2, 2, 2, 1, 2, 2, 1, 5]
def baseStart_1482450 : Nat := 118140960795 + 1482450 * 2 ^ 59
def prefixEnd_1482450 : Nat := 4983230072969 + 3 ^ 40 * 1482450 * 2
def baseEnd_1482450 : Nat := 507472930838553427504895

theorem tailTrace_1482450 : CollatzResearch.WordTrace tailWord_1482450 prefixEnd_1482450 507472930838553427504895 := by
  unfold tailWord_1482450
  simp only [CollatzResearch.WordTrace]
  refine ⟨13517348369836076787059201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36046262319562871432157869 13517348369836076787059201)
  ·
    refine ⟨10138011277377057590294401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13517348369836076787059201 10138011277377057590294401)
    ·
      refine ⟨7603508458032793192720801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10138011277377057590294401 7603508458032793192720801)
      ·
        refine ⟨5702631343524594894540601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7603508458032793192720801 5702631343524594894540601)
        ·
          refine ⟨4276973507643446170905451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5702631343524594894540601 4276973507643446170905451)
          ·
            refine ⟨6415460261465169256358177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4276973507643446170905451 6415460261465169256358177)
            ·
              refine ⟨4811595196098876942268633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6415460261465169256358177 4811595196098876942268633)
              ·
                refine ⟨3608696397074157706701475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4811595196098876942268633 3608696397074157706701475)
                ·
                  refine ⟨5413044595611236560052213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3608696397074157706701475 5413044595611236560052213)
                  ·
                    refine ⟨507472930838553427504895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5413044595611236560052213 507472930838553427504895)
                    ·
                      rfl

theorem cell22_1482450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_1482450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1482450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1482450 prefixEnd_1482450 := by exact prefixLift 1482450
  have htrace : WordTrace (prefixWord ++ tailWord_1482450) baseStart_1482450 baseEnd_1482450 := by
    simpa [prefixWord, tailWord_1482450, baseEnd_1482450] using wordTrace_append hprefix tailTrace_1482450
  have hstable : (prefixWord ++ tailWord_1482450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482450).length < 2 ^ (prefixWord ++ tailWord_1482450).sum := by decide
  have hdescent : baseEnd_1482450 < baseStart_1482450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482452 : List Nat := [2, 4, 1, 3, 1, 1, 1, 5, 4]
def baseStart_1482452 : Nat := 118140960795 + 1482452 * 2 ^ 59
def prefixEnd_1482452 : Nat := 4983230072969 + 3 ^ 40 * 1482452 * 2
def baseEnd_1482452 : Nat := 169157871826475362984963

theorem tailTrace_1482452 : CollatzResearch.WordTrace tailWord_1482452 prefixEnd_1482452 169157871826475362984963 := by
  unfold tailWord_1482452
  simp only [CollatzResearch.WordTrace]
  refine ⟨27034733212668530744904805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36046310950224707659873073 27034733212668530744904805)
  ·
    refine ⟨5069012477375349514669651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27034733212668530744904805 5069012477375349514669651)
    ·
      refine ⟨7603518716063024272004477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5069012477375349514669651 7603518716063024272004477)
      ·
        refine ⟨2851319518523634102001679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7603518716063024272004477 2851319518523634102001679)
        ·
          refine ⟨4276979277785451153002519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2851319518523634102001679 4276979277785451153002519)
          ·
            refine ⟨6415468916678176729503779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4276979277785451153002519 6415468916678176729503779)
            ·
              refine ⟨9623203375017265094255669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6415468916678176729503779 9623203375017265094255669)
              ·
                refine ⟨902175316407868602586469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9623203375017265094255669 902175316407868602586469)
                ·
                  refine ⟨169157871826475362984963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 902175316407868602586469 169157871826475362984963)
                  ·
                    rfl

theorem cell22_1482452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_1482452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1482452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1482452 prefixEnd_1482452 := by exact prefixLift 1482452
  have htrace : WordTrace (prefixWord ++ tailWord_1482452) baseStart_1482452 baseEnd_1482452 := by
    simpa [prefixWord, tailWord_1482452, baseEnd_1482452] using wordTrace_append hprefix tailTrace_1482452
  have hstable : (prefixWord ++ tailWord_1482452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482452).length < 2 ^ (prefixWord ++ tailWord_1482452).sum := by decide
  have hdescent : baseEnd_1482452 < baseStart_1482452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482467 : List Nat := [1, 1, 1, 7, 2, 1, 1, 1, 4, 3]
def baseStart_1482467 : Nat := 118140960795 + 1482467 * 2 ^ 59
def prefixEnd_1482467 : Nat := 4983230072969 + 3 ^ 40 * 1482467 * 2
def baseEnd_1482467 : Nat := 507478750285971049829843

theorem tailTrace_1482467 : CollatzResearch.WordTrace tailWord_1482467 prefixEnd_1482467 507478750285971049829843 := by
  unfold tailWord_1482467
  simp only [CollatzResearch.WordTrace]
  refine ⟨54070013520282719051605655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36046675680188479367737103 54070013520282719051605655)
  ·
    refine ⟨81105020280424078577408483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54070013520282719051605655 81105020280424078577408483)
    ·
      refine ⟨121657530420636117866112725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81105020280424078577408483 121657530420636117866112725)
      ·
        refine ⟨2851348369233659012487017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 121657530420636117866112725 2851348369233659012487017)
        ·
          refine ⟨2138511276925244259365263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2851348369233659012487017 2138511276925244259365263)
          ·
            refine ⟨3207766915387866389047895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2138511276925244259365263 3207766915387866389047895)
            ·
              refine ⟨4811650373081799583571843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3207766915387866389047895 4811650373081799583571843)
              ·
                refine ⟨7217475559622699375357765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4811650373081799583571843 7217475559622699375357765)
                ·
                  refine ⟨1353276667429256132879581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7217475559622699375357765 1353276667429256132879581)
                  ·
                    refine ⟨507478750285971049829843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1353276667429256132879581 507478750285971049829843)
                    ·
                      rfl

theorem cell22_1482467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 4, 3].length) (baseStart_1482467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1482467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1482467 prefixEnd_1482467 := by exact prefixLift 1482467
  have htrace : WordTrace (prefixWord ++ tailWord_1482467) baseStart_1482467 baseEnd_1482467 := by
    simpa [prefixWord, tailWord_1482467, baseEnd_1482467] using wordTrace_append hprefix tailTrace_1482467
  have hstable : (prefixWord ++ tailWord_1482467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482467).length < 2 ^ (prefixWord ++ tailWord_1482467).sum := by decide
  have hdescent : baseEnd_1482467 < baseStart_1482467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482484 : List Nat := [2, 6, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_1482484 : Nat := 118140960795 + 1482484 * 2 ^ 59
def prefixEnd_1482484 : Nat := 4983230072969 + 3 ^ 40 * 1482484 * 2
def baseEnd_1482484 : Nat := 507484569733388672154791

theorem tailTrace_1482484 : CollatzResearch.WordTrace tailWord_1482484 prefixEnd_1482484 507484569733388672154791 := by
  unfold tailWord_1482484
  simp only [CollatzResearch.WordTrace]
  refine ⟨27035316780610565477487253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36047089040814087303316337 27035316780610565477487253)
  ·
    refine ⟨1267280474091120256757215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27035316780610565477487253 1267280474091120256757215)
    ·
      refine ⟨1900920711136680385135823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1267280474091120256757215 1900920711136680385135823)
      ·
        refine ⟨2851381066705020577703735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1900920711136680385135823 2851381066705020577703735)
        ·
          refine ⟨4277071600057530866555603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2851381066705020577703735 4277071600057530866555603)
          ·
            refine ⟨6415607400086296299833405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4277071600057530866555603 6415607400086296299833405)
            ·
              refine ⟨2405852775032361112437527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6415607400086296299833405 2405852775032361112437527)
              ·
                refine ⟨3608779162548541668656291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2405852775032361112437527 3608779162548541668656291)
                ·
                  refine ⟨5413168743822812502984437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3608779162548541668656291 5413168743822812502984437)
                  ·
                    refine ⟨507484569733388672154791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5413168743822812502984437 507484569733388672154791)
                    ·
                      rfl

theorem cell22_1482484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_1482484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1482484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1482484 prefixEnd_1482484 := by exact prefixLift 1482484
  have htrace : WordTrace (prefixWord ++ tailWord_1482484) baseStart_1482484 baseEnd_1482484 := by
    simpa [prefixWord, tailWord_1482484, baseEnd_1482484] using wordTrace_append hprefix tailTrace_1482484
  have hstable : (prefixWord ++ tailWord_1482484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482484).length < 2 ^ (prefixWord ++ tailWord_1482484).sum := by decide
  have hdescent : baseEnd_1482484 < baseStart_1482484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482495 : List Nat := [1, 1, 2, 2, 1, 3, 4, 2, 3, 3]
def baseStart_1482495 : Nat := 118140960795 + 1482495 * 2 ^ 59
def prefixEnd_1482495 : Nat := 4983230072969 + 3 ^ 40 * 1482495 * 2
def baseEnd_1482495 : Nat := 507488335258188310129757

theorem tailTrace_1482495 : CollatzResearch.WordTrace tailWord_1482495 prefixEnd_1482495 507488335258188310129757 := by
  unfold tailWord_1482495
  simp only [CollatzResearch.WordTrace]
  refine ⟨54071034764181279833624939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36047356509454186555749959 54071034764181279833624939)
  ·
    refine ⟨81106552146271919750437409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54071034764181279833624939 81106552146271919750437409)
    ·
      refine ⟨60829914109703939812828057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81106552146271919750437409 60829914109703939812828057)
      ·
        refine ⟨45622435582277954859621043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60829914109703939812828057 45622435582277954859621043)
        ·
          refine ⟨68433653373416932289431565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45622435582277954859621043 68433653373416932289431565)
          ·
            refine ⟨25662620015031349608536837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68433653373416932289431565 25662620015031349608536837)
            ·
              refine ⟨4811741252818378051600657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25662620015031349608536837 4811741252818378051600657)
              ·
                refine ⟨3608805939613783538700493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4811741252818378051600657 3608805939613783538700493)
                ·
                  refine ⟨1353302227355168827012685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3608805939613783538700493 1353302227355168827012685)
                  ·
                    refine ⟨507488335258188310129757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1353302227355168827012685 507488335258188310129757)
                    ·
                      rfl

theorem cell22_1482495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 3, 3].length) (baseStart_1482495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1482495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1482495 prefixEnd_1482495 := by exact prefixLift 1482495
  have htrace : WordTrace (prefixWord ++ tailWord_1482495) baseStart_1482495 baseEnd_1482495 := by
    simpa [prefixWord, tailWord_1482495, baseEnd_1482495] using wordTrace_append hprefix tailTrace_1482495
  have hstable : (prefixWord ++ tailWord_1482495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482495).length < 2 ^ (prefixWord ++ tailWord_1482495).sum := by decide
  have hdescent : baseEnd_1482495 < baseStart_1482495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482508 : List Nat := [2, 2, 1, 2, 2, 1, 3, 2, 7]
def baseStart_1482508 : Nat := 118140960795 + 1482508 * 2 ^ 59
def prefixEnd_1482508 : Nat := 4983230072969 + 3 ^ 40 * 1482508 * 2
def baseEnd_1482508 : Nat := 169164261807953536518239

theorem tailTrace_1482508 : CollatzResearch.WordTrace tailWord_1482508 prefixEnd_1482508 169164261807953536518239 := by
  unfold tailWord_1482508
  simp only [CollatzResearch.WordTrace]
  refine ⟨27035754456567091526924089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36047672608756122035898785 27035754456567091526924089)
  ·
    refine ⟨20276815842425318645193067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27035754456567091526924089 20276815842425318645193067)
    ·
      refine ⟨30415223763637977967789601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20276815842425318645193067 30415223763637977967789601)
      ·
        refine ⟨22811417822728483475842201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30415223763637977967789601 22811417822728483475842201)
        ·
          refine ⟨17108563367046362606881651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22811417822728483475842201 17108563367046362606881651)
          ·
            refine ⟨25662845050569543910322477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17108563367046362606881651 25662845050569543910322477)
            ·
              refine ⟨9623566893963578966370929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25662845050569543910322477 9623566893963578966370929)
              ·
                refine ⟨7217675170472684224778197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9623566893963578966370929 7217675170472684224778197)
                ·
                  refine ⟨169164261807953536518239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7217675170472684224778197 169164261807953536518239)
                  ·
                    rfl

theorem cell22_1482508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 7].length) (baseStart_1482508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1482508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1482508 prefixEnd_1482508 := by exact prefixLift 1482508
  have htrace : WordTrace (prefixWord ++ tailWord_1482508) baseStart_1482508 baseEnd_1482508 := by
    simpa [prefixWord, tailWord_1482508, baseEnd_1482508] using wordTrace_append hprefix tailTrace_1482508
  have hstable : (prefixWord ++ tailWord_1482508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482508).length < 2 ^ (prefixWord ++ tailWord_1482508).sum := by decide
  have hdescent : baseEnd_1482508 < baseStart_1482508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482516 : List Nat := [2, 4, 4, 1, 1, 1, 1, 2, 2, 4]
def baseStart_1482516 : Nat := 118140960795 + 1482516 * 2 ^ 59
def prefixEnd_1482516 : Nat := 4983230072969 + 3 ^ 40 * 1482516 * 2
def baseEnd_1482516 : Nat := 507495523987351255354693

theorem tailTrace_1482516 : CollatzResearch.WordTrace tailWord_1482516 prefixEnd_1482516 507495523987351255354693 := by
  unfold tailWord_1482516
  simp only [CollatzResearch.WordTrace]
  refine ⟨27035900348552600210069701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36047867131403466946759601 27035900348552600210069701)
  ·
    refine ⟨5069231315353612539388069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27035900348552600210069701 5069231315353612539388069)
    ·
      refine ⟨950480871628802351135263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5069231315353612539388069 950480871628802351135263)
      ·
        refine ⟨1425721307443203526702895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 950480871628802351135263 1425721307443203526702895)
        ·
          refine ⟨2138581961164805290054343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1425721307443203526702895 2138581961164805290054343)
          ·
            refine ⟨3207872941747207935081515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2138581961164805290054343 3207872941747207935081515)
            ·
              refine ⟨4811809412620811902622273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3207872941747207935081515 4811809412620811902622273)
              ·
                refine ⟨3608857059465608926966705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4811809412620811902622273 3608857059465608926966705)
                ·
                  refine ⟨2706642794599206695225029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3608857059465608926966705 2706642794599206695225029)
                  ·
                    refine ⟨507495523987351255354693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2706642794599206695225029 507495523987351255354693)
                    ·
                      rfl

theorem cell22_1482516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_1482516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1482516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1482516 prefixEnd_1482516 := by exact prefixLift 1482516
  have htrace : WordTrace (prefixWord ++ tailWord_1482516) baseStart_1482516 baseEnd_1482516 := by
    simpa [prefixWord, tailWord_1482516, baseEnd_1482516] using wordTrace_append hprefix tailTrace_1482516
  have hstable : (prefixWord ++ tailWord_1482516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482516).length < 2 ^ (prefixWord ++ tailWord_1482516).sum := by decide
  have hdescent : baseEnd_1482516 < baseStart_1482516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482600 : List Nat := [2, 1, 4, 2, 1, 1, 2, 2, 1, 6]
def baseStart_1482600 : Nat := 118140960795 + 1482600 * 2 ^ 59
def prefixEnd_1482600 : Nat := 4983230072969 + 3 ^ 40 * 1482600 * 2
def baseEnd_1482600 : Nat := 507524278904003036254435

theorem tailTrace_1482600 : CollatzResearch.WordTrace tailWord_1482600 prefixEnd_1482600 507524278904003036254435 := by
  unfold tailWord_1482600
  simp only [CollatzResearch.WordTrace]
  refine ⟨27037432214400441383098627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36049909619200588510798169 27037432214400441383098627)
  ·
    refine ⟨40556148321600662074647941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27037432214400441383098627 40556148321600662074647941)
    ·
      refine ⟨7604277810300124138996489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40556148321600662074647941 7604277810300124138996489)
      ·
        refine ⟨5703208357725093104247367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7604277810300124138996489 5703208357725093104247367)
        ·
          refine ⟨8554812536587639656371051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5703208357725093104247367 8554812536587639656371051)
          ·
            refine ⟨12832218804881459484556577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8554812536587639656371051 12832218804881459484556577)
            ·
              refine ⟨9624164103661094613417433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12832218804881459484556577 9624164103661094613417433)
              ·
                refine ⟨7218123077745820960063075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9624164103661094613417433 7218123077745820960063075)
                ·
                  refine ⟨10827184616618731440094613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7218123077745820960063075 10827184616618731440094613)
                  ·
                    refine ⟨507524278904003036254435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10827184616618731440094613 507524278904003036254435)
                    ·
                      rfl

theorem cell22_1482600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_1482600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1482600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1482600 prefixEnd_1482600 := by exact prefixLift 1482600
  have htrace : WordTrace (prefixWord ++ tailWord_1482600) baseStart_1482600 baseEnd_1482600 := by
    simpa [prefixWord, tailWord_1482600, baseEnd_1482600] using wordTrace_append hprefix tailTrace_1482600
  have hstable : (prefixWord ++ tailWord_1482600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482600).length < 2 ^ (prefixWord ++ tailWord_1482600).sum := by decide
  have hdescent : baseEnd_1482600 < baseStart_1482600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482647 : List Nat := [1, 1, 3, 3, 1, 3, 1, 3, 3, 3]
def baseStart_1482647 : Nat := 118140960795 + 1482647 * 2 ^ 59
def prefixEnd_1482647 : Nat := 4983230072969 + 3 ^ 40 * 1482647 * 2
def baseEnd_1482647 : Nat := 507540367964510580329291

theorem tailTrace_1482647 : CollatzResearch.WordTrace tailWord_1482647 prefixEnd_1482647 507540367964510580329291 := by
  unfold tailWord_1482647
  simp only [CollatzResearch.WordTrace]
  refine ⟨54076578659630609793158195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36051052439753739862105463 54076578659630609793158195)
  ·
    refine ⟨81114867989445914689737293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54076578659630609793158195 81114867989445914689737293)
    ·
      refine ⟨30418075496042218008651485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81114867989445914689737293 30418075496042218008651485)
      ·
        refine ⟨11406778311015831753244307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30418075496042218008651485 11406778311015831753244307)
        ·
          refine ⟨17110167466523747629866461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11406778311015831753244307 17110167466523747629866461)
          ·
            refine ⟨6416312799946405361199923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17110167466523747629866461 6416312799946405361199923)
            ·
              refine ⟨9624469199919608041799885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6416312799946405361199923 9624469199919608041799885)
              ·
                refine ⟨3609175949969853015674957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9624469199919608041799885 3609175949969853015674957)
                ·
                  refine ⟨1353440981238694880878109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3609175949969853015674957 1353440981238694880878109)
                  ·
                    refine ⟨507540367964510580329291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1353440981238694880878109 507540367964510580329291)
                    ·
                      rfl

theorem cell22_1482647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 3, 3].length) (baseStart_1482647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1482647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1482647 prefixEnd_1482647 := by exact prefixLift 1482647
  have htrace : WordTrace (prefixWord ++ tailWord_1482647) baseStart_1482647 baseEnd_1482647 := by
    simpa [prefixWord, tailWord_1482647, baseEnd_1482647] using wordTrace_append hprefix tailTrace_1482647
  have hstable : (prefixWord ++ tailWord_1482647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482647).length < 2 ^ (prefixWord ++ tailWord_1482647).sum := by decide
  have hdescent : baseEnd_1482647 < baseStart_1482647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482705 : List Nat := [1, 2, 2, 1, 2, 1, 2, 5, 6]
def baseStart_1482705 : Nat := 118140960795 + 1482705 * 2 ^ 59
def prefixEnd_1482705 : Nat := 4983230072969 + 3 ^ 40 * 1482705 * 2
def baseEnd_1482705 : Nat := 169186740849939254126371

theorem tailTrace_1482705 : CollatzResearch.WordTrace tailWord_1482705 prefixEnd_1482705 169186740849939254126371 := by
  unfold tailWord_1482705
  simp only [CollatzResearch.WordTrace]
  refine ⟨54078694093420485698769569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36052462728946990465846379 54078694093420485698769569)
  ·
    refine ⟨40559020570065364274077177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54078694093420485698769569 40559020570065364274077177)
    ·
      refine ⟨30419265427549023205557883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40559020570065364274077177 30419265427549023205557883)
      ·
        refine ⟨45628898141323534808336825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30419265427549023205557883 45628898141323534808336825)
        ·
          refine ⟨34221673605992651106252619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45628898141323534808336825 34221673605992651106252619)
          ·
            refine ⟨51332510408988976659378929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34221673605992651106252619 51332510408988976659378929)
            ·
              refine ⟨38499382806741732494534197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51332510408988976659378929 38499382806741732494534197)
              ·
                refine ⟨3609317138132037421362581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38499382806741732494534197 3609317138132037421362581)
                ·
                  refine ⟨169186740849939254126371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3609317138132037421362581 169186740849939254126371)
                  ·
                    rfl

theorem cell22_1482705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 6].length) (baseStart_1482705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1482705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1482705 prefixEnd_1482705 := by exact prefixLift 1482705
  have htrace : WordTrace (prefixWord ++ tailWord_1482705) baseStart_1482705 baseEnd_1482705 := by
    simpa [prefixWord, tailWord_1482705, baseEnd_1482705] using wordTrace_append hprefix tailTrace_1482705
  have hstable : (prefixWord ++ tailWord_1482705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482705).length < 2 ^ (prefixWord ++ tailWord_1482705).sum := by decide
  have hdescent : baseEnd_1482705 < baseStart_1482705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482720 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 5, 5]
def baseStart_1482720 : Nat := 118140960795 + 1482720 * 2 ^ 59
def prefixEnd_1482720 : Nat := 4983230072969 + 3 ^ 40 * 1482720 * 2
def baseEnd_1482720 : Nat := 507565357356362723254067

theorem tailTrace_1482720 : CollatzResearch.WordTrace tailWord_1482720 prefixEnd_1482720 507565357356362723254067 := by
  unfold tailWord_1482720
  simp only [CollatzResearch.WordTrace]
  refine ⟨27039620594183071630282807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36052827458910762173710409 27039620594183071630282807)
  ·
    refine ⟨40559430891274607445424211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27039620594183071630282807 40559430891274607445424211)
    ·
      refine ⟨60839146336911911168136317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40559430891274607445424211 60839146336911911168136317)
      ·
        refine ⟨22814679876341966688051119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60839146336911911168136317 22814679876341966688051119)
        ·
          refine ⟨34222019814512950032076679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22814679876341966688051119 34222019814512950032076679)
          ·
            refine ⟨51333029721769425048115019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34222019814512950032076679 51333029721769425048115019)
            ·
              refine ⟨76999544582654137572172529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51333029721769425048115019 76999544582654137572172529)
              ·
                refine ⟨57749658436990603179129397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76999544582654137572172529 57749658436990603179129397)
                ·
                  refine ⟨5414030478467869048043381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57749658436990603179129397 5414030478467869048043381)
                  ·
                    refine ⟨507565357356362723254067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5414030478467869048043381 507565357356362723254067)
                    ·
                      rfl

theorem cell22_1482720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 5, 5].length) (baseStart_1482720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1482720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1482720 prefixEnd_1482720 := by exact prefixLift 1482720
  have htrace : WordTrace (prefixWord ++ tailWord_1482720) baseStart_1482720 baseEnd_1482720 := by
    simpa [prefixWord, tailWord_1482720, baseEnd_1482720] using wordTrace_append hprefix tailTrace_1482720
  have hstable : (prefixWord ++ tailWord_1482720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482720).length < 2 ^ (prefixWord ++ tailWord_1482720).sum := by decide
  have hdescent : baseEnd_1482720 < baseStart_1482720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482812 : List Nat := [2, 2, 2, 2, 2, 1, 3, 1, 7]
def baseStart_1482812 : Nat := 118140960795 + 1482812 * 2 ^ 59
def prefixEnd_1482812 : Nat := 4983230072969 + 3 ^ 40 * 1482812 * 2
def baseEnd_1482812 : Nat := 169198950278835049984595

theorem tailTrace_1482812 : CollatzResearch.WordTrace tailWord_1482812 prefixEnd_1482812 169198950278835049984595 := by
  unfold tailWord_1482812
  simp only [CollatzResearch.WordTrace]
  refine ⟨27041298352016421486457345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36055064469355228648609793 27041298352016421486457345)
  ·
    refine ⟨20280973764012316114843009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27041298352016421486457345 20280973764012316114843009)
    ·
      refine ⟨15210730323009237086132257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20280973764012316114843009 15210730323009237086132257)
      ·
        refine ⟨11408047742256927814599193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15210730323009237086132257 11408047742256927814599193)
        ·
          refine ⟨8556035806692695860949395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11408047742256927814599193 8556035806692695860949395)
          ·
            refine ⟨12834053710039043791424093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8556035806692695860949395 12834053710039043791424093)
            ·
              refine ⟨4812770141264641421784035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12834053710039043791424093 4812770141264641421784035)
              ·
                refine ⟨7219155211896962132676053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4812770141264641421784035 7219155211896962132676053)
                ·
                  refine ⟨169198950278835049984595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7219155211896962132676053 169198950278835049984595)
                  ·
                    rfl

theorem cell22_1482812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 7].length) (baseStart_1482812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1482812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1482812 prefixEnd_1482812 := by exact prefixLift 1482812
  have htrace : WordTrace (prefixWord ++ tailWord_1482812) baseStart_1482812 baseEnd_1482812 := by
    simpa [prefixWord, tailWord_1482812, baseEnd_1482812] using wordTrace_append hprefix tailTrace_1482812
  have hstable : (prefixWord ++ tailWord_1482812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482812).length < 2 ^ (prefixWord ++ tailWord_1482812).sum := by decide
  have hdescent : baseEnd_1482812 < baseStart_1482812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482816 : List Nat := [2, 1, 1, 2, 2, 4, 2, 4, 1, 3]
def baseStart_1482816 : Nat := 118140960795 + 1482816 * 2 ^ 59
def prefixEnd_1482816 : Nat := 4983230072969 + 3 ^ 40 * 1482816 * 2
def baseEnd_1482816 : Nat := 507598220118250472853773

theorem tailTrace_1482816 : CollatzResearch.WordTrace tailWord_1482816 prefixEnd_1482816 507598220118250472853773 := by
  unfold tailWord_1482816
  simp only [CollatzResearch.WordTrace]
  refine ⟨27041371298009175828030151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36055161730678901104040201 27041371298009175828030151)
  ·
    refine ⟨40562056947013763742045227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27041371298009175828030151 40562056947013763742045227)
    ·
      refine ⟨60843085420520645613067841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40562056947013763742045227 60843085420520645613067841)
      ·
        refine ⟨45632314065390484209800881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60843085420520645613067841 45632314065390484209800881)
        ·
          refine ⟨34224235549042863157350661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45632314065390484209800881 34224235549042863157350661)
          ·
            refine ⟨6417044165445536842003249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34224235549042863157350661 6417044165445536842003249)
            ·
              refine ⟨4812783124084152631502437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6417044165445536842003249 4812783124084152631502437)
              ·
                refine ⟨902396835765778618406707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4812783124084152631502437 902396835765778618406707)
                ·
                  refine ⟨1353595253648667927610061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 902396835765778618406707 1353595253648667927610061)
                  ·
                    refine ⟨507598220118250472853773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1353595253648667927610061 507598220118250472853773)
                    ·
                      rfl

theorem cell22_1482816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 4, 1, 3].length) (baseStart_1482816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1482816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1482816 prefixEnd_1482816 := by exact prefixLift 1482816
  have htrace : WordTrace (prefixWord ++ tailWord_1482816) baseStart_1482816 baseEnd_1482816 := by
    simpa [prefixWord, tailWord_1482816, baseEnd_1482816] using wordTrace_append hprefix tailTrace_1482816
  have hstable : (prefixWord ++ tailWord_1482816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482816).length < 2 ^ (prefixWord ++ tailWord_1482816).sum := by decide
  have hdescent : baseEnd_1482816 < baseStart_1482816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482887 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 3, 6]
def baseStart_1482887 : Nat := 118140960795 + 1482887 * 2 ^ 59
def prefixEnd_1482887 : Nat := 4983230072969 + 3 ^ 40 * 1482887 * 2
def baseEnd_1482887 : Nat := 507622524869229954328555

theorem tailTrace_1482887 : CollatzResearch.WordTrace tailWord_1482887 prefixEnd_1482887 507622524869229954328555 := by
  unfold tailWord_1482887
  simp only [CollatzResearch.WordTrace]
  refine ⟨54085332178761130781894915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36056888119174087187929943 54085332178761130781894915)
  ·
    refine ⟨81127998268141696172842373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54085332178761130781894915 81127998268141696172842373)
    ·
      refine ⟨15211499675276568032407945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81127998268141696172842373 15211499675276568032407945)
      ·
        refine ⟨11408624756457426024305959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15211499675276568032407945 11408624756457426024305959)
        ·
          refine ⟨17112937134686139036458939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11408624756457426024305959 17112937134686139036458939)
          ·
            refine ⟨25669405702029208554688409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17112937134686139036458939 25669405702029208554688409)
            ·
              refine ⟨19252054276521906416016307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25669405702029208554688409 19252054276521906416016307)
              ·
                refine ⟨28878081414782859624024461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19252054276521906416016307 28878081414782859624024461)
                ·
                  refine ⟨10829280530543572359009173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28878081414782859624024461 10829280530543572359009173)
                  ·
                    refine ⟨507622524869229954328555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10829280530543572359009173 507622524869229954328555)
                    ·
                      rfl

theorem cell22_1482887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_1482887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1482887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1482887 prefixEnd_1482887 := by exact prefixLift 1482887
  have htrace : WordTrace (prefixWord ++ tailWord_1482887) baseStart_1482887 baseEnd_1482887 := by
    simpa [prefixWord, tailWord_1482887, baseEnd_1482887] using wordTrace_append hprefix tailTrace_1482887
  have hstable : (prefixWord ++ tailWord_1482887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482887).length < 2 ^ (prefixWord ++ tailWord_1482887).sum := by decide
  have hdescent : baseEnd_1482887 < baseStart_1482887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482906 : List Nat := [3, 1, 1, 5, 2, 1, 1, 2, 1, 5]
def baseStart_1482906 : Nat := 118140960795 + 1482906 * 2 ^ 59
def prefixEnd_1482906 : Nat := 4983230072969 + 3 ^ 40 * 1482906 * 2
def baseEnd_1482906 : Nat := 507629028957520238103497

theorem tailTrace_1482906 : CollatzResearch.WordTrace tailWord_1482906 prefixEnd_1482906 507629028957520238103497 := by
  unfold tailWord_1482906
  simp only [CollatzResearch.WordTrace]
  refine ⟨13521506291423074256709143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36057350110461531351224381 13521506291423074256709143)
  ·
    refine ⟨20282259437134611385063715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13521506291423074256709143 20282259437134611385063715)
    ·
      refine ⟨30423389155701917077595573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20282259437134611385063715 30423389155701917077595573)
      ·
        refine ⟨2852192733347054726024585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30423389155701917077595573 2852192733347054726024585)
        ·
          refine ⟨2139144550010291044518439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2852192733347054726024585 2139144550010291044518439)
          ·
            refine ⟨3208716825015436566777659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2139144550010291044518439 3208716825015436566777659)
            ·
              refine ⟨4813075237523154850166489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3208716825015436566777659 4813075237523154850166489)
              ·
                refine ⟨3609806428142366137624867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4813075237523154850166489 3609806428142366137624867)
                ·
                  refine ⟨5414709642213549206437301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3609806428142366137624867 5414709642213549206437301)
                  ·
                    refine ⟨507629028957520238103497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5414709642213549206437301 507629028957520238103497)
                    ·
                      rfl

theorem cell22_1482906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 1, 5].length) (baseStart_1482906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1482906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1482906 prefixEnd_1482906 := by exact prefixLift 1482906
  have htrace : WordTrace (prefixWord ++ tailWord_1482906) baseStart_1482906 baseEnd_1482906 := by
    simpa [prefixWord, tailWord_1482906, baseEnd_1482906] using wordTrace_append hprefix tailTrace_1482906
  have hstable : (prefixWord ++ tailWord_1482906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482906).length < 2 ^ (prefixWord ++ tailWord_1482906).sum := by decide
  have hdescent : baseEnd_1482906 < baseStart_1482906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482910 : List Nat := [4, 3, 1, 1, 3, 1, 3, 1, 1, 4]
def baseStart_1482910 : Nat := 118140960795 + 1482910 * 2 ^ 59
def prefixEnd_1482910 : Nat := 4983230072969 + 3 ^ 40 * 1482910 * 2
def baseEnd_1482910 : Nat := 507630398239265561003485

theorem tailTrace_1482910 : CollatzResearch.WordTrace tailWord_1482910 prefixEnd_1482910 507630398239265561003485 := by
  unfold tailWord_1482910
  simp only [CollatzResearch.WordTrace]
  refine ⟨6760771382209725713747773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36057447371785203806654789 6760771382209725713747773)
  ·
    refine ⟨2535289268328647142655415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6760771382209725713747773 2535289268328647142655415)
    ·
      refine ⟨3802933902492970713983123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2535289268328647142655415 3802933902492970713983123)
      ·
        refine ⟨5704400853739456070974685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3802933902492970713983123 5704400853739456070974685)
        ·
          refine ⟨2139150320152296026615507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5704400853739456070974685 2139150320152296026615507)
          ·
            refine ⟨3208725480228444039923261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2139150320152296026615507 3208725480228444039923261)
            ·
              refine ⟨1203272055085666514971223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3208725480228444039923261 1203272055085666514971223)
              ·
                refine ⟨1804908082628499772456835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1203272055085666514971223 1804908082628499772456835)
                ·
                  refine ⟨2707362123942749658685253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1804908082628499772456835 2707362123942749658685253)
                  ·
                    refine ⟨507630398239265561003485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2707362123942749658685253 507630398239265561003485)
                    ·
                      rfl

theorem cell22_1482910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_1482910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1482910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1482910 prefixEnd_1482910 := by exact prefixLift 1482910
  have htrace : WordTrace (prefixWord ++ tailWord_1482910) baseStart_1482910 baseEnd_1482910 := by
    simpa [prefixWord, tailWord_1482910, baseEnd_1482910] using wordTrace_append hprefix tailTrace_1482910
  have hstable : (prefixWord ++ tailWord_1482910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482910).length < 2 ^ (prefixWord ++ tailWord_1482910).sum := by decide
  have hdescent : baseEnd_1482910 < baseStart_1482910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482919 : List Nat := [1, 1, 6, 2, 2, 10]
def baseStart_1482919 : Nat := 118140960795 + 1482919 * 2 ^ 59
def prefixEnd_1482919 : Nat := 4983230072969 + 3 ^ 40 * 1482919 * 2
def baseEnd_1482919 : Nat := 6267079989175216512697

theorem tailTrace_1482919 : CollatzResearch.WordTrace tailWord_1482919 prefixEnd_1482919 6267079989175216512697 := by
  unfold tailWord_1482919
  simp only [CollatzResearch.WordTrace]
  refine ⟨54086499314645200247059811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36057666209763466831373207 54086499314645200247059811)
  ·
    refine ⟨81129748971967800370589717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54086499314645200247059811 81129748971967800370589717)
    ·
      refine ⟨3802956983060990642371393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 81129748971967800370589717 3802956983060990642371393)
      ·
        refine ⟨2852217737295742981778545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3802956983060990642371393 2852217737295742981778545)
        ·
          refine ⟨2139163302971807236333909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2852217737295742981778545 2139163302971807236333909)
          ·
            refine ⟨6267079989175216512697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2139163302971807236333909 6267079989175216512697)
            ·
              rfl

theorem cell22_1482919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 10].length) (baseStart_1482919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1482919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1482919 prefixEnd_1482919 := by exact prefixLift 1482919
  have htrace : WordTrace (prefixWord ++ tailWord_1482919) baseStart_1482919 baseEnd_1482919 := by
    simpa [prefixWord, tailWord_1482919, baseEnd_1482919] using wordTrace_append hprefix tailTrace_1482919
  have hstable : (prefixWord ++ tailWord_1482919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482919).length < 2 ^ (prefixWord ++ tailWord_1482919).sum := by decide
  have hdescent : baseEnd_1482919 < baseStart_1482919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482925 : List Nat := [1, 5, 2, 1, 2, 3, 2, 2, 4]
def baseStart_1482925 : Nat := 118140960795 + 1482925 * 2 ^ 59
def prefixEnd_1482925 : Nat := 4983230072969 + 3 ^ 40 * 1482925 * 2
def baseEnd_1482925 : Nat := 169211844348603507292813

theorem tailTrace_1482925 : CollatzResearch.WordTrace tailWord_1482925 prefixEnd_1482925 169211844348603507292813 := by
  unfold tailWord_1482925
  simp only [CollatzResearch.WordTrace]
  refine ⟨54086718152623463271778229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36057812101748975514518819 54086718152623463271778229)
  ·
    refine ⟨5070629826808449681729209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54086718152623463271778229 5070629826808449681729209)
    ·
      refine ⟨3802972370106337261296907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5070629826808449681729209 3802972370106337261296907)
      ·
        refine ⟨5704458555159505891945361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3802972370106337261296907 5704458555159505891945361)
        ·
          refine ⟨4278343916369629418959021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5704458555159505891945361 4278343916369629418959021)
          ·
            refine ⟨1604378968638611032109633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4278343916369629418959021 1604378968638611032109633)
            ·
              refine ⟨1203284226478958274082225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1604378968638611032109633 1203284226478958274082225)
              ·
                refine ⟨902463169859218705561669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1203284226478958274082225 902463169859218705561669)
                ·
                  refine ⟨169211844348603507292813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 902463169859218705561669 169211844348603507292813)
                  ·
                    rfl

theorem cell22_1482925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_1482925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1482925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1482925 prefixEnd_1482925 := by exact prefixLift 1482925
  have htrace : WordTrace (prefixWord ++ tailWord_1482925) baseStart_1482925 baseEnd_1482925 := by
    simpa [prefixWord, tailWord_1482925, baseEnd_1482925] using wordTrace_append hprefix tailTrace_1482925
  have hstable : (prefixWord ++ tailWord_1482925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482925).length < 2 ^ (prefixWord ++ tailWord_1482925).sum := by decide
  have hdescent : baseEnd_1482925 < baseStart_1482925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482968 : List Nat := [2, 1, 2, 2, 4, 1, 1, 5, 1, 3]
def baseStart_1482968 : Nat := 118140960795 + 1482968 * 2 ^ 59
def prefixEnd_1482968 : Nat := 4983230072969 + 3 ^ 40 * 1482968 * 2
def baseEnd_1482968 : Nat := 507650252824572743053307

theorem tailTrace_1482968 : CollatzResearch.WordTrace tailWord_1482968 prefixEnd_1482968 507650252824572743053307 := by
  unfold tailWord_1482968
  simp only [CollatzResearch.WordTrace]
  refine ⟨27044143245733840807796779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36058857660978454410395705 27044143245733840807796779)
  ·
    refine ⟨40566214868600761211695169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27044143245733840807796779 40566214868600761211695169)
    ·
      refine ⟨30424661151450570908771377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40566214868600761211695169 30424661151450570908771377)
      ·
        refine ⟨22818495863587928181578533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30424661151450570908771377 22818495863587928181578533)
        ·
          refine ⟨4278467974422736534045975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22818495863587928181578533 4278467974422736534045975)
          ·
            refine ⟨6417701961634104801068963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4278467974422736534045975 6417701961634104801068963)
            ·
              refine ⟨9626552942451157201603445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6417701961634104801068963 9626552942451157201603445)
              ·
                refine ⟨902489338354795987650323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9626552942451157201603445 902489338354795987650323)
                ·
                  refine ⟨1353734007532193981475485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 902489338354795987650323 1353734007532193981475485)
                  ·
                    refine ⟨507650252824572743053307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1353734007532193981475485 507650252824572743053307)
                    ·
                      rfl

theorem cell22_1482968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 5, 1, 3].length) (baseStart_1482968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1482968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1482968 prefixEnd_1482968 := by exact prefixLift 1482968
  have htrace : WordTrace (prefixWord ++ tailWord_1482968) baseStart_1482968 baseEnd_1482968 := by
    simpa [prefixWord, tailWord_1482968, baseEnd_1482968] using wordTrace_append hprefix tailTrace_1482968
  have hstable : (prefixWord ++ tailWord_1482968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482968).length < 2 ^ (prefixWord ++ tailWord_1482968).sum := by decide
  have hdescent : baseEnd_1482968 < baseStart_1482968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1482981 : List Nat := [1, 3, 1, 4, 2, 1, 3, 2, 5]
def baseStart_1482981 : Nat := 118140960795 + 1482981 * 2 ^ 59
def prefixEnd_1482981 : Nat := 4983230072969 + 3 ^ 40 * 1482981 * 2
def baseEnd_1482981 : Nat := 169218234330081680826089

theorem tailTrace_1482981 : CollatzResearch.WordTrace tailWord_1482981 prefixEnd_1482981 169218234330081680826089 := by
  unfold tailWord_1482981
  simp only [CollatzResearch.WordTrace]
  refine ⟨54088760640420584835816797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36059173760280389890544531 54088760640420584835816797)
  ·
    refine ⟨20283285240157719313431299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54088760640420584835816797 20283285240157719313431299)
    ·
      refine ⟨30424927860236578970146949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20283285240157719313431299 30424927860236578970146949)
      ·
        refine ⟨5704673973794358556902553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30424927860236578970146949 5704673973794358556902553)
        ·
          refine ⟨4278505480345768917676915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5704673973794358556902553 4278505480345768917676915)
          ·
            refine ⟨6417758220518653376515373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4278505480345768917676915 6417758220518653376515373)
            ·
              refine ⟨2406659332694495016193265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6417758220518653376515373 2406659332694495016193265)
              ·
                refine ⟨1804994499520871262144949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2406659332694495016193265 1804994499520871262144949)
                ·
                  refine ⟨169218234330081680826089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1804994499520871262144949 169218234330081680826089)
                  ·
                    rfl

theorem cell22_1482981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 5].length) (baseStart_1482981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1482981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1482981 prefixEnd_1482981 := by exact prefixLift 1482981
  have htrace : WordTrace (prefixWord ++ tailWord_1482981) baseStart_1482981 baseEnd_1482981 := by
    simpa [prefixWord, tailWord_1482981, baseEnd_1482981] using wordTrace_append hprefix tailTrace_1482981
  have hstable : (prefixWord ++ tailWord_1482981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1482981).length < 2 ^ (prefixWord ++ tailWord_1482981).sum := by decide
  have hdescent : baseEnd_1482981 < baseStart_1482981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1482981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483009 : List Nat := [1, 2, 4, 1, 1, 2, 1, 4, 6]
def baseStart_1483009 : Nat := 118140960795 + 1483009 * 2 ^ 59
def prefixEnd_1483009 : Nat := 4983230072969 + 3 ^ 40 * 1483009 * 2
def baseEnd_1483009 : Nat := 169221429320820767592727

theorem tailTrace_1483009 : CollatzResearch.WordTrace tailWord_1483009 prefixEnd_1483009 169221429320820767592727 := by
  unfold tailWord_1483009
  simp only [CollatzResearch.WordTrace]
  refine ⟨54089781884319145617836081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36059854589546097078557387 54089781884319145617836081)
  ·
    refine ⟨40567336413239359213377061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54089781884319145617836081 40567336413239359213377061)
    ·
      refine ⟨7606375577482379852508199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40567336413239359213377061 7606375577482379852508199)
      ·
        refine ⟨11409563366223569778762299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7606375577482379852508199 11409563366223569778762299)
        ·
          refine ⟨17114345049335354668143449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11409563366223569778762299 17114345049335354668143449)
          ·
            refine ⟨12835758787001516001107587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17114345049335354668143449 12835758787001516001107587)
            ·
              refine ⟨19253638180502274001661381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12835758787001516001107587 19253638180502274001661381)
              ·
                refine ⟨3610057158844176375311509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19253638180502274001661381 3610057158844176375311509)
                ·
                  refine ⟨169221429320820767592727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3610057158844176375311509 169221429320820767592727)
                  ·
                    rfl

theorem cell22_1483009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 6].length) (baseStart_1483009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483009 prefixEnd_1483009 := by exact prefixLift 1483009
  have htrace : WordTrace (prefixWord ++ tailWord_1483009) baseStart_1483009 baseEnd_1483009 := by
    simpa [prefixWord, tailWord_1483009, baseEnd_1483009] using wordTrace_append hprefix tailTrace_1483009
  have hstable : (prefixWord ++ tailWord_1483009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483009).length < 2 ^ (prefixWord ++ tailWord_1483009).sum := by decide
  have hdescent : baseEnd_1483009 < baseStart_1483009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483011 : List Nat := [1, 1, 1, 3, 2, 3, 4, 2, 1, 4]
def baseStart_1483011 : Nat := 118140960795 + 1483011 * 2 ^ 59
def prefixEnd_1483011 : Nat := 4983230072969 + 3 ^ 40 * 1483011 * 2
def baseEnd_1483011 : Nat := 507664972603334964228175

theorem tailTrace_1483011 : CollatzResearch.WordTrace tailWord_1483011 prefixEnd_1483011 507664972603334964228175 := by
  unfold tailWord_1483011
  simp only [CollatzResearch.WordTrace]
  refine ⟨54089854830311899959408887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36059903220207933306272591 54089854830311899959408887)
  ·
    refine ⟨81134782245467849939113331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54089854830311899959408887 81134782245467849939113331)
    ·
      refine ⟨121702173368201774908669997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81134782245467849939113331 121702173368201774908669997)
      ·
        refine ⟨45638315013075665590751249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121702173368201774908669997 45638315013075665590751249)
        ·
          refine ⟨34228736259806749193063437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45638315013075665590751249 34228736259806749193063437)
          ·
            refine ⟨12835776097427530947398789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34228736259806749193063437 12835776097427530947398789)
            ·
              refine ⟨2406708018267662052637273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12835776097427530947398789 2406708018267662052637273)
              ·
                refine ⟨1805031013700746539477955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2406708018267662052637273 1805031013700746539477955)
                ·
                  refine ⟨2707546520551119809216933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1805031013700746539477955 2707546520551119809216933)
                  ·
                    refine ⟨507664972603334964228175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2707546520551119809216933 507664972603334964228175)
                    ·
                      rfl

theorem cell22_1483011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 4].length) (baseStart_1483011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483011 prefixEnd_1483011 := by exact prefixLift 1483011
  have htrace : WordTrace (prefixWord ++ tailWord_1483011) baseStart_1483011 baseEnd_1483011 := by
    simpa [prefixWord, tailWord_1483011, baseEnd_1483011] using wordTrace_append hprefix tailTrace_1483011
  have hstable : (prefixWord ++ tailWord_1483011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483011).length < 2 ^ (prefixWord ++ tailWord_1483011).sum := by decide
  have hdescent : baseEnd_1483011 < baseStart_1483011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483041 : List Nat := [1, 2, 3, 2, 1, 1, 4, 1, 4, 3]
def baseStart_1483041 : Nat := 118140960795 + 1483041 * 2 ^ 59
def prefixEnd_1483041 : Nat := 4983230072969 + 3 ^ 40 * 1483041 * 2
def baseEnd_1483041 : Nat := 507675242216424885978083

theorem tailTrace_1483041 : CollatzResearch.WordTrace tailWord_1483041 prefixEnd_1483041 507675242216424885978083 := by
  unfold tailWord_1483041
  simp only [CollatzResearch.WordTrace]
  refine ⟨54090949020203215083000977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36060632680135476722000651 54090949020203215083000977)
  ·
    refine ⟨40568211765152411312250733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54090949020203215083000977 40568211765152411312250733)
    ·
      refine ⟨15213079411932154242094025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40568211765152411312250733 15213079411932154242094025)
      ·
        refine ⟨11409809558949115681570519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15213079411932154242094025 11409809558949115681570519)
        ·
          refine ⟨17114714338423673522355779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11409809558949115681570519 17114714338423673522355779)
          ·
            refine ⟨25672071507635510283533669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17114714338423673522355779 25672071507635510283533669)
            ·
              refine ⟨4813513407681658178162563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25672071507635510283533669 4813513407681658178162563)
              ·
                refine ⟨7220270111522487267243845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4813513407681658178162563 7220270111522487267243845)
                ·
                  refine ⟨1353800645910466362608221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7220270111522487267243845 1353800645910466362608221)
                  ·
                    refine ⟨507675242216424885978083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1353800645910466362608221 507675242216424885978083)
                    ·
                      rfl

theorem cell22_1483041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_1483041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483041 prefixEnd_1483041 := by exact prefixLift 1483041
  have htrace : WordTrace (prefixWord ++ tailWord_1483041) baseStart_1483041 baseEnd_1483041 := by
    simpa [prefixWord, tailWord_1483041, baseEnd_1483041] using wordTrace_append hprefix tailTrace_1483041
  have hstable : (prefixWord ++ tailWord_1483041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483041).length < 2 ^ (prefixWord ++ tailWord_1483041).sum := by decide
  have hdescent : baseEnd_1483041 < baseStart_1483041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483043 : List Nat := [1, 1, 1, 4, 2, 2, 5, 2, 4]
def baseStart_1483043 : Nat := 118140960795 + 1483043 * 2 ^ 59
def prefixEnd_1483043 : Nat := 4983230072969 + 3 ^ 40 * 1483043 * 2
def baseEnd_1483043 : Nat := 169225308952432515809359

theorem tailTrace_1483043 : CollatzResearch.WordTrace tailWord_1483043 prefixEnd_1483043 169225308952432515809359 := by
  unfold tailWord_1483043
  simp only [CollatzResearch.WordTrace]
  refine ⟨54091021966195969424573783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36060681310797312949715855 54091021966195969424573783)
  ·
    refine ⟨81136532949293954136860675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54091021966195969424573783 81136532949293954136860675)
    ·
      refine ⟨121704799423940931205291013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81136532949293954136860675 121704799423940931205291013)
      ·
        refine ⟨22819649891988924600992065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121704799423940931205291013 22819649891988924600992065)
        ·
          refine ⟨17114737418991693450744049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22819649891988924600992065 17114737418991693450744049)
          ·
            refine ⟨12836053064243770088058037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17114737418991693450744049 12836053064243770088058037)
            ·
              refine ⟨1203379974772853445755441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12836053064243770088058037 1203379974772853445755441)
              ·
                refine ⟨902534981079640084316581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1203379974772853445755441 902534981079640084316581)
                ·
                  refine ⟨169225308952432515809359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 902534981079640084316581 169225308952432515809359)
                  ·
                    rfl

theorem cell22_1483043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 2, 4].length) (baseStart_1483043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483043 prefixEnd_1483043 := by exact prefixLift 1483043
  have htrace : WordTrace (prefixWord ++ tailWord_1483043) baseStart_1483043 baseEnd_1483043 := by
    simpa [prefixWord, tailWord_1483043, baseEnd_1483043] using wordTrace_append hprefix tailTrace_1483043
  have hstable : (prefixWord ++ tailWord_1483043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483043).length < 2 ^ (prefixWord ++ tailWord_1483043).sum := by decide
  have hdescent : baseEnd_1483043 < baseStart_1483043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483086 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 7, 3]
def baseStart_1483086 : Nat := 118140960795 + 1483086 * 2 ^ 59
def prefixEnd_1483086 : Nat := 4983230072969 + 3 ^ 40 * 1483086 * 2
def baseEnd_1483086 : Nat := 507690646636059768602945

theorem tailTrace_1483086 : CollatzResearch.WordTrace tailWord_1483086 prefixEnd_1483086 507690646636059768602945 := by
  unfold tailWord_1483086
  simp only [CollatzResearch.WordTrace]
  refine ⟨6761573788130023471048639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36061726870026791845592741 6761573788130023471048639)
  ·
    refine ⟨10142360682195035206572959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6761573788130023471048639 10142360682195035206572959)
    ·
      refine ⟨15213541023292552809859439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10142360682195035206572959 15213541023292552809859439)
      ·
        refine ⟨22820311534938829214789159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15213541023292552809859439 22820311534938829214789159)
        ·
          refine ⟨34230467302408243822183739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22820311534938829214789159 34230467302408243822183739)
          ·
            refine ⟨51345700953612365733275609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34230467302408243822183739 51345700953612365733275609)
            ·
              refine ⟨38509275715209274299956707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51345700953612365733275609 38509275715209274299956707)
              ·
                refine ⟨57763913572813911449935061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38509275715209274299956707 57763913572813911449935061)
                ·
                  refine ⟨1353841724362826049607853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 57763913572813911449935061 1353841724362826049607853)
                  ·
                    refine ⟨507690646636059768602945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1353841724362826049607853 507690646636059768602945)
                    ·
                      rfl

theorem cell22_1483086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_1483086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483086 prefixEnd_1483086 := by exact prefixLift 1483086
  have htrace : WordTrace (prefixWord ++ tailWord_1483086) baseStart_1483086 baseEnd_1483086 := by
    simpa [prefixWord, tailWord_1483086, baseEnd_1483086] using wordTrace_append hprefix tailTrace_1483086
  have hstable : (prefixWord ++ tailWord_1483086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483086).length < 2 ^ (prefixWord ++ tailWord_1483086).sum := by decide
  have hdescent : baseEnd_1483086 < baseStart_1483086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483137 : List Nat := [1, 2, 4, 3, 1, 2, 2, 3, 1, 3]
def baseStart_1483137 : Nat := 118140960795 + 1483137 * 2 ^ 59
def prefixEnd_1483137 : Nat := 4983230072969 + 3 ^ 40 * 1483137 * 2
def baseEnd_1483137 : Nat := 507708104978312635577789

theorem tailTrace_1483137 : CollatzResearch.WordTrace tailWord_1483137 prefixEnd_1483137 507708104978312635577789 := by
  unfold tailWord_1483137
  simp only [CollatzResearch.WordTrace]
  refine ⟨54094450427855423478495665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36062966951903615652330443 54094450427855423478495665)
  ·
    refine ⟨40570837820891567608871749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54094450427855423478495665 40570837820891567608871749)
    ·
      refine ⟨7607032091417168926663453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40570837820891567608871749 7607032091417168926663453)
      ·
        refine ⟨2852637034281438347498795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7607032091417168926663453 2852637034281438347498795)
        ·
          refine ⟨4278955551422157521248193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2852637034281438347498795 4278955551422157521248193)
          ·
            refine ⟨3209216663566618140936145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4278955551422157521248193 3209216663566618140936145)
            ·
              refine ⟨2406912497674963605702109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3209216663566618140936145 2406912497674963605702109)
              ·
                refine ⟨902592186628111352138291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2406912497674963605702109 902592186628111352138291)
                ·
                  refine ⟨1353888279942167028207437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 902592186628111352138291 1353888279942167028207437)
                  ·
                    refine ⟨507708104978312635577789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1353888279942167028207437 507708104978312635577789)
                    ·
                      rfl

theorem cell22_1483137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_1483137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483137 prefixEnd_1483137 := by exact prefixLift 1483137
  have htrace : WordTrace (prefixWord ++ tailWord_1483137) baseStart_1483137 baseEnd_1483137 := by
    simpa [prefixWord, tailWord_1483137, baseEnd_1483137] using wordTrace_append hprefix tailTrace_1483137
  have hstable : (prefixWord ++ tailWord_1483137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483137).length < 2 ^ (prefixWord ++ tailWord_1483137).sum := by decide
  have hdescent : baseEnd_1483137 < baseStart_1483137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483150 : List Nat := [4, 1, 1, 4, 1, 3, 1, 2, 5]
def baseStart_1483150 : Nat := 118140960795 + 1483150 * 2 ^ 59
def prefixEnd_1483150 : Nat := 4983230072969 + 3 ^ 40 * 1483150 * 2
def baseEnd_1483150 : Nat := 169237518381328311667583

theorem tailTrace_1483150 : CollatzResearch.WordTrace tailWord_1483150 prefixEnd_1483150 169237518381328311667583 := by
  unfold tailWord_1483150
  simp only [CollatzResearch.WordTrace]
  refine ⟨6761865572101040837339863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36063283051205551132479269 6761865572101040837339863)
  ·
    refine ⟨10142798358151561256009795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6761865572101040837339863 10142798358151561256009795)
    ·
      refine ⟨15214197537227341884014693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10142798358151561256009795 15214197537227341884014693)
      ·
        refine ⟨2852662038230126603252755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15214197537227341884014693 2852662038230126603252755)
        ·
          refine ⟨4278993057345189904879133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2852662038230126603252755 4278993057345189904879133)
          ·
            refine ⟨1604622396504446214329675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4278993057345189904879133 1604622396504446214329675)
            ·
              refine ⟨2406933594756669321494513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1604622396504446214329675 2406933594756669321494513)
              ·
                refine ⟨1805200196067501991120885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2406933594756669321494513 1805200196067501991120885)
                ·
                  refine ⟨169237518381328311667583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1805200196067501991120885 169237518381328311667583)
                  ·
                    rfl

theorem cell22_1483150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_1483150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483150 prefixEnd_1483150 := by exact prefixLift 1483150
  have htrace : WordTrace (prefixWord ++ tailWord_1483150) baseStart_1483150 baseEnd_1483150 := by
    simpa [prefixWord, tailWord_1483150, baseEnd_1483150] using wordTrace_append hprefix tailTrace_1483150
  have hstable : (prefixWord ++ tailWord_1483150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483150).length < 2 ^ (prefixWord ++ tailWord_1483150).sum := by decide
  have hdescent : baseEnd_1483150 < baseStart_1483150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483161 : List Nat := [1, 2, 1, 2, 1, 4, 4, 1, 6]
def baseStart_1483161 : Nat := 118140960795 + 1483161 * 2 ^ 59
def prefixEnd_1483161 : Nat := 4983230072969 + 3 ^ 40 * 1483161 * 2
def baseEnd_1483161 : Nat := 169238773556261524325905

theorem tailTrace_1483161 : CollatzResearch.WordTrace tailWord_1483161 prefixEnd_1483161 169238773556261524325905 := by
  unfold tailWord_1483161
  simp only [CollatzResearch.WordTrace]
  refine ⟨54095325779768475577369337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36063550519845650384912891 54095325779768475577369337)
  ·
    refine ⟨40571494334826356683027003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54095325779768475577369337 40571494334826356683027003)
    ·
      refine ⟨60857241502239535024540505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40571494334826356683027003 60857241502239535024540505)
      ·
        refine ⟨45642931126679651268405379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60857241502239535024540505 45642931126679651268405379)
        ·
          refine ⟨68464396690019476902608069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45642931126679651268405379 68464396690019476902608069)
          ·
            refine ⟨12837074379378651919239013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68464396690019476902608069 12837074379378651919239013)
            ·
              refine ⟨2406951446133497234857315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12837074379378651919239013 2406951446133497234857315)
              ·
                refine ⟨3610427169200245852285973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2406951446133497234857315 3610427169200245852285973)
                ·
                  refine ⟨169238773556261524325905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3610427169200245852285973 169238773556261524325905)
                  ·
                    rfl

theorem cell22_1483161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 6].length) (baseStart_1483161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483161 prefixEnd_1483161 := by exact prefixLift 1483161
  have htrace : WordTrace (prefixWord ++ tailWord_1483161) baseStart_1483161 baseEnd_1483161 := by
    simpa [prefixWord, tailWord_1483161, baseEnd_1483161] using wordTrace_append hprefix tailTrace_1483161
  have hstable : (prefixWord ++ tailWord_1483161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483161).length < 2 ^ (prefixWord ++ tailWord_1483161).sum := by decide
  have hdescent : baseEnd_1483161 < baseStart_1483161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483188 : List Nat := [2, 5, 2, 2, 2, 1, 1, 3, 1, 3]
def baseStart_1483188 : Nat := 118140960795 + 1483188 * 2 ^ 59
def prefixEnd_1483188 : Nat := 4983230072969 + 3 ^ 40 * 1483188 * 2
def baseEnd_1483188 : Nat := 507725563320565502552633

theorem tailTrace_1483188 : CollatzResearch.WordTrace tailWord_1483188 prefixEnd_1483188 507725563320565502552633 := by
  unfold tailWord_1483188
  simp only [CollatzResearch.WordTrace]
  refine ⟨27048155275335329594301109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36064207033780439459068145 27048155275335329594301109)
  ·
    refine ⟨2535764557062687149465729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27048155275335329594301109 2535764557062687149465729)
    ·
      refine ⟨1901823417797015362099297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2535764557062687149465729 1901823417797015362099297)
      ·
        refine ⟨1426367563347761521574473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1901823417797015362099297 1426367563347761521574473)
        ·
          refine ⟨1069775672510821141180855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1426367563347761521574473 1069775672510821141180855)
          ·
            refine ⟨1604663508766231711771283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1069775672510821141180855 1604663508766231711771283)
            ·
              refine ⟨2406995263149347567656925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1604663508766231711771283 2406995263149347567656925)
              ·
                refine ⟨902623223681005337871347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2406995263149347567656925 902623223681005337871347)
                ·
                  refine ⟨1353934835521508006807021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 902623223681005337871347 1353934835521508006807021)
                  ·
                    refine ⟨507725563320565502552633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1353934835521508006807021 507725563320565502552633)
                    ·
                      rfl

theorem cell22_1483188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_1483188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483188 prefixEnd_1483188 := by exact prefixLift 1483188
  have htrace : WordTrace (prefixWord ++ tailWord_1483188) baseStart_1483188 baseEnd_1483188 := by
    simpa [prefixWord, tailWord_1483188, baseEnd_1483188] using wordTrace_append hprefix tailTrace_1483188
  have hstable : (prefixWord ++ tailWord_1483188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483188).length < 2 ^ (prefixWord ++ tailWord_1483188).sum := by decide
  have hdescent : baseEnd_1483188 < baseStart_1483188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483191 : List Nat := [1, 1, 3, 1, 3, 3, 2, 1, 1, 6]
def baseStart_1483191 : Nat := 118140960795 + 1483191 * 2 ^ 59
def prefixEnd_1483191 : Nat := 4983230072969 + 3 ^ 40 * 1483191 * 2
def baseEnd_1483191 : Nat := 507726590281874494727623

theorem tailTrace_1483191 : CollatzResearch.WordTrace tailWord_1483191 prefixEnd_1483191 507726590281874494727623 := by
  unfold tailWord_1483191
  simp only [CollatzResearch.WordTrace]
  refine ⟨54096419969659790700961427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36064279979773193800640951 54096419969659790700961427)
  ·
    refine ⟨81144629954489686051442141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54096419969659790700961427 81144629954489686051442141)
    ·
      refine ⟨30429236232933632269290803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81144629954489686051442141 30429236232933632269290803)
      ·
        refine ⟨45643854349400448403936205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30429236232933632269290803 45643854349400448403936205)
        ·
          refine ⟨17116445381025168151476077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45643854349400448403936205 17116445381025168151476077)
          ·
            refine ⟨6418667017884438056803529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17116445381025168151476077 6418667017884438056803529)
            ·
              refine ⟨4814000263413328542602647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6418667017884438056803529 4814000263413328542602647)
              ·
                refine ⟨7221000395119992813903971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4814000263413328542602647 7221000395119992813903971)
                ·
                  refine ⟨10831500592679989220855957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7221000395119992813903971 10831500592679989220855957)
                  ·
                    refine ⟨507726590281874494727623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10831500592679989220855957 507726590281874494727623)
                    ·
                      rfl

theorem cell22_1483191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_1483191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483191 prefixEnd_1483191 := by exact prefixLift 1483191
  have htrace : WordTrace (prefixWord ++ tailWord_1483191) baseStart_1483191 baseEnd_1483191 := by
    simpa [prefixWord, tailWord_1483191, baseEnd_1483191] using wordTrace_append hprefix tailTrace_1483191
  have hstable : (prefixWord ++ tailWord_1483191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483191).length < 2 ^ (prefixWord ++ tailWord_1483191).sum := by decide
  have hdescent : baseEnd_1483191 < baseStart_1483191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483193 : List Nat := [1, 2, 1, 4, 3, 1, 1, 2, 4, 3]
def baseStart_1483193 : Nat := 118140960795 + 1483193 * 2 ^ 59
def prefixEnd_1483193 : Nat := 4983230072969 + 3 ^ 40 * 1483193 * 2
def baseEnd_1483193 : Nat := 507727274922747156177617

theorem tailTrace_1483193 : CollatzResearch.WordTrace tailWord_1483193 prefixEnd_1483193 507727274922747156177617 := by
  unfold tailWord_1483193
  simp only [CollatzResearch.WordTrace]
  refine ⟨54096492915652545042534233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36064328610435030028356155 54096492915652545042534233)
  ·
    refine ⟨40572369686739408781900675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54096492915652545042534233 40572369686739408781900675)
    ·
      refine ⟨60858554530109113172851013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40572369686739408781900675 60858554530109113172851013)
      ·
        refine ⟨11410978974395458719909565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60858554530109113172851013 11410978974395458719909565)
        ·
          refine ⟨4279117115398297019966087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11410978974395458719909565 4279117115398297019966087)
          ·
            refine ⟨6418675673097445529949131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4279117115398297019966087 6418675673097445529949131)
            ·
              refine ⟨9628013509646168294923697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6418675673097445529949131 9628013509646168294923697)
              ·
                refine ⟨7221010132234626221192773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9628013509646168294923697 7221010132234626221192773)
                ·
                  refine ⟨1353939399793992416473645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7221010132234626221192773 1353939399793992416473645)
                  ·
                    refine ⟨507727274922747156177617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1353939399793992416473645 507727274922747156177617)
                    ·
                      rfl

theorem cell22_1483193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 4, 3].length) (baseStart_1483193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483193 prefixEnd_1483193 := by exact prefixLift 1483193
  have htrace : WordTrace (prefixWord ++ tailWord_1483193) baseStart_1483193 baseEnd_1483193 := by
    simpa [prefixWord, tailWord_1483193, baseEnd_1483193] using wordTrace_append hprefix tailTrace_1483193
  have hstable : (prefixWord ++ tailWord_1483193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483193).length < 2 ^ (prefixWord ++ tailWord_1483193).sum := by decide
  have hdescent : baseEnd_1483193 < baseStart_1483193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483208 : List Nat := [2, 1, 3, 1, 3, 3, 1, 2, 2, 4]
def baseStart_1483208 : Nat := 118140960795 + 1483208 * 2 ^ 59
def prefixEnd_1483208 : Nat := 4983230072969 + 3 ^ 40 * 1483208 * 2
def baseEnd_1483208 : Nat := 507732409729292117052571

theorem tailTrace_1483208 : CollatzResearch.WordTrace tailWord_1483208 prefixEnd_1483208 507732409729292117052571 := by
  unfold tailWord_1483208
  simp only [CollatzResearch.WordTrace]
  refine ⟨27048520005299101302165139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36064693340398801736220185 27048520005299101302165139)
  ·
    refine ⟨40572780007948651953247709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27048520005299101302165139 40572780007948651953247709)
    ·
      refine ⟨15214792502980744482467891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40572780007948651953247709 15214792502980744482467891)
      ·
        refine ⟨22822188754471116723701837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15214792502980744482467891 22822188754471116723701837)
        ·
          refine ⟨8558320782926668771388189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22822188754471116723701837 8558320782926668771388189)
          ·
            refine ⟨3209370293597500789270571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8558320782926668771388189 3209370293597500789270571)
            ·
              refine ⟨4814055440396251183905857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3209370293597500789270571 4814055440396251183905857)
              ·
                refine ⟨3610541580297188387929393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4814055440396251183905857 3610541580297188387929393)
                ·
                  refine ⟨2707906185222891290947045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3610541580297188387929393 2707906185222891290947045)
                  ·
                    refine ⟨507732409729292117052571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2707906185222891290947045 507732409729292117052571)
                    ·
                      rfl

theorem cell22_1483208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_1483208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483208 prefixEnd_1483208 := by exact prefixLift 1483208
  have htrace : WordTrace (prefixWord ++ tailWord_1483208) baseStart_1483208 baseEnd_1483208 := by
    simpa [prefixWord, tailWord_1483208, baseEnd_1483208] using wordTrace_append hprefix tailTrace_1483208
  have hstable : (prefixWord ++ tailWord_1483208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483208).length < 2 ^ (prefixWord ++ tailWord_1483208).sum := by decide
  have hdescent : baseEnd_1483208 < baseStart_1483208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483212 : List Nat := [2, 2, 1, 4, 3, 1, 3, 2, 4]
def baseStart_1483212 : Nat := 118140960795 + 1483212 * 2 ^ 59
def prefixEnd_1483212 : Nat := 4983230072969 + 3 ^ 40 * 1483212 * 2
def baseEnd_1483212 : Nat := 169244593003679146650853

theorem tailTrace_1483212 : CollatzResearch.WordTrace tailWord_1483212 prefixEnd_1483212 169244593003679146650853 := by
  unfold tailWord_1483212
  simp only [CollatzResearch.WordTrace]
  refine ⟨27048592951291855643737945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36064790601722474191650593 27048592951291855643737945)
  ·
    refine ⟨20286444713468891732803459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27048592951291855643737945 20286444713468891732803459)
    ·
      refine ⟨30429667070203337599205189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20286444713468891732803459 30429667070203337599205189)
      ·
        refine ⟨5705562575663125799850973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30429667070203337599205189 5705562575663125799850973)
        ·
          refine ⟨2139585965873672174944115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5705562575663125799850973 2139585965873672174944115)
          ·
            refine ⟨3209378948810508262416173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2139585965873672174944115 3209378948810508262416173)
            ·
              refine ⟨1203517105803940598406065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3209378948810508262416173 1203517105803940598406065)
              ·
                refine ⟨902637829352955448804549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1203517105803940598406065 902637829352955448804549)
                ·
                  refine ⟨169244593003679146650853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 902637829352955448804549 169244593003679146650853)
                  ·
                    rfl

theorem cell22_1483212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 2, 4].length) (baseStart_1483212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483212 prefixEnd_1483212 := by exact prefixLift 1483212
  have htrace : WordTrace (prefixWord ++ tailWord_1483212) baseStart_1483212 baseEnd_1483212 := by
    simpa [prefixWord, tailWord_1483212, baseEnd_1483212] using wordTrace_append hprefix tailTrace_1483212
  have hstable : (prefixWord ++ tailWord_1483212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483212).length < 2 ^ (prefixWord ++ tailWord_1483212).sum := by decide
  have hdescent : baseEnd_1483212 < baseStart_1483212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483345 : List Nat := [1, 2, 2, 1, 3, 5, 1, 1, 1, 5]
def baseStart_1483345 : Nat := 118140960795 + 1483345 * 2 ^ 59
def prefixEnd_1483345 : Nat := 4983230072969 + 3 ^ 40 * 1483345 * 2
def baseEnd_1483345 : Nat := 507779307629069426377151

theorem tailTrace_1483345 : CollatzResearch.WordTrace tailWord_1483345 prefixEnd_1483345 507779307629069426377151 := by
  unfold tailWord_1483345
  simp only [CollatzResearch.WordTrace]
  refine ⟨54102036811101875002067489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36068024540734583334711659 54102036811101875002067489)
  ·
    refine ⟨40576527608326406251550617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54102036811101875002067489 40576527608326406251550617)
    ·
      refine ⟨30432395706244804688662963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40576527608326406251550617 30432395706244804688662963)
      ·
        refine ⟨45648593559367207032994445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30432395706244804688662963 45648593559367207032994445)
        ·
          refine ⟨17118222584762702637372917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45648593559367207032994445 17118222584762702637372917)
          ·
            refine ⟨1604833367321503372253711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17118222584762702637372917 1604833367321503372253711)
            ·
              refine ⟨2407250050982255058380567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1604833367321503372253711 2407250050982255058380567)
              ·
                refine ⟨3610875076473382587570851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2407250050982255058380567 3610875076473382587570851)
                ·
                  refine ⟨5416312614710073881356277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3610875076473382587570851 5416312614710073881356277)
                  ·
                    refine ⟨507779307629069426377151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5416312614710073881356277 507779307629069426377151)
                    ·
                      rfl

theorem cell22_1483345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 5].length) (baseStart_1483345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483345 prefixEnd_1483345 := by exact prefixLift 1483345
  have htrace : WordTrace (prefixWord ++ tailWord_1483345) baseStart_1483345 baseEnd_1483345 := by
    simpa [prefixWord, tailWord_1483345, baseEnd_1483345] using wordTrace_append hprefix tailTrace_1483345
  have hstable : (prefixWord ++ tailWord_1483345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483345).length < 2 ^ (prefixWord ++ tailWord_1483345).sum := by decide
  have hdescent : baseEnd_1483345 < baseStart_1483345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483433 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 5, 4]
def baseStart_1483433 : Nat := 118140960795 + 1483433 * 2 ^ 59
def prefixEnd_1483433 : Nat := 4983230072969 + 3 ^ 40 * 1483433 * 2
def baseEnd_1483433 : Nat := 507809431827466530176881

theorem tailTrace_1483433 : CollatzResearch.WordTrace tailWord_1483433 prefixEnd_1483433 507809431827466530176881 := by
  unfold tailWord_1483433
  simp only [CollatzResearch.WordTrace]
  refine ⟨54105246434783066031270953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36070164289855377354180635 54105246434783066031270953)
  ·
    refine ⟨40578934826087299523453215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54105246434783066031270953 40578934826087299523453215)
    ·
      refine ⟨60868402239130949285179823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40578934826087299523453215 60868402239130949285179823)
      ·
        refine ⟨91302603358696423927769735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60868402239130949285179823 91302603358696423927769735)
        ·
          refine ⟨136953905038044635891654603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91302603358696423927769735 136953905038044635891654603)
          ·
            refine ⟨205430857557066953837481905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136953905038044635891654603 205430857557066953837481905)
            ·
              refine ⟨154073143167800215378111429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205430857557066953837481905 154073143167800215378111429)
              ·
                refine ⟨28888714343962540383395893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 154073143167800215378111429 28888714343962540383395893)
                ·
                  refine ⟨2708316969746488160943365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28888714343962540383395893 2708316969746488160943365)
                  ·
                    refine ⟨507809431827466530176881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2708316969746488160943365 507809431827466530176881)
                    ·
                      rfl

theorem cell22_1483433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 4].length) (baseStart_1483433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483433 prefixEnd_1483433 := by exact prefixLift 1483433
  have htrace : WordTrace (prefixWord ++ tailWord_1483433) baseStart_1483433 baseEnd_1483433 := by
    simpa [prefixWord, tailWord_1483433, baseEnd_1483433] using wordTrace_append hprefix tailTrace_1483433
  have hstable : (prefixWord ++ tailWord_1483433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483433).length < 2 ^ (prefixWord ++ tailWord_1483433).sum := by decide
  have hdescent : baseEnd_1483433 < baseStart_1483433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483437 : List Nat := [1, 5, 2, 1, 1, 3, 2, 2, 5]
def baseStart_1483437 : Nat := 118140960795 + 1483437 * 2 ^ 59
def prefixEnd_1483437 : Nat := 4983230072969 + 3 ^ 40 * 1483437 * 2
def baseEnd_1483437 : Nat := 169270267036403951025623

theorem tailTrace_1483437 : CollatzResearch.WordTrace tailWord_1483437 prefixEnd_1483437 169270267036403951025623 := by
  unfold tailWord_1483437
  simp only [CollatzResearch.WordTrace]
  refine ⟨54105392326768574714416565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36070261551179049809611043 54105392326768574714416565)
  ·
    refine ⟨5072380530634553879476553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54105392326768574714416565 5072380530634553879476553)
    ·
      refine ⟨3804285397975915409607415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5072380530634553879476553 3804285397975915409607415)
      ·
        refine ⟨5706428096963873114411123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3804285397975915409607415 5706428096963873114411123)
        ·
          refine ⟨8559642145445809671616685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5706428096963873114411123 8559642145445809671616685)
          ·
            refine ⟨3209865804542178626856257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8559642145445809671616685 3209865804542178626856257)
            ·
              refine ⟨2407399353406633970142193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3209865804542178626856257 2407399353406633970142193)
              ·
                refine ⟨1805549515054975477606645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2407399353406633970142193 1805549515054975477606645)
                ·
                  refine ⟨169270267036403951025623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1805549515054975477606645 169270267036403951025623)
                  ·
                    rfl

theorem cell22_1483437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_1483437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483437 prefixEnd_1483437 := by exact prefixLift 1483437
  have htrace : WordTrace (prefixWord ++ tailWord_1483437) baseStart_1483437 baseEnd_1483437 := by
    simpa [prefixWord, tailWord_1483437, baseEnd_1483437] using wordTrace_append hprefix tailTrace_1483437
  have hstable : (prefixWord ++ tailWord_1483437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483437).length < 2 ^ (prefixWord ++ tailWord_1483437).sum := by decide
  have hdescent : baseEnd_1483437 < baseStart_1483437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483441 : List Nat := [1, 2, 2, 6, 1, 1, 1, 4, 1, 3]
def baseStart_1483441 : Nat := 118140960795 + 1483441 * 2 ^ 59
def prefixEnd_1483441 : Nat := 4983230072969 + 3 ^ 40 * 1483441 * 2
def baseEnd_1483441 : Nat := 507812170390957175976857

theorem tailTrace_1483441 : CollatzResearch.WordTrace tailWord_1483441 prefixEnd_1483441 507812170390957175976857 := by
  unfold tailWord_1483441
  simp only [CollatzResearch.WordTrace]
  refine ⟨54105538218754083397562177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36070358812502722265041451 54105538218754083397562177)
  ·
    refine ⟨40579153664065562548171633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54105538218754083397562177 40579153664065562548171633)
    ·
      refine ⟨30434365248049171911128725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40579153664065562548171633 30434365248049171911128725)
      ·
        refine ⟨1426610871002304933334159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30434365248049171911128725 1426610871002304933334159)
        ·
          refine ⟨2139916306503457400001239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1426610871002304933334159 2139916306503457400001239)
          ·
            refine ⟨3209874459755186100001859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2139916306503457400001239 3209874459755186100001859)
            ·
              refine ⟨4814811689632779150002789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3209874459755186100001859 4814811689632779150002789)
              ·
                refine ⟨902777191806146090625523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4814811689632779150002789 902777191806146090625523)
                ·
                  refine ⟨1354165787709219135938285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 902777191806146090625523 1354165787709219135938285)
                  ·
                    refine ⟨507812170390957175976857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1354165787709219135938285 507812170390957175976857)
                    ·
                      rfl

theorem cell22_1483441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 4, 1, 3].length) (baseStart_1483441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483441 prefixEnd_1483441 := by exact prefixLift 1483441
  have htrace : WordTrace (prefixWord ++ tailWord_1483441) baseStart_1483441 baseEnd_1483441 := by
    simpa [prefixWord, tailWord_1483441, baseEnd_1483441] using wordTrace_append hprefix tailTrace_1483441
  have hstable : (prefixWord ++ tailWord_1483441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483441).length < 2 ^ (prefixWord ++ tailWord_1483441).sum := by decide
  have hdescent : baseEnd_1483441 < baseStart_1483441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483480 : List Nat := [2, 1, 2, 2, 3, 2, 2, 2, 1, 5]
def baseStart_1483480 : Nat := 118140960795 + 1483480 * 2 ^ 59
def prefixEnd_1483480 : Nat := 4983230072969 + 3 ^ 40 * 1483480 * 2
def baseEnd_1483480 : Nat := 507825520887974074251737

theorem tailTrace_1483480 : CollatzResearch.WordTrace tailWord_1483480 prefixEnd_1483480 507825520887974074251737 := by
  unfold tailWord_1483480
  simp only [CollatzResearch.WordTrace]
  refine ⟨27053480332806396529115947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36071307110408528705487929 27053480332806396529115947)
  ·
    refine ⟨40580220499209594793673921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27053480332806396529115947 40580220499209594793673921)
    ·
      refine ⟨30435165374407196095255441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40580220499209594793673921 30435165374407196095255441)
      ·
        refine ⟨22826374030805397071441581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30435165374407196095255441 22826374030805397071441581)
        ·
          refine ⟨8559890261552023901790593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22826374030805397071441581 8559890261552023901790593)
          ·
            refine ⟨6419917696164017926342945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8559890261552023901790593 6419917696164017926342945)
            ·
              refine ⟨4814938272123013444757209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6419917696164017926342945 4814938272123013444757209)
              ·
                refine ⟨3611203704092260083567907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4814938272123013444757209 3611203704092260083567907)
                ·
                  refine ⟨5416805556138390125351861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3611203704092260083567907 5416805556138390125351861)
                  ·
                    refine ⟨507825520887974074251737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5416805556138390125351861 507825520887974074251737)
                    ·
                      rfl

theorem cell22_1483480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_1483480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483480 prefixEnd_1483480 := by exact prefixLift 1483480
  have htrace : WordTrace (prefixWord ++ tailWord_1483480) baseStart_1483480 baseEnd_1483480 := by
    simpa [prefixWord, tailWord_1483480, baseEnd_1483480] using wordTrace_append hprefix tailTrace_1483480
  have hstable : (prefixWord ++ tailWord_1483480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483480).length < 2 ^ (prefixWord ++ tailWord_1483480).sum := by decide
  have hdescent : baseEnd_1483480 < baseStart_1483480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483482 : List Nat := [3, 1, 1, 2, 2, 2, 4, 3, 4]
def baseStart_1483482 : Nat := 118140960795 + 1483482 * 2 ^ 59
def prefixEnd_1483482 : Nat := 4983230072969 + 3 ^ 40 * 1483482 * 2
def baseEnd_1483482 : Nat := 169275401842948911900577

theorem tailTrace_1483482 : CollatzResearch.WordTrace tailWord_1483482 prefixEnd_1483482 169275401842948911900577 := by
  unfold tailWord_1483482
  simp only [CollatzResearch.WordTrace]
  refine ⟨13526758402901386849951175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36071355741070364933203133 13526758402901386849951175)
  ·
    refine ⟨20290137604352080274926763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13526758402901386849951175 20290137604352080274926763)
    ·
      refine ⟨30435206406528120412390145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20290137604352080274926763 30435206406528120412390145)
      ·
        refine ⟨22826404804896090309292609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30435206406528120412390145 22826404804896090309292609)
        ·
          refine ⟨17119803603672067731969457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22826404804896090309292609 17119803603672067731969457)
          ·
            refine ⟨12839852702754050798977093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17119803603672067731969457 12839852702754050798977093)
            ·
              refine ⟨2407472381766384524808205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12839852702754050798977093 2407472381766384524808205)
              ·
                refine ⟨902802143162394196803077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2407472381766384524808205 902802143162394196803077)
                ·
                  refine ⟨169275401842948911900577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 902802143162394196803077 169275401842948911900577)
                  ·
                    rfl

theorem cell22_1483482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 3, 4].length) (baseStart_1483482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483482 prefixEnd_1483482 := by exact prefixLift 1483482
  have htrace : WordTrace (prefixWord ++ tailWord_1483482) baseStart_1483482 baseEnd_1483482 := by
    simpa [prefixWord, tailWord_1483482, baseEnd_1483482] using wordTrace_append hprefix tailTrace_1483482
  have hstable : (prefixWord ++ tailWord_1483482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483482).length < 2 ^ (prefixWord ++ tailWord_1483482).sum := by decide
  have hdescent : baseEnd_1483482 < baseStart_1483482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483484 : List Nat := [2, 2, 5, 1, 1, 2, 1, 3, 1, 4]
def baseStart_1483484 : Nat := 118140960795 + 1483484 * 2 ^ 59
def prefixEnd_1483484 : Nat := 4983230072969 + 3 ^ 40 * 1483484 * 2
def baseEnd_1483484 : Nat := 507826890169719397151725

theorem tailTrace_1483484 : CollatzResearch.WordTrace tailWord_1483484 prefixEnd_1483484 507826890169719397151725 := by
  unfold tailWord_1483484
  simp only [CollatzResearch.WordTrace]
  refine ⟨27053553278799150870688753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36071404371732201160918337 27053553278799150870688753)
  ·
    refine ⟨20290164959099363153016565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27053553278799150870688753 20290164959099363153016565)
    ·
      refine ⟨1902202964915565295595303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20290164959099363153016565 1902202964915565295595303)
      ·
        refine ⟨2853304447373347943392955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1902202964915565295595303 2853304447373347943392955)
        ·
          refine ⟨4279956671060021915089433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2853304447373347943392955 4279956671060021915089433)
          ·
            refine ⟨3209967503295016436317075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4279956671060021915089433 3209967503295016436317075)
            ·
              refine ⟨4814951254942524654475613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3209967503295016436317075 4814951254942524654475613)
              ·
                refine ⟨1805606720603446745428355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4814951254942524654475613 1805606720603446745428355)
                ·
                  refine ⟨2708410080905170118142533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1805606720603446745428355 2708410080905170118142533)
                  ·
                    refine ⟨507826890169719397151725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2708410080905170118142533 507826890169719397151725)
                    ·
                      rfl

theorem cell22_1483484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_1483484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483484 prefixEnd_1483484 := by exact prefixLift 1483484
  have htrace : WordTrace (prefixWord ++ tailWord_1483484) baseStart_1483484 baseEnd_1483484 := by
    simpa [prefixWord, tailWord_1483484, baseEnd_1483484] using wordTrace_append hprefix tailTrace_1483484
  have hstable : (prefixWord ++ tailWord_1483484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483484).length < 2 ^ (prefixWord ++ tailWord_1483484).sum := by decide
  have hdescent : baseEnd_1483484 < baseStart_1483484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483497 : List Nat := [1, 2, 1, 1, 1, 2, 7, 2, 2, 3]
def baseStart_1483497 : Nat := 118140960795 + 1483497 * 2 ^ 59
def prefixEnd_1483497 : Nat := 4983230072969 + 3 ^ 40 * 1483497 * 2
def baseEnd_1483497 : Nat := 507831340335391696576685

theorem tailTrace_1483497 : CollatzResearch.WordTrace tailWord_1483497 prefixEnd_1483497 507831340335391696576685 := by
  unfold tailWord_1483497
  simp only [CollatzResearch.WordTrace]
  refine ⟨54107580706551204961600745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36071720471034136641067163 54107580706551204961600745)
  ·
    refine ⟨40580685529913403721200559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54107580706551204961600745 40580685529913403721200559)
    ·
      refine ⟨60871028294870105581800839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40580685529913403721200559 60871028294870105581800839)
      ·
        refine ⟨91306542442305158372701259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60871028294870105581800839 91306542442305158372701259)
        ·
          refine ⟨136959813663457737559051889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91306542442305158372701259 136959813663457737559051889)
          ·
            refine ⟨102719860247593303169288917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136959813663457737559051889 102719860247593303169288917)
            ·
              refine ⟨2407496724552968043030209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 102719860247593303169288917 2407496724552968043030209)
              ·
                refine ⟨1805622543414726032272657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2407496724552968043030209 1805622543414726032272657)
                ·
                  refine ⟨1354216907561044524204493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1805622543414726032272657 1354216907561044524204493)
                  ·
                    refine ⟨507831340335391696576685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1354216907561044524204493 507831340335391696576685)
                    ·
                      rfl

theorem cell22_1483497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 2, 3].length) (baseStart_1483497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483497 prefixEnd_1483497 := by exact prefixLift 1483497
  have htrace : WordTrace (prefixWord ++ tailWord_1483497) baseStart_1483497 baseEnd_1483497 := by
    simpa [prefixWord, tailWord_1483497, baseEnd_1483497] using wordTrace_append hprefix tailTrace_1483497
  have hstable : (prefixWord ++ tailWord_1483497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483497).length < 2 ^ (prefixWord ++ tailWord_1483497).sum := by decide
  have hdescent : baseEnd_1483497 < baseStart_1483497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483510 : List Nat := [5, 1, 1, 1, 1, 2, 2, 9]
def baseStart_1483510 : Nat := 118140960795 + 1483510 * 2 ^ 59
def prefixEnd_1483510 : Nat := 4983230072969 + 3 ^ 40 * 1483510 * 2
def baseEnd_1483510 : Nat := 56426198944562666222405

theorem tailTrace_1483510 : CollatzResearch.WordTrace tailWord_1483510 prefixEnd_1483510 56426198944562666222405 := by
  unfold tailWord_1483510
  simp only [CollatzResearch.WordTrace]
  refine ⟨3381753428469006761363999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36072036570336072121215989 3381753428469006761363999)
  ·
    refine ⟨5072630142703510142045999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3381753428469006761363999 5072630142703510142045999)
    ·
      refine ⟨7608945214055265213068999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5072630142703510142045999 7608945214055265213068999)
      ·
        refine ⟨11413417821082897819603499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7608945214055265213068999 11413417821082897819603499)
        ·
          refine ⟨17120126731624346729405249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11413417821082897819603499 17120126731624346729405249)
          ·
            refine ⟨12840095048718260047053937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17120126731624346729405249 12840095048718260047053937)
            ·
              refine ⟨9630071286538695035290453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12840095048718260047053937 9630071286538695035290453)
              ·
                refine ⟨56426198944562666222405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9630071286538695035290453 56426198944562666222405)
                ·
                  rfl

theorem cell22_1483510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_1483510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483510 prefixEnd_1483510 := by exact prefixLift 1483510
  have htrace : WordTrace (prefixWord ++ tailWord_1483510) baseStart_1483510 baseEnd_1483510 := by
    simpa [prefixWord, tailWord_1483510, baseEnd_1483510] using wordTrace_append hprefix tailTrace_1483510
  have hstable : (prefixWord ++ tailWord_1483510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483510).length < 2 ^ (prefixWord ++ tailWord_1483510).sum := by decide
  have hdescent : baseEnd_1483510 < baseStart_1483510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483527 : List Nat := [1, 1, 4, 4, 1, 1, 4, 6]
def baseStart_1483527 : Nat := 118140960795 + 1483527 * 2 ^ 59
def prefixEnd_1483527 : Nat := 4983230072969 + 3 ^ 40 * 1483527 * 2
def baseEnd_1483527 : Nat := 56426845549831290925177

theorem tailTrace_1483527 : CollatzResearch.WordTrace tailWord_1483527 prefixEnd_1483527 56426845549831290925177 := by
  unfold tailWord_1483527
  simp only [CollatzResearch.WordTrace]
  refine ⟨54108674896442520085192835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36072449930961680056795223 54108674896442520085192835)
  ·
    refine ⟨81163012344663780127789253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54108674896442520085192835 81163012344663780127789253)
    ·
      refine ⟨15218064814624458773960485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81163012344663780127789253 15218064814624458773960485)
      ·
        refine ⟨2853387152742086020117591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15218064814624458773960485 2853387152742086020117591)
        ·
          refine ⟨4280080729113129030176387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2853387152742086020117591 4280080729113129030176387)
          ·
            refine ⟨6420121093669693545264581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4280080729113129030176387 6420121093669693545264581)
            ·
              refine ⟨1203772705063067539737109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6420121093669693545264581 1203772705063067539737109)
              ·
                refine ⟨56426845549831290925177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1203772705063067539737109 56426845549831290925177)
                ·
                  rfl

theorem cell22_1483527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 6].length) (baseStart_1483527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483527 prefixEnd_1483527 := by exact prefixLift 1483527
  have htrace : WordTrace (prefixWord ++ tailWord_1483527) baseStart_1483527 baseEnd_1483527 := by
    simpa [prefixWord, tailWord_1483527, baseEnd_1483527] using wordTrace_append hprefix tailTrace_1483527
  have hstable : (prefixWord ++ tailWord_1483527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483527).length < 2 ^ (prefixWord ++ tailWord_1483527).sum := by decide
  have hdescent : baseEnd_1483527 < baseStart_1483527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483555 : List Nat := [1, 1, 1, 4, 2, 1, 1, 6, 5]
def baseStart_1483555 : Nat := 118140960795 + 1483555 * 2 ^ 59
def prefixEnd_1483555 : Nat := 4983230072969 + 3 ^ 40 * 1483555 * 2
def baseEnd_1483555 : Nat := 169283731640232959542169

theorem tailTrace_1483555 : CollatzResearch.WordTrace tailWord_1483555 prefixEnd_1483555 169283731640232959542169 := by
  unfold tailWord_1483555
  simp only [CollatzResearch.WordTrace]
  refine ⟨54109696140341080867212119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36073130760227387244808079 54109696140341080867212119)
  ·
    refine ⟨81164544210511621300818179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54109696140341080867212119 81164544210511621300818179)
    ·
      refine ⟨121746816315767431951227269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81164544210511621300818179 121746816315767431951227269)
      ·
        refine ⟨22827528059206393490855113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121746816315767431951227269 22827528059206393490855113)
        ·
          refine ⟨17120646044404795118141335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22827528059206393490855113 17120646044404795118141335)
          ·
            refine ⟨25680969066607192677212003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17120646044404795118141335 25680969066607192677212003)
            ·
              refine ⟨38521453599910789015818005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25680969066607192677212003 38521453599910789015818005)
              ·
                refine ⟨1805693137495818235116469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38521453599910789015818005 1805693137495818235116469)
                ·
                  refine ⟨169283731640232959542169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1805693137495818235116469 169283731640232959542169)
                  ·
                    rfl

theorem cell22_1483555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 5].length) (baseStart_1483555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483555 prefixEnd_1483555 := by exact prefixLift 1483555
  have htrace : WordTrace (prefixWord ++ tailWord_1483555) baseStart_1483555 baseEnd_1483555 := by
    simpa [prefixWord, tailWord_1483555, baseEnd_1483555] using wordTrace_append hprefix tailTrace_1483555
  have hstable : (prefixWord ++ tailWord_1483555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483555).length < 2 ^ (prefixWord ++ tailWord_1483555).sum := by decide
  have hdescent : baseEnd_1483555 < baseStart_1483555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483565 : List Nat := [1, 5, 3, 2, 1, 2, 2, 1, 2, 3]
def baseStart_1483565 : Nat := 118140960795 + 1483565 * 2 ^ 59
def prefixEnd_1483565 : Nat := 4983230072969 + 3 ^ 40 * 1483565 * 2
def baseEnd_1483565 : Nat := 507854618125062185876477

theorem tailTrace_1483565 : CollatzResearch.WordTrace tailWord_1483565 prefixEnd_1483565 507854618125062185876477 := by
  unfold tailWord_1483565
  simp only [CollatzResearch.WordTrace]
  refine ⟨54110060870304852575076149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36073373913536568383384099 54110060870304852575076149)
  ·
    refine ⟨5072818206591079928913389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54110060870304852575076149 5072818206591079928913389)
    ·
      refine ⟨1902306827471654973342521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5072818206591079928913389 1902306827471654973342521)
      ·
        refine ⟨1426730120603741230006891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1902306827471654973342521 1426730120603741230006891)
        ·
          refine ⟨2140095180905611845010337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1426730120603741230006891 2140095180905611845010337)
          ·
            refine ⟨1605071385679208883757753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2140095180905611845010337 1605071385679208883757753)
            ·
              refine ⟨1203803539259406662818315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1605071385679208883757753 1203803539259406662818315)
              ·
                refine ⟨1805705308889109994227473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1203803539259406662818315 1805705308889109994227473)
                ·
                  refine ⟨1354278981666832495670605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1805705308889109994227473 1354278981666832495670605)
                  ·
                    refine ⟨507854618125062185876477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1354278981666832495670605 507854618125062185876477)
                    ·
                      rfl

theorem cell22_1483565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_1483565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483565 prefixEnd_1483565 := by exact prefixLift 1483565
  have htrace : WordTrace (prefixWord ++ tailWord_1483565) baseStart_1483565 baseEnd_1483565 := by
    simpa [prefixWord, tailWord_1483565, baseEnd_1483565] using wordTrace_append hprefix tailTrace_1483565
  have hstable : (prefixWord ++ tailWord_1483565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483565).length < 2 ^ (prefixWord ++ tailWord_1483565).sum := by decide
  have hdescent : baseEnd_1483565 < baseStart_1483565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483570 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 1, 7]
def baseStart_1483570 : Nat := 118140960795 + 1483570 * 2 ^ 59
def prefixEnd_1483570 : Nat := 4983230072969 + 3 ^ 40 * 1483570 * 2
def baseEnd_1483570 : Nat := 507856329727243839501461

theorem tailTrace_1483570 : CollatzResearch.WordTrace tailWord_1483570 prefixEnd_1483570 507856329727243839501461 := by
  unfold tailWord_1483570
  simp only [CollatzResearch.WordTrace]
  refine ⟨13527560808821684607252041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36073495490191158952672109 13527560808821684607252041)
  ·
    refine ⟨10145670606616263455439031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13527560808821684607252041 10145670606616263455439031)
    ·
      refine ⟨15218505909924395183158547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10145670606616263455439031 15218505909924395183158547)
      ·
        refine ⟨22827758864886592774737821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15218505909924395183158547 22827758864886592774737821)
        ·
          refine ⟨8560409574332472290526683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22827758864886592774737821 8560409574332472290526683)
          ·
            refine ⟨12840614361498708435790025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8560409574332472290526683 12840614361498708435790025)
            ·
              refine ⟨9630460771124031326842519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12840614361498708435790025 9630460771124031326842519)
              ·
                refine ⟨14445691156686046990263779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9630460771124031326842519 14445691156686046990263779)
                ·
                  refine ⟨21668536735029070485395669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14445691156686046990263779 21668536735029070485395669)
                  ·
                    refine ⟨507856329727243839501461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21668536735029070485395669 507856329727243839501461)
                    ·
                      rfl

theorem cell22_1483570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_1483570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483570 prefixEnd_1483570 := by exact prefixLift 1483570
  have htrace : WordTrace (prefixWord ++ tailWord_1483570) baseStart_1483570 baseEnd_1483570 := by
    simpa [prefixWord, tailWord_1483570, baseEnd_1483570] using wordTrace_append hprefix tailTrace_1483570
  have hstable : (prefixWord ++ tailWord_1483570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483570).length < 2 ^ (prefixWord ++ tailWord_1483570).sum := by decide
  have hdescent : baseEnd_1483570 < baseStart_1483570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483615 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 3, 5]
def baseStart_1483615 : Nat := 118140960795 + 1483615 * 2 ^ 59
def prefixEnd_1483615 : Nat := 4983230072969 + 3 ^ 40 * 1483615 * 2
def baseEnd_1483615 : Nat := 507871734146878722126323

theorem tailTrace_1483615 : CollatzResearch.WordTrace tailWord_1483615 prefixEnd_1483615 507871734146878722126323 := by
  unfold tailWord_1483615
  simp only [CollatzResearch.WordTrace]
  refine ⟨54111884520123711114396299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36074589680082474076264199 54111884520123711114396299)
  ·
    refine ⟨81167826780185566671594449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54111884520123711114396299 81167826780185566671594449)
    ·
      refine ⟨60875870085139175003695837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81167826780185566671594449 60875870085139175003695837)
      ·
        refine ⟨22828451281927190626385939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60875870085139175003695837 22828451281927190626385939)
        ·
          refine ⟨34242676922890785939578909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22828451281927190626385939 34242676922890785939578909)
          ·
            refine ⟨12841003846084044727342091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34242676922890785939578909 12841003846084044727342091)
            ·
              refine ⟨19261505769126067091013137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12841003846084044727342091 19261505769126067091013137)
              ·
                refine ⟨14446129326844550318259853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19261505769126067091013137 14446129326844550318259853)
                ·
                  refine ⟨5417298497566706369347445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14446129326844550318259853 5417298497566706369347445)
                  ·
                    refine ⟨507871734146878722126323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5417298497566706369347445 507871734146878722126323)
                    ·
                      rfl

theorem cell22_1483615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 5].length) (baseStart_1483615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483615 prefixEnd_1483615 := by exact prefixLift 1483615
  have htrace : WordTrace (prefixWord ++ tailWord_1483615) baseStart_1483615 baseEnd_1483615 := by
    simpa [prefixWord, tailWord_1483615, baseEnd_1483615] using wordTrace_append hprefix tailTrace_1483615
  have hstable : (prefixWord ++ tailWord_1483615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483615).length < 2 ^ (prefixWord ++ tailWord_1483615).sum := by decide
  have hdescent : baseEnd_1483615 < baseStart_1483615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483645 : List Nat := [1, 4, 1, 1, 2, 1, 2, 10]
def baseStart_1483645 : Nat := 118140960795 + 1483645 * 2 ^ 59
def prefixEnd_1483645 : Nat := 4983230072969 + 3 ^ 40 * 1483645 * 2
def baseEnd_1483645 : Nat := 56431333751107627097359

theorem tailTrace_1483645 : CollatzResearch.WordTrace tailWord_1483645 prefixEnd_1483645 56431333751107627097359 := by
  unfold tailWord_1483645
  simp only [CollatzResearch.WordTrace]
  refine ⟨54112978710015026237988389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36075319140010017491992259 54112978710015026237988389)
  ·
    refine ⟨10146183508127817419622823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54112978710015026237988389 10146183508127817419622823)
    ·
      refine ⟨15219275262191726129434235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10146183508127817419622823 15219275262191726129434235)
      ·
        refine ⟨22828912893287589194151353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15219275262191726129434235 22828912893287589194151353)
        ·
          refine ⟨17121684669965691895613515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22828912893287589194151353 17121684669965691895613515)
          ·
            refine ⟨25682527004948537843420273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17121684669965691895613515 25682527004948537843420273)
            ·
              refine ⟨19261895253711403382565205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25682527004948537843420273 19261895253711403382565205)
              ·
                refine ⟨56431333751107627097359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 19261895253711403382565205 56431333751107627097359)
                ·
                  rfl

theorem cell22_1483645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 10].length) (baseStart_1483645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483645 prefixEnd_1483645 := by exact prefixLift 1483645
  have htrace : WordTrace (prefixWord ++ tailWord_1483645) baseStart_1483645 baseEnd_1483645 := by
    simpa [prefixWord, tailWord_1483645, baseEnd_1483645] using wordTrace_append hprefix tailTrace_1483645
  have hstable : (prefixWord ++ tailWord_1483645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483645).length < 2 ^ (prefixWord ++ tailWord_1483645).sum := by decide
  have hdescent : baseEnd_1483645 < baseStart_1483645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483647 : List Nat := [1, 1, 2, 2, 1, 1, 7, 1, 2, 4]
def baseStart_1483647 : Nat := 118140960795 + 1483647 * 2 ^ 59
def prefixEnd_1483647 : Nat := 4983230072969 + 3 ^ 40 * 1483647 * 2
def baseEnd_1483647 : Nat := 507882688400841305326225

theorem tailTrace_1483647 : CollatzResearch.WordTrace tailWord_1483647 prefixEnd_1483647 507882688400841305326225 := by
  unfold tailWord_1483647
  simp only [CollatzResearch.WordTrace]
  refine ⟨54113051656007780579561195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36075367770671853719707463 54113051656007780579561195)
  ·
    refine ⟨81169577484011670869341793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54113051656007780579561195 81169577484011670869341793)
    ·
      refine ⟨60877183113008753152006345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81169577484011670869341793 60877183113008753152006345)
      ·
        refine ⟨45657887334756564864004759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60877183113008753152006345 45657887334756564864004759)
        ·
          refine ⟨68486831002134847296007139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45657887334756564864004759 68486831002134847296007139)
          ·
            refine ⟨102730246503202270944010709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68486831002134847296007139 102730246503202270944010709)
            ·
              refine ⟨2407740152418803225250251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 102730246503202270944010709 2407740152418803225250251)
              ·
                refine ⟨3611610228628204837875377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2407740152418803225250251 3611610228628204837875377)
                ·
                  refine ⟨2708707671471153628406533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3611610228628204837875377 2708707671471153628406533)
                  ·
                    refine ⟨507882688400841305326225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2708707671471153628406533 507882688400841305326225)
                    ·
                      rfl

theorem cell22_1483647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 2, 4].length) (baseStart_1483647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483647 prefixEnd_1483647 := by exact prefixLift 1483647
  have htrace : WordTrace (prefixWord ++ tailWord_1483647) baseStart_1483647 baseEnd_1483647 := by
    simpa [prefixWord, tailWord_1483647, baseEnd_1483647] using wordTrace_append hprefix tailTrace_1483647
  have hstable : (prefixWord ++ tailWord_1483647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483647).length < 2 ^ (prefixWord ++ tailWord_1483647).sum := by decide
  have hdescent : baseEnd_1483647 < baseStart_1483647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483666 : List Nat := [3, 2, 3, 2, 2, 1, 1, 1, 4, 3]
def baseStart_1483666 : Nat := 118140960795 + 1483666 * 2 ^ 59
def prefixEnd_1483666 : Nat := 4983230072969 + 3 ^ 40 * 1483666 * 2
def baseEnd_1483666 : Nat := 507889192489131589101167

theorem tailTrace_1483666 : CollatzResearch.WordTrace tailWord_1483666 prefixEnd_1483666 507889192489131589101167 := by
  unfold tailWord_1483666
  simp only [CollatzResearch.WordTrace]
  refine ⟨13528436160734736706125713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36075829761959297883001901 13528436160734736706125713)
  ·
    refine ⟨10146327120551052529594285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13528436160734736706125713 10146327120551052529594285)
    ·
      refine ⟨3804872670206644698597857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10146327120551052529594285 3804872670206644698597857)
      ·
        refine ⟨2853654502654983523948393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3804872670206644698597857 2853654502654983523948393)
        ·
          refine ⟨2140240876991237642961295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2853654502654983523948393 2140240876991237642961295)
          ·
            refine ⟨3210361315486856464441943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2140240876991237642961295 3210361315486856464441943)
            ·
              refine ⟨4815541973230284696662915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3210361315486856464441943 4815541973230284696662915)
              ·
                refine ⟨7223312959845427044994373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4815541973230284696662915 7223312959845427044994373)
                ·
                  refine ⟨1354371179971017570936445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7223312959845427044994373 1354371179971017570936445)
                  ·
                    refine ⟨507889192489131589101167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1354371179971017570936445 507889192489131589101167)
                    ·
                      rfl

theorem cell22_1483666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_1483666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483666 prefixEnd_1483666 := by exact prefixLift 1483666
  have htrace : WordTrace (prefixWord ++ tailWord_1483666) baseStart_1483666 baseEnd_1483666 := by
    simpa [prefixWord, tailWord_1483666, baseEnd_1483666] using wordTrace_append hprefix tailTrace_1483666
  have hstable : (prefixWord ++ tailWord_1483666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483666).length < 2 ^ (prefixWord ++ tailWord_1483666).sum := by decide
  have hdescent : baseEnd_1483666 < baseStart_1483666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483702 : List Nat := [5, 1, 4, 1, 1, 2, 1, 3, 4]
def baseStart_1483702 : Nat := 118140960795 + 1483702 * 2 ^ 59
def prefixEnd_1483702 : Nat := 4983230072969 + 3 ^ 40 * 1483702 * 2
def baseEnd_1483702 : Nat := 169300505341613165067019

theorem tailTrace_1483702 : CollatzResearch.WordTrace tailWord_1483702 prefixEnd_1483702 169300505341613165067019 := by
  unfold tailWord_1483702
  simp only [CollatzResearch.WordTrace]
  refine ⟨3382191104425532810800835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36076705113872349981875573 3382191104425532810800835)
  ·
    refine ⟨5073286656638299216201253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3382191104425532810800835 5073286656638299216201253)
    ·
      refine ⟨951241248119681103037735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5073286656638299216201253 951241248119681103037735)
      ·
        refine ⟨1426861872179521654556603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 951241248119681103037735 1426861872179521654556603)
        ·
          refine ⟨2140292808269282481834905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1426861872179521654556603 2140292808269282481834905)
          ·
            refine ⟨1605219606201961861376179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2140292808269282481834905 1605219606201961861376179)
            ·
              refine ⟨2407829409302942792064269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1605219606201961861376179 2407829409302942792064269)
              ·
                refine ⟨902936028488603547024101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2407829409302942792064269 902936028488603547024101)
                ·
                  refine ⟨169300505341613165067019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 902936028488603547024101 169300505341613165067019)
                  ·
                    rfl

theorem cell22_1483702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_1483702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483702 prefixEnd_1483702 := by exact prefixLift 1483702
  have htrace : WordTrace (prefixWord ++ tailWord_1483702) baseStart_1483702 baseEnd_1483702 := by
    simpa [prefixWord, tailWord_1483702, baseEnd_1483702] using wordTrace_append hprefix tailTrace_1483702
  have hstable : (prefixWord ++ tailWord_1483702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483702).length < 2 ^ (prefixWord ++ tailWord_1483702).sum := by decide
  have hdescent : baseEnd_1483702 < baseStart_1483702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483741 : List Nat := [1, 4, 3, 1, 2, 1, 4, 1, 5]
def baseStart_1483741 : Nat := 118140960795 + 1483741 * 2 ^ 59
def prefixEnd_1483741 : Nat := 4983230072969 + 3 ^ 40 * 1483741 * 2
def baseEnd_1483741 : Nat := 169304955507285464491979

theorem tailTrace_1483741 : CollatzResearch.WordTrace tailWord_1483741 prefixEnd_1483741 169304955507285464491979 := by
  unfold tailWord_1483741
  simp only [CollatzResearch.WordTrace]
  refine ⟨54116480117667234633483077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36077653411778156422322051 54116480117667234633483077)
  ·
    refine ⟨10146840022062606493778077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54116480117667234633483077 10146840022062606493778077)
    ·
      refine ⟨3805065008273477435166779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10146840022062606493778077 3805065008273477435166779)
      ·
        refine ⟨5707597512410216152750169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3805065008273477435166779 5707597512410216152750169)
        ·
          refine ⟨4280698134307662114562627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5707597512410216152750169 4280698134307662114562627)
          ·
            refine ⟨6421047201461493171843941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4280698134307662114562627 6421047201461493171843941)
            ·
              refine ⟨1203946350274029969720739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6421047201461493171843941 1203946350274029969720739)
              ·
                refine ⟨1805919525411044954581109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1203946350274029969720739 1805919525411044954581109)
                ·
                  refine ⟨169304955507285464491979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1805919525411044954581109 169304955507285464491979)
                  ·
                    rfl

theorem cell22_1483741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_1483741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483741 prefixEnd_1483741 := by exact prefixLift 1483741
  have htrace : WordTrace (prefixWord ++ tailWord_1483741) baseStart_1483741 baseEnd_1483741 := by
    simpa [prefixWord, tailWord_1483741, baseEnd_1483741] using wordTrace_append hprefix tailTrace_1483741
  have hstable : (prefixWord ++ tailWord_1483741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483741).length < 2 ^ (prefixWord ++ tailWord_1483741).sum := by decide
  have hdescent : baseEnd_1483741 < baseStart_1483741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483752 : List Nat := [2, 1, 4, 1, 1, 1, 2, 4, 6]
def baseStart_1483752 : Nat := 118140960795 + 1483752 * 2 ^ 59
def prefixEnd_1483752 : Nat := 4983230072969 + 3 ^ 40 * 1483752 * 2
def baseEnd_1483752 : Nat := 169306210682218677150301

theorem tailTrace_1483752 : CollatzResearch.WordTrace tailWord_1483752 prefixEnd_1483752 169306210682218677150301 := by
  unfold tailWord_1483752
  simp only [CollatzResearch.WordTrace]
  refine ⟨27058440660313691756066755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36077920880418255674755673 27058440660313691756066755)
  ·
    refine ⟨40587660990470537634100133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27058440660313691756066755 40587660990470537634100133)
    ·
      refine ⟨7610186435713225806393775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40587660990470537634100133 7610186435713225806393775)
      ·
        refine ⟨11415279653569838709590663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7610186435713225806393775 11415279653569838709590663)
        ·
          refine ⟨17122919480354758064385995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11415279653569838709590663 17122919480354758064385995)
          ·
            refine ⟨25684379220532137096578993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17122919480354758064385995 25684379220532137096578993)
            ·
              refine ⟨19263284415399102822434245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25684379220532137096578993 19263284415399102822434245)
              ·
                refine ⟨3611865827887331779206421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19263284415399102822434245 3611865827887331779206421)
                ·
                  refine ⟨169306210682218677150301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3611865827887331779206421 169306210682218677150301)
                  ·
                    rfl

theorem cell22_1483752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 6].length) (baseStart_1483752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483752 prefixEnd_1483752 := by exact prefixLift 1483752
  have htrace : WordTrace (prefixWord ++ tailWord_1483752) baseStart_1483752 baseEnd_1483752 := by
    simpa [prefixWord, tailWord_1483752, baseEnd_1483752] using wordTrace_append hprefix tailTrace_1483752
  have hstable : (prefixWord ++ tailWord_1483752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483752).length < 2 ^ (prefixWord ++ tailWord_1483752).sum := by decide
  have hdescent : baseEnd_1483752 < baseStart_1483752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483754 : List Nat := [3, 1, 3, 1, 2, 3, 1, 1, 3, 4]
def baseStart_1483754 : Nat := 118140960795 + 1483754 * 2 ^ 59
def prefixEnd_1483754 : Nat := 4983230072969 + 3 ^ 40 * 1483754 * 2
def baseEnd_1483754 : Nat := 507919316687528692900897

theorem tailTrace_1483754 : CollatzResearch.WordTrace tailWord_1483754 prefixEnd_1483754 507919316687528692900897 := by
  unfold tailWord_1483754
  simp only [CollatzResearch.WordTrace]
  refine ⟨13529238566655034463426579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36077969511080091902470877 13529238566655034463426579)
  ·
    refine ⟨20293857849982551695139869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13529238566655034463426579 20293857849982551695139869)
    ·
      refine ⟨7610196693743456885677451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20293857849982551695139869 7610196693743456885677451)
      ·
        refine ⟨11415295040615185328516177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7610196693743456885677451 11415295040615185328516177)
        ·
          refine ⟨8561471280461388996387133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11415295040615185328516177 8561471280461388996387133)
          ·
            refine ⟨3210551730173020873645175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8561471280461388996387133 3210551730173020873645175)
            ·
              refine ⟨4815827595259531310467763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3210551730173020873645175 4815827595259531310467763)
              ·
                refine ⟨7223741392889296965701645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4815827595259531310467763 7223741392889296965701645)
                ·
                  refine ⟨2708903022333486362138117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7223741392889296965701645 2708903022333486362138117)
                  ·
                    refine ⟨507919316687528692900897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2708903022333486362138117 507919316687528692900897)
                    ·
                      rfl

theorem cell22_1483754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_1483754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483754 prefixEnd_1483754 := by exact prefixLift 1483754
  have htrace : WordTrace (prefixWord ++ tailWord_1483754) baseStart_1483754 baseEnd_1483754 := by
    simpa [prefixWord, tailWord_1483754, baseEnd_1483754] using wordTrace_append hprefix tailTrace_1483754
  have hstable : (prefixWord ++ tailWord_1483754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483754).length < 2 ^ (prefixWord ++ tailWord_1483754).sum := by decide
  have hdescent : baseEnd_1483754 < baseStart_1483754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483769 : List Nat := [1, 2, 1, 3, 1, 3, 2, 5, 4]
def baseStart_1483769 : Nat := 118140960795 + 1483769 * 2 ^ 59
def prefixEnd_1483769 : Nat := 4983230072969 + 3 ^ 40 * 1483769 * 2
def baseEnd_1483769 : Nat := 169308150498024551258617

theorem tailTrace_1483769 : CollatzResearch.WordTrace tailWord_1483769 prefixEnd_1483769 169308150498024551258617 := by
  unfold tailWord_1483769
  simp only [CollatzResearch.WordTrace]
  refine ⟨54117501361565795415502361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36078334241043863610334907 54117501361565795415502361)
  ·
    refine ⟨40588126021174346561626771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54117501361565795415502361 40588126021174346561626771)
    ·
      refine ⟨60882189031761519842440157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40588126021174346561626771 60882189031761519842440157)
      ·
        refine ⟨22830820886910569940915059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60882189031761519842440157 22830820886910569940915059)
        ·
          refine ⟨34246231330365854911372589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22830820886910569940915059 34246231330365854911372589)
          ·
            refine ⟨12842336748887195591764721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34246231330365854911372589 12842336748887195591764721)
            ·
              refine ⟨9631752561665396693823541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12842336748887195591764721 9631752561665396693823541)
              ·
                refine ⟨902976802656130940045957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9631752561665396693823541 902976802656130940045957)
                ·
                  refine ⟨169308150498024551258617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 902976802656130940045957 169308150498024551258617)
                  ·
                    rfl

theorem cell22_1483769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 5, 4].length) (baseStart_1483769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483769 prefixEnd_1483769 := by exact prefixLift 1483769
  have htrace : WordTrace (prefixWord ++ tailWord_1483769) baseStart_1483769 baseEnd_1483769 := by
    simpa [prefixWord, tailWord_1483769, baseEnd_1483769] using wordTrace_append hprefix tailTrace_1483769
  have hstable : (prefixWord ++ tailWord_1483769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483769).length < 2 ^ (prefixWord ++ tailWord_1483769).sum := by decide
  have hdescent : baseEnd_1483769 < baseStart_1483769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483786 : List Nat := [3, 1, 2, 2, 3, 2, 1, 4, 4]
def baseStart_1483786 : Nat := 118140960795 + 1483786 * 2 ^ 59
def prefixEnd_1483786 : Nat := 4983230072969 + 3 ^ 40 * 1483786 * 2
def baseEnd_1483786 : Nat := 169310090313830425366933

theorem tailTrace_1483786 : CollatzResearch.WordTrace tailWord_1483786 prefixEnd_1483786 169310090313830425366933 := by
  unfold tailWord_1483786
  simp only [CollatzResearch.WordTrace]
  refine ⟨13529530350626051829717803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36078747601669471545914141 13529530350626051829717803)
  ·
    refine ⟨20294295525939077744576705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13529530350626051829717803 20294295525939077744576705)
    ·
      refine ⟨15220721644454308308432529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20294295525939077744576705 15220721644454308308432529)
      ·
        refine ⟨11415541233340731231324397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15220721644454308308432529 11415541233340731231324397)
        ·
          refine ⟨4280827962502774211746649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11415541233340731231324397 4280827962502774211746649)
          ·
            refine ⟨3210620971877080658809987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4280827962502774211746649 3210620971877080658809987)
            ·
              refine ⟨4815931457815620988214981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3210620971877080658809987 4815931457815620988214981)
              ·
                refine ⟨902987148340428935290309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4815931457815620988214981 902987148340428935290309)
                ·
                  refine ⟨169310090313830425366933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 902987148340428935290309 169310090313830425366933)
                  ·
                    rfl

theorem cell22_1483786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 4, 4].length) (baseStart_1483786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483786 prefixEnd_1483786 := by exact prefixLift 1483786
  have htrace : WordTrace (prefixWord ++ tailWord_1483786) baseStart_1483786 baseEnd_1483786 := by
    simpa [prefixWord, tailWord_1483786, baseEnd_1483786] using wordTrace_append hprefix tailTrace_1483786
  have hstable : (prefixWord ++ tailWord_1483786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483786).length < 2 ^ (prefixWord ++ tailWord_1483786).sum := by decide
  have hdescent : baseEnd_1483786 < baseStart_1483786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483829 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 7, 3]
def baseStart_1483829 : Nat := 118140960795 + 1483829 * 2 ^ 59
def prefixEnd_1483829 : Nat := 4983230072969 + 3 ^ 40 * 1483829 * 2
def baseEnd_1483829 : Nat := 507944990720253497275667

theorem tailTrace_1483829 : CollatzResearch.WordTrace tailWord_1483829 prefixEnd_1483829 507944990720253497275667 := by
  unfold tailWord_1483829
  simp only [CollatzResearch.WordTrace]
  refine ⟨54119689741348425662686541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36079793160898950441791027 54119689741348425662686541)
  ·
    refine ⟨20294883653005659623507453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54119689741348425662686541 20294883653005659623507453)
    ·
      refine ⟨7610581369877122358815295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20294883653005659623507453 7610581369877122358815295)
      ·
        refine ⟨11415872054815683538222943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7610581369877122358815295 11415872054815683538222943)
        ·
          refine ⟨17123808082223525307334415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11415872054815683538222943 17123808082223525307334415)
          ·
            refine ⟨25685712123335287961001623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17123808082223525307334415 25685712123335287961001623)
            ·
              refine ⟨38528568185002931941502435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25685712123335287961001623 38528568185002931941502435)
              ·
                refine ⟨57792852277504397912253653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38528568185002931941502435 57792852277504397912253653)
                ·
                  refine ⟨1354519975254009326068445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 57792852277504397912253653 1354519975254009326068445)
                  ·
                    refine ⟨507944990720253497275667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1354519975254009326068445 507944990720253497275667)
                    ·
                      rfl

theorem cell22_1483829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_1483829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483829 prefixEnd_1483829 := by exact prefixLift 1483829
  have htrace : WordTrace (prefixWord ++ tailWord_1483829) baseStart_1483829 baseEnd_1483829 := by
    simpa [prefixWord, tailWord_1483829, baseEnd_1483829] using wordTrace_append hprefix tailTrace_1483829
  have hstable : (prefixWord ++ tailWord_1483829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483829).length < 2 ^ (prefixWord ++ tailWord_1483829).sum := by decide
  have hdescent : baseEnd_1483829 < baseStart_1483829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483904 : List Nat := [2, 1, 1, 2, 1, 3, 5, 1, 6]
def baseStart_1483904 : Nat := 118140960795 + 1483904 * 2 ^ 59
def prefixEnd_1483904 : Nat := 4983230072969 + 3 ^ 40 * 1483904 * 2
def baseEnd_1483904 : Nat := 169323554917659433883479

theorem tailTrace_1483904 : CollatzResearch.WordTrace tailWord_1483904 prefixEnd_1483904 169323554917659433883479 := by
  unfold tailWord_1483904
  simp only [CollatzResearch.WordTrace]
  refine ⟨27061212608038356735833383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36081616810717808981111177 27061212608038356735833383)
  ·
    refine ⟨40591818912057535103750075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27061212608038356735833383 40591818912057535103750075)
    ·
      refine ⟨60887728368086302655625113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40591818912057535103750075 60887728368086302655625113)
      ·
        refine ⟨45665796276064726991718835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60887728368086302655625113 45665796276064726991718835)
        ·
          refine ⟨68498694414097090487578253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45665796276064726991718835 68498694414097090487578253)
          ·
            refine ⟨25687010405286408932841845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68498694414097090487578253 25687010405286408932841845)
            ·
              refine ⟨2408157225495600837453923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25687010405286408932841845 2408157225495600837453923)
              ·
                refine ⟨3612235838243401256180885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2408157225495600837453923 3612235838243401256180885)
                ·
                  refine ⟨169323554917659433883479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3612235838243401256180885 169323554917659433883479)
                  ·
                    rfl

theorem cell22_1483904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 6].length) (baseStart_1483904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483904 prefixEnd_1483904 := by exact prefixLift 1483904
  have htrace : WordTrace (prefixWord ++ tailWord_1483904) baseStart_1483904 baseEnd_1483904 := by
    simpa [prefixWord, tailWord_1483904, baseEnd_1483904] using wordTrace_append hprefix tailTrace_1483904
  have hstable : (prefixWord ++ tailWord_1483904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483904).length < 2 ^ (prefixWord ++ tailWord_1483904).sum := by decide
  have hdescent : baseEnd_1483904 < baseStart_1483904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483949 : List Nat := [1, 5, 2, 1, 13]
def baseStart_1483949 : Nat := 118140960795 + 1483949 * 2 ^ 59
def prefixEnd_1483949 : Nat := 4983230072969 + 3 ^ 40 * 1483949 * 2
def baseEnd_1483949 : Nat := 2090477650916103638993

theorem tailTrace_1483949 : CollatzResearch.WordTrace tailWord_1483949 prefixEnd_1483949 2090477650916103638993 := by
  unfold tailWord_1483949
  simp only [CollatzResearch.WordTrace]
  refine ⟨54124066500913686157054901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36082711000609124104703267 54124066500913686157054901)
  ·
    refine ⟨5074131234460658077223897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54124066500913686157054901 5074131234460658077223897)
    ·
      refine ⟨3805598425845493557917923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5074131234460658077223897 3805598425845493557917923)
      ·
        refine ⟨5708397638768240336876885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3805598425845493557917923 5708397638768240336876885)
        ·
          refine ⟨2090477650916103638993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 5708397638768240336876885 2090477650916103638993)
          ·
            rfl

theorem cell22_1483949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 13].length) (baseStart_1483949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483949 prefixEnd_1483949 := by exact prefixLift 1483949
  have htrace : WordTrace (prefixWord ++ tailWord_1483949) baseStart_1483949 baseEnd_1483949 := by
    simpa [prefixWord, tailWord_1483949, baseEnd_1483949] using wordTrace_append hprefix tailTrace_1483949
  have hstable : (prefixWord ++ tailWord_1483949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483949).length < 2 ^ (prefixWord ++ tailWord_1483949).sum := by decide
  have hdescent : baseEnd_1483949 < baseStart_1483949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483953 : List Nat := [1, 2, 2, 5, 1, 1, 1, 4, 2, 3]
def baseStart_1483953 : Nat := 118140960795 + 1483953 * 2 ^ 59
def prefixEnd_1483953 : Nat := 4983230072969 + 3 ^ 40 * 1483953 * 2
def baseEnd_1483953 : Nat := 507987438454358507175287

theorem tailTrace_1483953 : CollatzResearch.WordTrace tailWord_1483953 prefixEnd_1483953 507987438454358507175287 := by
  unfold tailWord_1483953
  simp only [CollatzResearch.WordTrace]
  refine ⟨54124212392899194840200513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36082808261932796560133675 54124212392899194840200513)
  ·
    refine ⟨40593159294674396130150385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54124212392899194840200513 40593159294674396130150385)
    ·
      refine ⟨30444869471005797097612789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40593159294674396130150385 30444869471005797097612789)
      ·
        refine ⟨2854206512906793477901199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30444869471005797097612789 2854206512906793477901199)
        ·
          refine ⟨4281309769360190216851799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2854206512906793477901199 4281309769360190216851799)
          ·
            refine ⟨6421964654040285325277699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4281309769360190216851799 6421964654040285325277699)
            ·
              refine ⟨9632946981060427987916549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6421964654040285325277699 9632946981060427987916549)
              ·
                refine ⟨1806177558948830247734353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9632946981060427987916549 1806177558948830247734353)
                ·
                  refine ⟨1354633169211622685800765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1806177558948830247734353 1354633169211622685800765)
                  ·
                    refine ⟨507987438454358507175287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1354633169211622685800765 507987438454358507175287)
                    ·
                      rfl

theorem cell22_1483953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 2, 3].length) (baseStart_1483953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483953 prefixEnd_1483953 := by exact prefixLift 1483953
  have htrace : WordTrace (prefixWord ++ tailWord_1483953) baseStart_1483953 baseEnd_1483953 := by
    simpa [prefixWord, tailWord_1483953, baseEnd_1483953] using wordTrace_append hprefix tailTrace_1483953
  have hstable : (prefixWord ++ tailWord_1483953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483953).length < 2 ^ (prefixWord ++ tailWord_1483953).sum := by decide
  have hdescent : baseEnd_1483953 < baseStart_1483953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483966 : List Nat := [4, 2, 1, 1, 3, 1, 3, 7]
def baseStart_1483966 : Nat := 118140960795 + 1483966 * 2 ^ 59
def prefixEnd_1483966 : Nat := 4983230072969 + 3 ^ 40 * 1483966 * 2
def baseEnd_1483966 : Nat := 56443543180003422955583

theorem tailTrace_1483966 : CollatzResearch.WordTrace tailWord_1483966 prefixEnd_1483966 56443543180003422955583 := by
  unfold tailWord_1483966
  simp only [CollatzResearch.WordTrace]
  refine ⟨6765585817731512257552969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36083124361234732040282501 6765585817731512257552969)
  ·
    refine ⟨5074189363298634193164727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6765585817731512257552969 5074189363298634193164727)
    ·
      refine ⟨7611284044947951289747091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5074189363298634193164727 7611284044947951289747091)
      ·
        refine ⟨11416926067421926934620637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7611284044947951289747091 11416926067421926934620637)
        ·
          refine ⟨4281347275283222600482739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11416926067421926934620637 4281347275283222600482739)
          ·
            refine ⟨6422020912924833900724109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4281347275283222600482739 6422020912924833900724109)
            ·
              refine ⟨2408257842346812712771541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6422020912924833900724109 2408257842346812712771541)
              ·
                refine ⟨56443543180003422955583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2408257842346812712771541 56443543180003422955583)
                ·
                  rfl

theorem cell22_1483966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 7].length) (baseStart_1483966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483966 prefixEnd_1483966 := by exact prefixLift 1483966
  have htrace : WordTrace (prefixWord ++ tailWord_1483966) baseStart_1483966 baseEnd_1483966 := by
    simpa [prefixWord, tailWord_1483966, baseEnd_1483966] using wordTrace_append hprefix tailTrace_1483966
  have hstable : (prefixWord ++ tailWord_1483966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483966).length < 2 ^ (prefixWord ++ tailWord_1483966).sum := by decide
  have hdescent : baseEnd_1483966 < baseStart_1483966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1483994 : List Nat := [3, 1, 1, 2, 2, 1, 1, 4, 7]
def baseStart_1483994 : Nat := 118140960795 + 1483994 * 2 ^ 59
def prefixEnd_1483994 : Nat := 4983230072969 + 3 ^ 40 * 1483994 * 2
def baseEnd_1483994 : Nat := 169333824530749355633387

theorem tailTrace_1483994 : CollatzResearch.WordTrace tailWord_1483994 prefixEnd_1483994 169333824530749355633387 := by
  unfold tailWord_1483994
  simp only [CollatzResearch.WordTrace]
  refine ⟨13531426946437664710610759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36083805190500439228295357 13531426946437664710610759)
  ·
    refine ⟨20297140419656497065916139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13531426946437664710610759 20297140419656497065916139)
    ·
      refine ⟨30445710629484745598874209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20297140419656497065916139 30445710629484745598874209)
      ·
        refine ⟨22834282972113559199155657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30445710629484745598874209 22834282972113559199155657)
        ·
          refine ⟨17125712229085169399366743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22834282972113559199155657 17125712229085169399366743)
          ·
            refine ⟨25688568343627754099050115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17125712229085169399366743 25688568343627754099050115)
            ·
              refine ⟨38532852515441631148575173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25688568343627754099050115 38532852515441631148575173)
              ·
                refine ⟨7224909846645305840357845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38532852515441631148575173 7224909846645305840357845)
                ·
                  refine ⟨169333824530749355633387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7224909846645305840357845 169333824530749355633387)
                  ·
                    rfl

theorem cell22_1483994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 7].length) (baseStart_1483994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1483994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1483994 prefixEnd_1483994 := by exact prefixLift 1483994
  have htrace : WordTrace (prefixWord ++ tailWord_1483994) baseStart_1483994 baseEnd_1483994 := by
    simpa [prefixWord, tailWord_1483994, baseEnd_1483994] using wordTrace_append hprefix tailTrace_1483994
  have hstable : (prefixWord ++ tailWord_1483994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1483994).length < 2 ^ (prefixWord ++ tailWord_1483994).sum := by decide
  have hdescent : baseEnd_1483994 < baseStart_1483994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1483994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484011 : List Nat := [1, 1, 1, 1, 2, 6, 3, 2, 5]
def baseStart_1484011 : Nat := 118140960795 + 1484011 * 2 ^ 59
def prefixEnd_1484011 : Nat := 4983230072969 + 3 ^ 40 * 1484011 * 2
def baseEnd_1484011 : Nat := 169335764346555229741703

theorem tailTrace_1484011 : CollatzResearch.WordTrace tailWord_1484011 prefixEnd_1484011 169335764346555229741703 := by
  unfold tailWord_1484011
  simp only [CollatzResearch.WordTrace]
  refine ⟨54126327826689070745811887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36084218551126047163874591 54126327826689070745811887)
  ·
    refine ⟨81189491740033606118717831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54126327826689070745811887 81189491740033606118717831)
    ·
      refine ⟨121784237610050409178076747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81189491740033606118717831 121784237610050409178076747)
      ·
        refine ⟨182676356415075613767115121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121784237610050409178076747 182676356415075613767115121)
        ·
          refine ⟨137007267311306710325336341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182676356415075613767115121 137007267311306710325336341)
          ·
            refine ⟨6422215655217502046500141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 137007267311306710325336341 6422215655217502046500141)
            ·
              refine ⟨2408330870706563267437553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6422215655217502046500141 2408330870706563267437553)
              ·
                refine ⟨1806248153029922450578165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2408330870706563267437553 1806248153029922450578165)
                ·
                  refine ⟨169335764346555229741703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1806248153029922450578165 169335764346555229741703)
                  ·
                    rfl

theorem cell22_1484011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 5].length) (baseStart_1484011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484011 prefixEnd_1484011 := by exact prefixLift 1484011
  have htrace : WordTrace (prefixWord ++ tailWord_1484011) baseStart_1484011 baseEnd_1484011 := by
    simpa [prefixWord, tailWord_1484011, baseEnd_1484011] using wordTrace_append hprefix tailTrace_1484011
  have hstable : (prefixWord ++ tailWord_1484011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484011).length < 2 ^ (prefixWord ++ tailWord_1484011).sum := by decide
  have hdescent : baseEnd_1484011 < baseStart_1484011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484058 : List Nat := [3, 1, 1, 3, 3, 1, 2, 3, 1, 4]
def baseStart_1484058 : Nat := 118140960795 + 1484058 * 2 ^ 59
def prefixEnd_1484058 : Nat := 4983230072969 + 3 ^ 40 * 1484058 * 2
def baseEnd_1484058 : Nat := 508023382100173233299965

theorem tailTrace_1484058 : CollatzResearch.WordTrace tailWord_1484058 prefixEnd_1484058 508023382100173233299965 := by
  unfold tailWord_1484058
  simp only [CollatzResearch.WordTrace]
  refine ⟨13532010514379699443193207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36085361371679198515181885 13532010514379699443193207)
  ·
    refine ⟨20298015771569549164789811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13532010514379699443193207 20298015771569549164789811)
    ·
      refine ⟨30447023657354323747184717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20298015771569549164789811 30447023657354323747184717)
      ·
        refine ⟨11417633871507871405194269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30447023657354323747184717 11417633871507871405194269)
        ·
          refine ⟨4281612701815451776947851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11417633871507871405194269 4281612701815451776947851)
          ·
            refine ⟨6422419052723177665421777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4281612701815451776947851 6422419052723177665421777)
            ·
              refine ⟨4816814289542383249066333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6422419052723177665421777 4816814289542383249066333)
              ·
                refine ⟨1806305358578393718399875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4816814289542383249066333 1806305358578393718399875)
                ·
                  refine ⟨2709458037867590577599813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1806305358578393718399875 2709458037867590577599813)
                  ·
                    refine ⟨508023382100173233299965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2709458037867590577599813 508023382100173233299965)
                    ·
                      rfl

theorem cell22_1484058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 1, 4].length) (baseStart_1484058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484058 prefixEnd_1484058 := by exact prefixLift 1484058
  have htrace : WordTrace (prefixWord ++ tailWord_1484058) baseStart_1484058 baseEnd_1484058 := by
    simpa [prefixWord, tailWord_1484058, baseEnd_1484058] using wordTrace_append hprefix tailTrace_1484058
  have hstable : (prefixWord ++ tailWord_1484058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484058).length < 2 ^ (prefixWord ++ tailWord_1484058).sum := by decide
  have hdescent : baseEnd_1484058 < baseStart_1484058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484103 : List Nat := [1, 1, 4, 1, 2, 4, 2, 1, 2, 4]
def baseStart_1484103 : Nat := 118140960795 + 1484103 * 2 ^ 59
def prefixEnd_1484103 : Nat := 4983230072969 + 3 ^ 40 * 1484103 * 2
def baseEnd_1484103 : Nat := 508038786519808115924827

theorem tailTrace_1484103 : CollatzResearch.WordTrace tailWord_1484103 prefixEnd_1484103 508038786519808115924827 := by
  unfold tailWord_1484103
  simp only [CollatzResearch.WordTrace]
  refine ⟨54129683342355770458160963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36086455561570513638773975 54129683342355770458160963)
  ·
    refine ⟨81194525013533655687241445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54129683342355770458160963 81194525013533655687241445)
    ·
      refine ⟨15223973440037560441357771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81194525013533655687241445 15223973440037560441357771)
      ·
        refine ⟨22835960160056340662036657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15223973440037560441357771 22835960160056340662036657)
        ·
          refine ⟨17126970120042255496527493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22835960160056340662036657 17126970120042255496527493)
          ·
            refine ⟨3211306897507922905598905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17126970120042255496527493 3211306897507922905598905)
            ·
              refine ⟨2408480173130942179199179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3211306897507922905598905 2408480173130942179199179)
              ·
                refine ⟨3612720259696413268798769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2408480173130942179199179 3612720259696413268798769)
                ·
                  refine ⟨2709540194772309951599077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3612720259696413268798769 2709540194772309951599077)
                  ·
                    refine ⟨508038786519808115924827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2709540194772309951599077 508038786519808115924827)
                    ·
                      rfl

theorem cell22_1484103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_1484103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484103 prefixEnd_1484103 := by exact prefixLift 1484103
  have htrace : WordTrace (prefixWord ++ tailWord_1484103) baseStart_1484103 baseEnd_1484103 := by
    simpa [prefixWord, tailWord_1484103, baseEnd_1484103] using wordTrace_append hprefix tailTrace_1484103
  have hstable : (prefixWord ++ tailWord_1484103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484103).length < 2 ^ (prefixWord ++ tailWord_1484103).sum := by decide
  have hdescent : baseEnd_1484103 < baseStart_1484103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484109 : List Nat := [1, 6, 1, 3, 1, 1, 3, 1, 1, 4]
def baseStart_1484109 : Nat := 118140960795 + 1484109 * 2 ^ 59
def prefixEnd_1484109 : Nat := 4983230072969 + 3 ^ 40 * 1484109 * 2
def baseEnd_1484109 : Nat := 508040840442426100274809

theorem tailTrace_1484109 : CollatzResearch.WordTrace tailWord_1484109 prefixEnd_1484109 508040840442426100274809 := by
  unfold tailWord_1484109
  simp only [CollatzResearch.WordTrace]
  refine ⟨54129902180334033482879381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36086601453556022321919587 54129902180334033482879381)
  ·
    refine ⟨2537339164703157819509971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54129902180334033482879381 2537339164703157819509971)
    ·
      refine ⟨3806008747054736729264957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2537339164703157819509971 3806008747054736729264957)
      ·
        refine ⟨1427253280145526273474359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3806008747054736729264957 1427253280145526273474359)
        ·
          refine ⟨2140879920218289410211539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1427253280145526273474359 2140879920218289410211539)
          ·
            refine ⟨3211319880327434115317309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2140879920218289410211539 3211319880327434115317309)
            ·
              refine ⟨1204244955122787793243991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3211319880327434115317309 1204244955122787793243991)
              ·
                refine ⟨1806367432684181689865987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1204244955122787793243991 1806367432684181689865987)
                ·
                  refine ⟨2709551149026272534798981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1806367432684181689865987 2709551149026272534798981)
                  ·
                    refine ⟨508040840442426100274809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2709551149026272534798981 508040840442426100274809)
                    ·
                      rfl

theorem cell22_1484109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_1484109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484109 prefixEnd_1484109 := by exact prefixLift 1484109
  have htrace : WordTrace (prefixWord ++ tailWord_1484109) baseStart_1484109 baseEnd_1484109 := by
    simpa [prefixWord, tailWord_1484109, baseEnd_1484109] using wordTrace_append hprefix tailTrace_1484109
  have hstable : (prefixWord ++ tailWord_1484109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484109).length < 2 ^ (prefixWord ++ tailWord_1484109).sum := by decide
  have hdescent : baseEnd_1484109 < baseStart_1484109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484131 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 2, 6]
def baseStart_1484131 : Nat := 118140960795 + 1484131 * 2 ^ 59
def prefixEnd_1484131 : Nat := 4983230072969 + 3 ^ 40 * 1484131 * 2
def baseEnd_1484131 : Nat := 508048371492025376224741

theorem tailTrace_1484131 : CollatzResearch.WordTrace tailWord_1484131 prefixEnd_1484131 508048371492025376224741 := by
  unfold tailWord_1484131
  simp only [CollatzResearch.WordTrace]
  refine ⟨54130704586254331240180247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36087136390836220826786831 54130704586254331240180247)
  ·
    refine ⟨81196056879381496860270371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54130704586254331240180247 81196056879381496860270371)
    ·
      refine ⟨121794085319072245290405557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81196056879381496860270371 121794085319072245290405557)
      ·
        refine ⟨11418195498663022995975521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121794085319072245290405557 11418195498663022995975521)
        ·
          refine ⟨8563646623997267246981641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11418195498663022995975521 8563646623997267246981641)
          ·
            refine ⟨6422734967997950435236231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8563646623997267246981641 6422734967997950435236231)
            ·
              refine ⟨9634102451996925652854347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6422734967997950435236231 9634102451996925652854347)
              ·
                refine ⟨14451153677995388479281521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9634102451996925652854347 14451153677995388479281521)
                ·
                  refine ⟨10838365258496541359461141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14451153677995388479281521 10838365258496541359461141)
                  ·
                    refine ⟨508048371492025376224741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10838365258496541359461141 508048371492025376224741)
                    ·
                      rfl

theorem cell22_1484131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 6].length) (baseStart_1484131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484131 prefixEnd_1484131 := by exact prefixLift 1484131
  have htrace : WordTrace (prefixWord ++ tailWord_1484131) baseStart_1484131 baseEnd_1484131 := by
    simpa [prefixWord, tailWord_1484131, baseEnd_1484131] using wordTrace_append hprefix tailTrace_1484131
  have hstable : (prefixWord ++ tailWord_1484131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484131).length < 2 ^ (prefixWord ++ tailWord_1484131).sum := by decide
  have hdescent : baseEnd_1484131 < baseStart_1484131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484133 : List Nat := [1, 3, 1, 3, 1, 2, 2, 3, 3, 3]
def baseStart_1484133 : Nat := 118140960795 + 1484133 * 2 ^ 59
def prefixEnd_1484133 : Nat := 4983230072969 + 3 ^ 40 * 1484133 * 2
def baseEnd_1484133 : Nat := 508049056132898037674735

theorem tailTrace_1484133 : CollatzResearch.WordTrace tailWord_1484133 prefixEnd_1484133 508049056132898037674735 := by
  unfold tailWord_1484133
  simp only [CollatzResearch.WordTrace]
  refine ⟨54130777532247085581753053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36087185021498057054502035 54130777532247085581753053)
  ·
    refine ⟨20299041574592657093157395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54130777532247085581753053 20299041574592657093157395)
    ·
      refine ⟨30448562361888985639736093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20299041574592657093157395 30448562361888985639736093)
      ·
        refine ⟨11418210885708369614901035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30448562361888985639736093 11418210885708369614901035)
        ·
          refine ⟨17127316328562554422351553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11418210885708369614901035 17127316328562554422351553)
          ·
            refine ⟨12845487246421915816763665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17127316328562554422351553 12845487246421915816763665)
            ·
              refine ⟨9634115434816436862572749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12845487246421915816763665 9634115434816436862572749)
              ·
                refine ⟨3612793288056163823464781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9634115434816436862572749 3612793288056163823464781)
                ·
                  refine ⟨1354797483021061433799293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3612793288056163823464781 1354797483021061433799293)
                  ·
                    refine ⟨508049056132898037674735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1354797483021061433799293 508049056132898037674735)
                    ·
                      rfl

theorem cell22_1484133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 3, 3].length) (baseStart_1484133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484133 prefixEnd_1484133 := by exact prefixLift 1484133
  have htrace : WordTrace (prefixWord ++ tailWord_1484133) baseStart_1484133 baseEnd_1484133 := by
    simpa [prefixWord, tailWord_1484133, baseEnd_1484133] using wordTrace_append hprefix tailTrace_1484133
  have hstable : (prefixWord ++ tailWord_1484133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484133).length < 2 ^ (prefixWord ++ tailWord_1484133).sum := by decide
  have hdescent : baseEnd_1484133 < baseStart_1484133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484135 : List Nat := [1, 1, 5, 1, 5, 1, 1, 7]
def baseStart_1484135 : Nat := 118140960795 + 1484135 * 2 ^ 59
def prefixEnd_1484135 : Nat := 4983230072969 + 3 ^ 40 * 1484135 * 2
def baseEnd_1484135 : Nat := 56449971197085633236081

theorem tailTrace_1484135 : CollatzResearch.WordTrace tailWord_1484135 prefixEnd_1484135 56449971197085633236081 := by
  unfold tailWord_1484135
  simp only [CollatzResearch.WordTrace]
  refine ⟨54130850478239839923325859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36087233652159893282217239 54130850478239839923325859)
  ·
    refine ⟨81196275717359759884988789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54130850478239839923325859 81196275717359759884988789)
    ·
      refine ⟨7612150848502477489217699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81196275717359759884988789 7612150848502477489217699)
      ·
        refine ⟨11418226272753716233826549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7612150848502477489217699 11418226272753716233826549)
        ·
          refine ⟨1070458713070660896921239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11418226272753716233826549 1070458713070660896921239)
          ·
            refine ⟨1605688069605991345381859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1070458713070660896921239 1605688069605991345381859)
            ·
              refine ⟨2408532104408987018072789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1605688069605991345381859 2408532104408987018072789)
              ·
                refine ⟨56449971197085633236081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2408532104408987018072789 56449971197085633236081)
                ·
                  rfl

theorem cell22_1484135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 7].length) (baseStart_1484135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484135 prefixEnd_1484135 := by exact prefixLift 1484135
  have htrace : WordTrace (prefixWord ++ tailWord_1484135) baseStart_1484135 baseEnd_1484135 := by
    simpa [prefixWord, tailWord_1484135, baseEnd_1484135] using wordTrace_append hprefix tailTrace_1484135
  have hstable : (prefixWord ++ tailWord_1484135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484135).length < 2 ^ (prefixWord ++ tailWord_1484135).sum := by decide
  have hdescent : baseEnd_1484135 < baseStart_1484135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484167 : List Nat := [1, 1, 4, 2, 2, 3, 2, 3, 1, 3]
def baseStart_1484167 : Nat := 118140960795 + 1484167 * 2 ^ 59
def prefixEnd_1484167 : Nat := 4983230072969 + 3 ^ 40 * 1484167 * 2
def baseEnd_1484167 : Nat := 508060695027733282324631

theorem tailTrace_1484167 : CollatzResearch.WordTrace tailWord_1484167 prefixEnd_1484167 508060695027733282324631 := by
  unfold tailWord_1484167
  simp only [CollatzResearch.WordTrace]
  refine ⟨54132017614123909388490755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36088011742749272925660503 54132017614123909388490755)
  ·
    refine ⟨81198026421185864082736133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54132017614123909388490755 81198026421185864082736133)
    ·
      refine ⟨15224629953972349515513025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81198026421185864082736133 15224629953972349515513025)
      ·
        refine ⟨11418472465479262136634769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15224629953972349515513025 11418472465479262136634769)
        ·
          refine ⟨8563854349109446602476077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11418472465479262136634769 8563854349109446602476077)
          ·
            refine ⟨3211445380916042475928529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8563854349109446602476077 3211445380916042475928529)
            ·
              refine ⟨2408584035687031856946397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3211445380916042475928529 2408584035687031856946397)
              ·
                refine ⟨903219013382636946354899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2408584035687031856946397 903219013382636946354899)
                ·
                  refine ⟨1354828520073955419532349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 903219013382636946354899 1354828520073955419532349)
                  ·
                    refine ⟨508060695027733282324631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1354828520073955419532349 508060695027733282324631)
                    ·
                      rfl

theorem cell22_1484167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 3, 1, 3].length) (baseStart_1484167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484167 prefixEnd_1484167 := by exact prefixLift 1484167
  have htrace : WordTrace (prefixWord ++ tailWord_1484167) baseStart_1484167 baseEnd_1484167 := by
    simpa [prefixWord, tailWord_1484167, baseEnd_1484167] using wordTrace_append hprefix tailTrace_1484167
  have hstable : (prefixWord ++ tailWord_1484167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484167).length < 2 ^ (prefixWord ++ tailWord_1484167).sum := by decide
  have hdescent : baseEnd_1484167 < baseStart_1484167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484180 : List Nat := [2, 4, 2, 1, 2, 1, 3, 2, 5]
def baseStart_1484180 : Nat := 118140960795 + 1484180 * 2 ^ 59
def prefixEnd_1484180 : Nat := 4983230072969 + 3 ^ 40 * 1484180 * 2
def baseEnd_1484180 : Nat := 169355048397801860583197

theorem tailTrace_1484180 : CollatzResearch.WordTrace tailWord_1484180 prefixEnd_1484180 169355048397801860583197 := by
  unfold tailWord_1484180
  simp only [CollatzResearch.WordTrace]
  refine ⟨27066245881538406304356997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36088327842051208405809329 27066245881538406304356997)
  ·
    refine ⟨5074921102788451182066937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27066245881538406304356997 5074921102788451182066937)
    ·
      refine ⟨3806190827091338386550203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5074921102788451182066937 3806190827091338386550203)
      ·
        refine ⟨5709286240637007579825305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3806190827091338386550203 5709286240637007579825305)
        ·
          refine ⟨4281964680477755684868979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5709286240637007579825305 4281964680477755684868979)
          ·
            refine ⟨6422947020716633527303469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4281964680477755684868979 6422947020716633527303469)
            ·
              refine ⟨2408605132768737572738801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6422947020716633527303469 2408605132768737572738801)
              ·
                refine ⟨1806453849576553179554101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2408605132768737572738801 1806453849576553179554101)
                ·
                  refine ⟨169355048397801860583197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1806453849576553179554101 169355048397801860583197)
                  ·
                    rfl

theorem cell22_1484180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_1484180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484180 prefixEnd_1484180 := by exact prefixLift 1484180
  have htrace : WordTrace (prefixWord ++ tailWord_1484180) baseStart_1484180 baseEnd_1484180 := by
    simpa [prefixWord, tailWord_1484180, baseEnd_1484180] using wordTrace_append hprefix tailTrace_1484180
  have hstable : (prefixWord ++ tailWord_1484180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484180).length < 2 ^ (prefixWord ++ tailWord_1484180).sum := by decide
  have hdescent : baseEnd_1484180 < baseStart_1484180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484238 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 4, 4]
def baseStart_1484238 : Nat := 118140960795 + 1484238 * 2 ^ 59
def prefixEnd_1484238 : Nat := 4983230072969 + 3 ^ 40 * 1484238 * 2
def baseEnd_1484238 : Nat := 508084999778712763799413

theorem tailTrace_1484238 : CollatzResearch.WordTrace tailWord_1484238 prefixEnd_1484238 508084999778712763799413 := by
  unfold tailWord_1484238
  simp only [CollatzResearch.WordTrace]
  refine ⟨6766825899608336064290671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36089738131244459009550245 6766825899608336064290671)
  ·
    refine ⟨10150238849412504096436007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6766825899608336064290671 10150238849412504096436007)
    ·
      refine ⟨15225358274118756144654011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10150238849412504096436007 15225358274118756144654011)
      ·
        refine ⟨22838037411178134216981017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15225358274118756144654011 22838037411178134216981017)
        ·
          refine ⟨17128528058383600662735763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22838037411178134216981017 17128528058383600662735763)
          ·
            refine ⟨25692792087575400994103645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17128528058383600662735763 25692792087575400994103645)
            ·
              refine ⟨9634797032840775372788867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25692792087575400994103645 9634797032840775372788867)
              ·
                refine ⟨14452195549261163059183301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9634797032840775372788867 14452195549261163059183301)
                ·
                  refine ⟨2709786665486468073596869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14452195549261163059183301 2709786665486468073596869)
                  ·
                    refine ⟨508084999778712763799413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2709786665486468073596869 508084999778712763799413)
                    ·
                      rfl

theorem cell22_1484238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_1484238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484238 prefixEnd_1484238 := by exact prefixLift 1484238
  have htrace : WordTrace (prefixWord ++ tailWord_1484238) baseStart_1484238 baseEnd_1484238 := by
    simpa [prefixWord, tailWord_1484238, baseEnd_1484238] using wordTrace_append hprefix tailTrace_1484238
  have hstable : (prefixWord ++ tailWord_1484238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484238).length < 2 ^ (prefixWord ++ tailWord_1484238).sum := by decide
  have hdescent : baseEnd_1484238 < baseStart_1484238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484253 : List Nat := [1, 4, 3, 1, 1, 2, 1, 9]
def baseStart_1484253 : Nat := 118140960795 + 1484253 * 2 ^ 59
def prefixEnd_1484253 : Nat := 4983230072969 + 3 ^ 40 * 1484253 * 2
def baseEnd_1484253 : Nat := 56454459398361969408263

theorem tailTrace_1484253 : CollatzResearch.WordTrace tailWord_1484253 prefixEnd_1484253 56454459398361969408263 := by
  unfold tailWord_1484253
  simp only [CollatzResearch.WordTrace]
  refine ⟨54135154291812346076121413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36090102861208230717414275 54135154291812346076121413)
  ·
    refine ⟨10150341429714814889272765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54135154291812346076121413 10150341429714814889272765)
    ·
      refine ⟨3806378036143055583477287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10150341429714814889272765 3806378036143055583477287)
      ·
        refine ⟨5709567054214583375215931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3806378036143055583477287 5709567054214583375215931)
        ·
          refine ⟨8564350581321875062823897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5709567054214583375215931 8564350581321875062823897)
          ·
            refine ⟨6423262935991406297117923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8564350581321875062823897 6423262935991406297117923)
            ·
              refine ⟨9634894403987109445676885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6423262935991406297117923 9634894403987109445676885)
              ·
                refine ⟨56454459398361969408263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9634894403987109445676885 56454459398361969408263)
                ·
                  rfl

theorem cell22_1484253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 9].length) (baseStart_1484253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484253 prefixEnd_1484253 := by exact prefixLift 1484253
  have htrace : WordTrace (prefixWord ++ tailWord_1484253) baseStart_1484253 baseEnd_1484253 := by
    simpa [prefixWord, tailWord_1484253, baseEnd_1484253] using wordTrace_append hprefix tailTrace_1484253
  have hstable : (prefixWord ++ tailWord_1484253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484253).length < 2 ^ (prefixWord ++ tailWord_1484253).sum := by decide
  have hdescent : baseEnd_1484253 < baseStart_1484253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484257 : List Nat := [1, 2, 3, 1, 2, 3, 4, 1, 2, 3]
def baseStart_1484257 : Nat := 118140960795 + 1484257 * 2 ^ 59
def prefixEnd_1484257 : Nat := 4983230072969 + 3 ^ 40 * 1484257 * 2
def baseEnd_1484257 : Nat := 508091503867003047574355

theorem tailTrace_1484257 : CollatzResearch.WordTrace tailWord_1484257 prefixEnd_1484257 508091503867003047574355 := by
  unfold tailWord_1484257
  simp only [CollatzResearch.WordTrace]
  refine ⟨54135300183797854759267025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36090200122531903172844683 54135300183797854759267025)
  ·
    refine ⟨40601475137848391069450269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54135300183797854759267025 40601475137848391069450269)
    ·
      refine ⟨15225553176693146651043851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40601475137848391069450269 15225553176693146651043851)
      ·
        refine ⟨22838329765039719976565777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15225553176693146651043851 22838329765039719976565777)
        ·
          refine ⟨17128747323779789982424333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22838329765039719976565777 17128747323779789982424333)
          ·
            refine ⟨6423280246417421243409125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17128747323779789982424333 6423280246417421243409125)
            ·
              refine ⟨1204365046203266483139211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6423280246417421243409125 1204365046203266483139211)
              ·
                refine ⟨1806547569304899724708817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1204365046203266483139211 1806547569304899724708817)
                ·
                  refine ⟨1354910676978674793531613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1806547569304899724708817 1354910676978674793531613)
                  ·
                    refine ⟨508091503867003047574355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1354910676978674793531613 508091503867003047574355)
                    ·
                      rfl

theorem cell22_1484257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_1484257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484257 prefixEnd_1484257 := by exact prefixLift 1484257
  have htrace : WordTrace (prefixWord ++ tailWord_1484257) baseStart_1484257 baseEnd_1484257 := by
    simpa [prefixWord, tailWord_1484257, baseEnd_1484257] using wordTrace_append hprefix tailTrace_1484257
  have hstable : (prefixWord ++ tailWord_1484257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484257).length < 2 ^ (prefixWord ++ tailWord_1484257).sum := by decide
  have hdescent : baseEnd_1484257 < baseStart_1484257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484349 : List Nat := [1, 4, 1, 3, 4, 1, 1, 2, 5]
def baseStart_1484349 : Nat := 118140960795 + 1484349 * 2 ^ 59
def prefixEnd_1484349 : Nat := 4983230072969 + 3 ^ 40 * 1484349 * 2
def baseEnd_1484349 : Nat := 169374332449048491424691

theorem tailTrace_1484349 : CollatzResearch.WordTrace tailWord_1484349 prefixEnd_1484349 169374332449048491424691 := by
  unfold tailWord_1484349
  simp only [CollatzResearch.WordTrace]
  refine ⟨54138655699464554471616101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36092437132976369647744067 54138655699464554471616101)
  ·
    refine ⟨10150997943649603963428019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54138655699464554471616101 10150997943649603963428019)
    ·
      refine ⟨15226496915474405945142029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10150997943649603963428019 15226496915474405945142029)
      ·
        refine ⟨5709936343302902229428261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15226496915474405945142029 5709936343302902229428261)
        ·
          refine ⟨1070613064369294168017799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5709936343302902229428261 1070613064369294168017799)
          ·
            refine ⟨1605919596553941252026699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1070613064369294168017799 1605919596553941252026699)
            ·
              refine ⟨2408879394830911878040049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1605919596553941252026699 2408879394830911878040049)
              ·
                refine ⟨1806659546123183908530037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2408879394830911878040049 1806659546123183908530037)
                ·
                  refine ⟨169374332449048491424691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1806659546123183908530037 169374332449048491424691)
                  ·
                    rfl

theorem cell22_1484349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_1484349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484349 prefixEnd_1484349 := by exact prefixLift 1484349
  have htrace : WordTrace (prefixWord ++ tailWord_1484349) baseStart_1484349 baseEnd_1484349 := by
    simpa [prefixWord, tailWord_1484349, baseEnd_1484349] using wordTrace_append hprefix tailTrace_1484349
  have hstable : (prefixWord ++ tailWord_1484349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484349).length < 2 ^ (prefixWord ++ tailWord_1484349).sum := by decide
  have hdescent : baseEnd_1484349 < baseStart_1484349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484375 : List Nat := [1, 1, 3, 2, 2, 3, 3, 1, 1, 5]
def baseStart_1484375 : Nat := 118140960795 + 1484375 * 2 ^ 59
def prefixEnd_1484375 : Nat := 4983230072969 + 3 ^ 40 * 1484375 * 2
def baseEnd_1484375 : Nat := 508131897678490073123993

theorem tailTrace_1484375 : CollatzResearch.WordTrace tailWord_1484375 prefixEnd_1484375 508131897678490073123993 := by
  unfold tailWord_1484375
  simp only [CollatzResearch.WordTrace]
  refine ⟨54139603997370360912062579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36093069331580240608041719 54139603997370360912062579)
  ·
    refine ⟨81209405996055541368093869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54139603997370360912062579 81209405996055541368093869)
    ·
      refine ⟨30453527248520828013035201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81209405996055541368093869 30453527248520828013035201)
      ·
        refine ⟨22840145436390621009776401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30453527248520828013035201 22840145436390621009776401)
        ·
          refine ⟨17130109077292965757332301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22840145436390621009776401 17130109077292965757332301)
          ·
            refine ⟨6423790903984862158999613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17130109077292965757332301 6423790903984862158999613)
            ·
              refine ⟨2408921588994323309624855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6423790903984862158999613 2408921588994323309624855)
              ·
                refine ⟨3613382383491484964437283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2408921588994323309624855 3613382383491484964437283)
                ·
                  refine ⟨5420073575237227446655925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3613382383491484964437283 5420073575237227446655925)
                  ·
                    refine ⟨508131897678490073123993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5420073575237227446655925 508131897678490073123993)
                    ·
                      rfl

theorem cell22_1484375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 5].length) (baseStart_1484375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484375 prefixEnd_1484375 := by exact prefixLift 1484375
  have htrace : WordTrace (prefixWord ++ tailWord_1484375) baseStart_1484375 baseEnd_1484375 := by
    simpa [prefixWord, tailWord_1484375, baseEnd_1484375] using wordTrace_append hprefix tailTrace_1484375
  have hstable : (prefixWord ++ tailWord_1484375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484375).length < 2 ^ (prefixWord ++ tailWord_1484375).sum := by decide
  have hdescent : baseEnd_1484375 < baseStart_1484375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484392 : List Nat := [2, 1, 4, 3, 1, 1, 1, 2, 4, 3]
def baseStart_1484392 : Nat := 118140960795 + 1484392 * 2 ^ 59
def prefixEnd_1484392 : Nat := 4983230072969 + 3 ^ 40 * 1484392 * 2
def baseEnd_1484392 : Nat := 508137717125907695448941

theorem tailTrace_1484392 : CollatzResearch.WordTrace tailWord_1484392 prefixEnd_1484392 508137717125907695448941 := by
  unfold tailWord_1484392
  simp only [CollatzResearch.WordTrace]
  refine ⟨27070112019154386407715715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36093482692205848543620953 27070112019154386407715715)
  ·
    refine ⟨40605168028731579611573573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27070112019154386407715715 40605168028731579611573573)
    ·
      refine ⟨7613469005387171177170045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40605168028731579611573573 7613469005387171177170045)
      ·
        refine ⟨2855050877020189191438767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7613469005387171177170045 2855050877020189191438767)
        ·
          refine ⟨4282576315530283787158151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2855050877020189191438767 4282576315530283787158151)
          ·
            refine ⟨6423864473295425680737227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4282576315530283787158151 6423864473295425680737227)
            ·
              refine ⟨9635796709943138521105841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6423864473295425680737227 9635796709943138521105841)
              ·
                refine ⟨7226847532457353890829381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9635796709943138521105841 7226847532457353890829381)
                ·
                  refine ⟨1355033912335753854530509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7226847532457353890829381 1355033912335753854530509)
                  ·
                    refine ⟨508137717125907695448941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1355033912335753854530509 508137717125907695448941)
                    ·
                      rfl

theorem cell22_1484392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_1484392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484392 prefixEnd_1484392 := by exact prefixLift 1484392
  have htrace : WordTrace (prefixWord ++ tailWord_1484392) baseStart_1484392 baseEnd_1484392 := by
    simpa [prefixWord, tailWord_1484392, baseEnd_1484392] using wordTrace_append hprefix tailTrace_1484392
  have hstable : (prefixWord ++ tailWord_1484392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484392).length < 2 ^ (prefixWord ++ tailWord_1484392).sum := by decide
  have hdescent : baseEnd_1484392 < baseStart_1484392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484394 : List Nat := [3, 1, 3, 2, 1, 4, 1, 3, 4]
def baseStart_1484394 : Nat := 118140960795 + 1484394 * 2 ^ 59
def prefixEnd_1484394 : Nat := 4983230072969 + 3 ^ 40 * 1484394 * 2
def baseEnd_1484394 : Nat := 169379467255593452299645

theorem tailTrace_1484394 : CollatzResearch.WordTrace tailWord_1484394 prefixEnd_1484394 169379467255593452299645 := by
  unfold tailWord_1484394
  simp only [CollatzResearch.WordTrace]
  refine ⟨13535074246075381789251059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36093531322867684771336157 13535074246075381789251059)
  ·
    refine ⟨20302611369113072683876589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13535074246075381789251059 20302611369113072683876589)
    ·
      refine ⟨7613479263417402256453721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20302611369113072683876589 7613479263417402256453721)
      ·
        refine ⟨5710109447563051692340291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7613479263417402256453721 5710109447563051692340291)
        ·
          refine ⟨8565164171344577538510437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5710109447563051692340291 8565164171344577538510437)
          ·
            refine ⟨1605968282127108288470707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8565164171344577538510437 1605968282127108288470707)
            ·
              refine ⟨2408952423190662432706061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1605968282127108288470707 2408952423190662432706061)
              ·
                refine ⟨903357158696498412264773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2408952423190662432706061 903357158696498412264773)
                ·
                  refine ⟨169379467255593452299645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 903357158696498412264773 169379467255593452299645)
                  ·
                    rfl

theorem cell22_1484394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 3, 4].length) (baseStart_1484394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484394 prefixEnd_1484394 := by exact prefixLift 1484394
  have htrace : WordTrace (prefixWord ++ tailWord_1484394) baseStart_1484394 baseEnd_1484394 := by
    simpa [prefixWord, tailWord_1484394, baseEnd_1484394] using wordTrace_append hprefix tailTrace_1484394
  have hstable : (prefixWord ++ tailWord_1484394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484394).length < 2 ^ (prefixWord ++ tailWord_1484394).sum := by decide
  have hdescent : baseEnd_1484394 < baseStart_1484394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484405 : List Nat := [1, 3, 4, 2, 1, 1, 10]
def baseStart_1484405 : Nat := 118140960795 + 1484405 * 2 ^ 59
def prefixEnd_1484405 : Nat := 4983230072969 + 3 ^ 40 * 1484405 * 2
def baseEnd_1484405 : Nat := 18820080270058518328663

theorem tailTrace_1484405 : CollatzResearch.WordTrace tailWord_1484405 prefixEnd_1484405 18820080270058518328663 := by
  unfold tailWord_1484405
  simp only [CollatzResearch.WordTrace]
  refine ⟨54140698187261676035654669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36093798791507784023769779 54140698187261676035654669)
  ·
    refine ⟨20302761820223128513370501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54140698187261676035654669 20302761820223128513370501)
    ·
      refine ⟨3806767841291836596256969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20302761820223128513370501 3806767841291836596256969)
      ·
        refine ⟨2855075880968877447192727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3806767841291836596256969 2855075880968877447192727)
        ·
          refine ⟨4282613821453316170789091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2855075880968877447192727 4282613821453316170789091)
          ·
            refine ⟨6423920732179974256183637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4282613821453316170789091 6423920732179974256183637)
            ·
              refine ⟨18820080270058518328663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6423920732179974256183637 18820080270058518328663)
              ·
                rfl

theorem cell22_1484405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 10].length) (baseStart_1484405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484405 prefixEnd_1484405 := by exact prefixLift 1484405
  have htrace : WordTrace (prefixWord ++ tailWord_1484405) baseStart_1484405 baseEnd_1484405 := by
    simpa [prefixWord, tailWord_1484405, baseEnd_1484405] using wordTrace_append hprefix tailTrace_1484405
  have hstable : (prefixWord ++ tailWord_1484405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484405).length < 2 ^ (prefixWord ++ tailWord_1484405).sum := by decide
  have hdescent : baseEnd_1484405 < baseStart_1484405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484426 : List Nat := [3, 1, 2, 3, 2, 3, 2, 1, 2, 3]
def baseStart_1484426 : Nat := 118140960795 + 1484426 * 2 ^ 59
def prefixEnd_1484426 : Nat := 4983230072969 + 3 ^ 40 * 1484426 * 2
def baseEnd_1484426 : Nat := 508149356020742940098837

theorem tailTrace_1484426 : CollatzResearch.WordTrace tailWord_1484426 prefixEnd_1484426 508149356020742940098837 := by
  unfold tailWord_1484426
  simp only [CollatzResearch.WordTrace]
  refine ⟨13535366030046399155542283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36094309413457064414779421 13535366030046399155542283)
  ·
    refine ⟨20303049045069598733313425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13535366030046399155542283 20303049045069598733313425)
    ·
      refine ⟨15227286783802199049985069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20303049045069598733313425 15227286783802199049985069)
      ·
        refine ⟨5710232543925824643744401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15227286783802199049985069 5710232543925824643744401)
        ·
          refine ⟨4282674407944368482808301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5710232543925824643744401 4282674407944368482808301)
          ·
            refine ⟨1606002902979138181053113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4282674407944368482808301 1606002902979138181053113)
            ·
              refine ⟨1204502177234353635789835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1606002902979138181053113 1204502177234353635789835)
              ·
                refine ⟨1806753265851530453684753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1204502177234353635789835 1806753265851530453684753)
                ·
                  refine ⟨1355064949388647840263565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1806753265851530453684753 1355064949388647840263565)
                  ·
                    refine ⟨508149356020742940098837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1355064949388647840263565 508149356020742940098837)
                    ·
                      rfl

theorem cell22_1484426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_1484426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484426 prefixEnd_1484426 := by exact prefixLift 1484426
  have htrace : WordTrace (prefixWord ++ tailWord_1484426) baseStart_1484426 baseEnd_1484426 := by
    simpa [prefixWord, tailWord_1484426, baseEnd_1484426] using wordTrace_append hprefix tailTrace_1484426
  have hstable : (prefixWord ++ tailWord_1484426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484426).length < 2 ^ (prefixWord ++ tailWord_1484426).sum := by decide
  have hdescent : baseEnd_1484426 < baseStart_1484426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484433 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 9]
def baseStart_1484433 : Nat := 118140960795 + 1484433 * 2 ^ 59
def prefixEnd_1484433 : Nat := 4983230072969 + 3 ^ 40 * 1484433 * 2
def baseEnd_1484433 : Nat := 169383917421265751724605

theorem tailTrace_1484433 : CollatzResearch.WordTrace tailWord_1484433 prefixEnd_1484433 169383917421265751724605 := by
  unfold tailWord_1484433
  simp only [CollatzResearch.WordTrace]
  refine ⟨54141719431160236817673953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36094479620773491211782635 54141719431160236817673953)
  ·
    refine ⟨40606289573370177613255465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54141719431160236817673953 40606289573370177613255465)
    ·
      refine ⟨30454717180027633209941599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40606289573370177613255465 30454717180027633209941599)
      ·
        refine ⟨45682075770041449814912399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30454717180027633209941599 45682075770041449814912399)
        ·
          refine ⟨68523113655062174722368599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45682075770041449814912399 68523113655062174722368599)
          ·
            refine ⟨102784670482593262083552899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68523113655062174722368599 102784670482593262083552899)
            ·
              refine ⟨154177005723889893125329349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102784670482593262083552899 154177005723889893125329349)
              ·
                refine ⟨28908188573229354960999253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 154177005723889893125329349 28908188573229354960999253)
                ·
                  refine ⟨169383917421265751724605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28908188573229354960999253 169383917421265751724605)
                  ·
                    rfl

theorem cell22_1484433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 9].length) (baseStart_1484433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484433 prefixEnd_1484433 := by exact prefixLift 1484433
  have htrace : WordTrace (prefixWord ++ tailWord_1484433) baseStart_1484433 baseEnd_1484433 := by
    simpa [prefixWord, tailWord_1484433, baseEnd_1484433] using wordTrace_append hprefix tailTrace_1484433
  have hstable : (prefixWord ++ tailWord_1484433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484433).length < 2 ^ (prefixWord ++ tailWord_1484433).sum := by decide
  have hdescent : baseEnd_1484433 < baseStart_1484433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484471 : List Nat := [1, 1, 3, 1, 5, 1, 4, 2, 1, 3]
def baseStart_1484471 : Nat := 118140960795 + 1484471 * 2 ^ 59
def prefixEnd_1484471 : Nat := 4983230072969 + 3 ^ 40 * 1484471 * 2
def baseEnd_1484471 : Nat := 508164760440377822723699

theorem tailTrace_1484471 : CollatzResearch.WordTrace tailWord_1484471 prefixEnd_1484471 508164760440377822723699 := by
  unfold tailWord_1484471
  simp only [CollatzResearch.WordTrace]
  refine ⟨54143105405022569307557267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36095403603348379538371511 54143105405022569307557267)
  ·
    refine ⟨81214658107533853961335901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54143105405022569307557267 81214658107533853961335901)
    ·
      refine ⟨30455496790325195235500963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81214658107533853961335901 30455496790325195235500963)
      ·
        refine ⟨45683245185487792853251445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30455496790325195235500963 45683245185487792853251445)
        ·
          refine ⟨4282804236139480579992323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45683245185487792853251445 4282804236139480579992323)
          ·
            refine ⟨6424206354209220869988485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4282804236139480579992323 6424206354209220869988485)
            ·
              refine ⟨1204538691414228913122841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6424206354209220869988485 1204538691414228913122841)
              ·
                refine ⟨903404018560671684842131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1204538691414228913122841 903404018560671684842131)
                ·
                  refine ⟨1355106027841007527263197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 903404018560671684842131 1355106027841007527263197)
                  ·
                    refine ⟨508164760440377822723699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1355106027841007527263197 508164760440377822723699)
                    ·
                      rfl

theorem cell22_1484471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 2, 1, 3].length) (baseStart_1484471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484471 prefixEnd_1484471 := by exact prefixLift 1484471
  have htrace : WordTrace (prefixWord ++ tailWord_1484471) baseStart_1484471 baseEnd_1484471 := by
    simpa [prefixWord, tailWord_1484471, baseEnd_1484471] using wordTrace_append hprefix tailTrace_1484471
  have hstable : (prefixWord ++ tailWord_1484471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484471).length < 2 ^ (prefixWord ++ tailWord_1484471).sum := by decide
  have hdescent : baseEnd_1484471 < baseStart_1484471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484480 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 5, 4]
def baseStart_1484480 : Nat := 118140960795 + 1484480 * 2 ^ 59
def prefixEnd_1484480 : Nat := 4983230072969 + 3 ^ 40 * 1484480 * 2
def baseEnd_1484480 : Nat := 508167841324304799248671

theorem tailTrace_1484480 : CollatzResearch.WordTrace tailWord_1484480 prefixEnd_1484480 508167841324304799248671 := by
  unfold tailWord_1484480
  simp only [CollatzResearch.WordTrace]
  refine ⟨27071716830994981922317447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36095622441326642563089929 27071716830994981922317447)
  ·
    refine ⟨40607575246492472883476171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27071716830994981922317447 40607575246492472883476171)
    ·
      refine ⟨60911362869738709325214257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40607575246492472883476171 60911362869738709325214257)
      ·
        refine ⟨45683522152304031993910693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60911362869738709325214257 45683522152304031993910693)
        ·
          refine ⟨8565660403557005998858255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45683522152304031993910693 8565660403557005998858255)
          ·
            refine ⟨12848490605335508998287383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8565660403557005998858255 12848490605335508998287383)
            ·
              refine ⟨19272735908003263497431075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12848490605335508998287383 19272735908003263497431075)
              ·
                refine ⟨28909103862004895246146613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19272735908003263497431075 28909103862004895246146613)
                ·
                  refine ⟨2710228487062958929326245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28909103862004895246146613 2710228487062958929326245)
                  ·
                    refine ⟨508167841324304799248671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2710228487062958929326245 508167841324304799248671)
                    ·
                      rfl

theorem cell22_1484480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 5, 4].length) (baseStart_1484480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484480 prefixEnd_1484480 := by exact prefixLift 1484480
  have htrace : WordTrace (prefixWord ++ tailWord_1484480) baseStart_1484480 baseEnd_1484480 := by
    simpa [prefixWord, tailWord_1484480, baseEnd_1484480] using wordTrace_append hprefix tailTrace_1484480
  have hstable : (prefixWord ++ tailWord_1484480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484480).length < 2 ^ (prefixWord ++ tailWord_1484480).sum := by decide
  have hdescent : baseEnd_1484480 < baseStart_1484480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484512 : List Nat := [2, 1, 1, 3, 1, 2, 3, 5, 4]
def baseStart_1484512 : Nat := 118140960795 + 1484512 * 2 ^ 59
def prefixEnd_1484512 : Nat := 4983230072969 + 3 ^ 40 * 1484512 * 2
def baseEnd_1484512 : Nat := 169392931859422460816191

theorem tailTrace_1484512 : CollatzResearch.WordTrace tailWord_1484512 prefixEnd_1484512 169392931859422460816191 := by
  unfold tailWord_1484512
  simp only [CollatzResearch.WordTrace]
  refine ⟨27072300398937016654899895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36096400531916022206533193 27072300398937016654899895)
  ·
    refine ⟨40608450598405524982349843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27072300398937016654899895 40608450598405524982349843)
    ·
      refine ⟨60912675897608287473524765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40608450598405524982349843 60912675897608287473524765)
      ·
        refine ⟨22842253461603107802571787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60912675897608287473524765 22842253461603107802571787)
        ·
          refine ⟨34263380192404661703857681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22842253461603107802571787 34263380192404661703857681)
          ·
            refine ⟨25697535144303496277893261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34263380192404661703857681 25697535144303496277893261)
            ·
              refine ⟨9636575679113811104209973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25697535144303496277893261 9636575679113811104209973)
              ·
                refine ⟨903428969916919791019685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9636575679113811104209973 903428969916919791019685)
                ·
                  refine ⟨169392931859422460816191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 903428969916919791019685 169392931859422460816191)
                  ·
                    rfl

theorem cell22_1484512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 5, 4].length) (baseStart_1484512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484512 prefixEnd_1484512 := by exact prefixLift 1484512
  have htrace : WordTrace (prefixWord ++ tailWord_1484512) baseStart_1484512 baseEnd_1484512 := by
    simpa [prefixWord, tailWord_1484512, baseEnd_1484512] using wordTrace_append hprefix tailTrace_1484512
  have hstable : (prefixWord ++ tailWord_1484512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484512).length < 2 ^ (prefixWord ++ tailWord_1484512).sum := by decide
  have hdescent : baseEnd_1484512 < baseStart_1484512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484527 : List Nat := [1, 1, 2, 1, 5, 1, 3, 1, 4, 3]
def baseStart_1484527 : Nat := 118140960795 + 1484527 * 2 ^ 59
def prefixEnd_1484527 : Nat := 4983230072969 + 3 ^ 40 * 1484527 * 2
def baseEnd_1484527 : Nat := 508183930384812343323527

theorem tailTrace_1484527 : CollatzResearch.WordTrace tailWord_1484527 prefixEnd_1484527 508183930384812343323527 := by
  unfold tailWord_1484527
  simp only [CollatzResearch.WordTrace]
  refine ⟨54145147892819690871595835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36096765261879793914397223 54145147892819690871595835)
  ·
    refine ⟨81217721839229536307393753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54145147892819690871595835 81217721839229536307393753)
    ·
      refine ⟨60913291379422152230545315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81217721839229536307393753 60913291379422152230545315)
      ·
        refine ⟨91369937069133228345817973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60913291379422152230545315 91369937069133228345817973)
        ·
          refine ⟨8565931600231240157420435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91369937069133228345817973 8565931600231240157420435)
          ·
            refine ⟨12848897400346860236130653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8565931600231240157420435 12848897400346860236130653)
            ·
              refine ⟨4818336525130072588548995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12848897400346860236130653 4818336525130072588548995)
              ·
                refine ⟨7227504787695108882823493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4818336525130072588548995 7227504787695108882823493)
                ·
                  refine ⟨1355157147692832915529405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7227504787695108882823493 1355157147692832915529405)
                  ·
                    refine ⟨508183930384812343323527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1355157147692832915529405 508183930384812343323527)
                    ·
                      rfl

theorem cell22_1484527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 4, 3].length) (baseStart_1484527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484527 prefixEnd_1484527 := by exact prefixLift 1484527
  have htrace : WordTrace (prefixWord ++ tailWord_1484527) baseStart_1484527 baseEnd_1484527 := by
    simpa [prefixWord, tailWord_1484527, baseEnd_1484527] using wordTrace_append hprefix tailTrace_1484527
  have hstable : (prefixWord ++ tailWord_1484527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484527).length < 2 ^ (prefixWord ++ tailWord_1484527).sum := by decide
  have hdescent : baseEnd_1484527 < baseStart_1484527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484540 : List Nat := [2, 2, 2, 1, 3, 1, 2, 9]
def baseStart_1484540 : Nat := 118140960795 + 1484540 * 2 ^ 59
def prefixEnd_1484540 : Nat := 4983230072969 + 3 ^ 40 * 1484540 * 2
def baseEnd_1484540 : Nat := 56465375616720515860943

theorem tailTrace_1484540 : CollatzResearch.WordTrace tailWord_1484540 prefixEnd_1484540 56465375616720515860943 := by
  unfold tailWord_1484540
  simp only [CollatzResearch.WordTrace]
  refine ⟨27072811020886297045909537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36097081361181729394546049 27072811020886297045909537)
  ·
    refine ⟨20304608265664722784432153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27072811020886297045909537 20304608265664722784432153)
    ·
      refine ⟨15228456199248542088324115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20304608265664722784432153 15228456199248542088324115)
      ·
        refine ⟨22842684298872813132486173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15228456199248542088324115 22842684298872813132486173)
        ·
          refine ⟨8566006612077304924682315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22842684298872813132486173 8566006612077304924682315)
          ·
            refine ⟨12849009918115957387023473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8566006612077304924682315 12849009918115957387023473)
            ·
              refine ⟨9636757438586968040267605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12849009918115957387023473 9636757438586968040267605)
              ·
                refine ⟨56465375616720515860943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9636757438586968040267605 56465375616720515860943)
                ·
                  rfl

theorem cell22_1484540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 9].length) (baseStart_1484540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484540 prefixEnd_1484540 := by exact prefixLift 1484540
  have htrace : WordTrace (prefixWord ++ tailWord_1484540) baseStart_1484540 baseEnd_1484540 := by
    simpa [prefixWord, tailWord_1484540, baseEnd_1484540] using wordTrace_append hprefix tailTrace_1484540
  have hstable : (prefixWord ++ tailWord_1484540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484540).length < 2 ^ (prefixWord ++ tailWord_1484540).sum := by decide
  have hdescent : baseEnd_1484540 < baseStart_1484540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484636 : List Nat := [2, 2, 4, 2, 2, 1, 2, 2, 5]
def baseStart_1484636 : Nat := 118140960795 + 1484636 * 2 ^ 59
def prefixEnd_1484636 : Nat := 4983230072969 + 3 ^ 40 * 1484636 * 2
def baseEnd_1484636 : Nat := 169407081104124130782731

theorem tailTrace_1484636 : CollatzResearch.WordTrace tailWord_1484636 prefixEnd_1484636 169407081104124130782731 := by
  unfold tailWord_1484636
  simp only [CollatzResearch.WordTrace]
  refine ⟨27074561724712401243656881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36099415632949868324875841 27074561724712401243656881)
  ·
    refine ⟨20305921293534300932742661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27074561724712401243656881 20305921293534300932742661)
    ·
      refine ⟨3807360242537681424889249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20305921293534300932742661 3807360242537681424889249)
      ·
        refine ⟨2855520181903261068666937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3807360242537681424889249 2855520181903261068666937)
        ·
          refine ⟨2141640136427445801500203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2855520181903261068666937 2141640136427445801500203)
          ·
            refine ⟨3212460204641168702250305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2141640136427445801500203 3212460204641168702250305)
            ·
              refine ⟨2409345153480876526687729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3212460204641168702250305 2409345153480876526687729)
              ·
                refine ⟨1807008865110657395015797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2409345153480876526687729 1807008865110657395015797)
                ·
                  refine ⟨169407081104124130782731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1807008865110657395015797 169407081104124130782731)
                  ·
                    rfl

theorem cell22_1484636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 5].length) (baseStart_1484636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484636 prefixEnd_1484636 := by exact prefixLift 1484636
  have htrace : WordTrace (prefixWord ++ tailWord_1484636) baseStart_1484636 baseEnd_1484636 := by
    simpa [prefixWord, tailWord_1484636, baseEnd_1484636] using wordTrace_append hprefix tailTrace_1484636
  have hstable : (prefixWord ++ tailWord_1484636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484636).length < 2 ^ (prefixWord ++ tailWord_1484636).sum := by decide
  have hdescent : baseEnd_1484636 < baseStart_1484636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484647 : List Nat := [1, 1, 5, 1, 2, 1, 2, 3, 6]
def baseStart_1484647 : Nat := 118140960795 + 1484647 * 2 ^ 59
def prefixEnd_1484647 : Nat := 4983230072969 + 3 ^ 40 * 1484647 * 2
def baseEnd_1484647 : Nat := 169408336279057343441053

theorem tailTrace_1484647 : CollatzResearch.WordTrace tailWord_1484647 prefixEnd_1484647 169408336279057343441053 := by
  unfold tailWord_1484647
  simp only [CollatzResearch.WordTrace]
  refine ⟨54149524652384951365964195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36099683101589967577309463 54149524652384951365964195)
  ·
    refine ⟨81224286978577427048946293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54149524652384951365964195 81224286978577427048946293)
    ·
      refine ⟨7614776904241633785838715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81224286978577427048946293 7614776904241633785838715)
      ·
        refine ⟨11422165356362450678758073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7614776904241633785838715 11422165356362450678758073)
        ·
          refine ⟨8566624017271838009068555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11422165356362450678758073 8566624017271838009068555)
          ·
            refine ⟨12849936025907757013602833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8566624017271838009068555 12849936025907757013602833)
            ·
              refine ⟨9637452019430817760202125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12849936025907757013602833 9637452019430817760202125)
              ·
                refine ⟨3614044507286556660075797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9637452019430817760202125 3614044507286556660075797)
                ·
                  refine ⟨169408336279057343441053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3614044507286556660075797 169408336279057343441053)
                  ·
                    rfl

theorem cell22_1484647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 6].length) (baseStart_1484647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484647 prefixEnd_1484647 := by exact prefixLift 1484647
  have htrace : WordTrace (prefixWord ++ tailWord_1484647) baseStart_1484647 baseEnd_1484647 := by
    simpa [prefixWord, tailWord_1484647, baseEnd_1484647] using wordTrace_append hprefix tailTrace_1484647
  have hstable : (prefixWord ++ tailWord_1484647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484647).length < 2 ^ (prefixWord ++ tailWord_1484647).sum := by decide
  have hdescent : baseEnd_1484647 < baseStart_1484647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484677 : List Nat := [1, 3, 1, 1, 3, 2, 3, 1, 1, 6]
def baseStart_1484677 : Nat := 118140960795 + 1484677 * 2 ^ 59
def prefixEnd_1484677 : Nat := 4983230072969 + 3 ^ 40 * 1484677 * 2
def baseEnd_1484677 : Nat := 508235278450261952073067

theorem tailTrace_1484677 : CollatzResearch.WordTrace tailWord_1484677 prefixEnd_1484677 508235278450261952073067 := by
  unfold tailWord_1484677
  simp only [CollatzResearch.WordTrace]
  refine ⟨54150618842276266489556285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36100412561517510993037523 54150618842276266489556285)
  ·
    refine ⟨20306482065853599933583607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54150618842276266489556285 20306482065853599933583607)
    ·
      refine ⟨30459723098780399900375411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20306482065853599933583607 30459723098780399900375411)
      ·
        refine ⟨45689584648170599850563117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30459723098780399900375411 45689584648170599850563117)
        ·
          refine ⟨17133594243063974943961169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45689584648170599850563117 17133594243063974943961169)
          ·
            refine ⟨12850195682297981207970877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17133594243063974943961169 12850195682297981207970877)
            ·
              refine ⟨4818823380861742952989079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12850195682297981207970877 4818823380861742952989079)
              ·
                refine ⟨7228235071292614429483619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4818823380861742952989079 7228235071292614429483619)
                ·
                  refine ⟨10842352606938921644225429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7228235071292614429483619 10842352606938921644225429)
                  ·
                    refine ⟨508235278450261952073067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10842352606938921644225429 508235278450261952073067)
                    ·
                      rfl

theorem cell22_1484677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_1484677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484677 prefixEnd_1484677 := by exact prefixLift 1484677
  have htrace : WordTrace (prefixWord ++ tailWord_1484677) baseStart_1484677 baseEnd_1484677 := by
    simpa [prefixWord, tailWord_1484677, baseEnd_1484677] using wordTrace_append hprefix tailTrace_1484677
  have hstable : (prefixWord ++ tailWord_1484677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484677).length < 2 ^ (prefixWord ++ tailWord_1484677).sum := by decide
  have hdescent : baseEnd_1484677 < baseStart_1484677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484722 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 2, 6]
def baseStart_1484722 : Nat := 118140960795 + 1484722 * 2 ^ 59
def prefixEnd_1484722 : Nat := 4983230072969 + 3 ^ 40 * 1484722 * 2
def baseEnd_1484722 : Nat := 508250682869896834697929

theorem tailTrace_1484722 : CollatzResearch.WordTrace tailWord_1484722 prefixEnd_1484722 508250682869896834697929 := by
  unfold tailWord_1484722
  simp only [CollatzResearch.WordTrace]
  refine ⟨13538065031778309793736105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36101506751408826116629613 13538065031778309793736105)
  ·
    refine ⟨10153548773833732345302079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13538065031778309793736105 10153548773833732345302079)
    ·
      refine ⟨15230323160750598517953119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10153548773833732345302079 15230323160750598517953119)
      ·
        refine ⟨22845484741125897776929679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15230323160750598517953119 22845484741125897776929679)
        ·
          refine ⟨34268227111688846665394519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22845484741125897776929679 34268227111688846665394519)
          ·
            refine ⟨51402340667533269998091779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34268227111688846665394519 51402340667533269998091779)
            ·
              refine ⟨77103511001299904997137669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51402340667533269998091779 77103511001299904997137669)
              ·
                refine ⟨14456908312743732186963313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77103511001299904997137669 14456908312743732186963313)
                ·
                  refine ⟨10842681234557799140222485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14456908312743732186963313 10842681234557799140222485)
                  ·
                    refine ⟨508250682869896834697929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10842681234557799140222485 508250682869896834697929)
                    ·
                      rfl

theorem cell22_1484722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_1484722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484722 prefixEnd_1484722 := by exact prefixLift 1484722
  have htrace : WordTrace (prefixWord ++ tailWord_1484722) baseStart_1484722 baseEnd_1484722 := by
    simpa [prefixWord, tailWord_1484722, baseEnd_1484722] using wordTrace_append hprefix tailTrace_1484722
  have hstable : (prefixWord ++ tailWord_1484722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484722).length < 2 ^ (prefixWord ++ tailWord_1484722).sum := by decide
  have hdescent : baseEnd_1484722 < baseStart_1484722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484741 : List Nat := [1, 3, 1, 1, 1, 1, 1, 9, 1, 3]
def baseStart_1484741 : Nat := 118140960795 + 1484741 * 2 ^ 59
def prefixEnd_1484741 : Nat := 4983230072969 + 3 ^ 40 * 1484741 * 2
def baseEnd_1484741 : Nat := 508257186958187118472871

theorem tailTrace_1484741 : CollatzResearch.WordTrace tailWord_1484741 prefixEnd_1484741 508257186958187118472871 := by
  unfold tailWord_1484741
  simp only [CollatzResearch.WordTrace]
  refine ⟨54152953114044405419886077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36101968742696270279924051 54152953114044405419886077)
  ·
    refine ⟨20307357417766652032457279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54152953114044405419886077 20307357417766652032457279)
    ·
      refine ⟨30461036126649978048685919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20307357417766652032457279 30461036126649978048685919)
      ·
        refine ⟨45691554189974967073028879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30461036126649978048685919 45691554189974967073028879)
        ·
          refine ⟨68537331284962450609543319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45691554189974967073028879 68537331284962450609543319)
          ·
            refine ⟨102805996927443675914314979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68537331284962450609543319 102805996927443675914314979)
            ·
              refine ⟨154208995391165513871472469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102805996927443675914314979 154208995391165513871472469)
              ·
                refine ⟨903568332370110432840659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 154208995391165513871472469 903568332370110432840659)
                ·
                  refine ⟨1355352498555165649260989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 903568332370110432840659 1355352498555165649260989)
                  ·
                    refine ⟨508257186958187118472871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1355352498555165649260989 508257186958187118472871)
                    ·
                      rfl

theorem cell22_1484741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 9, 1, 3].length) (baseStart_1484741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484741 prefixEnd_1484741 := by exact prefixLift 1484741
  have htrace : WordTrace (prefixWord ++ tailWord_1484741) baseStart_1484741 baseEnd_1484741 := by
    simpa [prefixWord, tailWord_1484741, baseEnd_1484741] using wordTrace_append hprefix tailTrace_1484741
  have hstable : (prefixWord ++ tailWord_1484741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484741).length < 2 ^ (prefixWord ++ tailWord_1484741).sum := by decide
  have hdescent : baseEnd_1484741 < baseStart_1484741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484752 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 4, 5]
def baseStart_1484752 : Nat := 118140960795 + 1484752 * 2 ^ 59
def prefixEnd_1484752 : Nat := 4983230072969 + 3 ^ 40 * 1484752 * 2
def baseEnd_1484752 : Nat := 508260952482986756447837

theorem tailTrace_1484752 : CollatzResearch.WordTrace tailWord_1484752 prefixEnd_1484752 508260952482986756447837 := by
  unfold tailWord_1484752
  simp only [CollatzResearch.WordTrace]
  refine ⟨27076677158502277149268255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36102236211336369532357673 27076677158502277149268255)
  ·
    refine ⟨40615015737753415723902383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27076677158502277149268255 40615015737753415723902383)
    ·
      refine ⟨60922523606630123585853575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40615015737753415723902383 60922523606630123585853575)
      ·
        refine ⟨91383785409945185378780363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60922523606630123585853575 91383785409945185378780363)
        ·
          refine ⟨137075678114917778068170545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91383785409945185378780363 137075678114917778068170545)
          ·
            refine ⟨102806758586188333551127909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137075678114917778068170545 102806758586188333551127909)
            ·
              refine ⟨19276267234910312540836483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102806758586188333551127909 19276267234910312540836483)
              ·
                refine ⟨28914400852365468811254725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19276267234910312540836483 28914400852365468811254725)
                ·
                  refine ⟨5421450159818525402110261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28914400852365468811254725 5421450159818525402110261)
                  ·
                    refine ⟨508260952482986756447837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5421450159818525402110261 508260952482986756447837)
                    ·
                      rfl

theorem cell22_1484752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 4, 5].length) (baseStart_1484752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484752 prefixEnd_1484752 := by exact prefixLift 1484752
  have htrace : WordTrace (prefixWord ++ tailWord_1484752) baseStart_1484752 baseEnd_1484752 := by
    simpa [prefixWord, tailWord_1484752, baseEnd_1484752] using wordTrace_append hprefix tailTrace_1484752
  have hstable : (prefixWord ++ tailWord_1484752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484752).length < 2 ^ (prefixWord ++ tailWord_1484752).sum := by decide
  have hdescent : baseEnd_1484752 < baseStart_1484752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484764 : List Nat := [2, 2, 6, 1, 1, 2, 2, 1, 2, 3]
def baseStart_1484764 : Nat := 118140960795 + 1484764 * 2 ^ 59
def prefixEnd_1484764 : Nat := 4983230072969 + 3 ^ 40 * 1484764 * 2
def baseEnd_1484764 : Nat := 508265060328222725147801

theorem tailTrace_1484764 : CollatzResearch.WordTrace tailWord_1484764 prefixEnd_1484764 508265060328222725147801 := by
  unfold tailWord_1484764
  simp only [CollatzResearch.WordTrace]
  refine ⟨27076895996480540173986673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36102527995307386898648897 27076895996480540173986673)
  ·
    refine ⟨20307671997360405130490005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27076895996480540173986673 20307671997360405130490005)
    ·
      refine ⟨951922124876268990491719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20307671997360405130490005 951922124876268990491719)
      ·
        refine ⟨1427883187314403485737579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 951922124876268990491719 1427883187314403485737579)
        ·
          refine ⟨2141824780971605228606369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1427883187314403485737579 2141824780971605228606369)
          ·
            refine ⟨1606368585728703921454777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2141824780971605228606369 1606368585728703921454777)
            ·
              refine ⟨1204776439296527941091083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1606368585728703921454777 1204776439296527941091083)
              ·
                refine ⟨1807164658944791911636625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1204776439296527941091083 1807164658944791911636625)
                ·
                  refine ⟨1355373494208593933727469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1807164658944791911636625 1355373494208593933727469)
                  ·
                    refine ⟨508265060328222725147801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1355373494208593933727469 508265060328222725147801)
                    ·
                      rfl

theorem cell22_1484764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_1484764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484764 prefixEnd_1484764 := by exact prefixLift 1484764
  have htrace : WordTrace (prefixWord ++ tailWord_1484764) baseStart_1484764 baseEnd_1484764 := by
    simpa [prefixWord, tailWord_1484764, baseEnd_1484764] using wordTrace_append hprefix tailTrace_1484764
  have hstable : (prefixWord ++ tailWord_1484764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484764).length < 2 ^ (prefixWord ++ tailWord_1484764).sum := by decide
  have hdescent : baseEnd_1484764 < baseStart_1484764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484771 : List Nat := [1, 1, 1, 6, 1, 2, 4, 1, 5]
def baseStart_1484771 : Nat := 118140960795 + 1484771 * 2 ^ 59
def prefixEnd_1484771 : Nat := 4983230072969 + 3 ^ 40 * 1484771 * 2
def baseEnd_1484771 : Nat := 169422485523759013407593

theorem tailTrace_1484771 : CollatzResearch.WordTrace tailWord_1484771 prefixEnd_1484771 169422485523759013407593 := by
  unfold tailWord_1484771
  simp only [CollatzResearch.WordTrace]
  refine ⟨54154047303935720543478167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36102698202623813695652111 54154047303935720543478167)
  ·
    refine ⟨81231070955903580815217251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54154047303935720543478167 81231070955903580815217251)
    ·
      refine ⟨121846606433855371222825877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81231070955903580815217251 121846606433855371222825877)
      ·
        refine ⟨5711559676586970526069963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 121846606433855371222825877 5711559676586970526069963)
        ·
          refine ⟨8567339514880455789104945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5711559676586970526069963 8567339514880455789104945)
          ·
            refine ⟨6425504636160341841828709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8567339514880455789104945 6425504636160341841828709)
            ·
              refine ⟨1204782119280064095342883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6425504636160341841828709 1204782119280064095342883)
              ·
                refine ⟨1807173178920096143014325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1204782119280064095342883 1807173178920096143014325)
                ·
                  refine ⟨169422485523759013407593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1807173178920096143014325 169422485523759013407593)
                  ·
                    rfl

theorem cell22_1484771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 5].length) (baseStart_1484771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484771 prefixEnd_1484771 := by exact prefixLift 1484771
  have htrace : WordTrace (prefixWord ++ tailWord_1484771) baseStart_1484771 baseEnd_1484771 := by
    simpa [prefixWord, tailWord_1484771, baseEnd_1484771] using wordTrace_append hprefix tailTrace_1484771
  have hstable : (prefixWord ++ tailWord_1484771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484771).length < 2 ^ (prefixWord ++ tailWord_1484771).sum := by decide
  have hdescent : baseEnd_1484771 < baseStart_1484771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484814 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 3, 5]
def baseStart_1484814 : Nat := 118140960795 + 1484814 * 2 ^ 59
def prefixEnd_1484814 : Nat := 4983230072969 + 3 ^ 40 * 1484814 * 2
def baseEnd_1484814 : Nat := 508282176350039261397647

theorem tailTrace_1484814 : CollatzResearch.WordTrace tailWord_1484814 prefixEnd_1484814 508282176350039261397647 := by
  unfold tailWord_1484814
  simp only [CollatzResearch.WordTrace]
  refine ⟨6769451955347492360911687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36103743761853292591528997 6769451955347492360911687)
  ·
    refine ⟨10154177933021238541367531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6769451955347492360911687 10154177933021238541367531)
    ·
      refine ⟨15231266899531857812051297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10154177933021238541367531 15231266899531857812051297)
      ·
        refine ⟨11423450174648893359038473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15231266899531857812051297 11423450174648893359038473)
        ·
          refine ⟨8567587630986670019278855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11423450174648893359038473 8567587630986670019278855)
          ·
            refine ⟨12851381446480005028918283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8567587630986670019278855 12851381446480005028918283)
            ·
              refine ⟨19277072169720007543377425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12851381446480005028918283 19277072169720007543377425)
              ·
                refine ⟨14457804127290005657533069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19277072169720007543377425 14457804127290005657533069)
                ·
                  refine ⟨5421676547733752121574901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14457804127290005657533069 5421676547733752121574901)
                  ·
                    refine ⟨508282176350039261397647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5421676547733752121574901 508282176350039261397647)
                    ·
                      rfl

theorem cell22_1484814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_1484814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484814 prefixEnd_1484814 := by exact prefixLift 1484814
  have htrace : WordTrace (prefixWord ++ tailWord_1484814) baseStart_1484814 baseEnd_1484814 := by
    simpa [prefixWord, tailWord_1484814, baseEnd_1484814] using wordTrace_append hprefix tailTrace_1484814
  have hstable : (prefixWord ++ tailWord_1484814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484814).length < 2 ^ (prefixWord ++ tailWord_1484814).sum := by decide
  have hdescent : baseEnd_1484814 < baseStart_1484814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484827 : List Nat := [1, 1, 1, 1, 1, 1, 3, 13]
def baseStart_1484827 : Nat := 118140960795 + 1484827 * 2 ^ 59
def prefixEnd_1484827 : Nat := 4983230072969 + 3 ^ 40 * 1484827 * 2
def baseEnd_1484827 : Nat := 56476291835079062313623

theorem tailTrace_1484827 : CollatzResearch.WordTrace tailWord_1484827 prefixEnd_1484827 56476291835079062313623 := by
  unfold tailWord_1484827
  simp only [CollatzResearch.WordTrace]
  refine ⟨54156089791732842107516735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36104059861155228071677823 54156089791732842107516735)
  ·
    refine ⟨81234134687599263161275103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54156089791732842107516735 81234134687599263161275103)
    ·
      refine ⟨121851202031398894741912655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81234134687599263161275103 121851202031398894741912655)
      ·
        refine ⟨182776803047098342112868983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121851202031398894741912655 182776803047098342112868983)
        ·
          refine ⟨274165204570647513169303475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182776803047098342112868983 274165204570647513169303475)
          ·
            refine ⟨411247806855971269753955213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274165204570647513169303475 411247806855971269753955213)
            ·
              refine ⟨154217927570989226157733205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 411247806855971269753955213 154217927570989226157733205)
              ·
                refine ⟨56476291835079062313623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 154217927570989226157733205 56476291835079062313623)
                ·
                  rfl

theorem cell22_1484827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 13].length) (baseStart_1484827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484827 prefixEnd_1484827 := by exact prefixLift 1484827
  have htrace : WordTrace (prefixWord ++ tailWord_1484827) baseStart_1484827 baseEnd_1484827 := by
    simpa [prefixWord, tailWord_1484827, baseEnd_1484827] using wordTrace_append hprefix tailTrace_1484827
  have hstable : (prefixWord ++ tailWord_1484827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484827).length < 2 ^ (prefixWord ++ tailWord_1484827).sum := by decide
  have hdescent : baseEnd_1484827 < baseStart_1484827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484831 : List Nat := [1, 1, 2, 4, 1, 2, 1, 5, 2, 3]
def baseStart_1484831 : Nat := 118140960795 + 1484831 * 2 ^ 59
def prefixEnd_1484831 : Nat := 4983230072969 + 3 ^ 40 * 1484831 * 2
def baseEnd_1484831 : Nat := 508287995797456883722595

theorem tailTrace_1484831 : CollatzResearch.WordTrace tailWord_1484831 prefixEnd_1484831 508287995797456883722595 := by
  unfold tailWord_1484831
  simp only [CollatzResearch.WordTrace]
  refine ⟨54156235683718350790662347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36104157122478900527108231 54156235683718350790662347)
  ·
    refine ⟨81234353525577526185993521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54156235683718350790662347 81234353525577526185993521)
    ·
      refine ⟨60925765144183144639495141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81234353525577526185993521 60925765144183144639495141)
      ·
        refine ⟨11423580964534339619905339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60925765144183144639495141 11423580964534339619905339)
        ·
          refine ⟨17135371446801509429858009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11423580964534339619905339 17135371446801509429858009)
          ·
            refine ⟨12851528585101132072393507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17135371446801509429858009 12851528585101132072393507)
            ·
              refine ⟨19277292877651698108590261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12851528585101132072393507 19277292877651698108590261)
              ·
                refine ⟨1807246207279846697680337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19277292877651698108590261 1807246207279846697680337)
                ·
                  refine ⟨1355434655459885023260253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1807246207279846697680337 1355434655459885023260253)
                  ·
                    refine ⟨508287995797456883722595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1355434655459885023260253 508287995797456883722595)
                    ·
                      rfl

theorem cell22_1484831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 2, 3].length) (baseStart_1484831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484831 prefixEnd_1484831 := by exact prefixLift 1484831
  have htrace : WordTrace (prefixWord ++ tailWord_1484831) baseStart_1484831 baseEnd_1484831 := by
    simpa [prefixWord, tailWord_1484831, baseEnd_1484831] using wordTrace_append hprefix tailTrace_1484831
  have hstable : (prefixWord ++ tailWord_1484831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484831).length < 2 ^ (prefixWord ++ tailWord_1484831).sum := by decide
  have hdescent : baseEnd_1484831 < baseStart_1484831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484846 : List Nat := [4, 1, 3, 1, 1, 3, 1, 1, 1, 6]
def baseStart_1484846 : Nat := 118140960795 + 1484846 * 2 ^ 59
def prefixEnd_1484846 : Nat := 4983230072969 + 3 ^ 40 * 1484846 * 2
def baseEnd_1484846 : Nat := 508293130604001844597549

theorem tailTrace_1484846 : CollatzResearch.WordTrace tailWord_1484846 prefixEnd_1484846 508293130604001844597549 := by
  unfold tailWord_1484846
  simp only [CollatzResearch.WordTrace]
  refine ⟨6769597847333001044057299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36104521852442672234972261 6769597847333001044057299)
  ·
    refine ⟨10154396770999501566085949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6769597847333001044057299 10154396770999501566085949)
    ·
      refine ⟨3807898789124813087282231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10154396770999501566085949 3807898789124813087282231)
      ·
        refine ⟨5711848183687219630923347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3807898789124813087282231 5711848183687219630923347)
        ·
          refine ⟨8567772275530829446385021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5711848183687219630923347 8567772275530829446385021)
          ·
            refine ⟨3212914603324061042394383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8567772275530829446385021 3212914603324061042394383)
            ·
              refine ⟨4819371904986091563591575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3212914603324061042394383 4819371904986091563591575)
              ·
                refine ⟨7229057857479137345387363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4819371904986091563591575 7229057857479137345387363)
                ·
                  refine ⟨10843586786218706018081045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7229057857479137345387363 10843586786218706018081045)
                  ·
                    refine ⟨508293130604001844597549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10843586786218706018081045 508293130604001844597549)
                    ·
                      rfl

theorem cell22_1484846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_1484846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484846 prefixEnd_1484846 := by exact prefixLift 1484846
  have htrace : WordTrace (prefixWord ++ tailWord_1484846) baseStart_1484846 baseEnd_1484846 := by
    simpa [prefixWord, tailWord_1484846, baseEnd_1484846] using wordTrace_append hprefix tailTrace_1484846
  have hstable : (prefixWord ++ tailWord_1484846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484846).length < 2 ^ (prefixWord ++ tailWord_1484846).sum := by decide
  have hdescent : baseEnd_1484846 < baseStart_1484846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484852 : List Nat := [2, 5, 1, 2, 2, 2, 2, 1, 1, 4]
def baseStart_1484852 : Nat := 118140960795 + 1484852 * 2 ^ 59
def prefixEnd_1484852 : Nat := 4983230072969 + 3 ^ 40 * 1484852 * 2
def baseEnd_1484852 : Nat := 508295184526619828947531

theorem tailTrace_1484852 : CollatzResearch.WordTrace tailWord_1484852 prefixEnd_1484852 508295184526619828947531 := by
  unfold tailWord_1484852
  simp only [CollatzResearch.WordTrace]
  refine ⟨27078500808321135688588405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36104667744428180918117873 27078500808321135688588405)
  ·
    refine ⟨2538609450780106470805163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27078500808321135688588405 2538609450780106470805163)
    ·
      refine ⟨3807914176170159706207745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2538609450780106470805163 3807914176170159706207745)
      ·
        refine ⟨2855935632127619779655809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3807914176170159706207745 2855935632127619779655809)
        ·
          refine ⟨2141951724095714834741857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2855935632127619779655809 2141951724095714834741857)
          ·
            refine ⟨1606463793071786126056393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2141951724095714834741857 1606463793071786126056393)
            ·
              refine ⟨1204847844803839594542295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1606463793071786126056393 1204847844803839594542295)
              ·
                refine ⟨1807271767205759391813443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1204847844803839594542295 1807271767205759391813443)
                ·
                  refine ⟨2710907650808639087720165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1807271767205759391813443 2710907650808639087720165)
                  ·
                    refine ⟨508295184526619828947531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2710907650808639087720165 508295184526619828947531)
                    ·
                      rfl

theorem cell22_1484852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_1484852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484852 prefixEnd_1484852 := by exact prefixLift 1484852
  have htrace : WordTrace (prefixWord ++ tailWord_1484852) baseStart_1484852 baseEnd_1484852 := by
    simpa [prefixWord, tailWord_1484852, baseEnd_1484852] using wordTrace_append hprefix tailTrace_1484852
  have hstable : (prefixWord ++ tailWord_1484852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484852).length < 2 ^ (prefixWord ++ tailWord_1484852).sum := by decide
  have hdescent : baseEnd_1484852 < baseStart_1484852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484865 : List Nat := [1, 2, 5, 1, 2, 3, 1, 2, 2, 3]
def baseStart_1484865 : Nat := 118140960795 + 1484865 * 2 ^ 59
def prefixEnd_1484865 : Nat := 4983230072969 + 3 ^ 40 * 1484865 * 2
def baseEnd_1484865 : Nat := 508299634692292128372491

theorem tailTrace_1484865 : CollatzResearch.WordTrace tailWord_1484865 prefixEnd_1484865 508299634692292128372491 := by
  unfold tailWord_1484865
  simp only [CollatzResearch.WordTrace]
  refine ⟨54157475765595174597400049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36104983843730116398266699 54157475765595174597400049)
  ·
    refine ⟨40618106824196380948050037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54157475765595174597400049 40618106824196380948050037)
    ·
      refine ⟨3807947514768410713879691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40618106824196380948050037 3807947514768410713879691)
      ·
        refine ⟨5711921272152616070819537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3807947514768410713879691 5711921272152616070819537)
        ·
          refine ⟨4283940954114462053114653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5711921272152616070819537 4283940954114462053114653)
          ·
            refine ⟨1606477857792923269917995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4283940954114462053114653 1606477857792923269917995)
            ·
              refine ⟨2409716786689384904876993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1606477857792923269917995 2409716786689384904876993)
              ·
                refine ⟨1807287590017038678657745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2409716786689384904876993 1807287590017038678657745)
                ·
                  refine ⟨1355465692512779008993309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1807287590017038678657745 1355465692512779008993309)
                  ·
                    refine ⟨508299634692292128372491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1355465692512779008993309 508299634692292128372491)
                    ·
                      rfl

theorem cell22_1484865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_1484865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484865 prefixEnd_1484865 := by exact prefixLift 1484865
  have htrace : WordTrace (prefixWord ++ tailWord_1484865) baseStart_1484865 baseEnd_1484865 := by
    simpa [prefixWord, tailWord_1484865, baseEnd_1484865] using wordTrace_append hprefix tailTrace_1484865
  have hstable : (prefixWord ++ tailWord_1484865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484865).length < 2 ^ (prefixWord ++ tailWord_1484865).sum := by decide
  have hdescent : baseEnd_1484865 < baseStart_1484865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484876 : List Nat := [2, 2, 1, 3, 1, 1, 3, 3, 3, 3]
def baseStart_1484876 : Nat := 118140960795 + 1484876 * 2 ^ 59
def prefixEnd_1484876 : Nat := 4983230072969 + 3 ^ 40 * 1484876 * 2
def baseEnd_1484876 : Nat := 508303400217091766347457

theorem tailTrace_1484876 : CollatzResearch.WordTrace tailWord_1484876 prefixEnd_1484876 508303400217091766347457 := by
  unfold tailWord_1484876
  simp only [CollatzResearch.WordTrace]
  refine ⟨27078938484277661738025241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36105251312370215650700321 27078938484277661738025241)
  ·
    refine ⟨20309203863208246303518931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27078938484277661738025241 20309203863208246303518931)
    ·
      refine ⟨30463805794812369455278397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20309203863208246303518931 30463805794812369455278397)
      ·
        refine ⟨11423927173054638545729399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30463805794812369455278397 11423927173054638545729399)
        ·
          refine ⟨17135890759581957818594099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11423927173054638545729399 17135890759581957818594099)
          ·
            refine ⟨25703836139372936727891149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17135890759581957818594099 25703836139372936727891149)
            ·
              refine ⟨9638938552264851272959181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25703836139372936727891149 9638938552264851272959181)
              ·
                refine ⟨3614601957099319227359693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9638938552264851272959181 3614601957099319227359693)
                ·
                  refine ⟨1355475733912244710259885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3614601957099319227359693 1355475733912244710259885)
                  ·
                    refine ⟨508303400217091766347457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1355475733912244710259885 508303400217091766347457)
                    ·
                      rfl

theorem cell22_1484876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 3, 3].length) (baseStart_1484876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484876 prefixEnd_1484876 := by exact prefixLift 1484876
  have htrace : WordTrace (prefixWord ++ tailWord_1484876) baseStart_1484876 baseEnd_1484876 := by
    simpa [prefixWord, tailWord_1484876, baseEnd_1484876] using wordTrace_append hprefix tailTrace_1484876
  have hstable : (prefixWord ++ tailWord_1484876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484876).length < 2 ^ (prefixWord ++ tailWord_1484876).sum := by decide
  have hdescent : baseEnd_1484876 < baseStart_1484876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1484983 : List Nat := [1, 1, 3, 1, 4, 2, 1, 4, 2, 3]
def baseStart_1484983 : Nat := 118140960795 + 1484983 * 2 ^ 59
def prefixEnd_1484983 : Nat := 4983230072969 + 3 ^ 40 * 1484983 * 2
def baseEnd_1484983 : Nat := 508340028503779153922129

theorem tailTrace_1484983 : CollatzResearch.WordTrace tailWord_1484983 prefixEnd_1484983 508340028503779153922129 := by
  unfold tailWord_1484983
  simp only [CollatzResearch.WordTrace]
  refine ⟨54161779579167680750195603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36107853052778453833463735 54161779579167680750195603)
  ·
    refine ⟨81242669368751521125293405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54161779579167680750195603 81242669368751521125293405)
    ·
      refine ⟨30466001013281820421985027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81242669368751521125293405 30466001013281820421985027)
      ·
        refine ⟨45699001519922730632977541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30466001013281820421985027 45699001519922730632977541)
        ·
          refine ⟨8568562784985511993683289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45699001519922730632977541 8568562784985511993683289)
          ·
            refine ⟨6426422088739133995262467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8568562784985511993683289 6426422088739133995262467)
            ·
              refine ⟨9639633133108700992893701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6426422088739133995262467 9639633133108700992893701)
              ·
                refine ⟨1807431212457881436167569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9639633133108700992893701 1807431212457881436167569)
                ·
                  refine ⟨1355573409343411077125677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1807431212457881436167569 1355573409343411077125677)
                  ·
                    refine ⟨508340028503779153922129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1355573409343411077125677 508340028503779153922129)
                    ·
                      rfl

theorem cell22_1484983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 2, 3].length) (baseStart_1484983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1484983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1484983 prefixEnd_1484983 := by exact prefixLift 1484983
  have htrace : WordTrace (prefixWord ++ tailWord_1484983) baseStart_1484983 baseEnd_1484983 := by
    simpa [prefixWord, tailWord_1484983, baseEnd_1484983] using wordTrace_append hprefix tailTrace_1484983
  have hstable : (prefixWord ++ tailWord_1484983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1484983).length < 2 ^ (prefixWord ++ tailWord_1484983).sum := by decide
  have hdescent : baseEnd_1484983 < baseStart_1484983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1484983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485056 : List Nat := [2, 1, 1, 2, 1, 1, 6, 1, 2, 5]
def baseStart_1485056 : Nat := 118140960795 + 1485056 * 2 ^ 59
def prefixEnd_1485056 : Nat := 4983230072969 + 3 ^ 40 * 1485056 * 2
def baseEnd_1485056 : Nat := 508365017895631296846905

theorem tailTrace_1485056 : CollatzResearch.WordTrace tailWord_1485056 prefixEnd_1485056 508365017895631296846905 := by
  unfold tailWord_1485056
  simp only [CollatzResearch.WordTrace]
  refine ⟨27082221053951607108801511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36109628071935476145068681 27082221053951607108801511)
  ·
    refine ⟨40623331580927410663202267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27082221053951607108801511 40623331580927410663202267)
    ·
      refine ⟨60934997371391115994803401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40623331580927410663202267 60934997371391115994803401)
      ·
        refine ⟨45701248028543336996102551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60934997371391115994803401 45701248028543336996102551)
        ·
          refine ⟨68551872042815005494153827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45701248028543336996102551 68551872042815005494153827)
          ·
            refine ⟨102827808064222508241230741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68551872042815005494153827 102827808064222508241230741)
            ·
              refine ⟨4820053503010430073807691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 102827808064222508241230741 4820053503010430073807691)
              ·
                refine ⟨7230080254515645110711537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4820053503010430073807691 7230080254515645110711537)
                ·
                  refine ⟨5422560190886733833033653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7230080254515645110711537 5422560190886733833033653)
                  ·
                    refine ⟨508365017895631296846905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5422560190886733833033653 508365017895631296846905)
                    ·
                      rfl

theorem cell22_1485056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 1, 2, 5].length) (baseStart_1485056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1485056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1485056 prefixEnd_1485056 := by exact prefixLift 1485056
  have htrace : WordTrace (prefixWord ++ tailWord_1485056) baseStart_1485056 baseEnd_1485056 := by
    simpa [prefixWord, tailWord_1485056, baseEnd_1485056] using wordTrace_append hprefix tailTrace_1485056
  have hstable : (prefixWord ++ tailWord_1485056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485056).length < 2 ^ (prefixWord ++ tailWord_1485056).sum := by decide
  have hdescent : baseEnd_1485056 < baseStart_1485056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485071 : List Nat := [1, 1, 2, 1, 1, 1, 3, 5, 3, 4]
def baseStart_1485071 : Nat := 118140960795 + 1485071 * 2 ^ 59
def prefixEnd_1485071 : Nat := 4983230072969 + 3 ^ 40 * 1485071 * 2
def baseEnd_1485071 : Nat := 508370152702176257721859

theorem tailTrace_1485071 : CollatzResearch.WordTrace tailWord_1485071 prefixEnd_1485071 508370152702176257721859 := by
  unfold tailWord_1485071
  simp only [CollatzResearch.WordTrace]
  refine ⟨54164989202848871779399067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36109992801899247852932711 54164989202848871779399067)
  ·
    refine ⟨81247483804273307669098601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54164989202848871779399067 81247483804273307669098601)
    ·
      refine ⟨60935612853204980751823951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81247483804273307669098601 60935612853204980751823951)
      ·
        refine ⟨91403419279807471127735927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60935612853204980751823951 91403419279807471127735927)
        ·
          refine ⟨137105128919711206691603891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91403419279807471127735927 137105128919711206691603891)
          ·
            refine ⟨205657693379566810037405837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137105128919711206691603891 205657693379566810037405837)
            ·
              refine ⟨77121635017337553764027189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 205657693379566810037405837 77121635017337553764027189)
              ·
                refine ⟨7230153282875395665377549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77121635017337553764027189 7230153282875395665377549)
                ·
                  refine ⟨2711307481078273374516581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7230153282875395665377549 2711307481078273374516581)
                  ·
                    refine ⟨508370152702176257721859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2711307481078273374516581 508370152702176257721859)
                    ·
                      rfl

theorem cell22_1485071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 4].length) (baseStart_1485071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1485071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1485071 prefixEnd_1485071 := by exact prefixLift 1485071
  have htrace : WordTrace (prefixWord ++ tailWord_1485071) baseStart_1485071 baseEnd_1485071 := by
    simpa [prefixWord, tailWord_1485071, baseEnd_1485071] using wordTrace_append hprefix tailTrace_1485071
  have hstable : (prefixWord ++ tailWord_1485071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485071).length < 2 ^ (prefixWord ++ tailWord_1485071).sum := by decide
  have hdescent : baseEnd_1485071 < baseStart_1485071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485103 : List Nat := [1, 1, 2, 1, 2, 1, 4, 6, 4]
def baseStart_1485103 : Nat := 118140960795 + 1485103 * 2 ^ 59
def prefixEnd_1485103 : Nat := 4983230072969 + 3 ^ 40 * 1485103 * 2
def baseEnd_1485103 : Nat := 169460368985379613640587

theorem tailTrace_1485103 : CollatzResearch.WordTrace tailWord_1485103 prefixEnd_1485103 169460368985379613640587 := by
  unfold tailWord_1485103
  simp only [CollatzResearch.WordTrace]
  refine ⟨54166156338732941244563963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36110770892488627496375975 54166156338732941244563963)
  ·
    refine ⟨81249234508099411866845945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54166156338732941244563963 81249234508099411866845945)
    ·
      refine ⟨60936925881074558900134459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81249234508099411866845945 60936925881074558900134459)
      ·
        refine ⟨91405388821611838350201689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60936925881074558900134459 91405388821611838350201689)
        ·
          refine ⟨68554041616208878762651267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91405388821611838350201689 68554041616208878762651267)
          ·
            refine ⟨102831062424313318143976901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68554041616208878762651267 102831062424313318143976901)
            ·
              refine ⟨19280824204558747151995669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102831062424313318143976901 19280824204558747151995669)
              ·
                refine ⟨903788634588691272749797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19280824204558747151995669 903788634588691272749797)
                ·
                  refine ⟨169460368985379613640587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 903788634588691272749797 169460368985379613640587)
                  ·
                    rfl

theorem cell22_1485103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 6, 4].length) (baseStart_1485103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1485103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1485103 prefixEnd_1485103 := by exact prefixLift 1485103
  have htrace : WordTrace (prefixWord ++ tailWord_1485103) baseStart_1485103 baseEnd_1485103 := by
    simpa [prefixWord, tailWord_1485103, baseEnd_1485103] using wordTrace_append hprefix tailTrace_1485103
  have hstable : (prefixWord ++ tailWord_1485103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485103).length < 2 ^ (prefixWord ++ tailWord_1485103).sum := by decide
  have hdescent : baseEnd_1485103 < baseStart_1485103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485148 : List Nat := [2, 2, 4, 3, 11]
def baseStart_1485148 : Nat := 118140960795 + 1485148 * 2 ^ 59
def prefixEnd_1485148 : Nat := 4983230072969 + 3 ^ 40 * 1485148 * 2
def baseEnd_1485148 : Nat := 2092166713480550302661

theorem tailTrace_1485148 : CollatzResearch.WordTrace tailWord_1485148 prefixEnd_1485148 2092166713480550302661 := by
  unfold tailWord_1485148
  simp only [CollatzResearch.WordTrace]
  refine ⟨27083898811784956964976049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36111865082379942619968065 27083898811784956964976049)
  ·
    refine ⟨20312924108838717723732037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27083898811784956964976049 20312924108838717723732037)
    ·
      refine ⟨3808673270407259573199757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20312924108838717723732037 3808673270407259573199757)
      ·
        refine ⟨1428252476402722339949909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3808673270407259573199757 1428252476402722339949909)
        ·
          refine ⟨2092166713480550302661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1428252476402722339949909 2092166713480550302661)
          ·
            rfl

theorem cell22_1485148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 11].length) (baseStart_1485148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1485148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1485148 prefixEnd_1485148 := by exact prefixLift 1485148
  have htrace : WordTrace (prefixWord ++ tailWord_1485148) baseStart_1485148 baseEnd_1485148 := by
    simpa [prefixWord, tailWord_1485148, baseEnd_1485148] using wordTrace_append hprefix tailTrace_1485148
  have hstable : (prefixWord ++ tailWord_1485148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485148).length < 2 ^ (prefixWord ++ tailWord_1485148).sum := by decide
  have hdescent : baseEnd_1485148 < baseStart_1485148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485152 : List Nat := [2, 1, 1, 3, 5, 1, 2, 2, 2, 3]
def baseStart_1485152 : Nat := 118140960795 + 1485152 * 2 ^ 59
def prefixEnd_1485152 : Nat := 4983230072969 + 3 ^ 40 * 1485152 * 2
def baseEnd_1485152 : Nat := 508397880657519046446611

theorem tailTrace_1485152 : CollatzResearch.WordTrace tailWord_1485152 prefixEnd_1485152 508397880657519046446611 := by
  unfold tailWord_1485152
  simp only [CollatzResearch.WordTrace]
  refine ⟨27083971757777711306548855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36111962343703615075398473 27083971757777711306548855)
  ·
    refine ⟨40625957636666566959823283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27083971757777711306548855 40625957636666566959823283)
    ·
      refine ⟨60938936454999850439734925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40625957636666566959823283 60938936454999850439734925)
      ·
        refine ⟨22852101170624943914900597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60938936454999850439734925 22852101170624943914900597)
        ·
          refine ⟨2142384484746088492021931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22852101170624943914900597 2142384484746088492021931)
          ·
            refine ⟨3213576727119132738032897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2142384484746088492021931 3213576727119132738032897)
            ·
              refine ⟨2410182545339349553524673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3213576727119132738032897 2410182545339349553524673)
              ·
                refine ⟨1807636909004512165143505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2410182545339349553524673 1807636909004512165143505)
                ·
                  refine ⟨1355727681753384123857629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1807636909004512165143505 1355727681753384123857629)
                  ·
                    refine ⟨508397880657519046446611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1355727681753384123857629 508397880657519046446611)
                    ·
                      rfl

theorem cell22_1485152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 2, 3].length) (baseStart_1485152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1485152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1485152 prefixEnd_1485152 := by exact prefixLift 1485152
  have htrace : WordTrace (prefixWord ++ tailWord_1485152) baseStart_1485152 baseEnd_1485152 := by
    simpa [prefixWord, tailWord_1485152, baseEnd_1485152] using wordTrace_append hprefix tailTrace_1485152
  have hstable : (prefixWord ++ tailWord_1485152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485152).length < 2 ^ (prefixWord ++ tailWord_1485152).sum := by decide
  have hdescent : baseEnd_1485152 < baseStart_1485152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485154 : List Nat := [3, 3, 2, 1, 1, 4, 2, 2, 4]
def baseStart_1485154 : Nat := 118140960795 + 1485154 * 2 ^ 59
def prefixEnd_1485154 : Nat := 4983230072969 + 3 ^ 40 * 1485154 * 2
def baseEnd_1485154 : Nat := 169466188432797235965535

theorem tailTrace_1485154 : CollatzResearch.WordTrace tailWord_1485154 prefixEnd_1485154 169466188432797235965535 := by
  unfold tailWord_1485154
  simp only [CollatzResearch.WordTrace]
  refine ⟨13542004115387044238667629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36112010974365451303113677 13542004115387044238667629)
  ·
    refine ⟨5078251543270141589500361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13542004115387044238667629 5078251543270141589500361)
    ·
      refine ⟨3808688657452606192125271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5078251543270141589500361 3808688657452606192125271)
      ·
        refine ⟨5713032986178909288187907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3808688657452606192125271 5713032986178909288187907)
        ·
          refine ⟨8569549479268363932281861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5713032986178909288187907 8569549479268363932281861)
          ·
            refine ⟨1606790527362818237302849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8569549479268363932281861 1606790527362818237302849)
            ·
              refine ⟨1205092895522113677977137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1606790527362818237302849 1205092895522113677977137)
              ·
                refine ⟨903819671641585258482853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1205092895522113677977137 903819671641585258482853)
                ·
                  refine ⟨169466188432797235965535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 903819671641585258482853 169466188432797235965535)
                  ·
                    rfl

theorem cell22_1485154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_1485154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1485154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1485154 prefixEnd_1485154 := by exact prefixLift 1485154
  have htrace : WordTrace (prefixWord ++ tailWord_1485154) baseStart_1485154 baseEnd_1485154 := by
    simpa [prefixWord, tailWord_1485154, baseEnd_1485154] using wordTrace_append hprefix tailTrace_1485154
  have hstable : (prefixWord ++ tailWord_1485154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485154).length < 2 ^ (prefixWord ++ tailWord_1485154).sum := by decide
  have hdescent : baseEnd_1485154 < baseStart_1485154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485161 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 1, 8]
def baseStart_1485161 : Nat := 118140960795 + 1485161 * 2 ^ 59
def prefixEnd_1485161 : Nat := 4983230072969 + 3 ^ 40 * 1485161 * 2
def baseEnd_1485161 : Nat := 508400961541446022971583

theorem tailTrace_1485161 : CollatzResearch.WordTrace tailWord_1485161 prefixEnd_1485161 508400961541446022971583 := by
  unfold tailWord_1485161
  simp only [CollatzResearch.WordTrace]
  refine ⟨54168271772522817150175337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36112181181681878100116891 54168271772522817150175337)
  ·
    refine ⟨40626203829392112862631503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54168271772522817150175337 40626203829392112862631503)
    ·
      refine ⟨60939305744088169293947255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40626203829392112862631503 60939305744088169293947255)
      ·
        refine ⟨91408958616132253940920883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60939305744088169293947255 91408958616132253940920883)
        ·
          refine ⟨137113437924198380911381325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91408958616132253940920883 137113437924198380911381325)
          ·
            refine ⟨51417539221574392841767997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137113437924198380911381325 51417539221574392841767997)
            ·
              refine ⟨19281577208090397315662999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51417539221574392841767997 19281577208090397315662999)
              ·
                refine ⟨28922365812135595973494499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19281577208090397315662999 28922365812135595973494499)
                ·
                  refine ⟨43383548718203393960241749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28922365812135595973494499 43383548718203393960241749)
                  ·
                    refine ⟨508400961541446022971583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 43383548718203393960241749 508400961541446022971583)
                    ·
                      rfl

theorem cell22_1485161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 8].length) (baseStart_1485161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1485161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1485161 prefixEnd_1485161 := by exact prefixLift 1485161
  have htrace : WordTrace (prefixWord ++ tailWord_1485161) baseStart_1485161 baseEnd_1485161 := by
    simpa [prefixWord, tailWord_1485161, baseEnd_1485161] using wordTrace_append hprefix tailTrace_1485161
  have hstable : (prefixWord ++ tailWord_1485161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485161).length < 2 ^ (prefixWord ++ tailWord_1485161).sum := by decide
  have hdescent : baseEnd_1485161 < baseStart_1485161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485210 : List Nat := [3, 1, 1, 4, 1, 2, 3, 2, 5]
def baseStart_1485210 : Nat := 118140960795 + 1485210 * 2 ^ 59
def prefixEnd_1485210 : Nat := 4983230072969 + 3 ^ 40 * 1485210 * 2
def baseEnd_1485210 : Nat := 169472578414275409498811

theorem tailTrace_1485210 : CollatzResearch.WordTrace tailWord_1485210 prefixEnd_1485210 169472578414275409498811 := by
  unfold tailWord_1485210
  simp only [CollatzResearch.WordTrace]
  refine ⟨13542514737336324629677271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36113372632896865679139389 13542514737336324629677271)
  ·
    refine ⟨20313772106004486944515907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13542514737336324629677271 20313772106004486944515907)
    ·
      refine ⟨30470658159006730416773861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20313772106004486944515907 30470658159006730416773861)
      ·
        refine ⟨5713248404813761953145099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30470658159006730416773861 5713248404813761953145099)
        ·
          refine ⟨8569872607220642929717649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5713248404813761953145099 8569872607220642929717649)
          ·
            refine ⟨6427404455415482197288237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8569872607220642929717649 6427404455415482197288237)
            ·
              refine ⟨2410276670780805823983089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6427404455415482197288237 2410276670780805823983089)
              ·
                refine ⟨1807707503085604367987317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2410276670780805823983089 1807707503085604367987317)
                ·
                  refine ⟨169472578414275409498811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1807707503085604367987317 169472578414275409498811)
                  ·
                    rfl

theorem cell22_1485210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 5].length) (baseStart_1485210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1485210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1485210 prefixEnd_1485210 := by exact prefixLift 1485210
  have htrace : WordTrace (prefixWord ++ tailWord_1485210) baseStart_1485210 baseEnd_1485210 := by
    simpa [prefixWord, tailWord_1485210, baseEnd_1485210] using wordTrace_append hprefix tailTrace_1485210
  have hstable : (prefixWord ++ tailWord_1485210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485210).length < 2 ^ (prefixWord ++ tailWord_1485210).sum := by decide
  have hdescent : baseEnd_1485210 < baseStart_1485210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485214 : List Nat := [4, 3, 1, 2, 1, 2, 2, 1, 3, 3]
def baseStart_1485214 : Nat := 118140960795 + 1485214 * 2 ^ 59
def prefixEnd_1485214 : Nat := 4983230072969 + 3 ^ 40 * 1485214 * 2
def baseEnd_1485214 : Nat := 508419104524571551396421

theorem tailTrace_1485214 : CollatzResearch.WordTrace tailWord_1485214 prefixEnd_1485214 508419104524571551396421 := by
  unfold tailWord_1485214
  simp only [CollatzResearch.WordTrace]
  refine ⟨6771275605166350900231837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36113469894220538134569797 6771275605166350900231837)
  ·
    refine ⟨2539228351937381587586939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6771275605166350900231837 2539228351937381587586939)
    ·
      refine ⟨3808842527906072381380409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2539228351937381587586939 3808842527906072381380409)
      ·
        refine ⟨2856631895929554286035307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3808842527906072381380409 2856631895929554286035307)
        ·
          refine ⟨4284947843894331429052961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2856631895929554286035307 4284947843894331429052961)
          ·
            refine ⟨3213710882920748571789721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4284947843894331429052961 3213710882920748571789721)
            ·
              refine ⟨2410283162190561428842291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3213710882920748571789721 2410283162190561428842291)
              ·
                refine ⟨3615424743285842143263437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2410283162190561428842291 3615424743285842143263437)
                ·
                  refine ⟨1355784278732190803723789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3615424743285842143263437 1355784278732190803723789)
                  ·
                    refine ⟨508419104524571551396421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1355784278732190803723789 508419104524571551396421)
                    ·
                      rfl

theorem cell22_1485214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_1485214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1485214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1485214 prefixEnd_1485214 := by exact prefixLift 1485214
  have htrace : WordTrace (prefixWord ++ tailWord_1485214) baseStart_1485214 baseEnd_1485214 := by
    simpa [prefixWord, tailWord_1485214, baseEnd_1485214] using wordTrace_append hprefix tailTrace_1485214
  have hstable : (prefixWord ++ tailWord_1485214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485214).length < 2 ^ (prefixWord ++ tailWord_1485214).sum := by decide
  have hdescent : baseEnd_1485214 < baseStart_1485214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485287 : List Nat := [1, 1, 5, 2, 1, 1, 3, 3, 2, 3]
def baseStart_1485287 : Nat := 118140960795 + 1485287 * 2 ^ 59
def prefixEnd_1485287 : Nat := 4983230072969 + 3 ^ 40 * 1485287 * 2
def baseEnd_1485287 : Nat := 508444093916423694321197

theorem tailTrace_1485287 : CollatzResearch.WordTrace tailWord_1485287 prefixEnd_1485287 508444093916423694321197 := by
  unfold tailWord_1485287
  simp only [CollatzResearch.WordTrace]
  refine ⟨54172867370066340669262115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36115244913377560446174743 54172867370066340669262115)
  ·
    refine ⟨81259301055099511003893173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54172867370066340669262115 81259301055099511003893173)
    ·
      refine ⟨7618059473915579156614985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81259301055099511003893173 7618059473915579156614985)
      ·
        refine ⟨5713544605436684367461239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7618059473915579156614985 5713544605436684367461239)
        ·
          refine ⟨8570316908155026551191859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5713544605436684367461239 8570316908155026551191859)
          ·
            refine ⟨12855475362232539826787789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8570316908155026551191859 12855475362232539826787789)
            ·
              refine ⟨4820803260837202435045421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12855475362232539826787789 4820803260837202435045421)
              ·
                refine ⟨1807801222813950913142033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4820803260837202435045421 1807801222813950913142033)
                ·
                  refine ⟨1355850917110463184856525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1807801222813950913142033 1355850917110463184856525)
                  ·
                    refine ⟨508444093916423694321197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1355850917110463184856525 508444093916423694321197)
                    ·
                      rfl

theorem cell22_1485287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_1485287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1485287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1485287 prefixEnd_1485287 := by exact prefixLift 1485287
  have htrace : WordTrace (prefixWord ++ tailWord_1485287) baseStart_1485287 baseEnd_1485287 := by
    simpa [prefixWord, tailWord_1485287, baseEnd_1485287] using wordTrace_append hprefix tailTrace_1485287
  have hstable : (prefixWord ++ tailWord_1485287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485287).length < 2 ^ (prefixWord ++ tailWord_1485287).sum := by decide
  have hdescent : baseEnd_1485287 < baseStart_1485287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485302 : List Nat := [5, 1, 1, 1, 2, 1, 4, 1, 2, 4]
def baseStart_1485302 : Nat := 118140960795 + 1485302 * 2 ^ 59
def prefixEnd_1485302 : Nat := 4983230072969 + 3 ^ 40 * 1485302 * 2
def baseEnd_1485302 : Nat := 508449228722968655196151

theorem tailTrace_1485302 : CollatzResearch.WordTrace tailWord_1485302 prefixEnd_1485302 508449228722968655196151 := by
  unfold tailWord_1485302
  simp only [CollatzResearch.WordTrace]
  refine ⟨3385838404063249889441135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36115609643341332154038773 3385838404063249889441135)
  ·
    refine ⟨5078757606094874834161703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3385838404063249889441135 5078757606094874834161703)
    ·
      refine ⟨7618136409142312251242555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5078757606094874834161703 7618136409142312251242555)
      ·
        refine ⟨11427204613713468376863833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7618136409142312251242555 11427204613713468376863833)
        ·
          refine ⟨8570403460285101282647875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11427204613713468376863833 8570403460285101282647875)
          ·
            refine ⟨12855605190427651923971813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8570403460285101282647875 12855605190427651923971813)
            ·
              refine ⟨2410425973205184735744715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12855605190427651923971813 2410425973205184735744715)
              ·
                refine ⟨3615638959807777103617073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2410425973205184735744715 3615638959807777103617073)
                ·
                  refine ⟨2711729219855832827712805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3615638959807777103617073 2711729219855832827712805)
                  ·
                    refine ⟨508449228722968655196151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2711729219855832827712805 508449228722968655196151)
                    ·
                      rfl

theorem cell22_1485302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_1485302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1485302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1485302 prefixEnd_1485302 := by exact prefixLift 1485302
  have htrace : WordTrace (prefixWord ++ tailWord_1485302) baseStart_1485302 baseEnd_1485302 := by
    simpa [prefixWord, tailWord_1485302, baseEnd_1485302] using wordTrace_append hprefix tailTrace_1485302
  have hstable : (prefixWord ++ tailWord_1485302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485302).length < 2 ^ (prefixWord ++ tailWord_1485302).sum := by decide
  have hdescent : baseEnd_1485302 < baseStart_1485302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485345 : List Nat := [1, 2, 3, 2, 2, 1, 1, 5, 5]
def baseStart_1485345 : Nat := 118140960795 + 1485345 * 2 ^ 59
def prefixEnd_1485345 : Nat := 4983230072969 + 3 ^ 40 * 1485345 * 2
def baseEnd_1485345 : Nat := 169487982833910292123673

theorem tailTrace_1485345 : CollatzResearch.WordTrace tailWord_1485345 prefixEnd_1485345 169487982833910292123673 := by
  unfold tailWord_1485345
  simp only [CollatzResearch.WordTrace]
  refine ⟨54174982803856216574873489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36116655202570811049915659 54174982803856216574873489)
  ·
    refine ⟨40631237102892162431155117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54174982803856216574873489 40631237102892162431155117)
    ·
      refine ⟨15236713913584560911683169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40631237102892162431155117 15236713913584560911683169)
      ·
        refine ⟨11427535435188420683762377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15236713913584560911683169 11427535435188420683762377)
        ·
          refine ⟨8570651576391315512821783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11427535435188420683762377 8570651576391315512821783)
          ·
            refine ⟨12855977364586973269232675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8570651576391315512821783 12855977364586973269232675)
            ·
              refine ⟨19283966046880459903849013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12855977364586973269232675 19283966046880459903849013)
              ·
                refine ⟨1807871816895043115985845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19283966046880459903849013 1807871816895043115985845)
                ·
                  refine ⟨169487982833910292123673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1807871816895043115985845 169487982833910292123673)
                  ·
                    rfl

theorem cell22_1485345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 5].length) (baseStart_1485345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1485345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1485345 prefixEnd_1485345 := by exact prefixLift 1485345
  have htrace : WordTrace (prefixWord ++ tailWord_1485345) baseStart_1485345 baseEnd_1485345 := by
    simpa [prefixWord, tailWord_1485345, baseEnd_1485345] using wordTrace_append hprefix tailTrace_1485345
  have hstable : (prefixWord ++ tailWord_1485345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485345).length < 2 ^ (prefixWord ++ tailWord_1485345).sum := by decide
  have hdescent : baseEnd_1485345 < baseStart_1485345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485366 : List Nat := [5, 1, 2, 1, 2, 1, 1, 5, 1, 3]
def baseStart_1485366 : Nat := 118140960795 + 1485366 * 2 ^ 59
def prefixEnd_1485366 : Nat := 4983230072969 + 3 ^ 40 * 1485366 * 2
def baseEnd_1485366 : Nat := 508471137230893821595955

theorem tailTrace_1485366 : CollatzResearch.WordTrace tailWord_1485366 prefixEnd_1485366 508471137230893821595955 := by
  unfold tailWord_1485366
  simp only [CollatzResearch.WordTrace]
  refine ⟨3385984296048758572586747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36117165824520091440925301 3385984296048758572586747)
  ·
    refine ⟨5078976444073137858880121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3385984296048758572586747 5078976444073137858880121)
    ·
      refine ⟨3809232333054853394160091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5078976444073137858880121 3809232333054853394160091)
      ·
        refine ⟨5713848499582280091240137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3809232333054853394160091 5713848499582280091240137)
        ·
          refine ⟨4285386374686710068430103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5713848499582280091240137 4285386374686710068430103)
          ·
            refine ⟨6428079562030065102645155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4285386374686710068430103 6428079562030065102645155)
            ·
              refine ⟨9642119343045097653967733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6428079562030065102645155 9642119343045097653967733)
              ·
                refine ⟨903948688410477905059475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9642119343045097653967733 903948688410477905059475)
                ·
                  refine ⟨1355923032615716857589213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 903948688410477905059475 1355923032615716857589213)
                  ·
                    refine ⟨508471137230893821595955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1355923032615716857589213 508471137230893821595955)
                    ·
                      rfl

theorem cell22_1485366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_1485366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1485366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1485366 prefixEnd_1485366 := by exact prefixLift 1485366
  have htrace : WordTrace (prefixWord ++ tailWord_1485366) baseStart_1485366 baseEnd_1485366 := by
    simpa [prefixWord, tailWord_1485366, baseEnd_1485366] using wordTrace_append hprefix tailTrace_1485366
  have hstable : (prefixWord ++ tailWord_1485366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485366).length < 2 ^ (prefixWord ++ tailWord_1485366).sum := by decide
  have hdescent : baseEnd_1485366 < baseStart_1485366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485390 : List Nat := [4, 1, 1, 1, 1, 2, 3, 3, 6]
def baseStart_1485390 : Nat := 118140960795 + 1485390 * 2 ^ 59
def prefixEnd_1485390 : Nat := 4983230072969 + 3 ^ 40 * 1485390 * 2
def baseEnd_1485390 : Nat := 169493117640455252998627

theorem tailTrace_1485390 : CollatzResearch.WordTrace tailWord_1485390 prefixEnd_1485390 169493117640455252998627 := by
  unfold tailWord_1485390
  simp only [CollatzResearch.WordTrace]
  refine ⟨6772078011086648657532703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36117749392462126173507749 6772078011086648657532703)
  ·
    refine ⟨10158117016629972986299055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6772078011086648657532703 10158117016629972986299055)
    ·
      refine ⟨15237175524944959479448583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10158117016629972986299055 15237175524944959479448583)
      ·
        refine ⟨22855763287417439219172875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15237175524944959479448583 22855763287417439219172875)
        ·
          refine ⟨34283644931126158828759313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22855763287417439219172875 34283644931126158828759313)
          ·
            refine ⟨25712733698344619121569485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34283644931126158828759313 25712733698344619121569485)
            ·
              refine ⟨9642275136879232170588557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25712733698344619121569485 9642275136879232170588557)
              ·
                refine ⟨3615853176329712063970709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9642275136879232170588557 3615853176329712063970709)
                ·
                  refine ⟨169493117640455252998627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3615853176329712063970709 169493117640455252998627)
                  ·
                    rfl

theorem cell22_1485390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_1485390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1485390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1485390 prefixEnd_1485390 := by exact prefixLift 1485390
  have htrace : WordTrace (prefixWord ++ tailWord_1485390) baseStart_1485390 baseEnd_1485390 := by
    simpa [prefixWord, tailWord_1485390, baseEnd_1485390] using wordTrace_append hprefix tailTrace_1485390
  have hstable : (prefixWord ++ tailWord_1485390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485390).length < 2 ^ (prefixWord ++ tailWord_1485390).sum := by decide
  have hdescent : baseEnd_1485390 < baseStart_1485390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485420 : List Nat := [2, 2, 1, 1, 3, 1, 4, 1, 1, 6]
def baseStart_1485420 : Nat := 118140960795 + 1485420 * 2 ^ 59
def prefixEnd_1485420 : Nat := 4983230072969 + 3 ^ 40 * 1485420 * 2
def baseEnd_1485420 : Nat := 508489622534455680745789

theorem tailTrace_1485420 : CollatzResearch.WordTrace tailWord_1485420 prefixEnd_1485420 508489622534455680745789 := by
  unfold tailWord_1485420
  simp only [CollatzResearch.WordTrace]
  refine ⟨27088859139292252191926857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36118478852389669589235809 27088859139292252191926857)
  ·
    refine ⟨20316644354469189143945143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27088859139292252191926857 20316644354469189143945143)
    ·
      refine ⟨30474966531703783715917715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20316644354469189143945143 30474966531703783715917715)
      ·
        refine ⟨45712449797555675573876573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30474966531703783715917715 45712449797555675573876573)
        ·
          refine ⟨17142168674083378340203715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45712449797555675573876573 17142168674083378340203715)
          ·
            refine ⟨25713253011125067510305573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17142168674083378340203715 25713253011125067510305573)
            ·
              refine ⟨4821234939585950158182295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25713253011125067510305573 4821234939585950158182295)
              ·
                refine ⟨7231852409378925237273443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4821234939585950158182295 7231852409378925237273443)
                ·
                  refine ⟨10847778614068387855910165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7231852409378925237273443 10847778614068387855910165)
                  ·
                    refine ⟨508489622534455680745789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10847778614068387855910165 508489622534455680745789)
                    ·
                      rfl

theorem cell22_1485420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_1485420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1485420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1485420 prefixEnd_1485420 := by exact prefixLift 1485420
  have htrace : WordTrace (prefixWord ++ tailWord_1485420) baseStart_1485420 baseEnd_1485420 := by
    simpa [prefixWord, tailWord_1485420, baseEnd_1485420] using wordTrace_append hprefix tailTrace_1485420
  have hstable : (prefixWord ++ tailWord_1485420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485420).length < 2 ^ (prefixWord ++ tailWord_1485420).sum := by decide
  have hdescent : baseEnd_1485420 < baseStart_1485420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485501 : List Nat := [1, 4, 1, 2, 1, 4, 1, 4, 1, 3]
def baseStart_1485501 : Nat := 118140960795 + 1485501 * 2 ^ 59
def prefixEnd_1485501 : Nat := 4983230072969 + 3 ^ 40 * 1485501 * 2
def baseEnd_1485501 : Nat := 508517350489798469470541

theorem tailTrace_1485501 : CollatzResearch.WordTrace tailWord_1485501 prefixEnd_1485501 508517350489798469470541 := by
  unfold tailWord_1485501
  simp only [CollatzResearch.WordTrace]
  refine ⟨54180672591291055217552357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36120448394194036811701571 54180672591291055217552357)
  ·
    refine ⟨10158876110867072853291067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54180672591291055217552357 10158876110867072853291067)
    ·
      refine ⟨15238314166300609279936601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10158876110867072853291067 15238314166300609279936601)
      ·
        refine ⟨11428735624725456959952451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15238314166300609279936601 11428735624725456959952451)
        ·
          refine ⟨17143103437088185439928677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11428735624725456959952451 17143103437088185439928677)
          ·
            refine ⟨3214331894454034769986627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17143103437088185439928677 3214331894454034769986627)
            ·
              refine ⟨4821497841681052154979941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3214331894454034769986627 4821497841681052154979941)
              ·
                refine ⟨904030845315197279058739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4821497841681052154979941 904030845315197279058739)
                ·
                  refine ⟨1356046267972795918588109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 904030845315197279058739 1356046267972795918588109)
                  ·
                    refine ⟨508517350489798469470541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1356046267972795918588109 508517350489798469470541)
                    ·
                      rfl

theorem cell22_1485501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 4, 1, 3].length) (baseStart_1485501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1485501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1485501 prefixEnd_1485501 := by exact prefixLift 1485501
  have htrace : WordTrace (prefixWord ++ tailWord_1485501) baseStart_1485501 baseEnd_1485501 := by
    simpa [prefixWord, tailWord_1485501, baseEnd_1485501] using wordTrace_append hprefix tailTrace_1485501
  have hstable : (prefixWord ++ tailWord_1485501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485501).length < 2 ^ (prefixWord ++ tailWord_1485501).sum := by decide
  have hdescent : baseEnd_1485501 < baseStart_1485501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485512 : List Nat := [2, 1, 3, 1, 2, 4, 1, 1, 2, 5]
def baseStart_1485512 : Nat := 118140960795 + 1485512 * 2 ^ 59
def prefixEnd_1485512 : Nat := 4983230072969 + 3 ^ 40 * 1485512 * 2
def baseEnd_1485512 : Nat := 508521116014598107445507

theorem tailTrace_1485512 : CollatzResearch.WordTrace tailWord_1485512 prefixEnd_1485512 508521116014598107445507 := by
  unfold tailWord_1485512
  simp only [CollatzResearch.WordTrace]
  refine ⟨27090536897125602048101395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36120715862834136064135193 27090536897125602048101395)
  ·
    refine ⟨40635805345688403072152093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27090536897125602048101395 40635805345688403072152093)
    ·
      refine ⟨15238427004633151152057035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40635805345688403072152093 15238427004633151152057035)
      ·
        refine ⟨22857640506949726728085553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15238427004633151152057035 22857640506949726728085553)
        ·
          refine ⟨17143230380212295046064165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22857640506949726728085553 17143230380212295046064165)
          ·
            refine ⟨3214355696289805321137031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17143230380212295046064165 3214355696289805321137031)
            ·
              refine ⟨4821533544434707981705547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3214355696289805321137031 4821533544434707981705547)
              ·
                refine ⟨7232300316652061972558321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4821533544434707981705547 7232300316652061972558321)
                ·
                  refine ⟨5424225237489046479418741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7232300316652061972558321 5424225237489046479418741)
                  ·
                    refine ⟨508521116014598107445507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5424225237489046479418741 508521116014598107445507)
                    ·
                      rfl

theorem cell22_1485512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_1485512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1485512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1485512 prefixEnd_1485512 := by exact prefixLift 1485512
  have htrace : WordTrace (prefixWord ++ tailWord_1485512) baseStart_1485512 baseEnd_1485512 := by
    simpa [prefixWord, tailWord_1485512, baseEnd_1485512] using wordTrace_append hprefix tailTrace_1485512
  have hstable : (prefixWord ++ tailWord_1485512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485512).length < 2 ^ (prefixWord ++ tailWord_1485512).sum := by decide
  have hdescent : baseEnd_1485512 < baseStart_1485512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485527 : List Nat := [1, 1, 3, 2, 1, 4, 2, 1, 3, 4]
def baseStart_1485527 : Nat := 118140960795 + 1485527 * 2 ^ 59
def prefixEnd_1485527 : Nat := 4983230072969 + 3 ^ 40 * 1485527 * 2
def baseEnd_1485527 : Nat := 508526250821143068320461

theorem tailTrace_1485527 : CollatzResearch.WordTrace tailWord_1485527 prefixEnd_1485527 508526250821143068320461 := by
  unfold tailWord_1485527
  simp only [CollatzResearch.WordTrace]
  refine ⟨54181620889196861657998835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36121080592797907771999223 54181620889196861657998835)
  ·
    refine ⟨81272431333795292486998253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54181620889196861657998835 81272431333795292486998253)
    ·
      refine ⟨30477161750173234682624345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81272431333795292486998253 30477161750173234682624345)
      ·
        refine ⟨22857871312629926011968259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30477161750173234682624345 22857871312629926011968259)
        ·
          refine ⟨34286806968944889017952389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22857871312629926011968259 34286806968944889017952389)
          ·
            refine ⟨6428776306677166690866073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34286806968944889017952389 6428776306677166690866073)
            ·
              refine ⟨4821582230007875018149555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6428776306677166690866073 4821582230007875018149555)
              ·
                refine ⟨7232373345011812527224333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4821582230007875018149555 7232373345011812527224333)
                ·
                  refine ⟨2712140004379429697709125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7232373345011812527224333 2712140004379429697709125)
                  ·
                    refine ⟨508526250821143068320461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2712140004379429697709125 508526250821143068320461)
                    ·
                      rfl

theorem cell22_1485527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_1485527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1485527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1485527 prefixEnd_1485527 := by exact prefixLift 1485527
  have htrace : WordTrace (prefixWord ++ tailWord_1485527) baseStart_1485527 baseEnd_1485527 := by
    simpa [prefixWord, tailWord_1485527, baseEnd_1485527] using wordTrace_append hprefix tailTrace_1485527
  have hstable : (prefixWord ++ tailWord_1485527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485527).length < 2 ^ (prefixWord ++ tailWord_1485527).sum := by decide
  have hdescent : baseEnd_1485527 < baseStart_1485527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485572 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 3, 6]
def baseStart_1485572 : Nat := 118140960795 + 1485572 * 2 ^ 59
def prefixEnd_1485572 : Nat := 4983230072969 + 3 ^ 40 * 1485572 * 2
def baseEnd_1485572 : Nat := 508541655240777950945323

theorem tailTrace_1485572 : CollatzResearch.WordTrace tailWord_1485572 prefixEnd_1485572 508541655240777950945323 := by
  unfold tailWord_1485572
  simp only [CollatzResearch.WordTrace]
  refine ⟨27091631087016917171693485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36122174782689222895591313 27091631087016917171693485)
  ·
    refine ⟨10159361657631343939385057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27091631087016917171693485 10159361657631343939385057)
    ·
      refine ⟨7619521243223507954538793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10159361657631343939385057 7619521243223507954538793)
      ·
        refine ⟨5714640932417630965904095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7619521243223507954538793 5714640932417630965904095)
        ·
          refine ⟨8571961398626446448856143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5714640932417630965904095 8571961398626446448856143)
          ·
            refine ⟨12857942097939669673284215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8571961398626446448856143 12857942097939669673284215)
            ·
              refine ⟨19286913146909504509926323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12857942097939669673284215 19286913146909504509926323)
              ·
                refine ⟨28930369720364256764889485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19286913146909504509926323 28930369720364256764889485)
                ·
                  refine ⟨10848888645136596286833557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28930369720364256764889485 10848888645136596286833557)
                  ·
                    refine ⟨508541655240777950945323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10848888645136596286833557 508541655240777950945323)
                    ·
                      rfl

theorem cell22_1485572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_1485572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1485572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1485572 prefixEnd_1485572 := by exact prefixLift 1485572
  have htrace : WordTrace (prefixWord ++ tailWord_1485572) baseStart_1485572 baseEnd_1485572 := by
    simpa [prefixWord, tailWord_1485572, baseEnd_1485572] using wordTrace_append hprefix tailTrace_1485572
  have hstable : (prefixWord ++ tailWord_1485572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485572).length < 2 ^ (prefixWord ++ tailWord_1485572).sum := by decide
  have hdescent : baseEnd_1485572 < baseStart_1485572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485604 : List Nat := [2, 3, 1, 3, 3, 2, 8]
def baseStart_1485604 : Nat := 118140960795 + 1485604 * 2 ^ 59
def prefixEnd_1485604 : Nat := 4983230072969 + 3 ^ 40 * 1485604 * 2
def baseEnd_1485604 : Nat := 18835281833138538301675

theorem tailTrace_1485604 : CollatzResearch.WordTrace tailWord_1485604 prefixEnd_1485604 18835281833138538301675 := by
  unfold tailWord_1485604
  simp only [CollatzResearch.WordTrace]
  refine ⟨27092214654958951904275933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36122952873278602539034577 27092214654958951904275933)
  ·
    refine ⟨10159580495609606964103475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27092214654958951904275933 10159580495609606964103475)
    ·
      refine ⟨15239370743414410446155213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10159580495609606964103475 15239370743414410446155213)
      ·
        refine ⟨5714764028780403917308205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15239370743414410446155213 5714764028780403917308205)
        ·
          refine ⟨2143036510792651468990577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5714764028780403917308205 2143036510792651468990577)
          ·
            refine ⟨1607277383094488601742933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2143036510792651468990577 1607277383094488601742933)
            ·
              refine ⟨18835281833138538301675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1607277383094488601742933 18835281833138538301675)
              ·
                rfl

theorem cell22_1485604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 8].length) (baseStart_1485604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1485604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1485604 prefixEnd_1485604 := by exact prefixLift 1485604
  have htrace : WordTrace (prefixWord ++ tailWord_1485604) baseStart_1485604 baseEnd_1485604 := by
    simpa [prefixWord, tailWord_1485604, baseEnd_1485604] using wordTrace_append hprefix tailTrace_1485604
  have hstable : (prefixWord ++ tailWord_1485604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485604).length < 2 ^ (prefixWord ++ tailWord_1485604).sum := by decide
  have hdescent : baseEnd_1485604 < baseStart_1485604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485610 : List Nat := [3, 1, 4, 3, 1, 1, 3, 2, 4]
def baseStart_1485610 : Nat := 118140960795 + 1485610 * 2 ^ 59
def prefixEnd_1485610 : Nat := 4983230072969 + 3 ^ 40 * 1485610 * 2
def baseEnd_1485610 : Nat := 169518221139119506165069

theorem tailTrace_1485610 : CollatzResearch.WordTrace tailWord_1485610 prefixEnd_1485610 169518221139119506165069 := by
  unfold tailWord_1485610
  simp only [CollatzResearch.WordTrace]
  refine ⟨13546162036974041708317571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36123098765264111222180189 13546162036974041708317571)
  ·
    refine ⟨20319243055461062562476357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13546162036974041708317571 20319243055461062562476357)
    ·
      refine ⟨3809858072898949230464317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20319243055461062562476357 3809858072898949230464317)
      ·
        refine ⟨1428696777337105961424119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3809858072898949230464317 1428696777337105961424119)
        ·
          refine ⟨2143045166005658942136179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1428696777337105961424119 2143045166005658942136179)
          ·
            refine ⟨3214567749008488413204269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2143045166005658942136179 3214567749008488413204269)
            ·
              refine ⟨1205462905878183154951601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3214567749008488413204269 1205462905878183154951601)
              ·
                refine ⟨904097179408637366213701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1205462905878183154951601 904097179408637366213701)
                ·
                  refine ⟨169518221139119506165069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 904097179408637366213701 169518221139119506165069)
                  ·
                    rfl

theorem cell22_1485610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 2, 4].length) (baseStart_1485610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1485610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1485610 prefixEnd_1485610 := by exact prefixLift 1485610
  have htrace : WordTrace (prefixWord ++ tailWord_1485610) baseStart_1485610 baseEnd_1485610 := by
    simpa [prefixWord, tailWord_1485610, baseEnd_1485610] using wordTrace_append hprefix tailTrace_1485610
  have hstable : (prefixWord ++ tailWord_1485610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485610).length < 2 ^ (prefixWord ++ tailWord_1485610).sum := by decide
  have hdescent : baseEnd_1485610 < baseStart_1485610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485617 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 2, 6]
def baseStart_1485617 : Nat := 118140960795 + 1485617 * 2 ^ 59
def prefixEnd_1485617 : Nat := 4983230072969 + 3 ^ 40 * 1485617 * 2
def baseEnd_1485617 : Nat := 508557059660412833570185

theorem tailTrace_1485617 : CollatzResearch.WordTrace tailWord_1485617 prefixEnd_1485617 508557059660412833570185 := by
  unfold tailWord_1485617
  simp only [CollatzResearch.WordTrace]
  refine ⟨54184903458870807028775105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36123268972580538019183403 54184903458870807028775105)
  ·
    refine ⟨40638677594153105271581329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54184903458870807028775105 40638677594153105271581329)
    ·
      refine ⟨30479008195614828953685997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40638677594153105271581329 30479008195614828953685997)
      ·
        refine ⟨11429628073355560857632249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30479008195614828953685997 11429628073355560857632249)
        ·
          refine ⟨8572221055016670643224187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11429628073355560857632249 8572221055016670643224187)
          ·
            refine ⟨12858331582525005964836281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8572221055016670643224187 12858331582525005964836281)
            ·
              refine ⟨9643748686893754473627211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12858331582525005964836281 9643748686893754473627211)
              ·
                refine ⟨14465623030340631710440817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9643748686893754473627211 14465623030340631710440817)
                ·
                  refine ⟨10849217272755473782830613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14465623030340631710440817 10849217272755473782830613)
                  ·
                    refine ⟨508557059660412833570185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10849217272755473782830613 508557059660412833570185)
                    ·
                      rfl

theorem cell22_1485617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_1485617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1485617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1485617 prefixEnd_1485617 := by exact prefixLift 1485617
  have htrace : WordTrace (prefixWord ++ tailWord_1485617) baseStart_1485617 baseEnd_1485617 := by
    simpa [prefixWord, tailWord_1485617, baseEnd_1485617] using wordTrace_append hprefix tailTrace_1485617
  have hstable : (prefixWord ++ tailWord_1485617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485617).length < 2 ^ (prefixWord ++ tailWord_1485617).sum := by decide
  have hdescent : baseEnd_1485617 < baseStart_1485617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485784 : List Nat := [2, 1, 2, 2, 2, 3, 2, 1, 7]
def baseStart_1485784 : Nat := 118140960795 + 1485784 * 2 ^ 59
def prefixEnd_1485784 : Nat := 4983230072969 + 3 ^ 40 * 1485784 * 2
def baseEnd_1485784 : Nat := 169538075724426688214891

theorem tailTrace_1485784 : CollatzResearch.WordTrace tailWord_1485784 prefixEnd_1485784 169538075724426688214891 := by
  unfold tailWord_1485784
  simp only [CollatzResearch.WordTrace]
  refine ⟨27095497224632897275052203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36127329632843863033402937 27095497224632897275052203)
  ·
    refine ⟨40643245836949345912578305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27095497224632897275052203 40643245836949345912578305)
    ·
      refine ⟨30482434377712009434433729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40643245836949345912578305 30482434377712009434433729)
      ·
        refine ⟨22861825783284007075825297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30482434377712009434433729 22861825783284007075825297)
        ·
          refine ⟨17146369337463005306868973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22861825783284007075825297 17146369337463005306868973)
          ·
            refine ⟨6429888501548626990075865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17146369337463005306868973 6429888501548626990075865)
            ·
              refine ⟨4822416376161470242556899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6429888501548626990075865 4822416376161470242556899)
              ·
                refine ⟨7233624564242205363835349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4822416376161470242556899 7233624564242205363835349)
                ·
                  refine ⟨169538075724426688214891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7233624564242205363835349 169538075724426688214891)
                  ·
                    rfl

theorem cell22_1485784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 7].length) (baseStart_1485784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1485784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1485784 prefixEnd_1485784 := by exact prefixLift 1485784
  have htrace : WordTrace (prefixWord ++ tailWord_1485784) baseStart_1485784 baseEnd_1485784 := by
    simpa [prefixWord, tailWord_1485784, baseEnd_1485784] using wordTrace_append hprefix tailTrace_1485784
  have hstable : (prefixWord ++ tailWord_1485784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485784).length < 2 ^ (prefixWord ++ tailWord_1485784).sum := by decide
  have hdescent : baseEnd_1485784 < baseStart_1485784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485861 : List Nat := [1, 3, 1, 2, 2, 2, 4, 1, 1, 5]
def baseStart_1485861 : Nat := 118140960795 + 1485861 * 2 ^ 59
def prefixEnd_1485861 : Nat := 4983230072969 + 3 ^ 40 * 1485861 * 2
def baseEnd_1485861 : Nat := 508640585846877530469437

theorem tailTrace_1485861 : CollatzResearch.WordTrace tailWord_1485861 prefixEnd_1485861 508640585846877530469437 := by
  unfold tailWord_1485861
  simp only [CollatzResearch.WordTrace]
  refine ⟨54193802869986836700657437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36129201913324557800438291 54193802869986836700657437)
  ·
    refine ⟨20322676076245063762746539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54193802869986836700657437 20322676076245063762746539)
    ·
      refine ⟨30484014114367595644119809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20322676076245063762746539 30484014114367595644119809)
      ·
        refine ⟨22863010585775696733089857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30484014114367595644119809 22863010585775696733089857)
        ·
          refine ⟨17147257939331772549817393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22863010585775696733089857 17147257939331772549817393)
          ·
            refine ⟨12860443454498829412363045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17147257939331772549817393 12860443454498829412363045)
            ·
              refine ⟨2411333147718530514818071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12860443454498829412363045 2411333147718530514818071)
              ·
                refine ⟨3616999721577795772227107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2411333147718530514818071 3616999721577795772227107)
                ·
                  refine ⟨5425499582366693658340661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3616999721577795772227107 5425499582366693658340661)
                  ·
                    refine ⟨508640585846877530469437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5425499582366693658340661 508640585846877530469437)
                    ·
                      rfl

theorem cell22_1485861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 5].length) (baseStart_1485861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1485861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1485861 prefixEnd_1485861 := by exact prefixLift 1485861
  have htrace : WordTrace (prefixWord ++ tailWord_1485861) baseStart_1485861 baseEnd_1485861 := by
    simpa [prefixWord, tailWord_1485861, baseEnd_1485861] using wordTrace_append hprefix tailTrace_1485861
  have hstable : (prefixWord ++ tailWord_1485861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485861).length < 2 ^ (prefixWord ++ tailWord_1485861).sum := by decide
  have hdescent : baseEnd_1485861 < baseStart_1485861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485863 : List Nat := [1, 1, 7, 1, 1, 2, 1, 2, 6]
def baseStart_1485863 : Nat := 118140960795 + 1485863 * 2 ^ 59
def prefixEnd_1485863 : Nat := 4983230072969 + 3 ^ 40 * 1485863 * 2
def baseEnd_1485863 : Nat := 169547090162583397306477

theorem tailTrace_1485863 : CollatzResearch.WordTrace tailWord_1485863 prefixEnd_1485863 169547090162583397306477 := by
  unfold tailWord_1485863
  simp only [CollatzResearch.WordTrace]
  refine ⟨54193875815979591042230243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36129250543986394028153495 54193875815979591042230243)
  ·
    refine ⟨81290813723969386563345365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54193875815979591042230243 81290813723969386563345365)
    ·
      refine ⟨1905253446655532497578407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 81290813723969386563345365 1905253446655532497578407)
      ·
        refine ⟨2857880169983298746367611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1905253446655532497578407 2857880169983298746367611)
        ·
          refine ⟨4286820254974948119551417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2857880169983298746367611 4286820254974948119551417)
          ·
            refine ⟨3215115191231211089663563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4286820254974948119551417 3215115191231211089663563)
            ·
              refine ⟨4822672786846816634495345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3215115191231211089663563 4822672786846816634495345)
              ·
                refine ⟨3617004590135112475871509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4822672786846816634495345 3617004590135112475871509)
                ·
                  refine ⟨169547090162583397306477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3617004590135112475871509 169547090162583397306477)
                  ·
                    rfl

theorem cell22_1485863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 6].length) (baseStart_1485863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1485863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1485863 prefixEnd_1485863 := by exact prefixLift 1485863
  have htrace : WordTrace (prefixWord ++ tailWord_1485863) baseStart_1485863 baseEnd_1485863 := by
    simpa [prefixWord, tailWord_1485863, baseEnd_1485863] using wordTrace_append hprefix tailTrace_1485863
  have hstable : (prefixWord ++ tailWord_1485863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485863).length < 2 ^ (prefixWord ++ tailWord_1485863).sum := by decide
  have hdescent : baseEnd_1485863 < baseStart_1485863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485878 : List Nat := [5, 1, 2, 1, 1, 2, 2, 2, 1, 5]
def baseStart_1485878 : Nat := 118140960795 + 1485878 * 2 ^ 59
def prefixEnd_1485878 : Nat := 4983230072969 + 3 ^ 40 * 1485878 * 2
def baseEnd_1485878 : Nat := 508646405294295152794385

theorem tailTrace_1485878 : CollatzResearch.WordTrace tailWord_1485878 prefixEnd_1485878 508646405294295152794385 := by
  unfold tailWord_1485878
  simp only [CollatzResearch.WordTrace]
  refine ⟨3387151431932828037751643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36129615273950165736017525 3387151431932828037751643)
  ·
    refine ⟨5080727147899242056627465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3387151431932828037751643 5080727147899242056627465)
    ·
      refine ⟨3810545360924431542470599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5080727147899242056627465 3810545360924431542470599)
      ·
        refine ⟨5715818041386647313705899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3810545360924431542470599 5715818041386647313705899)
        ·
          refine ⟨8573727062079970970558849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5715818041386647313705899 8573727062079970970558849)
          ·
            refine ⟨6430295296559978227919137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8573727062079970970558849 6430295296559978227919137)
            ·
              refine ⟨4822721472419983670939353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6430295296559978227919137 4822721472419983670939353)
              ·
                refine ⟨3617041104314987753204515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4822721472419983670939353 3617041104314987753204515)
                ·
                  refine ⟨5425561656472481629806773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3617041104314987753204515 5425561656472481629806773)
                  ·
                    refine ⟨508646405294295152794385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5425561656472481629806773 508646405294295152794385)
                    ·
                      rfl

theorem cell22_1485878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_1485878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1485878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1485878 prefixEnd_1485878 := by exact prefixLift 1485878
  have htrace : WordTrace (prefixWord ++ tailWord_1485878) baseStart_1485878 baseEnd_1485878 := by
    simpa [prefixWord, tailWord_1485878, baseEnd_1485878] using wordTrace_append hprefix tailTrace_1485878
  have hstable : (prefixWord ++ tailWord_1485878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485878).length < 2 ^ (prefixWord ++ tailWord_1485878).sum := by decide
  have hdescent : baseEnd_1485878 < baseStart_1485878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485895 : List Nat := [1, 1, 4, 1, 3, 4, 1, 2, 2, 3]
def baseStart_1485895 : Nat := 118140960795 + 1485895 * 2 ^ 59
def prefixEnd_1485895 : Nat := 4983230072969 + 3 ^ 40 * 1485895 * 2
def baseEnd_1485895 : Nat := 508652224741712775119333

theorem tailTrace_1485895 : CollatzResearch.WordTrace tailWord_1485895 prefixEnd_1485895 508652224741712775119333 := by
  unfold tailWord_1485895
  simp only [CollatzResearch.WordTrace]
  refine ⟨54195042951863660507395139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36130028634575773671596759 54195042951863660507395139)
  ·
    refine ⟨81292564427795490761092709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54195042951863660507395139 81292564427795490761092709)
    ·
      refine ⟨15242355830211654517704883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81292564427795490761092709 15242355830211654517704883)
      ·
        refine ⟨22863533745317481776557325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15242355830211654517704883 22863533745317481776557325)
        ·
          refine ⟨8573825154494055666208997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22863533745317481776557325 8573825154494055666208997)
          ·
            refine ⟨1607592216467635437414187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8573825154494055666208997 1607592216467635437414187)
            ·
              refine ⟨2411388324701453156121281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1607592216467635437414187 2411388324701453156121281)
              ·
                refine ⟨1808541243526089867090961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2411388324701453156121281 1808541243526089867090961)
                ·
                  refine ⟨1356405932644567400318221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1808541243526089867090961 1356405932644567400318221)
                  ·
                    refine ⟨508652224741712775119333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1356405932644567400318221 508652224741712775119333)
                    ·
                      rfl

theorem cell22_1485895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_1485895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1485895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1485895 prefixEnd_1485895 := by exact prefixLift 1485895
  have htrace : WordTrace (prefixWord ++ tailWord_1485895) baseStart_1485895 baseEnd_1485895 := by
    simpa [prefixWord, tailWord_1485895, baseEnd_1485895] using wordTrace_append hprefix tailTrace_1485895
  have hstable : (prefixWord ++ tailWord_1485895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485895).length < 2 ^ (prefixWord ++ tailWord_1485895).sum := by decide
  have hdescent : baseEnd_1485895 < baseStart_1485895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485904 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 1, 8]
def baseStart_1485904 : Nat := 118140960795 + 1485904 * 2 ^ 59
def prefixEnd_1485904 : Nat := 4983230072969 + 3 ^ 40 * 1485904 * 2
def baseEnd_1485904 : Nat := 508655305625639751644305

theorem tailTrace_1485904 : CollatzResearch.WordTrace tailWord_1485904 prefixEnd_1485904 508655305625639751644305 := by
  unfold tailWord_1485904
  simp only [CollatzResearch.WordTrace]
  refine ⟨27097685604415527522236383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36130247472554036696315177 27097685604415527522236383)
  ·
    refine ⟨40646528406623291283354575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27097685604415527522236383 40646528406623291283354575)
    ·
      refine ⟨60969792609934936925031863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40646528406623291283354575 60969792609934936925031863)
      ·
        refine ⟨91454688914902405387547795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60969792609934936925031863 91454688914902405387547795)
        ·
          refine ⟨137182033372353608081321693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91454688914902405387547795 137182033372353608081321693)
          ·
            refine ⟨51443262514632603030495635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137182033372353608081321693 51443262514632603030495635)
            ·
              refine ⟨77164893771948904545743453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51443262514632603030495635 77164893771948904545743453)
              ·
                refine ⟨28936835164480839204653795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77164893771948904545743453 28936835164480839204653795)
                ·
                  refine ⟨43405252746721258806980693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28936835164480839204653795 43405252746721258806980693)
                  ·
                    refine ⟨508655305625639751644305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 43405252746721258806980693 508655305625639751644305)
                    ·
                      rfl

theorem cell22_1485904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 1, 8].length) (baseStart_1485904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1485904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1485904 prefixEnd_1485904 := by exact prefixLift 1485904
  have htrace : WordTrace (prefixWord ++ tailWord_1485904) baseStart_1485904 baseEnd_1485904 := by
    simpa [prefixWord, tailWord_1485904, baseEnd_1485904] using wordTrace_append hprefix tailTrace_1485904
  have hstable : (prefixWord ++ tailWord_1485904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485904).length < 2 ^ (prefixWord ++ tailWord_1485904).sum := by decide
  have hdescent : baseEnd_1485904 < baseStart_1485904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485957 : List Nat := [1, 3, 1, 1, 7, 1, 1, 1, 3, 3]
def baseStart_1485957 : Nat := 118140960795 + 1485957 * 2 ^ 59
def prefixEnd_1485957 : Nat := 4983230072969 + 3 ^ 40 * 1485957 * 2
def baseEnd_1485957 : Nat := 508673448608765280069143

theorem tailTrace_1485957 : CollatzResearch.WordTrace tailWord_1485957 prefixEnd_1485957 508673448608765280069143 := by
  unfold tailWord_1485957
  simp only [CollatzResearch.WordTrace]
  refine ⟨54197304277639045096152125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36131536185092696730768083 54197304277639045096152125)
  ·
    refine ⟨20323989104114641911057047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54197304277639045096152125 20323989104114641911057047)
    ·
      refine ⟨30485983656171962866585571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20323989104114641911057047 30485983656171962866585571)
      ·
        refine ⟨45728975484257944299878357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30485983656171962866585571 45728975484257944299878357)
        ·
          refine ⟨1071772862912295569528399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 45728975484257944299878357 1071772862912295569528399)
          ·
            refine ⟨1607659294368443354292599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1071772862912295569528399 1607659294368443354292599)
            ·
              refine ⟨2411488941552665031438899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1607659294368443354292599 2411488941552665031438899)
              ·
                refine ⟨3617233412328997547158349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2411488941552665031438899 3617233412328997547158349)
                ·
                  refine ⟨1356462529623374080184381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3617233412328997547158349 1356462529623374080184381)
                  ·
                    refine ⟨508673448608765280069143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1356462529623374080184381 508673448608765280069143)
                    ·
                      rfl

theorem cell22_1485957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 3, 3].length) (baseStart_1485957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1485957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1485957 prefixEnd_1485957 := by exact prefixLift 1485957
  have htrace : WordTrace (prefixWord ++ tailWord_1485957) baseStart_1485957 baseEnd_1485957 := by
    simpa [prefixWord, tailWord_1485957, baseEnd_1485957] using wordTrace_append hprefix tailTrace_1485957
  have hstable : (prefixWord ++ tailWord_1485957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485957).length < 2 ^ (prefixWord ++ tailWord_1485957).sum := by decide
  have hdescent : baseEnd_1485957 < baseStart_1485957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485970 : List Nat := [3, 2, 3, 1, 1, 2, 4, 1, 5]
def baseStart_1485970 : Nat := 118140960795 + 1485970 * 2 ^ 59
def prefixEnd_1485970 : Nat := 4983230072969 + 3 ^ 40 * 1485970 * 2
def baseEnd_1485970 : Nat := 169559299591479193164701

theorem tailTrace_1485970 : CollatzResearch.WordTrace tailWord_1485970 prefixEnd_1485970 169559299591479193164701 := by
  unfold tailWord_1485970
  simp only [CollatzResearch.WordTrace]
  refine ⟨13549444606647987079093841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36131852284394632210916909 13549444606647987079093841)
  ·
    refine ⟨10162083454985990309320381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13549444606647987079093841 10162083454985990309320381)
    ·
      refine ⟨3810781295619746365995143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10162083454985990309320381 3810781295619746365995143)
      ·
        refine ⟨5716171943429619548992715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3810781295619746365995143 5716171943429619548992715)
        ·
          refine ⟨8574257915144429323489073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5716171943429619548992715 8574257915144429323489073)
          ·
            refine ⟨6430693436358321992616805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8574257915144429323489073 6430693436358321992616805)
            ·
              refine ⟨1205755019317185373615651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6430693436358321992616805 1205755019317185373615651)
              ·
                refine ⟨1808632528975778060423477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1205755019317185373615651 1808632528975778060423477)
                ·
                  refine ⟨169559299591479193164701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1808632528975778060423477 169559299591479193164701)
                  ·
                    rfl

theorem cell22_1485970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_1485970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1485970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1485970 prefixEnd_1485970 := by exact prefixLift 1485970
  have htrace : WordTrace (prefixWord ++ tailWord_1485970) baseStart_1485970 baseEnd_1485970 := by
    simpa [prefixWord, tailWord_1485970, baseEnd_1485970] using wordTrace_append hprefix tailTrace_1485970
  have hstable : (prefixWord ++ tailWord_1485970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485970).length < 2 ^ (prefixWord ++ tailWord_1485970).sum := by decide
  have hdescent : baseEnd_1485970 < baseStart_1485970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1485981 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 8]
def baseStart_1485981 : Nat := 118140960795 + 1485981 * 2 ^ 59
def prefixEnd_1485981 : Nat := 4983230072969 + 3 ^ 40 * 1485981 * 2
def baseEnd_1485981 : Nat := 169560554766412405823023

theorem tailTrace_1485981 : CollatzResearch.WordTrace tailWord_1485981 prefixEnd_1485981 169560554766412405823023 := by
  unfold tailWord_1485981
  simp only [CollatzResearch.WordTrace]
  refine ⟨54198179629552097195025797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36132119753034731463350531 54198179629552097195025797)
  ·
    refine ⟨10162158680541018224067337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54198179629552097195025797 10162158680541018224067337)
    ·
      refine ⟨7621619010405763668050503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10162158680541018224067337 7621619010405763668050503)
      ·
        refine ⟨11432428515608645502075755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7621619010405763668050503 11432428515608645502075755)
        ·
          refine ⟨17148642773412968253113633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11432428515608645502075755 17148642773412968253113633)
          ·
            refine ⟨12861482080059726189835225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17148642773412968253113633 12861482080059726189835225)
            ·
              refine ⟨9646111560044794642376419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12861482080059726189835225 9646111560044794642376419)
              ·
                refine ⟨14469167340067191963564629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9646111560044794642376419 14469167340067191963564629)
                ·
                  refine ⟨169560554766412405823023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14469167340067191963564629 169560554766412405823023)
                  ·
                    rfl

theorem cell22_1485981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_1485981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1485981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1485981 prefixEnd_1485981 := by exact prefixLift 1485981
  have htrace : WordTrace (prefixWord ++ tailWord_1485981) baseStart_1485981 baseEnd_1485981 := by
    simpa [prefixWord, tailWord_1485981, baseEnd_1485981] using wordTrace_append hprefix tailTrace_1485981
  have hstable : (prefixWord ++ tailWord_1485981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1485981).length < 2 ^ (prefixWord ++ tailWord_1485981).sum := by decide
  have hdescent : baseEnd_1485981 < baseStart_1485981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1485981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486011 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 4, 4]
def baseStart_1486011 : Nat := 118140960795 + 1486011 * 2 ^ 59
def prefixEnd_1486011 : Nat := 4983230072969 + 3 ^ 40 * 1486011 * 2
def baseEnd_1486011 : Nat := 508691933912327139218977

theorem tailTrace_1486011 : CollatzResearch.WordTrace tailWord_1486011 prefixEnd_1486011 508691933912327139218977 := by
  unfold tailWord_1486011
  simp only [CollatzResearch.WordTrace]
  refine ⟨54199273819443412318617887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36132849212962274879078591 54199273819443412318617887)
  ·
    refine ⟨81298910729165118477926831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54199273819443412318617887 81298910729165118477926831)
    ·
      refine ⟨121948366093747677716890247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81298910729165118477926831 121948366093747677716890247)
      ·
        refine ⟨182922549140621516575335371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121948366093747677716890247 182922549140621516575335371)
        ·
          refine ⟨274383823710932274863003057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182922549140621516575335371 274383823710932274863003057)
          ·
            refine ⟨205787867783199206147252293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274383823710932274863003057 205787867783199206147252293)
            ·
              refine ⟨38585225209349851152609805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 205787867783199206147252293 38585225209349851152609805)
              ·
                refine ⟨14469459453506194182228677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38585225209349851152609805 14469459453506194182228677)
                ·
                  refine ⟨2713023647532411409167877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14469459453506194182228677 2713023647532411409167877)
                  ·
                    refine ⟨508691933912327139218977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2713023647532411409167877 508691933912327139218977)
                    ·
                      rfl

theorem cell22_1486011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 4].length) (baseStart_1486011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1486011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1486011 prefixEnd_1486011 := by exact prefixLift 1486011
  have htrace : WordTrace (prefixWord ++ tailWord_1486011) baseStart_1486011 baseEnd_1486011 := by
    simpa [prefixWord, tailWord_1486011, baseEnd_1486011] using wordTrace_append hprefix tailTrace_1486011
  have hstable : (prefixWord ++ tailWord_1486011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486011).length < 2 ^ (prefixWord ++ tailWord_1486011).sum := by decide
  have hdescent : baseEnd_1486011 < baseStart_1486011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486013 : List Nat := [1, 4, 1, 2, 1, 1, 2, 3, 4, 3]
def baseStart_1486013 : Nat := 118140960795 + 1486013 * 2 ^ 59
def prefixEnd_1486013 : Nat := 4983230072969 + 3 ^ 40 * 1486013 * 2
def baseEnd_1486013 : Nat := 508692618553199800668971

theorem tailTrace_1486013 : CollatzResearch.WordTrace tailWord_1486013 prefixEnd_1486013 508692618553199800668971 := by
  unfold tailWord_1486013
  simp only [CollatzResearch.WordTrace]
  refine ⟨54199346765436166660190693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36132897843624111106793795 54199346765436166660190693)
  ·
    refine ⟨10162377518519281248785755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54199346765436166660190693 10162377518519281248785755)
    ·
      refine ⟨15243566277778921873178633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10162377518519281248785755 15243566277778921873178633)
      ·
        refine ⟨11432674708334191404883975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15243566277778921873178633 11432674708334191404883975)
        ·
          refine ⟨17149012062501287107325963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11432674708334191404883975 17149012062501287107325963)
          ·
            refine ⟨25723518093751930660988945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17149012062501287107325963 25723518093751930660988945)
            ·
              refine ⟨19292638570313947995741709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25723518093751930660988945 19292638570313947995741709)
              ·
                refine ⟨7234739463867730498403141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19292638570313947995741709 7234739463867730498403141)
                ·
                  refine ⟨1356513649475199468450589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7234739463867730498403141 1356513649475199468450589)
                  ·
                    refine ⟨508692618553199800668971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1356513649475199468450589 508692618553199800668971)
                    ·
                      rfl

theorem cell22_1486013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_1486013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1486013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1486013 prefixEnd_1486013 := by exact prefixLift 1486013
  have htrace : WordTrace (prefixWord ++ tailWord_1486013) baseStart_1486013 baseEnd_1486013 := by
    simpa [prefixWord, tailWord_1486013, baseEnd_1486013] using wordTrace_append hprefix tailTrace_1486013
  have hstable : (prefixWord ++ tailWord_1486013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486013).length < 2 ^ (prefixWord ++ tailWord_1486013).sum := by decide
  have hdescent : baseEnd_1486013 < baseStart_1486013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486015 : List Nat := [1, 1, 2, 2, 2, 2, 6, 2, 4]
def baseStart_1486015 : Nat := 118140960795 + 1486015 * 2 ^ 59
def prefixEnd_1486015 : Nat := 4983230072969 + 3 ^ 40 * 1486015 * 2
def baseEnd_1486015 : Nat := 169564434398024154039655

theorem tailTrace_1486015 : CollatzResearch.WordTrace tailWord_1486015 prefixEnd_1486015 169564434398024154039655 := by
  unfold tailWord_1486015
  simp only [CollatzResearch.WordTrace]
  refine ⟨54199419711428921001763499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36132946474285947334508999 54199419711428921001763499)
  ·
    refine ⟨81299129567143381502645249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54199419711428921001763499 81299129567143381502645249)
    ·
      refine ⟨60974347175357536126983937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81299129567143381502645249 60974347175357536126983937)
      ·
        refine ⟨45730760381518152095237953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60974347175357536126983937 45730760381518152095237953)
        ·
          refine ⟨34298070286138614071428465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45730760381518152095237953 34298070286138614071428465)
          ·
            refine ⟨25723552714603960553571349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34298070286138614071428465 25723552714603960553571349)
            ·
              refine ⟨1205791533497060650948657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25723552714603960553571349 1205791533497060650948657)
              ·
                refine ⟨904343650122795488211493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1205791533497060650948657 904343650122795488211493)
                ·
                  refine ⟨169564434398024154039655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 904343650122795488211493 169564434398024154039655)
                  ·
                    rfl

theorem cell22_1486015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 2, 4].length) (baseStart_1486015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1486015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1486015 prefixEnd_1486015 := by exact prefixLift 1486015
  have htrace : WordTrace (prefixWord ++ tailWord_1486015) baseStart_1486015 baseEnd_1486015 := by
    simpa [prefixWord, tailWord_1486015, baseEnd_1486015] using wordTrace_append hprefix tailTrace_1486015
  have hstable : (prefixWord ++ tailWord_1486015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486015).length < 2 ^ (prefixWord ++ tailWord_1486015).sum := by decide
  have hdescent : baseEnd_1486015 < baseStart_1486015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486030 : List Nat := [4, 1, 1, 1, 5, 1, 2, 1, 1, 5]
def baseStart_1486030 : Nat := 118140960795 + 1486030 * 2 ^ 59
def prefixEnd_1486030 : Nat := 4983230072969 + 3 ^ 40 * 1486030 * 2
def baseEnd_1486030 : Nat := 508698438000617422993919

theorem tailTrace_1486030 : CollatzResearch.WordTrace tailWord_1486030 prefixEnd_1486030 508698438000617422993919 := by
  unfold tailWord_1486030
  simp only [CollatzResearch.WordTrace]
  refine ⟨6774995850796822320444943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36133311204249719042373029 6774995850796822320444943)
  ·
    refine ⟨10162493776195233480667415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6774995850796822320444943 10162493776195233480667415)
    ·
      refine ⟨15243740664292850221001123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10162493776195233480667415 15243740664292850221001123)
      ·
        refine ⟨22865610996439275331501685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15243740664292850221001123 22865610996439275331501685)
        ·
          refine ⟨2143651030916182062328283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22865610996439275331501685 2143651030916182062328283)
          ·
            refine ⟨3215476546374273093492425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2143651030916182062328283 3215476546374273093492425)
            ·
              refine ⟨2411607409780704820119319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3215476546374273093492425 2411607409780704820119319)
              ·
                refine ⟨3617411114671057230178979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2411607409780704820119319 3617411114671057230178979)
                ·
                  refine ⟨5426116672006585845268469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3617411114671057230178979 5426116672006585845268469)
                  ·
                    refine ⟨508698438000617422993919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5426116672006585845268469 508698438000617422993919)
                    ·
                      rfl

theorem cell22_1486030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_1486030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1486030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1486030 prefixEnd_1486030 := by exact prefixLift 1486030
  have htrace : WordTrace (prefixWord ++ tailWord_1486030) baseStart_1486030 baseEnd_1486030 := by
    simpa [prefixWord, tailWord_1486030, baseEnd_1486030] using wordTrace_append hprefix tailTrace_1486030
  have hstable : (prefixWord ++ tailWord_1486030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486030).length < 2 ^ (prefixWord ++ tailWord_1486030).sum := by decide
  have hdescent : baseEnd_1486030 < baseStart_1486030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486045 : List Nat := [1, 4, 3, 2, 2, 1, 1, 1, 1, 6]
def baseStart_1486045 : Nat := 118140960795 + 1486045 * 2 ^ 59
def prefixEnd_1486045 : Nat := 4983230072969 + 3 ^ 40 * 1486045 * 2
def baseEnd_1486045 : Nat := 508703572807162383868873

theorem tailTrace_1486045 : CollatzResearch.WordTrace tailWord_1486045 prefixEnd_1486045 508703572807162383868873 := by
  unfold tailWord_1486045
  simp only [CollatzResearch.WordTrace]
  refine ⟨54200513901320236125355589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36133675934213490750237059 54200513901320236125355589)
  ·
    refine ⟨10162596356497544273504173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54200513901320236125355589 10162596356497544273504173)
    ·
      refine ⟨3810973633686579102564065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10162596356497544273504173 3810973633686579102564065)
      ·
        refine ⟨2858230225264934326923049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3810973633686579102564065 2858230225264934326923049)
        ·
          refine ⟨2143672668948700745192287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2858230225264934326923049 2143672668948700745192287)
          ·
            refine ⟨3215509003423051117788431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2143672668948700745192287 3215509003423051117788431)
            ·
              refine ⟨4823263505134576676682647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3215509003423051117788431 4823263505134576676682647)
              ·
                refine ⟨7234895257701865015023971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4823263505134576676682647 7234895257701865015023971)
                ·
                  refine ⟨10852342886552797522535957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7234895257701865015023971 10852342886552797522535957)
                  ·
                    refine ⟨508703572807162383868873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10852342886552797522535957 508703572807162383868873)
                    ·
                      rfl

theorem cell22_1486045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_1486045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1486045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1486045 prefixEnd_1486045 := by exact prefixLift 1486045
  have htrace : WordTrace (prefixWord ++ tailWord_1486045) baseStart_1486045 baseEnd_1486045 := by
    simpa [prefixWord, tailWord_1486045, baseEnd_1486045] using wordTrace_append hprefix tailTrace_1486045
  have hstable : (prefixWord ++ tailWord_1486045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486045).length < 2 ^ (prefixWord ++ tailWord_1486045).sum := by decide
  have hdescent : baseEnd_1486045 < baseStart_1486045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486071 : List Nat := [1, 1, 3, 1, 1, 1, 2, 5, 7]
def baseStart_1486071 : Nat := 118140960795 + 1486071 * 2 ^ 59
def prefixEnd_1486071 : Nat := 4983230072969 + 3 ^ 40 * 1486071 * 2
def baseEnd_1486071 : Nat := 169570824379502327572931

theorem tailTrace_1486071 : CollatzResearch.WordTrace tailWord_1486071 prefixEnd_1486071 169570824379502327572931 := by
  unfold tailWord_1486071
  simp only [CollatzResearch.WordTrace]
  refine ⟨54201462199226042565802067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36134308132817361710534711 54201462199226042565802067)
  ·
    refine ⟨81302193298839063848703101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54201462199226042565802067 81302193298839063848703101)
    ·
      refine ⟨30488322487064648943263663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81302193298839063848703101 30488322487064648943263663)
      ·
        refine ⟨45732483730596973414895495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30488322487064648943263663 45732483730596973414895495)
        ·
          refine ⟨68598725595895460122343243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45732483730596973414895495 68598725595895460122343243)
          ·
            refine ⟨102898088393843190183514865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68598725595895460122343243 102898088393843190183514865)
            ·
              refine ⟨77173566295382392637636149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102898088393843190183514865 77173566295382392637636149)
              ·
                refine ⟨7235021840192099309778389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77173566295382392637636149 7235021840192099309778389)
                ·
                  refine ⟨169570824379502327572931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7235021840192099309778389 169570824379502327572931)
                  ·
                    rfl

theorem cell22_1486071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 7].length) (baseStart_1486071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1486071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1486071 prefixEnd_1486071 := by exact prefixLift 1486071
  have htrace : WordTrace (prefixWord ++ tailWord_1486071) baseStart_1486071 baseEnd_1486071 := by
    simpa [prefixWord, tailWord_1486071, baseEnd_1486071] using wordTrace_append hprefix tailTrace_1486071
  have hstable : (prefixWord ++ tailWord_1486071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486071).length < 2 ^ (prefixWord ++ tailWord_1486071).sum := by decide
  have hdescent : baseEnd_1486071 < baseStart_1486071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486109 : List Nat := [1, 4, 2, 3, 1, 1, 3, 3, 1, 3]
def baseStart_1486109 : Nat := 118140960795 + 1486109 * 2 ^ 59
def prefixEnd_1486109 : Nat := 4983230072969 + 3 ^ 40 * 1486109 * 2
def baseEnd_1486109 : Nat := 508725481315087550268677

theorem tailTrace_1486109 : CollatzResearch.WordTrace tailWord_1486109 prefixEnd_1486109 508725481315087550268677 := by
  unfold tailWord_1486109
  simp only [CollatzResearch.WordTrace]
  refine ⟨54202848173088375055685381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36135232115392250037123587 54202848173088375055685381)
  ·
    refine ⟨10163034032454070322941009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54202848173088375055685381 10163034032454070322941009)
    ·
      refine ⟨7622275524340552742205757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10163034032454070322941009 7622275524340552742205757)
      ·
        refine ⟨2858353321627707278327159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7622275524340552742205757 2858353321627707278327159)
        ·
          refine ⟨4287529982441560917490739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2858353321627707278327159 4287529982441560917490739)
          ·
            refine ⟨6431294973662341376236109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4287529982441560917490739 6431294973662341376236109)
            ·
              refine ⟨2411735615123378016088541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6431294973662341376236109 2411735615123378016088541)
              ·
                refine ⟨904400855671266756033203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2411735615123378016088541 904400855671266756033203)
                ·
                  refine ⟨1356601283506900134049805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 904400855671266756033203 1356601283506900134049805)
                  ·
                    refine ⟨508725481315087550268677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1356601283506900134049805 508725481315087550268677)
                    ·
                      rfl

theorem cell22_1486109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_1486109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1486109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1486109 prefixEnd_1486109 := by exact prefixLift 1486109
  have htrace : WordTrace (prefixWord ++ tailWord_1486109) baseStart_1486109 baseEnd_1486109 := by
    simpa [prefixWord, tailWord_1486109, baseEnd_1486109] using wordTrace_append hprefix tailTrace_1486109
  have hstable : (prefixWord ++ tailWord_1486109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486109).length < 2 ^ (prefixWord ++ tailWord_1486109).sum := by decide
  have hdescent : baseEnd_1486109 < baseStart_1486109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486165 : List Nat := [1, 3, 2, 2, 3, 2, 1, 2, 1, 5]
def baseStart_1486165 : Nat := 118140960795 + 1486165 * 2 ^ 59
def prefixEnd_1486165 : Nat := 4983230072969 + 3 ^ 40 * 1486165 * 2
def baseEnd_1486165 : Nat := 508744651259522070868505

theorem tailTrace_1486165 : CollatzResearch.WordTrace tailWord_1486165 prefixEnd_1486165 508744651259522070868505 := by
  unfold tailWord_1486165
  simp only [CollatzResearch.WordTrace]
  refine ⟨54204890660885496619723949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36136593773923664413149299 54204890660885496619723949)
  ·
    refine ⟨20326833997832061232396481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54204890660885496619723949 20326833997832061232396481)
    ·
      refine ⟨15245125498374045924297361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20326833997832061232396481 15245125498374045924297361)
      ·
        refine ⟨11433844123780534443223021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15245125498374045924297361 11433844123780534443223021)
        ·
          refine ⟨4287691546417700416208633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11433844123780534443223021 4287691546417700416208633)
          ·
            refine ⟨3215768659813275312156475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4287691546417700416208633 3215768659813275312156475)
            ·
              refine ⟨4823652989719912968234713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3215768659813275312156475 4823652989719912968234713)
              ·
                refine ⟨3617739742289934726176035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4823652989719912968234713 3617739742289934726176035)
                ·
                  refine ⟨5426609613434902089264053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3617739742289934726176035 5426609613434902089264053)
                  ·
                    refine ⟨508744651259522070868505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5426609613434902089264053 508744651259522070868505)
                    ·
                      rfl

theorem cell22_1486165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_1486165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1486165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1486165 prefixEnd_1486165 := by exact prefixLift 1486165
  have htrace : WordTrace (prefixWord ++ tailWord_1486165) baseStart_1486165 baseEnd_1486165 := by
    simpa [prefixWord, tailWord_1486165, baseEnd_1486165] using wordTrace_append hprefix tailTrace_1486165
  have hstable : (prefixWord ++ tailWord_1486165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486165).length < 2 ^ (prefixWord ++ tailWord_1486165).sum := by decide
  have hdescent : baseEnd_1486165 < baseStart_1486165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486180 : List Nat := [2, 3, 1, 1, 3, 2, 2, 2, 2, 4]
def baseStart_1486180 : Nat := 118140960795 + 1486180 * 2 ^ 59
def prefixEnd_1486180 : Nat := 4983230072969 + 3 ^ 40 * 1486180 * 2
def baseEnd_1486180 : Nat := 508749786066067031743459

theorem tailTrace_1486180 : CollatzResearch.WordTrace tailWord_1486180 prefixEnd_1486180 508749786066067031743459 := by
  unfold tailWord_1486180
  simp only [CollatzResearch.WordTrace]
  refine ⟨27102718877915577090759997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36136958503887436121013329 27102718877915577090759997)
  ·
    refine ⟨10163519579218341409034999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27102718877915577090759997 10163519579218341409034999)
    ·
      refine ⟨15245279368827512113552499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10163519579218341409034999 15245279368827512113552499)
      ·
        refine ⟨22867919053241268170328749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15245279368827512113552499 22867919053241268170328749)
        ·
          refine ⟨8575469644965475563873281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22867919053241268170328749 8575469644965475563873281)
          ·
            refine ⟨6431602233724106672904961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8575469644965475563873281 6431602233724106672904961)
            ·
              refine ⟨4823701675293080004678721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6431602233724106672904961 4823701675293080004678721)
              ·
                refine ⟨3617776256469810003509041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4823701675293080004678721 3617776256469810003509041)
                ·
                  refine ⟨2713332192352357502631781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3617776256469810003509041 2713332192352357502631781)
                  ·
                    refine ⟨508749786066067031743459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2713332192352357502631781 508749786066067031743459)
                    ·
                      rfl

theorem cell22_1486180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_1486180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1486180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1486180 prefixEnd_1486180 := by exact prefixLift 1486180
  have htrace : WordTrace (prefixWord ++ tailWord_1486180) baseStart_1486180 baseEnd_1486180 := by
    simpa [prefixWord, tailWord_1486180, baseEnd_1486180] using wordTrace_append hprefix tailTrace_1486180
  have hstable : (prefixWord ++ tailWord_1486180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486180).length < 2 ^ (prefixWord ++ tailWord_1486180).sum := by decide
  have hdescent : baseEnd_1486180 < baseStart_1486180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486257 : List Nat := [1, 2, 2, 4, 1, 1, 5, 1, 5]
def baseStart_1486257 : Nat := 118140960795 + 1486257 * 2 ^ 59
def prefixEnd_1486257 : Nat := 4983230072969 + 3 ^ 40 * 1486257 * 2
def baseEnd_1486257 : Nat := 169592048246554832522741

theorem tailTrace_1486257 : CollatzResearch.WordTrace tailWord_1486257 prefixEnd_1486257 169592048246554832522741 := by
  unfold tailWord_1486257
  simp only [CollatzResearch.WordTrace]
  refine ⟨54208246176552196332073025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36138830784368130888048683 54208246176552196332073025)
  ·
    refine ⟨40656184632414147249054769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54208246176552196332073025 40656184632414147249054769)
    ·
      refine ⟨30492138474310610436791077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40656184632414147249054769 30492138474310610436791077)
      ·
        refine ⟨5717275963933239456898327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30492138474310610436791077 5717275963933239456898327)
        ·
          refine ⟨8575913945899859185347491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5717275963933239456898327 8575913945899859185347491)
          ·
            refine ⟨12863870918849788778021237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8575913945899859185347491 12863870918849788778021237)
            ·
              refine ⟨1205987898642167697939491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12863870918849788778021237 1205987898642167697939491)
              ·
                refine ⟨1808981847963251546909237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1205987898642167697939491 1808981847963251546909237)
                ·
                  refine ⟨169592048246554832522741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1808981847963251546909237 169592048246554832522741)
                  ·
                    rfl

theorem cell22_1486257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 5].length) (baseStart_1486257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1486257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1486257 prefixEnd_1486257 := by exact prefixLift 1486257
  have htrace : WordTrace (prefixWord ++ tailWord_1486257) baseStart_1486257 baseEnd_1486257 := by
    simpa [prefixWord, tailWord_1486257, baseEnd_1486257] using wordTrace_append hprefix tailTrace_1486257
  have hstable : (prefixWord ++ tailWord_1486257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486257).length < 2 ^ (prefixWord ++ tailWord_1486257).sum := by decide
  have hdescent : baseEnd_1486257 < baseStart_1486257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486362 : List Nat := [3, 1, 1, 3, 1, 1, 1, 5, 3, 3]
def baseStart_1486362 : Nat := 118140960795 + 1486362 * 2 ^ 59
def prefixEnd_1486362 : Nat := 4983230072969 + 3 ^ 40 * 1486362 * 2
def baseEnd_1486362 : Nat := 508812088385479223692901

theorem tailTrace_1486362 : CollatzResearch.WordTrace tailWord_1486362 prefixEnd_1486362 508812088385479223692901 := by
  unfold tailWord_1486362
  simp only [CollatzResearch.WordTrace]
  refine ⟨13553018960292949816161335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36141383894114532843096893 13553018960292949816161335)
  ·
    refine ⟨20329528440439424724242003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13553018960292949816161335 20329528440439424724242003)
    ·
      refine ⟨30494292660659137086363005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20329528440439424724242003 30494292660659137086363005)
      ·
        refine ⟨11435359747747176407386127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30494292660659137086363005 11435359747747176407386127)
        ·
          refine ⟨17153039621620764611079191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11435359747747176407386127 17153039621620764611079191)
          ·
            refine ⟨25729559432431146916618787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17153039621620764611079191 25729559432431146916618787)
            ·
              refine ⟨38594339148646720374928181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25729559432431146916618787 38594339148646720374928181)
              ·
                refine ⟨3618219295185630035149517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38594339148646720374928181 3618219295185630035149517)
                ·
                  refine ⟨1356832235694611263181069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3618219295185630035149517 1356832235694611263181069)
                  ·
                    refine ⟨508812088385479223692901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1356832235694611263181069 508812088385479223692901)
                    ·
                      rfl

theorem cell22_1486362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 3, 3].length) (baseStart_1486362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1486362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1486362 prefixEnd_1486362 := by exact prefixLift 1486362
  have htrace : WordTrace (prefixWord ++ tailWord_1486362) baseStart_1486362 baseEnd_1486362 := by
    simpa [prefixWord, tailWord_1486362, baseEnd_1486362] using wordTrace_append hprefix tailTrace_1486362
  have hstable : (prefixWord ++ tailWord_1486362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486362).length < 2 ^ (prefixWord ++ tailWord_1486362).sum := by decide
  have hdescent : baseEnd_1486362 < baseStart_1486362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486437 : List Nat := [1, 3, 1, 3, 3, 1, 2, 2, 6]
def baseStart_1486437 : Nat := 118140960795 + 1486437 * 2 ^ 59
def prefixEnd_1486437 : Nat := 4983230072969 + 3 ^ 40 * 1486437 * 2
def baseEnd_1486437 : Nat := 169612587472734676022557

theorem tailTrace_1486437 : CollatzResearch.WordTrace tailWord_1486437 prefixEnd_1486437 169612587472734676022557 := by
  unfold tailWord_1486437
  simp only [CollatzResearch.WordTrace]
  refine ⟨54214811315900087073625565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36143207543933391382417043 54214811315900087073625565)
  ·
    refine ⟨20330554243462532652609587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54214811315900087073625565 20330554243462532652609587)
    ·
      refine ⟨30495831365193798978914381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20330554243462532652609587 30495831365193798978914381)
      ·
        refine ⟨11435936761947674617092893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30495831365193798978914381 11435936761947674617092893)
        ·
          refine ⟨4288476285730377981409835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11435936761947674617092893 4288476285730377981409835)
          ·
            refine ⟨6432714428595566972114753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4288476285730377981409835 6432714428595566972114753)
            ·
              refine ⟨4824535821446675229086065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6432714428595566972114753 4824535821446675229086065)
              ·
                refine ⟨3618401866085006421814549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4824535821446675229086065 3618401866085006421814549)
                ·
                  refine ⟨169612587472734676022557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3618401866085006421814549 169612587472734676022557)
                  ·
                    rfl

theorem cell22_1486437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 6].length) (baseStart_1486437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1486437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1486437 prefixEnd_1486437 := by exact prefixLift 1486437
  have htrace : WordTrace (prefixWord ++ tailWord_1486437) baseStart_1486437 baseEnd_1486437 := by
    simpa [prefixWord, tailWord_1486437, baseEnd_1486437] using wordTrace_append hprefix tailTrace_1486437
  have hstable : (prefixWord ++ tailWord_1486437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486437).length < 2 ^ (prefixWord ++ tailWord_1486437).sum := by decide
  have hdescent : baseEnd_1486437 < baseStart_1486437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486469 : List Nat := [1, 3, 1, 1, 4, 1, 2, 4, 2, 3]
def baseStart_1486469 : Nat := 118140960795 + 1486469 * 2 ^ 59
def prefixEnd_1486469 : Nat := 4983230072969 + 3 ^ 40 * 1486469 * 2
def baseEnd_1486469 : Nat := 508848716672166611267573

theorem tailTrace_1486469 : CollatzResearch.WordTrace tailWord_1486469 prefixEnd_1486469 508848716672166611267573 := by
  unfold tailWord_1486469
  simp only [CollatzResearch.WordTrace]
  refine ⟨54215978451784156538790461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36143985634522771025860307 54215978451784156538790461)
  ·
    refine ⟨20330991919419058702046423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54215978451784156538790461 20330991919419058702046423)
    ·
      refine ⟨30496487879128588053069635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20330991919419058702046423 30496487879128588053069635)
      ·
        refine ⟨45744731818692882079604453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30496487879128588053069635 45744731818692882079604453)
        ·
          refine ⟨8577137216004915389925835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45744731818692882079604453 8577137216004915389925835)
          ·
            refine ⟨12865705824007373084888753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8577137216004915389925835 12865705824007373084888753)
            ·
              refine ⟨9649279368005529813666565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12865705824007373084888753 9649279368005529813666565)
              ·
                refine ⟨1809239881501036840062481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9649279368005529813666565 1809239881501036840062481)
                ·
                  refine ⟨1356929911125777630046861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1809239881501036840062481 1356929911125777630046861)
                  ·
                    refine ⟨508848716672166611267573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1356929911125777630046861 508848716672166611267573)
                    ·
                      rfl

theorem cell22_1486469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 2, 3].length) (baseStart_1486469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1486469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1486469 prefixEnd_1486469 := by exact prefixLift 1486469
  have htrace : WordTrace (prefixWord ++ tailWord_1486469) baseStart_1486469 baseEnd_1486469 := by
    simpa [prefixWord, tailWord_1486469, baseEnd_1486469] using wordTrace_append hprefix tailTrace_1486469
  have hstable : (prefixWord ++ tailWord_1486469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486469).length < 2 ^ (prefixWord ++ tailWord_1486469).sum := by decide
  have hdescent : baseEnd_1486469 < baseStart_1486469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486471 : List Nat := [1, 1, 4, 2, 1, 4, 3, 2, 4]
def baseStart_1486471 : Nat := 118140960795 + 1486471 * 2 ^ 59
def prefixEnd_1486471 : Nat := 4983230072969 + 3 ^ 40 * 1486471 * 2
def baseEnd_1486471 : Nat := 169616467104346424239189

theorem tailTrace_1486471 : CollatzResearch.WordTrace tailWord_1486471 prefixEnd_1486471 169616467104346424239189 := by
  unfold tailWord_1486471
  simp only [CollatzResearch.WordTrace]
  refine ⟨54216051397776910880363267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36144034265184607253575511 54216051397776910880363267)
  ·
    refine ⟨81324077096665366320544901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54216051397776910880363267 81324077096665366320544901)
    ·
      refine ⟨15248264455624756185102169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81324077096665366320544901 15248264455624756185102169)
      ·
        refine ⟨11436198341718567138826627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15248264455624756185102169 11436198341718567138826627)
        ·
          refine ⟨17154297512577850708239941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11436198341718567138826627 17154297512577850708239941)
          ·
            refine ⟨3216430783608347007794989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17154297512577850708239941 3216430783608347007794989)
            ·
              refine ⟨1206161543853130127923121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3216430783608347007794989 1206161543853130127923121)
              ·
                refine ⟨904621157889847595942341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1206161543853130127923121 904621157889847595942341)
                ·
                  refine ⟨169616467104346424239189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 904621157889847595942341 169616467104346424239189)
                  ·
                    rfl

theorem cell22_1486471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 2, 4].length) (baseStart_1486471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1486471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1486471 prefixEnd_1486471 := by exact prefixLift 1486471
  have htrace : WordTrace (prefixWord ++ tailWord_1486471) baseStart_1486471 baseEnd_1486471 := by
    simpa [prefixWord, tailWord_1486471, baseEnd_1486471] using wordTrace_append hprefix tailTrace_1486471
  have hstable : (prefixWord ++ tailWord_1486471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486471).length < 2 ^ (prefixWord ++ tailWord_1486471).sum := by decide
  have hdescent : baseEnd_1486471 < baseStart_1486471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486604 : List Nat := [2, 2, 1, 2, 2, 1, 5, 1, 1, 5]
def baseStart_1486604 : Nat := 118140960795 + 1486604 * 2 ^ 59
def prefixEnd_1486604 : Nat := 4983230072969 + 3 ^ 40 * 1486604 * 2
def baseEnd_1486604 : Nat := 508894929931071259142159

theorem tailTrace_1486604 : CollatzResearch.WordTrace tailWord_1486604 prefixEnd_1486604 508894929931071259142159 := by
  unfold tailWord_1486604
  simp only [CollatzResearch.WordTrace]
  refine ⟨27110451153147537297477433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36147268204196716396636577 27110451153147537297477433)
  ·
    refine ⟨20332838364860652973108075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27110451153147537297477433 20332838364860652973108075)
    ·
      refine ⟨30499257547290979459662113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20332838364860652973108075 30499257547290979459662113)
      ·
        refine ⟨22874443160468234594746585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30499257547290979459662113 22874443160468234594746585)
        ·
          refine ⟨17155832370351175946059939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22874443160468234594746585 17155832370351175946059939)
          ·
            refine ⟨25733748555526763919089909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17155832370351175946059939 25733748555526763919089909)
            ·
              refine ⟨2412538927080634117414679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25733748555526763919089909 2412538927080634117414679)
              ·
                refine ⟨3618808390620951176122019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2412538927080634117414679 3618808390620951176122019)
                ·
                  refine ⟨5428212585931426764183029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3618808390620951176122019 5428212585931426764183029)
                  ·
                    refine ⟨508894929931071259142159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5428212585931426764183029 508894929931071259142159)
                    ·
                      rfl

theorem cell22_1486604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 1, 5].length) (baseStart_1486604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1486604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1486604 prefixEnd_1486604 := by exact prefixLift 1486604
  have htrace : WordTrace (prefixWord ++ tailWord_1486604) baseStart_1486604 baseEnd_1486604 := by
    simpa [prefixWord, tailWord_1486604, baseEnd_1486604] using wordTrace_append hprefix tailTrace_1486604
  have hstable : (prefixWord ++ tailWord_1486604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486604).length < 2 ^ (prefixWord ++ tailWord_1486604).sum := by decide
  have hdescent : baseEnd_1486604 < baseStart_1486604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486655 : List Nat := [1, 1, 2, 2, 6, 2, 2, 1, 2, 3]
def baseStart_1486655 : Nat := 118140960795 + 1486655 * 2 ^ 59
def prefixEnd_1486655 : Nat := 4983230072969 + 3 ^ 40 * 1486655 * 2
def baseEnd_1486655 : Nat := 508912388273324126117003

theorem tailTrace_1486655 : CollatzResearch.WordTrace tailWord_1486655 prefixEnd_1486655 508912388273324126117003 := by
  unfold tailWord_1486655
  simp only [CollatzResearch.WordTrace]
  refine ⟨54222762429110310305061419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36148508286073540203374279 54222762429110310305061419)
  ·
    refine ⟨81334143643665465457592129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54222762429110310305061419 81334143643665465457592129)
    ·
      refine ⟨61000607732749099093194097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81334143643665465457592129 61000607732749099093194097)
      ·
        refine ⟨45750455799561824319895573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61000607732749099093194097 45750455799561824319895573)
        ·
          refine ⟨2144552615604460514995105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45750455799561824319895573 2144552615604460514995105)
          ·
            refine ⟨1608414461703345386246329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2144552615604460514995105 1608414461703345386246329)
            ·
              refine ⟨1206310846277509039684747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1608414461703345386246329 1206310846277509039684747)
              ·
                refine ⟨1809466269416263559527121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1206310846277509039684747 1809466269416263559527121)
                ·
                  refine ⟨1357099702062197669645341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1809466269416263559527121 1357099702062197669645341)
                  ·
                    refine ⟨508912388273324126117003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1357099702062197669645341 508912388273324126117003)
                    ·
                      rfl

theorem cell22_1486655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 2, 3].length) (baseStart_1486655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1486655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1486655 prefixEnd_1486655 := by exact prefixLift 1486655
  have htrace : WordTrace (prefixWord ++ tailWord_1486655) baseStart_1486655 baseEnd_1486655 := by
    simpa [prefixWord, tailWord_1486655, baseEnd_1486655] using wordTrace_append hprefix tailTrace_1486655
  have hstable : (prefixWord ++ tailWord_1486655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486655).length < 2 ^ (prefixWord ++ tailWord_1486655).sum := by decide
  have hdescent : baseEnd_1486655 < baseStart_1486655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486696 : List Nat := [2, 1, 4, 2, 1, 1, 4, 2, 5]
def baseStart_1486696 : Nat := 118140960795 + 1486696 * 2 ^ 59
def prefixEnd_1486696 : Nat := 4983230072969 + 3 ^ 40 * 1486696 * 2
def baseEnd_1486696 : Nat := 169642141137071228613959

theorem tailTrace_1486696 : CollatzResearch.WordTrace tailWord_1486696 prefixEnd_1486696 169642141137071228613959 := by
  unfold tailWord_1486696
  simp only [CollatzResearch.WordTrace]
  refine ⟨27112128910980887153651971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36149505214641182871535961 27112128910980887153651971)
  ·
    refine ⟨40668193366471330730477957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27112128910980887153651971 40668193366471330730477957)
    ·
      refine ⟨7625286256213374511964617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40668193366471330730477957 7625286256213374511964617)
      ·
        refine ⟨5718964692160030883973463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7625286256213374511964617 5718964692160030883973463)
        ·
          refine ⟨8578447038240046325960195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5718964692160030883973463 8578447038240046325960195)
          ·
            refine ⟨12867670557360069488940293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8578447038240046325960195 12867670557360069488940293)
            ·
              refine ⟨2412688229505013029176305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12867670557360069488940293 2412688229505013029176305)
              ·
                refine ⟨1809516172128759771882229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2412688229505013029176305 1809516172128759771882229)
                ·
                  refine ⟨169642141137071228613959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1809516172128759771882229 169642141137071228613959)
                  ·
                    rfl

theorem cell22_1486696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 5].length) (baseStart_1486696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1486696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1486696 prefixEnd_1486696 := by exact prefixLift 1486696
  have htrace : WordTrace (prefixWord ++ tailWord_1486696) baseStart_1486696 baseEnd_1486696 := by
    simpa [prefixWord, tailWord_1486696, baseEnd_1486696] using wordTrace_append hprefix tailTrace_1486696
  have hstable : (prefixWord ++ tailWord_1486696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486696).length < 2 ^ (prefixWord ++ tailWord_1486696).sum := by decide
  have hdescent : baseEnd_1486696 < baseStart_1486696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486700 : List Nat := [2, 2, 1, 1, 4, 2, 4, 2, 1, 3]
def baseStart_1486700 : Nat := 118140960795 + 1486700 * 2 ^ 59
def prefixEnd_1486700 : Nat := 4983230072969 + 3 ^ 40 * 1486700 * 2
def baseEnd_1486700 : Nat := 508927792692959008741865

theorem tailTrace_1486700 : CollatzResearch.WordTrace tailWord_1486700 prefixEnd_1486700 508927792692959008741865 := by
  unfold tailWord_1486700
  simp only [CollatzResearch.WordTrace]
  refine ⟨27112201856973641495224777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36149602475964855326966369 27112201856973641495224777)
  ·
    refine ⟨20334151392730231121418583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27112201856973641495224777 20334151392730231121418583)
    ·
      refine ⟨30501227089095346682127875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20334151392730231121418583 30501227089095346682127875)
      ·
        refine ⟨45751840633643020023191813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30501227089095346682127875 45751840633643020023191813)
        ·
          refine ⟨8578470118808066254348465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45751840633643020023191813 8578470118808066254348465)
          ·
            refine ⟨6433852589106049690761349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8578470118808066254348465 6433852589106049690761349)
            ·
              refine ⟨1206347360457384317017753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6433852589106049690761349 1206347360457384317017753)
              ·
                refine ⟨904760520343038237763315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1206347360457384317017753 904760520343038237763315)
                ·
                  refine ⟨1357140780514557356644973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 904760520343038237763315 1357140780514557356644973)
                  ·
                    refine ⟨508927792692959008741865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1357140780514557356644973 508927792692959008741865)
                    ·
                      rfl

theorem cell22_1486700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 2, 1, 3].length) (baseStart_1486700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1486700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1486700 prefixEnd_1486700 := by exact prefixLift 1486700
  have htrace : WordTrace (prefixWord ++ tailWord_1486700) baseStart_1486700 baseEnd_1486700 := by
    simpa [prefixWord, tailWord_1486700, baseEnd_1486700] using wordTrace_append hprefix tailTrace_1486700
  have hstable : (prefixWord ++ tailWord_1486700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486700).length < 2 ^ (prefixWord ++ tailWord_1486700).sum := by decide
  have hdescent : baseEnd_1486700 < baseStart_1486700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486724 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 8]
def baseStart_1486724 : Nat := 118140960795 + 1486724 * 2 ^ 59
def prefixEnd_1486724 : Nat := 4983230072969 + 3 ^ 40 * 1486724 * 2
def baseEnd_1486724 : Nat := 169645336127810315380597

theorem tailTrace_1486724 : CollatzResearch.WordTrace tailWord_1486724 prefixEnd_1486724 169645336127810315380597 := by
  unfold tailWord_1486724
  simp only [CollatzResearch.WordTrace]
  refine ⟨27112639532930167544661613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36150186043906890059548817 27112639532930167544661613)
  ·
    refine ⟨10167239824848812829248105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27112639532930167544661613 10167239824848812829248105)
    ·
      refine ⟨7625429868636609621936079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10167239824848812829248105 7625429868636609621936079)
      ·
        refine ⟨11438144802954914432904119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7625429868636609621936079 11438144802954914432904119)
        ·
          refine ⟨17157217204432371649356179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11438144802954914432904119 17157217204432371649356179)
          ·
            refine ⟨25735825806648557474034269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17157217204432371649356179 25735825806648557474034269)
            ·
              refine ⟨9650934677493209052762851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25735825806648557474034269 9650934677493209052762851)
              ·
                refine ⟨14476402016239813579144277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9650934677493209052762851 14476402016239813579144277)
                ·
                  refine ⟨169645336127810315380597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14476402016239813579144277 169645336127810315380597)
                  ·
                    rfl

theorem cell22_1486724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_1486724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1486724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1486724 prefixEnd_1486724 := by exact prefixLift 1486724
  have htrace : WordTrace (prefixWord ++ tailWord_1486724) baseStart_1486724 baseEnd_1486724 := by
    simpa [prefixWord, tailWord_1486724, baseEnd_1486724] using wordTrace_append hprefix tailTrace_1486724
  have hstable : (prefixWord ++ tailWord_1486724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486724).length < 2 ^ (prefixWord ++ tailWord_1486724).sum := by decide
  have hdescent : baseEnd_1486724 < baseStart_1486724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486743 : List Nat := [1, 1, 3, 3, 1, 3, 4, 1, 1, 4]
def baseStart_1486743 : Nat := 118140960795 + 1486743 * 2 ^ 59
def prefixEnd_1486743 : Nat := 4983230072969 + 3 ^ 40 * 1486743 * 2
def baseEnd_1486743 : Nat := 508942512471721229916733

theorem tailTrace_1486743 : CollatzResearch.WordTrace tailWord_1486743 prefixEnd_1486743 508942512471721229916733 := by
  unfold tailWord_1486743
  simp only [CollatzResearch.WordTrace]
  refine ⟨54225972052791501334264883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36150648035194334222843255 54225972052791501334264883)
  ·
    refine ⟨81338958079187252001397325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54225972052791501334264883 81338958079187252001397325)
    ·
      refine ⟨30502109279695219500523997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81338958079187252001397325 30502109279695219500523997)
      ·
        refine ⟨11438290979885707312696499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30502109279695219500523997 11438290979885707312696499)
        ·
          refine ⟨17157436469828560969044749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11438290979885707312696499 17157436469828560969044749)
          ·
            refine ⟨6434038676185710363391781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17157436469828560969044749 6434038676185710363391781)
            ·
              refine ⟨1206382251784820693135959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6434038676185710363391781 1206382251784820693135959)
              ·
                refine ⟨1809573377677231039703939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1206382251784820693135959 1809573377677231039703939)
                ·
                  refine ⟨2714360066515846559555909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1809573377677231039703939 2714360066515846559555909)
                  ·
                    refine ⟨508942512471721229916733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2714360066515846559555909 508942512471721229916733)
                    ·
                      rfl

theorem cell22_1486743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 1, 4].length) (baseStart_1486743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1486743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1486743 prefixEnd_1486743 := by exact prefixLift 1486743
  have htrace : WordTrace (prefixWord ++ tailWord_1486743) baseStart_1486743 baseEnd_1486743 := by
    simpa [prefixWord, tailWord_1486743, baseEnd_1486743] using wordTrace_append hprefix tailTrace_1486743
  have hstable : (prefixWord ++ tailWord_1486743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486743).length < 2 ^ (prefixWord ++ tailWord_1486743).sum := by decide
  have hdescent : baseEnd_1486743 < baseStart_1486743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486773 : List Nat := [1, 3, 3, 2, 1, 4, 1, 1, 1, 5]
def baseStart_1486773 : Nat := 118140960795 + 1486773 * 2 ^ 59
def prefixEnd_1486773 : Nat := 4983230072969 + 3 ^ 40 * 1486773 * 2
def baseEnd_1486773 : Nat := 508952782084811151666641

theorem tailTrace_1486773 : CollatzResearch.WordTrace tailWord_1486773 prefixEnd_1486773 508952782084811151666641 := by
  unfold tailWord_1486773
  simp only [CollatzResearch.WordTrace]
  refine ⟨54227066242682816457856973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36151377495121877638571315 54227066242682816457856973)
  ·
    refine ⟨20335149841006056171696365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54227066242682816457856973 20335149841006056171696365)
    ·
      refine ⟨7625681190377271064386137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20335149841006056171696365 7625681190377271064386137)
      ·
        refine ⟨5719260892782953298289603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7625681190377271064386137 5719260892782953298289603)
        ·
          refine ⟨8578891339174429947434405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5719260892782953298289603 8578891339174429947434405)
          ·
            refine ⟨1608542126095205615143951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8578891339174429947434405 1608542126095205615143951)
            ·
              refine ⟨2412813189142808422715927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1608542126095205615143951 2412813189142808422715927)
              ·
                refine ⟨3619219783714212634073891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2412813189142808422715927 3619219783714212634073891)
                ·
                  refine ⟨5428829675571318951110837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3619219783714212634073891 5428829675571318951110837)
                  ·
                    refine ⟨508952782084811151666641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5428829675571318951110837 508952782084811151666641)
                    ·
                      rfl

theorem cell22_1486773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_1486773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1486773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1486773 prefixEnd_1486773 := by exact prefixLift 1486773
  have htrace : WordTrace (prefixWord ++ tailWord_1486773) baseStart_1486773 baseEnd_1486773 := by
    simpa [prefixWord, tailWord_1486773, baseEnd_1486773] using wordTrace_append hprefix tailTrace_1486773
  have hstable : (prefixWord ++ tailWord_1486773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486773).length < 2 ^ (prefixWord ++ tailWord_1486773).sum := by decide
  have hdescent : baseEnd_1486773 < baseStart_1486773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486784 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 2, 7]
def baseStart_1486784 : Nat := 118140960795 + 1486784 * 2 ^ 59
def prefixEnd_1486784 : Nat := 4983230072969 + 3 ^ 40 * 1486784 * 2
def baseEnd_1486784 : Nat := 508956547609610789641607

theorem tailTrace_1486784 : CollatzResearch.WordTrace tailWord_1486784 prefixEnd_1486784 508956547609610789641607 := by
  unfold tailWord_1486784
  simp only [CollatzResearch.WordTrace]
  refine ⟨27113733722821482668253703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36151644963761976891004937 27113733722821482668253703)
  ·
    refine ⟨40670600584232224002380555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27113733722821482668253703 40670600584232224002380555)
    ·
      refine ⟨61005900876348336003570833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40670600584232224002380555 61005900876348336003570833)
      ·
        refine ⟨45754425657261252002678125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61005900876348336003570833 45754425657261252002678125)
        ·
          refine ⟨17157909621472969501004297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45754425657261252002678125 17157909621472969501004297)
          ·
            refine ⟨12868432216104727125753223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17157909621472969501004297 12868432216104727125753223)
            ·
              refine ⟨19302648324157090688629835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12868432216104727125753223 19302648324157090688629835)
              ·
                refine ⟨28953972486235636032944753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19302648324157090688629835 28953972486235636032944753)
                ·
                  refine ⟨21715479364676727024708565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28953972486235636032944753 21715479364676727024708565)
                  ·
                    refine ⟨508956547609610789641607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21715479364676727024708565 508956547609610789641607)
                    ·
                      rfl

theorem cell22_1486784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 2, 7].length) (baseStart_1486784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1486784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1486784 prefixEnd_1486784 := by exact prefixLift 1486784
  have htrace : WordTrace (prefixWord ++ tailWord_1486784) baseStart_1486784 baseEnd_1486784 := by
    simpa [prefixWord, tailWord_1486784, baseEnd_1486784] using wordTrace_append hprefix tailTrace_1486784
  have hstable : (prefixWord ++ tailWord_1486784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486784).length < 2 ^ (prefixWord ++ tailWord_1486784).sum := by decide
  have hdescent : baseEnd_1486784 < baseStart_1486784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486831 : List Nat := [1, 1, 2, 1, 4, 2, 3, 3, 5]
def baseStart_1486831 : Nat := 118140960795 + 1486831 * 2 ^ 59
def prefixEnd_1486831 : Nat := 4983230072969 + 3 ^ 40 * 1486831 * 2
def baseEnd_1486831 : Nat := 169657545556706111238821

theorem tailTrace_1486831 : CollatzResearch.WordTrace tailWord_1486831 prefixEnd_1486831 169657545556706111238821 := by
  unfold tailWord_1486831
  simp only [CollatzResearch.WordTrace]
  refine ⟨54229181676472692363468347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36152787784315128242312231 54229181676472692363468347)
  ·
    refine ⟨81343772514709038545202521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54229181676472692363468347 81343772514709038545202521)
    ·
      refine ⟨61007829386031778908901891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81343772514709038545202521 61007829386031778908901891)
      ·
        refine ⟨91511744079047668363352837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61007829386031778908901891 91511744079047668363352837)
        ·
          refine ⟨17158452014821437818128657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91511744079047668363352837 17158452014821437818128657)
          ·
            refine ⟨12868839011116078363596493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17158452014821437818128657 12868839011116078363596493)
            ·
              refine ⟨4825814629168529386348685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12868839011116078363596493 4825814629168529386348685)
              ·
                refine ⟨1809680485938198519880757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4825814629168529386348685 1809680485938198519880757)
                ·
                  refine ⟨169657545556706111238821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1809680485938198519880757 169657545556706111238821)
                  ·
                    rfl

theorem cell22_1486831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 5].length) (baseStart_1486831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1486831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1486831 prefixEnd_1486831 := by exact prefixLift 1486831
  have htrace : WordTrace (prefixWord ++ tailWord_1486831) baseStart_1486831 baseEnd_1486831 := by
    simpa [prefixWord, tailWord_1486831, baseEnd_1486831] using wordTrace_append hprefix tailTrace_1486831
  have hstable : (prefixWord ++ tailWord_1486831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486831).length < 2 ^ (prefixWord ++ tailWord_1486831).sum := by decide
  have hdescent : baseEnd_1486831 < baseStart_1486831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486869 : List Nat := [1, 3, 2, 1, 5, 2, 2, 2, 1, 3]
def baseStart_1486869 : Nat := 118140960795 + 1486869 * 2 ^ 59
def prefixEnd_1486869 : Nat := 4983230072969 + 3 ^ 40 * 1486869 * 2
def baseEnd_1486869 : Nat := 508985644846698901266347

theorem tailTrace_1486869 : CollatzResearch.WordTrace tailWord_1486869 prefixEnd_1486869 508985644846698901266347 := by
  unfold tailWord_1486869
  simp only [CollatzResearch.WordTrace]
  refine ⟨54230567650335024853351661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36153711766890016568901107 54230567650335024853351661)
  ·
    refine ⟨20336462868875634320006873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54230567650335024853351661 20336462868875634320006873)
    ·
      refine ⟨15252347151656725740005155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20336462868875634320006873 15252347151656725740005155)
      ·
        refine ⟨22878520727485088610007733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15252347151656725740005155 22878520727485088610007733)
        ·
          refine ⟨2144861318201727057188225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22878520727485088610007733 2144861318201727057188225)
          ·
            refine ⟨1608645988651295292891169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2144861318201727057188225 1608645988651295292891169)
            ·
              refine ⟨1206484491488471469668377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1608645988651295292891169 1206484491488471469668377)
              ·
                refine ⟨904863368616353602251283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1206484491488471469668377 904863368616353602251283)
                ·
                  refine ⟨1357295052924530403376925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 904863368616353602251283 1357295052924530403376925)
                  ·
                    refine ⟨508985644846698901266347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1357295052924530403376925 508985644846698901266347)
                    ·
                      rfl

theorem cell22_1486869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 2, 1, 3].length) (baseStart_1486869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1486869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1486869 prefixEnd_1486869 := by exact prefixLift 1486869
  have htrace : WordTrace (prefixWord ++ tailWord_1486869) baseStart_1486869 baseEnd_1486869 := by
    simpa [prefixWord, tailWord_1486869, baseEnd_1486869] using wordTrace_append hprefix tailTrace_1486869
  have hstable : (prefixWord ++ tailWord_1486869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486869).length < 2 ^ (prefixWord ++ tailWord_1486869).sum := by decide
  have hdescent : baseEnd_1486869 < baseStart_1486869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486908 : List Nat := [2, 2, 2, 2, 2, 1, 2, 2, 4, 3]
def baseStart_1486908 : Nat := 118140960795 + 1486908 * 2 ^ 59
def prefixEnd_1486908 : Nat := 4983230072969 + 3 ^ 40 * 1486908 * 2
def baseEnd_1486908 : Nat := 508998995343715799541227

theorem tailTrace_1486908 : CollatzResearch.WordTrace tailWord_1486908 prefixEnd_1486908 508998995343715799541227 := by
  unfold tailWord_1486908
  simp only [CollatzResearch.WordTrace]
  refine ⟨27115995048596867257010689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36154660064795823009347585 27115995048596867257010689)
  ·
    refine ⟨20336996286447650442758017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27115995048596867257010689 20336996286447650442758017)
    ·
      refine ⟨15252747214835737832068513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20336996286447650442758017 15252747214835737832068513)
      ·
        refine ⟨11439560411126803374051385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15252747214835737832068513 11439560411126803374051385)
        ·
          refine ⟨8579670308345102530538539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11439560411126803374051385 8579670308345102530538539)
          ·
            refine ⟨12869505462517653795807809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8579670308345102530538539 12869505462517653795807809)
            ·
              refine ⟨9652129096888240346855857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12869505462517653795807809 9652129096888240346855857)
              ·
                refine ⟨7239096822666180260141893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9652129096888240346855857 7239096822666180260141893)
                ·
                  refine ⟨1357330654249908798776605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7239096822666180260141893 1357330654249908798776605)
                  ·
                    refine ⟨508998995343715799541227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1357330654249908798776605 508998995343715799541227)
                    ·
                      rfl

theorem cell22_1486908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_1486908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1486908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1486908 prefixEnd_1486908 := by exact prefixLift 1486908
  have htrace : WordTrace (prefixWord ++ tailWord_1486908) baseStart_1486908 baseEnd_1486908 := by
    simpa [prefixWord, tailWord_1486908, baseEnd_1486908] using wordTrace_append hprefix tailTrace_1486908
  have hstable : (prefixWord ++ tailWord_1486908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486908).length < 2 ^ (prefixWord ++ tailWord_1486908).sum := by decide
  have hdescent : baseEnd_1486908 < baseStart_1486908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486925 : List Nat := [1, 6, 1, 1, 1, 1, 3, 1, 4, 3]
def baseStart_1486925 : Nat := 118140960795 + 1486925 * 2 ^ 59
def prefixEnd_1486925 : Nat := 4983230072969 + 3 ^ 40 * 1486925 * 2
def baseEnd_1486925 : Nat := 509004814791133421866175

theorem tailTrace_1486925 : CollatzResearch.WordTrace tailWord_1486925 prefixEnd_1486925 509004814791133421866175 := by
  unfold tailWord_1486925
  simp only [CollatzResearch.WordTrace]
  refine ⟨54232610138132146417390229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36155073425421430944926819 54232610138132146417390229)
  ·
    refine ⟨2542153600224944363315167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54232610138132146417390229 2542153600224944363315167)
    ·
      refine ⟨3813230400337416544972751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2542153600224944363315167 3813230400337416544972751)
      ·
        refine ⟨5719845600506124817459127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3813230400337416544972751 5719845600506124817459127)
        ·
          refine ⟨8579768400759187226188691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5719845600506124817459127 8579768400759187226188691)
          ·
            refine ⟨12869652601138780839283037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8579768400759187226188691 12869652601138780839283037)
            ·
              refine ⟨4826119725427042814731139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12869652601138780839283037 4826119725427042814731139)
              ·
                refine ⟨7239179588140564222096709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4826119725427042814731139 7239179588140564222096709)
                ·
                  refine ⟨1357346172776355791643133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7239179588140564222096709 1357346172776355791643133)
                  ·
                    refine ⟨509004814791133421866175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1357346172776355791643133 509004814791133421866175)
                    ·
                      rfl

theorem cell22_1486925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_1486925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1486925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1486925 prefixEnd_1486925 := by exact prefixLift 1486925
  have htrace : WordTrace (prefixWord ++ tailWord_1486925) baseStart_1486925 baseEnd_1486925 := by
    simpa [prefixWord, tailWord_1486925, baseEnd_1486925] using wordTrace_append hprefix tailTrace_1486925
  have hstable : (prefixWord ++ tailWord_1486925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486925).length < 2 ^ (prefixWord ++ tailWord_1486925).sum := by decide
  have hdescent : baseEnd_1486925 < baseStart_1486925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1486953 : List Nat := [1, 2, 1, 1, 1, 5, 1, 4, 3, 3]
def baseStart_1486953 : Nat := 118140960795 + 1486953 * 2 ^ 59
def prefixEnd_1486953 : Nat := 4983230072969 + 3 ^ 40 * 1486953 * 2
def baseEnd_1486953 : Nat := 509014399763350682166089

theorem tailTrace_1486953 : CollatzResearch.WordTrace tailWord_1486953 prefixEnd_1486953 509014399763350682166089 := by
  unfold tailWord_1486953
  simp only [CollatzResearch.WordTrace]
  refine ⟨54233631382030707199409513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36155754254687138132939675 54233631382030707199409513)
  ·
    refine ⟨40675223536523030399557135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54233631382030707199409513 40675223536523030399557135)
    ·
      refine ⟨61012835304784545599335703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40675223536523030399557135 61012835304784545599335703)
      ·
        refine ⟨91519252957176818399003555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61012835304784545599335703 91519252957176818399003555)
        ·
          refine ⟨137278879435765227598505333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91519252957176818399003555 137278879435765227598505333)
          ·
            refine ⟨12869894947102990087359875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137278879435765227598505333 12869894947102990087359875)
            ·
              refine ⟨19304842420654485131039813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12869894947102990087359875 19304842420654485131039813)
              ·
                refine ⟨3619657953872715962069965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19304842420654485131039813 3619657953872715962069965)
                ·
                  refine ⟨1357371732702268485776237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3619657953872715962069965 1357371732702268485776237)
                  ·
                    refine ⟨509014399763350682166089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1357371732702268485776237 509014399763350682166089)
                    ·
                      rfl

theorem cell22_1486953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 3, 3].length) (baseStart_1486953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1486953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1486953 prefixEnd_1486953 := by exact prefixLift 1486953
  have htrace : WordTrace (prefixWord ++ tailWord_1486953) baseStart_1486953 baseEnd_1486953 := by
    simpa [prefixWord, tailWord_1486953, baseEnd_1486953] using wordTrace_append hprefix tailTrace_1486953
  have hstable : (prefixWord ++ tailWord_1486953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1486953).length < 2 ^ (prefixWord ++ tailWord_1486953).sum := by decide
  have hdescent : baseEnd_1486953 < baseStart_1486953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1486953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487000 : List Nat := [2, 1, 2, 4, 3, 1, 1, 3, 5]
def baseStart_1487000 : Nat := 118140960795 + 1487000 * 2 ^ 59
def prefixEnd_1487000 : Nat := 4983230072969 + 3 ^ 40 * 1487000 * 2
def baseEnd_1487000 : Nat := 169676829607952742080315

theorem tailTrace_1487000 : CollatzResearch.WordTrace tailWord_1487000 prefixEnd_1487000 169676829607952742080315 := by
  unfold tailWord_1487000
  simp only [CollatzResearch.WordTrace]
  refine ⟨27117672806430217113185227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36156897075240289484246969 27117672806430217113185227)
  ·
    refine ⟨40676509209645325669777841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27117672806430217113185227 40676509209645325669777841)
    ·
      refine ⟨30507381907233994252333381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40676509209645325669777841 30507381907233994252333381)
      ·
        refine ⟨5720134107606373922312509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30507381907233994252333381 5720134107606373922312509)
        ·
          refine ⟨2145050290352390220867191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5720134107606373922312509 2145050290352390220867191)
          ·
            refine ⟨3217575435528585331300787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2145050290352390220867191 3217575435528585331300787)
            ·
              refine ⟨4826363153292877996951181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3217575435528585331300787 4826363153292877996951181)
              ·
                refine ⟨1809886182484829248856693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4826363153292877996951181 1809886182484829248856693)
                ·
                  refine ⟨169676829607952742080315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1809886182484829248856693 169676829607952742080315)
                  ·
                    rfl

theorem cell22_1487000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 3, 5].length) (baseStart_1487000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1487000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1487000 prefixEnd_1487000 := by exact prefixLift 1487000
  have htrace : WordTrace (prefixWord ++ tailWord_1487000) baseStart_1487000 baseEnd_1487000 := by
    simpa [prefixWord, tailWord_1487000, baseEnd_1487000] using wordTrace_append hprefix tailTrace_1487000
  have hstable : (prefixWord ++ tailWord_1487000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487000).length < 2 ^ (prefixWord ++ tailWord_1487000).sum := by decide
  have hdescent : baseEnd_1487000 < baseStart_1487000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487013 : List Nat := [1, 3, 1, 2, 1, 3, 3, 1, 3, 4]
def baseStart_1487013 : Nat := 118140960795 + 1487013 * 2 ^ 59
def prefixEnd_1487013 : Nat := 4983230072969 + 3 ^ 40 * 1487013 * 2
def baseEnd_1487013 : Nat := 509034938989530525665905

theorem tailTrace_1487013 : CollatzResearch.WordTrace tailWord_1487013 prefixEnd_1487013 509034938989530525665905 := by
  unfold tailWord_1487013
  simp only [CollatzResearch.WordTrace]
  refine ⟨54235819761813337446593693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36157213174542224964395795 54235819761813337446593693)
  ·
    refine ⟨20338432410680001542472635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54235819761813337446593693 20338432410680001542472635)
    ·
      refine ⟨30507648616020002313708953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20338432410680001542472635 30507648616020002313708953)
      ·
        refine ⟨22880736462015001735281715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30507648616020002313708953 22880736462015001735281715)
        ·
          refine ⟨34321104693022502602922573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22880736462015001735281715 34321104693022502602922573)
          ·
            refine ⟨12870414259883438476095965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34321104693022502602922573 12870414259883438476095965)
            ·
              refine ⟨4826405347456289428535987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12870414259883438476095965 4826405347456289428535987)
              ·
                refine ⟨7239608021184434142803981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4826405347456289428535987 7239608021184434142803981)
                ·
                  refine ⟨2714853007944162803551493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7239608021184434142803981 2714853007944162803551493)
                  ·
                    refine ⟨509034938989530525665905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2714853007944162803551493 509034938989530525665905)
                    ·
                      rfl

theorem cell22_1487013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_1487013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1487013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1487013 prefixEnd_1487013 := by exact prefixLift 1487013
  have htrace : WordTrace (prefixWord ++ tailWord_1487013) baseStart_1487013 baseEnd_1487013 := by
    simpa [prefixWord, tailWord_1487013, baseEnd_1487013] using wordTrace_append hprefix tailTrace_1487013
  have hstable : (prefixWord ++ tailWord_1487013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487013).length < 2 ^ (prefixWord ++ tailWord_1487013).sum := by decide
  have hdescent : baseEnd_1487013 < baseStart_1487013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487038 : List Nat := [4, 2, 1, 1, 5, 1, 2, 2, 1, 3]
def baseStart_1487038 : Nat := 118140960795 + 1487038 * 2 ^ 59
def prefixEnd_1487038 : Nat := 4983230072969 + 3 ^ 40 * 1487038 * 2
def baseEnd_1487038 : Nat := 509043497000438793790829

theorem tailTrace_1487038 : CollatzResearch.WordTrace tailWord_1487038 prefixEnd_1487038 509043497000438793790829 := by
  unfold tailWord_1487038
  simp only [CollatzResearch.WordTrace]
  refine ⟨6779591448340345839531721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36157821057815177810835845 6779591448340345839531721)
  ·
    refine ⟨5084693586255259379648791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6779591448340345839531721 5084693586255259379648791)
    ·
      refine ⟨7627040379382889069473187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5084693586255259379648791 7627040379382889069473187)
      ·
        refine ⟨11440560569074333604209781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7627040379382889069473187 11440560569074333604209781)
        ·
          refine ⟨1072552553350718775394667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11440560569074333604209781 1072552553350718775394667)
          ·
            refine ⟨1608828830026078163092001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1072552553350718775394667 1608828830026078163092001)
            ·
              refine ⟨1206621622519558622319001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1608828830026078163092001 1206621622519558622319001)
              ·
                refine ⟨904966216889668966739251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1206621622519558622319001 904966216889668966739251)
                ·
                  refine ⟨1357449325334503450108877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 904966216889668966739251 1357449325334503450108877)
                  ·
                    refine ⟨509043497000438793790829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1357449325334503450108877 509043497000438793790829)
                    ·
                      rfl

theorem cell22_1487038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_1487038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1487038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1487038 prefixEnd_1487038 := by exact prefixLift 1487038
  have htrace : WordTrace (prefixWord ++ tailWord_1487038) baseStart_1487038 baseEnd_1487038 := by
    simpa [prefixWord, tailWord_1487038, baseEnd_1487038] using wordTrace_append hprefix tailTrace_1487038
  have hstable : (prefixWord ++ tailWord_1487038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487038).length < 2 ^ (prefixWord ++ tailWord_1487038).sum := by decide
  have hdescent : baseEnd_1487038 < baseStart_1487038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487043 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 8, 3]
def baseStart_1487043 : Nat := 118140960795 + 1487043 * 2 ^ 59
def prefixEnd_1487043 : Nat := 4983230072969 + 3 ^ 40 * 1487043 * 2
def baseEnd_1487043 : Nat := 509045208602620447415813

theorem tailTrace_1487043 : CollatzResearch.WordTrace tailWord_1487043 prefixEnd_1487043 509045208602620447415813 := by
  unfold tailWord_1487043
  simp only [CollatzResearch.WordTrace]
  refine ⟨54236913951704652570185783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36157942634469768380123855 54236913951704652570185783)
  ·
    refine ⟨81355370927556978855278675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54236913951704652570185783 81355370927556978855278675)
    ·
      refine ⟨122033056391335468282918013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81355370927556978855278675 122033056391335468282918013)
      ·
        refine ⟨45762396146750800606094255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122033056391335468282918013 45762396146750800606094255)
        ·
          refine ⟨68643594220126200909141383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45762396146750800606094255 68643594220126200909141383)
          ·
            refine ⟨102965391330189301363712075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68643594220126200909141383 102965391330189301363712075)
            ·
              refine ⟨154448086995283952045568113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102965391330189301363712075 154448086995283952045568113)
              ·
                refine ⟨115836065246462964034176085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154448086995283952045568113 115836065246462964034176085)
                ·
                  refine ⟨1357453889606987859775501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 115836065246462964034176085 1357453889606987859775501)
                  ·
                    refine ⟨509045208602620447415813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1357453889606987859775501 509045208602620447415813)
                    ·
                      rfl

theorem cell22_1487043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 8, 3].length) (baseStart_1487043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1487043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1487043 prefixEnd_1487043 := by exact prefixLift 1487043
  have htrace : WordTrace (prefixWord ++ tailWord_1487043) baseStart_1487043 baseEnd_1487043 := by
    simpa [prefixWord, tailWord_1487043, baseEnd_1487043] using wordTrace_append hprefix tailTrace_1487043
  have hstable : (prefixWord ++ tailWord_1487043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487043).length < 2 ^ (prefixWord ++ tailWord_1487043).sum := by decide
  have hdescent : baseEnd_1487043 < baseStart_1487043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487062 : List Nat := [5, 2, 1, 2, 1, 2, 1, 2, 6]
def baseStart_1487062 : Nat := 118140960795 + 1487062 * 2 ^ 59
def prefixEnd_1487062 : Nat := 4983230072969 + 3 ^ 40 * 1487062 * 2
def baseEnd_1487062 : Nat := 169683904230303577063585

theorem tailTrace_1487062 : CollatzResearch.WordTrace tailWord_1487062 prefixEnd_1487062 169683904230303577063585 := by
  unfold tailWord_1487062
  simp only [CollatzResearch.WordTrace]
  refine ⟨3389850433664738675945465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36158404625757212543418293 3389850433664738675945465)
  ·
    refine ⟨2542387825248554006959099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3389850433664738675945465 2542387825248554006959099)
    ·
      refine ⟨3813581737872831010438649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2542387825248554006959099 3813581737872831010438649)
      ·
        refine ⟨2860186303404623257828987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3813581737872831010438649 2860186303404623257828987)
        ·
          refine ⟨4290279455106934886743481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2860186303404623257828987 4290279455106934886743481)
          ·
            refine ⟨3217709591330201165057611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4290279455106934886743481 3217709591330201165057611)
            ·
              refine ⟨4826564386995301747586417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3217709591330201165057611 4826564386995301747586417)
              ·
                refine ⟨3619923290246476310689813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4826564386995301747586417 3619923290246476310689813)
                ·
                  refine ⟨169683904230303577063585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3619923290246476310689813 169683904230303577063585)
                  ·
                    rfl

theorem cell22_1487062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_1487062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1487062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1487062 prefixEnd_1487062 := by exact prefixLift 1487062
  have htrace : WordTrace (prefixWord ++ tailWord_1487062) baseStart_1487062 baseEnd_1487062 := by
    simpa [prefixWord, tailWord_1487062, baseEnd_1487062] using wordTrace_append hprefix tailTrace_1487062
  have hstable : (prefixWord ++ tailWord_1487062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487062).length < 2 ^ (prefixWord ++ tailWord_1487062).sum := by decide
  have hdescent : baseEnd_1487062 < baseStart_1487062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487111 : List Nat := [1, 1, 4, 5, 1, 1, 3, 1, 2, 3]
def baseStart_1487111 : Nat := 118140960795 + 1487111 * 2 ^ 59
def prefixEnd_1487111 : Nat := 4983230072969 + 3 ^ 40 * 1487111 * 2
def baseEnd_1487111 : Nat := 509068486392290936715605

theorem tailTrace_1487111 : CollatzResearch.WordTrace tailWord_1487111 prefixEnd_1487111 509068486392290936715605 := by
  unfold tailWord_1487111
  simp only [CollatzResearch.WordTrace]
  refine ⟨54239394115458300183661187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36159596076972200122440791 54239394115458300183661187)
  ·
    refine ⟨81359091173187450275491781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54239394115458300183661187 81359091173187450275491781)
    ·
      refine ⟨15254829594972646926654709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81359091173187450275491781 15254829594972646926654709)
      ·
        refine ⟨1430140274528685649373879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15254829594972646926654709 1430140274528685649373879)
        ·
          refine ⟨2145210411793028474060819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1430140274528685649373879 2145210411793028474060819)
          ·
            refine ⟨3217815617689542711091229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2145210411793028474060819 3217815617689542711091229)
            ·
              refine ⟨1206680856633578516659211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3217815617689542711091229 1206680856633578516659211)
              ·
                refine ⟨1810021284950367774988817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1206680856633578516659211 1810021284950367774988817)
                ·
                  refine ⟨1357515963712775831241613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1810021284950367774988817 1357515963712775831241613)
                  ·
                    refine ⟨509068486392290936715605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1357515963712775831241613 509068486392290936715605)
                    ·
                      rfl

theorem cell22_1487111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_1487111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1487111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1487111 prefixEnd_1487111 := by exact prefixLift 1487111
  have htrace : WordTrace (prefixWord ++ tailWord_1487111) baseStart_1487111 baseEnd_1487111 := by
    simpa [prefixWord, tailWord_1487111, baseEnd_1487111] using wordTrace_append hprefix tailTrace_1487111
  have hstable : (prefixWord ++ tailWord_1487111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487111).length < 2 ^ (prefixWord ++ tailWord_1487111).sum := by decide
  have hdescent : baseEnd_1487111 < baseStart_1487111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487308 : List Nat := [2, 2, 1, 4, 3, 2, 1, 3, 1, 3]
def baseStart_1487308 : Nat := 118140960795 + 1487308 * 2 ^ 59
def prefixEnd_1487308 : Nat := 4983230072969 + 3 ^ 40 * 1487308 * 2
def baseEnd_1487308 : Nat := 509135923518248089540001

theorem tailTrace_1487308 : CollatzResearch.WordTrace tailWord_1487308 prefixEnd_1487308 509135923518248089540001 := by
  unfold tailWord_1487308
  simp only [CollatzResearch.WordTrace]
  refine ⟨27123289647872301414291289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36164386197163068552388385 27123289647872301414291289)
  ·
    refine ⟨20342467235904226060718467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27123289647872301414291289 20342467235904226060718467)
    ·
      refine ⟨30513700853856339091077701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20342467235904226060718467 30513700853856339091077701)
      ·
        refine ⟨5721318910098063579577069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30513700853856339091077701 5721318910098063579577069)
        ·
          refine ⟨2145494591286773842341401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5721318910098063579577069 2145494591286773842341401)
          ·
            refine ⟨1609120943465080381756051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2145494591286773842341401 1609120943465080381756051)
            ·
              refine ⟨2413681415197620572634077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1609120943465080381756051 2413681415197620572634077)
              ·
                refine ⟨905130530699107714737779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2413681415197620572634077 905130530699107714737779)
                ·
                  refine ⟨1357695796048661572106669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 905130530699107714737779 1357695796048661572106669)
                  ·
                    refine ⟨509135923518248089540001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1357695796048661572106669 509135923518248089540001)
                    ·
                      rfl

theorem cell22_1487308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 3, 1, 3].length) (baseStart_1487308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1487308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1487308 prefixEnd_1487308 := by exact prefixLift 1487308
  have htrace : WordTrace (prefixWord ++ tailWord_1487308) baseStart_1487308 baseEnd_1487308 := by
    simpa [prefixWord, tailWord_1487308, baseEnd_1487308] using wordTrace_append hprefix tailTrace_1487308
  have hstable : (prefixWord ++ tailWord_1487308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487308).length < 2 ^ (prefixWord ++ tailWord_1487308).sum := by decide
  have hdescent : baseEnd_1487308 < baseStart_1487308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487364 : List Nat := [2, 3, 2, 3, 1, 2, 1, 2, 1, 5]
def baseStart_1487364 : Nat := 118140960795 + 1487364 * 2 ^ 59
def prefixEnd_1487364 : Nat := 4983230072969 + 3 ^ 40 * 1487364 * 2
def baseEnd_1487364 : Nat := 509155093462682610139829

theorem tailTrace_1487364 : CollatzResearch.WordTrace tailWord_1487364 prefixEnd_1487364 509155093462682610139829 := by
  unfold tailWord_1487364
  simp only [CollatzResearch.WordTrace]
  refine ⟨27124310891770862196310573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36165747855694482928414097 27124310891770862196310573)
  ·
    refine ⟨10171616584414073323616465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27124310891770862196310573 10171616584414073323616465)
    ·
      refine ⟨7628712438310554992712349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10171616584414073323616465 7628712438310554992712349)
      ·
        refine ⟨2860767164366458122267131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7628712438310554992712349 2860767164366458122267131)
        ·
          refine ⟨4291150746549687183400697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2860767164366458122267131 4291150746549687183400697)
          ·
            refine ⟨3218363059912265387550523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4291150746549687183400697 3218363059912265387550523)
            ·
              refine ⟨4827544589868398081325785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3218363059912265387550523 4827544589868398081325785)
              ·
                refine ⟨3620658442401298560994339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4827544589868398081325785 3620658442401298560994339)
                ·
                  refine ⟨5430987663601947841491509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3620658442401298560994339 5430987663601947841491509)
                  ·
                    refine ⟨509155093462682610139829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5430987663601947841491509 509155093462682610139829)
                    ·
                      rfl

theorem cell22_1487364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_1487364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1487364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1487364 prefixEnd_1487364 := by exact prefixLift 1487364
  have htrace : WordTrace (prefixWord ++ tailWord_1487364) baseStart_1487364 baseEnd_1487364 := by
    simpa [prefixWord, tailWord_1487364, baseEnd_1487364] using wordTrace_append hprefix tailTrace_1487364
  have hstable : (prefixWord ++ tailWord_1487364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487364).length < 2 ^ (prefixWord ++ tailWord_1487364).sum := by decide
  have hdescent : baseEnd_1487364 < baseStart_1487364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487477 : List Nat := [1, 3, 4, 2, 3, 1, 1, 3, 1, 3]
def baseStart_1487477 : Nat := 118140960795 + 1487477 * 2 ^ 59
def prefixEnd_1487477 : Nat := 4983230072969 + 3 ^ 40 * 1487477 * 2
def baseEnd_1487477 : Nat := 509193775671987982064483

theorem tailTrace_1487477 : CollatzResearch.WordTrace tailWord_1487477 prefixEnd_1487477 509193775671987982064483 := by
  unfold tailWord_1487477
  simp only [CollatzResearch.WordTrace]
  refine ⟨54252743232132344691484685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36168495488088229794323123 54252743232132344691484685)
  ·
    refine ⟨20344778712049629259306757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54252743232132344691484685 20344778712049629259306757)
    ·
      refine ⟨3814646008509305486120017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20344778712049629259306757 3814646008509305486120017)
      ·
        refine ⟨2860984506381979114590013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3814646008509305486120017 2860984506381979114590013)
        ·
          refine ⟨1072869189893242167971255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2860984506381979114590013 1072869189893242167971255)
          ·
            refine ⟨1609303784839863251956883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1072869189893242167971255 1609303784839863251956883)
            ·
              refine ⟨2413955677259794877935325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1609303784839863251956883 2413955677259794877935325)
              ·
                refine ⟨905233378972423079225747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2413955677259794877935325 905233378972423079225747)
                ·
                  refine ⟨1357850068458634618838621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 905233378972423079225747 1357850068458634618838621)
                  ·
                    refine ⟨509193775671987982064483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1357850068458634618838621 509193775671987982064483)
                    ·
                      rfl

theorem cell22_1487477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_1487477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1487477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1487477 prefixEnd_1487477 := by exact prefixLift 1487477
  have htrace : WordTrace (prefixWord ++ tailWord_1487477) baseStart_1487477 baseEnd_1487477 := by
    simpa [prefixWord, tailWord_1487477, baseEnd_1487477] using wordTrace_append hprefix tailTrace_1487477
  have hstable : (prefixWord ++ tailWord_1487477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487477).length < 2 ^ (prefixWord ++ tailWord_1487477).sum := by decide
  have hdescent : baseEnd_1487477 < baseStart_1487477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487649 : List Nat := [1, 2, 3, 2, 1, 2, 1, 3, 1, 6]
def baseStart_1487649 : Nat := 118140960795 + 1487649 * 2 ^ 59
def prefixEnd_1487649 : Nat := 4983230072969 + 3 ^ 40 * 1487649 * 2
def baseEnd_1487649 : Nat := 509252654787036866763955

theorem tailTrace_1487649 : CollatzResearch.WordTrace tailWord_1487649 prefixEnd_1487649 509252654787036866763955 := by
  unfold tailWord_1487649
  simp only [CollatzResearch.WordTrace]
  refine ⟨54259016587509218066746001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36172677725006145377830667 54259016587509218066746001)
  ·
    refine ⟨40694262440631913550059501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54259016587509218066746001 40694262440631913550059501)
    ·
      refine ⟨15260348415236967581272313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40694262440631913550059501 15260348415236967581272313)
      ·
        refine ⟨11445261311427725685954235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15260348415236967581272313 11445261311427725685954235)
        ·
          refine ⟨17167891967141588528931353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11445261311427725685954235 17167891967141588528931353)
          ·
            refine ⟨12875918975356191396698515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17167891967141588528931353 12875918975356191396698515)
            ·
              refine ⟨19313878463034287095047773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12875918975356191396698515 19313878463034287095047773)
              ·
                refine ⟨7242704423637857660642915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19313878463034287095047773 7242704423637857660642915)
                ·
                  refine ⟨10864056635456786490964373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7242704423637857660642915 10864056635456786490964373)
                  ·
                    refine ⟨509252654787036866763955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10864056635456786490964373 509252654787036866763955)
                    ·
                      rfl

theorem cell22_1487649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_1487649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1487649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1487649 prefixEnd_1487649 := by exact prefixLift 1487649
  have htrace : WordTrace (prefixWord ++ tailWord_1487649) baseStart_1487649 baseEnd_1487649 := by
    simpa [prefixWord, tailWord_1487649, baseEnd_1487649] using wordTrace_append hprefix tailTrace_1487649
  have hstable : (prefixWord ++ tailWord_1487649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487649).length < 2 ^ (prefixWord ++ tailWord_1487649).sum := by decide
  have hdescent : baseEnd_1487649 < baseStart_1487649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487666 : List Nat := [3, 2, 1, 1, 3, 1, 3, 2, 2, 4]
def baseStart_1487666 : Nat := 118140960795 + 1487666 * 2 ^ 59
def prefixEnd_1487666 : Nat := 4983230072969 + 3 ^ 40 * 1487666 * 2
def baseEnd_1487666 : Nat := 509258474234454489088903

theorem tailTrace_1487666 : CollatzResearch.WordTrace tailWord_1487666 prefixEnd_1487666 509258474234454489088903 := by
  unfold tailWord_1487666
  simp only [CollatzResearch.WordTrace]
  refine ⟨13564909157111907492528713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36173091085631753313409901 13564909157111907492528713)
  ·
    refine ⟨10173681867833930619396535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13564909157111907492528713 10173681867833930619396535)
    ·
      refine ⟨15260522801750895929094803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10173681867833930619396535 15260522801750895929094803)
      ·
        refine ⟨22890784202626343893642205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15260522801750895929094803 22890784202626343893642205)
        ·
          refine ⟨8584044075984878960115827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22890784202626343893642205 8584044075984878960115827)
          ·
            refine ⟨12876066113977318440173741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8584044075984878960115827 12876066113977318440173741)
            ·
              refine ⟨4828524792741494415065153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12876066113977318440173741 4828524792741494415065153)
              ·
                refine ⟨3621393594556120811298865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4828524792741494415065153 3621393594556120811298865)
                ·
                  refine ⟨2716045195917090608474149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3621393594556120811298865 2716045195917090608474149)
                  ·
                    refine ⟨509258474234454489088903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2716045195917090608474149 509258474234454489088903)
                    ·
                      rfl

theorem cell22_1487666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_1487666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1487666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1487666 prefixEnd_1487666 := by exact prefixLift 1487666
  have htrace : WordTrace (prefixWord ++ tailWord_1487666) baseStart_1487666 baseEnd_1487666 := by
    simpa [prefixWord, tailWord_1487666, baseEnd_1487666] using wordTrace_append hprefix tailTrace_1487666
  have hstable : (prefixWord ++ tailWord_1487666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487666).length < 2 ^ (prefixWord ++ tailWord_1487666).sum := by decide
  have hdescent : baseEnd_1487666 < baseStart_1487666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487670 : List Nat := [5, 1, 2, 2, 2, 2, 1, 1, 6]
def baseStart_1487670 : Nat := 118140960795 + 1487670 * 2 ^ 59
def prefixEnd_1487670 : Nat := 4983230072969 + 3 ^ 40 * 1487670 * 2
def baseEnd_1487670 : Nat := 169753281172066603996297

theorem tailTrace_1487670 : CollatzResearch.WordTrace tailWord_1487670 prefixEnd_1487670 169753281172066603996297 := by
  unfold tailWord_1487670
  simp only [CollatzResearch.WordTrace]
  refine ⟨3391236407527071165828779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36173188346955425768840309 3391236407527071165828779)
  ·
    refine ⟨5086854611290606748743169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3391236407527071165828779 5086854611290606748743169)
    ·
      refine ⟨3815140958467955061557377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5086854611290606748743169 3815140958467955061557377)
      ·
        refine ⟨2861355718850966296168033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3815140958467955061557377 2861355718850966296168033)
        ·
          refine ⟨2146016789138224722126025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2861355718850966296168033 2146016789138224722126025)
          ·
            refine ⟨1609512591853668541594519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2146016789138224722126025 1609512591853668541594519)
            ·
              refine ⟨2414268887780502812391779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1609512591853668541594519 2414268887780502812391779)
              ·
                refine ⟨3621403331670754218587669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2414268887780502812391779 3621403331670754218587669)
                ·
                  refine ⟨169753281172066603996297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3621403331670754218587669 169753281172066603996297)
                  ·
                    rfl

theorem cell22_1487670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_1487670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1487670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1487670 prefixEnd_1487670 := by exact prefixLift 1487670
  have htrace : WordTrace (prefixWord ++ tailWord_1487670) baseStart_1487670 baseEnd_1487670 := by
    simpa [prefixWord, tailWord_1487670, baseEnd_1487670] using wordTrace_append hprefix tailTrace_1487670
  have hstable : (prefixWord ++ tailWord_1487670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487670).length < 2 ^ (prefixWord ++ tailWord_1487670).sum := by decide
  have hdescent : baseEnd_1487670 < baseStart_1487670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487696 : List Nat := [2, 1, 1, 1, 1, 4, 2, 4, 3, 3]
def baseStart_1487696 : Nat := 118140960795 + 1487696 * 2 ^ 59
def prefixEnd_1487696 : Nat := 4983230072969 + 3 ^ 40 * 1487696 * 2
def baseEnd_1487696 : Nat := 509268743847544410838811

theorem tailTrace_1487696 : CollatzResearch.WordTrace tailWord_1487696 prefixEnd_1487696 509268743847544410838811 := by
  unfold tailWord_1487696
  simp only [CollatzResearch.WordTrace]
  refine ⟨27130365409169472546853471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36173820545559296729137961 27130365409169472546853471)
  ·
    refine ⟨40695548113754208820280207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27130365409169472546853471 40695548113754208820280207)
    ·
      refine ⟨61043322170631313230420311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40695548113754208820280207 61043322170631313230420311)
      ·
        refine ⟨91564983255946969845630467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61043322170631313230420311 91564983255946969845630467)
        ·
          refine ⟨137347474883920454768445701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91564983255946969845630467 137347474883920454768445701)
          ·
            refine ⟨25752651540735085269083569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137347474883920454768445701 25752651540735085269083569)
            ·
              refine ⟨19314488655551313951812677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25752651540735085269083569 19314488655551313951812677)
              ·
                refine ⟨3621466622915871365964877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19314488655551313951812677 3621466622915871365964877)
                ·
                  refine ⟨1358049983593451762236829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3621466622915871365964877 1358049983593451762236829)
                  ·
                    refine ⟨509268743847544410838811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1358049983593451762236829 509268743847544410838811)
                    ·
                      rfl

theorem cell22_1487696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 3, 3].length) (baseStart_1487696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1487696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1487696 prefixEnd_1487696 := by exact prefixLift 1487696
  have htrace : WordTrace (prefixWord ++ tailWord_1487696) baseStart_1487696 baseEnd_1487696 := by
    simpa [prefixWord, tailWord_1487696, baseEnd_1487696] using wordTrace_append hprefix tailTrace_1487696
  have hstable : (prefixWord ++ tailWord_1487696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487696).length < 2 ^ (prefixWord ++ tailWord_1487696).sum := by decide
  have hdescent : baseEnd_1487696 < baseStart_1487696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487756 : List Nat := [2, 2, 1, 2, 1, 2, 4, 1, 3, 4]
def baseStart_1487756 : Nat := 118140960795 + 1487756 * 2 ^ 59
def prefixEnd_1487756 : Nat := 4983230072969 + 3 ^ 40 * 1487756 * 2
def baseEnd_1487756 : Nat := 509289283073724254338627

theorem tailTrace_1487756 : CollatzResearch.WordTrace tailWord_1487756 prefixEnd_1487756 509289283073724254338627 := by
  unfold tailWord_1487756
  simp only [CollatzResearch.WordTrace]
  refine ⟨27131459599060787670445561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36175279465414383560594081 27131459599060787670445561)
  ·
    refine ⟨20348594699295590752834171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27131459599060787670445561 20348594699295590752834171)
    ·
      refine ⟨30522892048943386129251257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20348594699295590752834171 30522892048943386129251257)
      ·
        refine ⟨22892169036707539596938443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30522892048943386129251257 22892169036707539596938443)
        ·
          refine ⟨34338253555061309395407665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22892169036707539596938443 34338253555061309395407665)
          ·
            refine ⟨25753690166295982046555749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34338253555061309395407665 25753690166295982046555749)
            ·
              refine ⟨4828816906180496633729203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25753690166295982046555749 4828816906180496633729203)
              ·
                refine ⟨7243225359270744950593805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4828816906180496633729203 7243225359270744950593805)
                ·
                  refine ⟨2716209509726529356472677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7243225359270744950593805 2716209509726529356472677)
                  ·
                    refine ⟨509289283073724254338627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2716209509726529356472677 509289283073724254338627)
                    ·
                      rfl

theorem cell22_1487756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_1487756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1487756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1487756 prefixEnd_1487756 := by exact prefixLift 1487756
  have htrace : WordTrace (prefixWord ++ tailWord_1487756) baseStart_1487756 baseEnd_1487756 := by
    simpa [prefixWord, tailWord_1487756, baseEnd_1487756] using wordTrace_append hprefix tailTrace_1487756
  have hstable : (prefixWord ++ tailWord_1487756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487756).length < 2 ^ (prefixWord ++ tailWord_1487756).sum := by decide
  have hdescent : baseEnd_1487756 < baseStart_1487756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487773 : List Nat := [1, 4, 2, 1, 2, 1, 3, 3, 1, 4]
def baseStart_1487773 : Nat := 118140960795 + 1487773 * 2 ^ 59
def prefixEnd_1487773 : Nat := 4983230072969 + 3 ^ 40 * 1487773 * 2
def baseEnd_1487773 : Nat := 509295102521141876663575

theorem tailTrace_1487773 : CollatzResearch.WordTrace tailWord_1487773 prefixEnd_1487773 509295102521141876663575 := by
  unfold tailWord_1487773
  simp only [CollatzResearch.WordTrace]
  refine ⟨54263539239059987244259973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36175692826039991496173315 54263539239059987244259973)
  ·
    refine ⟨10174413607323747608298745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54263539239059987244259973 10174413607323747608298745)
    ·
      refine ⟨7630810205492810706224059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10174413607323747608298745 7630810205492810706224059)
      ·
        refine ⟨11446215308239216059336089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7630810205492810706224059 11446215308239216059336089)
        ·
          refine ⟨8584661481179412044502067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11446215308239216059336089 8584661481179412044502067)
          ·
            refine ⟨12876992221769118066753101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8584661481179412044502067 12876992221769118066753101)
            ·
              refine ⟨4828872083163419275032413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12876992221769118066753101 4828872083163419275032413)
              ·
                refine ⟨1810827031186282228137155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4828872083163419275032413 1810827031186282228137155)
                ·
                  refine ⟨2716240546779423342205733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1810827031186282228137155 2716240546779423342205733)
                  ·
                    refine ⟨509295102521141876663575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2716240546779423342205733 509295102521141876663575)
                    ·
                      rfl

theorem cell22_1487773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_1487773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1487773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1487773 prefixEnd_1487773 := by exact prefixLift 1487773
  have htrace : WordTrace (prefixWord ++ tailWord_1487773) baseStart_1487773 baseEnd_1487773 := by
    simpa [prefixWord, tailWord_1487773, baseEnd_1487773] using wordTrace_append hprefix tailTrace_1487773
  have hstable : (prefixWord ++ tailWord_1487773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487773).length < 2 ^ (prefixWord ++ tailWord_1487773).sum := by decide
  have hdescent : baseEnd_1487773 < baseStart_1487773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487801 : List Nat := [1, 2, 1, 4, 2, 2, 1, 2, 1, 6]
def baseStart_1487801 : Nat := 118140960795 + 1487801 * 2 ^ 59
def prefixEnd_1487801 : Nat := 4983230072969 + 3 ^ 40 * 1487801 * 2
def baseEnd_1487801 : Nat := 509304687493359136963489

theorem tailTrace_1487801 : CollatzResearch.WordTrace tailWord_1487801 prefixEnd_1487801 509304687493359136963489 := by
  unfold tailWord_1487801
  simp only [CollatzResearch.WordTrace]
  refine ⟨54264560482958548026279257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36176373655305698684186171 54264560482958548026279257)
  ·
    refine ⟨40698420362218911019709443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54264560482958548026279257 40698420362218911019709443)
    ·
      refine ⟨61047630543328366529564165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40698420362218911019709443 61047630543328366529564165)
      ·
        refine ⟨11446430726874068724293281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61047630543328366529564165 11446430726874068724293281)
        ·
          refine ⟨8584823045155551543219961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11446430726874068724293281 8584823045155551543219961)
          ·
            refine ⟨6438617283866663657414971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8584823045155551543219961 6438617283866663657414971)
            ·
              refine ⟨9657925925799995486122457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6438617283866663657414971 9657925925799995486122457)
              ·
                refine ⟨7243444444349996614591843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9657925925799995486122457 7243444444349996614591843)
                ·
                  refine ⟨10865166666524994921887765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7243444444349996614591843 10865166666524994921887765)
                  ·
                    refine ⟨509304687493359136963489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10865166666524994921887765 509304687493359136963489)
                    ·
                      rfl

theorem cell22_1487801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 6].length) (baseStart_1487801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1487801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1487801 prefixEnd_1487801 := by exact prefixLift 1487801
  have htrace : WordTrace (prefixWord ++ tailWord_1487801) baseStart_1487801 baseEnd_1487801 := by
    simpa [prefixWord, tailWord_1487801, baseEnd_1487801] using wordTrace_append hprefix tailTrace_1487801
  have hstable : (prefixWord ++ tailWord_1487801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487801).length < 2 ^ (prefixWord ++ tailWord_1487801).sum := by decide
  have hdescent : baseEnd_1487801 < baseStart_1487801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487854 : List Nat := [4, 1, 2, 1, 4, 2, 2, 1, 2, 3]
def baseStart_1487854 : Nat := 118140960795 + 1487854 * 2 ^ 59
def prefixEnd_1487854 : Nat := 4983230072969 + 3 ^ 40 * 1487854 * 2
def baseEnd_1487854 : Nat := 509322830476484665388327

theorem tailTrace_1487854 : CollatzResearch.WordTrace tailWord_1487854 prefixEnd_1487854 509322830476484665388327 := by
  unfold tailWord_1487854
  simp only [CollatzResearch.WordTrace]
  refine ⟨6783311693970817259744827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36177662367844358718639077 6783311693970817259744827)
  ·
    refine ⟨10174967540956225889617241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6783311693970817259744827 10174967540956225889617241)
    ·
      refine ⟨7631225655717169417212931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10174967540956225889617241 7631225655717169417212931)
      ·
        refine ⟨11446838483575754125819397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7631225655717169417212931 11446838483575754125819397)
        ·
          refine ⟨2146282215670453898591137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11446838483575754125819397 2146282215670453898591137)
          ·
            refine ⟨1609711661752840423943353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2146282215670453898591137 1609711661752840423943353)
            ·
              refine ⟨1207283746314630317957515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1609711661752840423943353 1207283746314630317957515)
              ·
                refine ⟨1810925619471945476936273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1207283746314630317957515 1810925619471945476936273)
                ·
                  refine ⟨1358194214603959107702205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1810925619471945476936273 1358194214603959107702205)
                  ·
                    refine ⟨509322830476484665388327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1358194214603959107702205 509322830476484665388327)
                    ·
                      rfl

theorem cell22_1487854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_1487854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1487854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1487854 prefixEnd_1487854 := by exact prefixLift 1487854
  have htrace : WordTrace (prefixWord ++ tailWord_1487854) baseStart_1487854 baseEnd_1487854 := by
    simpa [prefixWord, tailWord_1487854, baseEnd_1487854] using wordTrace_append hprefix tailTrace_1487854
  have hstable : (prefixWord ++ tailWord_1487854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487854).length < 2 ^ (prefixWord ++ tailWord_1487854).sum := by decide
  have hdescent : baseEnd_1487854 < baseStart_1487854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487895 : List Nat := [1, 1, 3, 5, 1, 2, 2, 2, 5]
def baseStart_1487895 : Nat := 118140960795 + 1487895 * 2 ^ 59
def prefixEnd_1487895 : Nat := 4983230072969 + 3 ^ 40 * 1487895 * 2
def baseEnd_1487895 : Nat := 169778955204791408371067

theorem tailTrace_1487895 : CollatzResearch.WordTrace tailWord_1487895 prefixEnd_1487895 169778955204791408371067 := by
  unfold tailWord_1487895
  simp only [CollatzResearch.WordTrace]
  refine ⟨54267988944618002080201139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36178659296412001386800759 54267988944618002080201139)
  ·
    refine ⟨81401983416927003120301709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54267988944618002080201139 81401983416927003120301709)
    ·
      refine ⟨30525743781347626170113141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81401983416927003120301709 30525743781347626170113141)
      ·
        refine ⟨2861788479501339953448107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30525743781347626170113141 2861788479501339953448107)
        ·
          refine ⟨4292682719252009930172161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2861788479501339953448107 4292682719252009930172161)
          ·
            refine ⟨3219512039439007447629121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4292682719252009930172161 3219512039439007447629121)
            ·
              refine ⟨2414634029579255585721841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3219512039439007447629121 2414634029579255585721841)
              ·
                refine ⟨1810975522184441689291381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2414634029579255585721841 1810975522184441689291381)
                ·
                  refine ⟨169778955204791408371067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1810975522184441689291381 169778955204791408371067)
                  ·
                    rfl

theorem cell22_1487895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 2, 5].length) (baseStart_1487895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1487895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1487895 prefixEnd_1487895 := by exact prefixLift 1487895
  have htrace : WordTrace (prefixWord ++ tailWord_1487895) baseStart_1487895 baseEnd_1487895 := by
    simpa [prefixWord, tailWord_1487895, baseEnd_1487895] using wordTrace_append hprefix tailTrace_1487895
  have hstable : (prefixWord ++ tailWord_1487895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487895).length < 2 ^ (prefixWord ++ tailWord_1487895).sum := by decide
  have hdescent : baseEnd_1487895 < baseStart_1487895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487953 : List Nat := [1, 2, 2, 1, 3, 1, 2, 4, 2, 4]
def baseStart_1487953 : Nat := 118140960795 + 1487953 * 2 ^ 59
def prefixEnd_1487953 : Nat := 4983230072969 + 3 ^ 40 * 1487953 * 2
def baseEnd_1487953 : Nat := 509356720199681407163023

theorem tailTrace_1487953 : CollatzResearch.WordTrace tailWord_1487953 prefixEnd_1487953 509356720199681407163023 := by
  unfold tailWord_1487953
  simp only [CollatzResearch.WordTrace]
  refine ⟨54270104378407877985812513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36180069585605251990541675 54270104378407877985812513)
  ·
    refine ⟨40702578283805908489359385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54270104378407877985812513 40702578283805908489359385)
    ·
      refine ⟨30526933712854431367019539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40702578283805908489359385 30526933712854431367019539)
      ·
        refine ⟨45790400569281647050529309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30526933712854431367019539 45790400569281647050529309)
        ·
          refine ⟨17171400213480617643948491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45790400569281647050529309 17171400213480617643948491)
          ·
            refine ⟨25757100320220926465922737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17171400213480617643948491 25757100320220926465922737)
            ·
              refine ⟨19317825240165694849442053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25757100320220926465922737 19317825240165694849442053)
              ·
                refine ⟨3622092232531067784270385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19317825240165694849442053 3622092232531067784270385)
                ·
                  refine ⟨2716569174398300838202789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3622092232531067784270385 2716569174398300838202789)
                  ·
                    refine ⟨509356720199681407163023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2716569174398300838202789 509356720199681407163023)
                    ·
                      rfl

theorem cell22_1487953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_1487953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1487953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1487953 prefixEnd_1487953 := by exact prefixLift 1487953
  have htrace : WordTrace (prefixWord ++ tailWord_1487953) baseStart_1487953 baseEnd_1487953 := by
    simpa [prefixWord, tailWord_1487953, baseEnd_1487953] using wordTrace_append hprefix tailTrace_1487953
  have hstable : (prefixWord ++ tailWord_1487953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487953).length < 2 ^ (prefixWord ++ tailWord_1487953).sum := by decide
  have hdescent : baseEnd_1487953 < baseStart_1487953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1487970 : List Nat := [3, 3, 2, 2, 1, 1, 1, 2, 1, 6]
def baseStart_1487970 : Nat := 118140960795 + 1487970 * 2 ^ 59
def prefixEnd_1487970 : Nat := 4983230072969 + 3 ^ 40 * 1487970 * 2
def baseEnd_1487970 : Nat := 509362539647099029487971

theorem tailTrace_1487970 : CollatzResearch.WordTrace tailWord_1487970 prefixEnd_1487970 509362539647099029487971 := by
  unfold tailWord_1487970
  simp only [CollatzResearch.WordTrace]
  refine ⟨13567681104836572472295341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36180482946230859926120909 13567681104836572472295341)
  ·
    refine ⟨5087880414313714677110753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13567681104836572472295341 5087880414313714677110753)
    ·
      refine ⟨3815910310735286007833065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5087880414313714677110753 3815910310735286007833065)
      ·
        refine ⟨2861932733051464505874799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3815910310735286007833065 2861932733051464505874799)
        ·
          refine ⟨4292899099577196758812199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2861932733051464505874799 4292899099577196758812199)
          ·
            refine ⟨6439348649365795138218299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4292899099577196758812199 6439348649365795138218299)
            ·
              refine ⟨9659022974048692707327449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6439348649365795138218299 9659022974048692707327449)
              ·
                refine ⟨7244267230536519530495587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9659022974048692707327449 7244267230536519530495587)
                ·
                  refine ⟨10866400845804779295743381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7244267230536519530495587 10866400845804779295743381)
                  ·
                    refine ⟨509362539647099029487971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10866400845804779295743381 509362539647099029487971)
                    ·
                      rfl

theorem cell22_1487970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_1487970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1487970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1487970 prefixEnd_1487970 := by exact prefixLift 1487970
  have htrace : WordTrace (prefixWord ++ tailWord_1487970) baseStart_1487970 baseEnd_1487970 := by
    simpa [prefixWord, tailWord_1487970, baseEnd_1487970] using wordTrace_append hprefix tailTrace_1487970
  have hstable : (prefixWord ++ tailWord_1487970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1487970).length < 2 ^ (prefixWord ++ tailWord_1487970).sum := by decide
  have hdescent : baseEnd_1487970 < baseStart_1487970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1487970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488068 : List Nat := [2, 3, 3, 1, 3, 2, 2, 2, 1, 3]
def baseStart_1488068 : Nat := 118140960795 + 1488068 * 2 ^ 59
def prefixEnd_1488068 : Nat := 4983230072969 + 3 ^ 40 * 1488068 * 2
def baseEnd_1488068 : Nat := 509396087049859440537671

theorem tailTrace_1488068 : CollatzResearch.WordTrace tailWord_1488068 prefixEnd_1488068 509396087049859440537671 := by
  unfold tailWord_1488068
  simp only [CollatzResearch.WordTrace]
  refine ⟨27137149386495626313124429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36182865848660835084165905 27137149386495626313124429)
  ·
    refine ⟨10176431019935859867421661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27137149386495626313124429 10176431019935859867421661)
    ·
      refine ⟨3816161632475947450283123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10176431019935859867421661 3816161632475947450283123)
      ·
        refine ⟨5724242448713921175424685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3816161632475947450283123 5724242448713921175424685)
        ·
          refine ⟨2146590918267720440784257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5724242448713921175424685 2146590918267720440784257)
          ·
            refine ⟨1609943188700790330588193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2146590918267720440784257 1609943188700790330588193)
            ·
              refine ⟨1207457391525592747941145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1609943188700790330588193 1207457391525592747941145)
              ·
                refine ⟨905593043644194560955859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1207457391525592747941145 905593043644194560955859)
                ·
                  refine ⟨1358389565466291841433789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 905593043644194560955859 1358389565466291841433789)
                  ·
                    refine ⟨509396087049859440537671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1358389565466291841433789 509396087049859440537671)
                    ·
                      rfl

theorem cell22_1488068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_1488068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488068 prefixEnd_1488068 := by exact prefixLift 1488068
  have htrace : WordTrace (prefixWord ++ tailWord_1488068) baseStart_1488068 baseEnd_1488068 := by
    simpa [prefixWord, tailWord_1488068, baseEnd_1488068] using wordTrace_append hprefix tailTrace_1488068
  have hstable : (prefixWord ++ tailWord_1488068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488068).length < 2 ^ (prefixWord ++ tailWord_1488068).sum := by decide
  have hdescent : baseEnd_1488068 < baseStart_1488068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488090 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 6, 3]
def baseStart_1488090 : Nat := 118140960795 + 1488090 * 2 ^ 59
def prefixEnd_1488090 : Nat := 4983230072969 + 3 ^ 40 * 1488090 * 2
def baseEnd_1488090 : Nat := 509403618099458716487603

theorem tailTrace_1488090 : CollatzResearch.WordTrace tailWord_1488090 prefixEnd_1488090 509403618099458716487603 := by
  unfold tailWord_1488090
  simp only [CollatzResearch.WordTrace]
  refine ⟨13568775294727887595887431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36183400785941033589033149 13568775294727887595887431)
  ·
    refine ⟨20353162942091831393831147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13568775294727887595887431 20353162942091831393831147)
    ·
      refine ⟨30529744413137747090746721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20353162942091831393831147 30529744413137747090746721)
      ·
        refine ⟨22897308309853310318060041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30529744413137747090746721 22897308309853310318060041)
        ·
          refine ⟨17172981232389982738545031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22897308309853310318060041 17172981232389982738545031)
          ·
            refine ⟨25759471848584974107817547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17172981232389982738545031 25759471848584974107817547)
            ·
              refine ⟨38639207772877461161726321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25759471848584974107817547 38639207772877461161726321)
              ·
                refine ⟨28979405829658095871294741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38639207772877461161726321 28979405829658095871294741)
                ·
                  refine ⟨1358409648265223243966941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28979405829658095871294741 1358409648265223243966941)
                  ·
                    refine ⟨509403618099458716487603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1358409648265223243966941 509403618099458716487603)
                    ·
                      rfl

theorem cell22_1488090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 6, 3].length) (baseStart_1488090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488090 prefixEnd_1488090 := by exact prefixLift 1488090
  have htrace : WordTrace (prefixWord ++ tailWord_1488090) baseStart_1488090 baseEnd_1488090 := by
    simpa [prefixWord, tailWord_1488090, baseEnd_1488090] using wordTrace_append hprefix tailTrace_1488090
  have hstable : (prefixWord ++ tailWord_1488090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488090).length < 2 ^ (prefixWord ++ tailWord_1488090).sum := by decide
  have hdescent : baseEnd_1488090 < baseStart_1488090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488109 : List Nat := [1, 5, 1, 2, 2, 2, 2, 3, 4]
def baseStart_1488109 : Nat := 118140960795 + 1488109 * 2 ^ 59
def prefixEnd_1488109 : Nat := 4983230072969 + 3 ^ 40 * 1488109 * 2
def baseEnd_1488109 : Nat := 169803374062583000087515

theorem tailTrace_1488109 : CollatzResearch.WordTrace tailWord_1488109 prefixEnd_1488109 169803374062583000087515 := by
  unfold tailWord_1488109
  simp only [CollatzResearch.WordTrace]
  refine ⟨54275794165842716628491381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36183862777228477752327587 54275794165842716628491381)
  ·
    refine ⟨5088355703047754683921067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54275794165842716628491381 5088355703047754683921067)
    ·
      refine ⟨7632533554571632025881601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5088355703047754683921067 7632533554571632025881601)
      ·
        refine ⟨5724400165928724019411201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7632533554571632025881601 5724400165928724019411201)
        ·
          refine ⟨4293300124446543014558401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5724400165928724019411201 4293300124446543014558401)
          ·
            refine ⟨3219975093334907260918801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4293300124446543014558401 3219975093334907260918801)
            ·
              refine ⟨2414981320001180445689101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3219975093334907260918801 2414981320001180445689101)
              ·
                refine ⟨905617995000442667133413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2414981320001180445689101 905617995000442667133413)
                ·
                  refine ⟨169803374062583000087515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 905617995000442667133413 169803374062583000087515)
                  ·
                    rfl

theorem cell22_1488109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_1488109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488109 prefixEnd_1488109 := by exact prefixLift 1488109
  have htrace : WordTrace (prefixWord ++ tailWord_1488109) baseStart_1488109 baseEnd_1488109 := by
    simpa [prefixWord, tailWord_1488109, baseEnd_1488109] using wordTrace_append hprefix tailTrace_1488109
  have hstable : (prefixWord ++ tailWord_1488109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488109).length < 2 ^ (prefixWord ++ tailWord_1488109).sum := by decide
  have hdescent : baseEnd_1488109 < baseStart_1488109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488111 : List Nat := [1, 1, 2, 1, 8, 1, 2, 1, 1, 4]
def baseStart_1488111 : Nat := 118140960795 + 1488111 * 2 ^ 59
def prefixEnd_1488111 : Nat := 4983230072969 + 3 ^ 40 * 1488111 * 2
def baseEnd_1488111 : Nat := 509410806828621661712539

theorem tailTrace_1488111 : CollatzResearch.WordTrace tailWord_1488111 prefixEnd_1488111 509410806828621661712539 := by
  unfold tailWord_1488111
  simp only [CollatzResearch.WordTrace]
  refine ⟨54275867111835470970064187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36183911407890313980042791 54275867111835470970064187)
  ·
    refine ⟨81413800667753206455096281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54275867111835470970064187 81413800667753206455096281)
    ·
      refine ⟨61060350500814904841322211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81413800667753206455096281 61060350500814904841322211)
      ·
        refine ⟨91590525751222357261983317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61060350500814904841322211 91590525751222357261983317)
        ·
          refine ⟨1073326473647136999163867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 91590525751222357261983317 1073326473647136999163867)
          ·
            refine ⟨1609989710470705498745801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1073326473647136999163867 1609989710470705498745801)
            ·
              refine ⟨1207492282853029124059351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1609989710470705498745801 1207492282853029124059351)
              ·
                refine ⟨1811238424279543686089027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1207492282853029124059351 1811238424279543686089027)
                ·
                  refine ⟨2716857636419315529133541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1811238424279543686089027 2716857636419315529133541)
                  ·
                    refine ⟨509410806828621661712539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2716857636419315529133541 509410806828621661712539)
                    ·
                      rfl

theorem cell22_1488111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 1, 4].length) (baseStart_1488111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488111 prefixEnd_1488111 := by exact prefixLift 1488111
  have htrace : WordTrace (prefixWord ++ tailWord_1488111) baseStart_1488111 baseEnd_1488111 := by
    simpa [prefixWord, tailWord_1488111, baseEnd_1488111] using wordTrace_append hprefix tailTrace_1488111
  have hstable : (prefixWord ++ tailWord_1488111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488111).length < 2 ^ (prefixWord ++ tailWord_1488111).sum := by decide
  have hdescent : baseEnd_1488111 < baseStart_1488111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488152 : List Nat := [2, 1, 2, 3, 1, 3, 2, 2, 3, 3]
def baseStart_1488152 : Nat := 118140960795 + 1488152 * 2 ^ 59
def prefixEnd_1488152 : Nat := 4983230072969 + 3 ^ 40 * 1488152 * 2
def baseEnd_1488152 : Nat := 509424841966511221437413

theorem tailTrace_1488152 : CollatzResearch.WordTrace tailWord_1488152 prefixEnd_1488152 509424841966511221437413 := by
  unfold tailWord_1488152
  simp only [CollatzResearch.WordTrace]
  refine ⟨27138681252343467486153355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36184908336457956648204473 27138681252343467486153355)
  ·
    refine ⟨40708021878515201229230033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27138681252343467486153355 40708021878515201229230033)
    ·
      refine ⟨30531016408886400921922525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40708021878515201229230033 30531016408886400921922525)
      ·
        refine ⟨11449131153332400345720947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30531016408886400921922525 11449131153332400345720947)
        ·
          refine ⟨17173696729998600518581421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11449131153332400345720947 17173696729998600518581421)
          ·
            refine ⟨6440136273749475194468033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17173696729998600518581421 6440136273749475194468033)
            ·
              refine ⟨4830102205312106395851025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6440136273749475194468033 4830102205312106395851025)
              ·
                refine ⟨3622576653984079796888269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4830102205312106395851025 3622576653984079796888269)
                ·
                  refine ⟨1358466245244029923833101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3622576653984079796888269 1358466245244029923833101)
                  ·
                    refine ⟨509424841966511221437413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1358466245244029923833101 509424841966511221437413)
                    ·
                      rfl

theorem cell22_1488152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 3, 3].length) (baseStart_1488152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488152 prefixEnd_1488152 := by exact prefixLift 1488152
  have htrace : WordTrace (prefixWord ++ tailWord_1488152) baseStart_1488152 baseEnd_1488152 := by
    simpa [prefixWord, tailWord_1488152, baseEnd_1488152] using wordTrace_append hprefix tailTrace_1488152
  have hstable : (prefixWord ++ tailWord_1488152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488152).length < 2 ^ (prefixWord ++ tailWord_1488152).sum := by decide
  have hdescent : baseEnd_1488152 < baseStart_1488152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488165 : List Nat := [1, 3, 1, 2, 4, 1, 1, 2, 7]
def baseStart_1488165 : Nat := 118140960795 + 1488165 * 2 ^ 59
def prefixEnd_1488165 : Nat := 4983230072969 + 3 ^ 40 * 1488165 * 2
def baseEnd_1488165 : Nat := 169809764044061173620791

theorem tailTrace_1488165 : CollatzResearch.WordTrace tailWord_1488165 prefixEnd_1488165 169809764044061173620791 := by
  unfold tailWord_1488165
  simp only [CollatzResearch.WordTrace]
  refine ⟨54277836653639838192529949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36185224435759892128353299 54277836653639838192529949)
  ·
    refine ⟨20354188745114939322198731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54277836653639838192529949 20354188745114939322198731)
    ·
      refine ⟨30531283117672408983298097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20354188745114939322198731 30531283117672408983298097)
      ·
        refine ⟨22898462338254306737473573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30531283117672408983298097 22898462338254306737473573)
        ·
          refine ⟨4293461688422682513276295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22898462338254306737473573 4293461688422682513276295)
          ·
            refine ⟨6440192532634023769914443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4293461688422682513276295 6440192532634023769914443)
            ·
              refine ⟨9660288798951035654871665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6440192532634023769914443 9660288798951035654871665)
              ·
                refine ⟨7245216599213276741153749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9660288798951035654871665 7245216599213276741153749)
                ·
                  refine ⟨169809764044061173620791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7245216599213276741153749 169809764044061173620791)
                  ·
                    rfl

theorem cell22_1488165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 7].length) (baseStart_1488165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488165 prefixEnd_1488165 := by exact prefixLift 1488165
  have htrace : WordTrace (prefixWord ++ tailWord_1488165) baseStart_1488165 baseEnd_1488165 := by
    simpa [prefixWord, tailWord_1488165, baseEnd_1488165] using wordTrace_append hprefix tailTrace_1488165
  have hstable : (prefixWord ++ tailWord_1488165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488165).length < 2 ^ (prefixWord ++ tailWord_1488165).sum := by decide
  have hdescent : baseEnd_1488165 < baseStart_1488165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488186 : List Nat := [3, 1, 1, 1, 4, 1, 5, 2, 1, 3]
def baseStart_1488186 : Nat := 118140960795 + 1488186 * 2 ^ 59
def prefixEnd_1488186 : Nat := 4983230072969 + 3 ^ 40 * 1488186 * 2
def baseEnd_1488186 : Nat := 509436480861346466087309

theorem tailTrace_1488186 : CollatzResearch.WordTrace tailWord_1488186 prefixEnd_1488186 509436480861346466087309 := by
  unfold tailWord_1488186
  simp only [CollatzResearch.WordTrace]
  refine ⟨13569650646640939694761103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36185735057709172519362941 13569650646640939694761103)
  ·
    refine ⟨20354475969961409542141655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13569650646640939694761103 20354475969961409542141655)
    ·
      refine ⟨30531713954942114313212483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20354475969961409542141655 30531713954942114313212483)
      ·
        refine ⟨45797570932413171469818725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30531713954942114313212483 45797570932413171469818725)
        ·
          refine ⟨8587044549827469650591011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45797570932413171469818725 8587044549827469650591011)
          ·
            refine ⟨12880566824741204475886517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8587044549827469650591011 12880566824741204475886517)
            ·
              refine ⟨1207553139819487919614361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12880566824741204475886517 1207553139819487919614361)
              ·
                refine ⟨905664854864615939710771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1207553139819487919614361 905664854864615939710771)
                ·
                  refine ⟨1358497282296923909566157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 905664854864615939710771 1358497282296923909566157)
                  ·
                    refine ⟨509436480861346466087309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1358497282296923909566157 509436480861346466087309)
                    ·
                      rfl

theorem cell22_1488186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 2, 1, 3].length) (baseStart_1488186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488186 prefixEnd_1488186 := by exact prefixLift 1488186
  have htrace : WordTrace (prefixWord ++ tailWord_1488186) baseStart_1488186 baseEnd_1488186 := by
    simpa [prefixWord, tailWord_1488186, baseEnd_1488186] using wordTrace_append hprefix tailTrace_1488186
  have hstable : (prefixWord ++ tailWord_1488186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488186).length < 2 ^ (prefixWord ++ tailWord_1488186).sum := by decide
  have hdescent : baseEnd_1488186 < baseStart_1488186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488195 : List Nat := [1, 1, 1, 3, 1, 3, 1, 4, 3, 4]
def baseStart_1488195 : Nat := 118140960795 + 1488195 * 2 ^ 59
def prefixEnd_1488195 : Nat := 4983230072969 + 3 ^ 40 * 1488195 * 2
def baseEnd_1488195 : Nat := 509439561745273442612281

theorem tailTrace_1488195 : CollatzResearch.WordTrace tailWord_1488195 prefixEnd_1488195 509439561745273442612281 := by
  unfold tailWord_1488195
  simp only [CollatzResearch.WordTrace]
  refine ⟨54278930843531153316122039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36185953895687435544081359 54278930843531153316122039)
  ·
    refine ⟨81418396265296729974183059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54278930843531153316122039 81418396265296729974183059)
    ·
      refine ⟨122127594397945094961274589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81418396265296729974183059 122127594397945094961274589)
      ·
        refine ⟨45797847899229410610477971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122127594397945094961274589 45797847899229410610477971)
        ·
          refine ⟨68696771848844115915716957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45797847899229410610477971 68696771848844115915716957)
          ·
            refine ⟨25761289443316543468393859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68696771848844115915716957 25761289443316543468393859)
            ·
              refine ⟨38641934164974815202590789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25761289443316543468393859 38641934164974815202590789)
              ·
                refine ⟨7245362655932777850485773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38641934164974815202590789 7245362655932777850485773)
                ·
                  refine ⟨2717010995974791693932165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7245362655932777850485773 2717010995974791693932165)
                  ·
                    refine ⟨509439561745273442612281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2717010995974791693932165 509439561745273442612281)
                    ·
                      rfl

theorem cell22_1488195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 4].length) (baseStart_1488195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488195 prefixEnd_1488195 := by exact prefixLift 1488195
  have htrace : WordTrace (prefixWord ++ tailWord_1488195) baseStart_1488195 baseEnd_1488195 := by
    simpa [prefixWord, tailWord_1488195, baseEnd_1488195] using wordTrace_append hprefix tailTrace_1488195
  have hstable : (prefixWord ++ tailWord_1488195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488195).length < 2 ^ (prefixWord ++ tailWord_1488195).sum := by decide
  have hdescent : baseEnd_1488195 < baseStart_1488195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488199 : List Nat := [1, 1, 4, 1, 2, 5, 2, 1, 5]
def baseStart_1488199 : Nat := 118140960795 + 1488199 * 2 ^ 59
def prefixEnd_1488199 : Nat := 4983230072969 + 3 ^ 40 * 1488199 * 2
def baseEnd_1488199 : Nat := 169813643675672921837423

theorem tailTrace_1488199 : CollatzResearch.WordTrace tailWord_1488199 prefixEnd_1488199 169813643675672921837423 := by
  unfold tailWord_1488199
  simp only [CollatzResearch.WordTrace]
  refine ⟨54279076735516661999267651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36186051157011107999511767 54279076735516661999267651)
  ·
    refine ⟨81418615103274992998901477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54279076735516661999267651 81418615103274992998901477)
    ·
      refine ⟨15265990331864061187294027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81418615103274992998901477 15265990331864061187294027)
      ·
        refine ⟨22898985497796091780941041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15265990331864061187294027 22898985497796091780941041)
        ·
          refine ⟨17174239123347068835705781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22898985497796091780941041 17174239123347068835705781)
          ·
            refine ⟨1610084917813787703347417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17174239123347068835705781 1610084917813787703347417)
            ·
              refine ⟨1207563688360340777510563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1610084917813787703347417 1207563688360340777510563)
              ·
                refine ⟨1811345532540511166265845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1207563688360340777510563 1811345532540511166265845)
                ·
                  refine ⟨169813643675672921837423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1811345532540511166265845 169813643675672921837423)
                  ·
                    rfl

theorem cell22_1488199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 5].length) (baseStart_1488199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488199 prefixEnd_1488199 := by exact prefixLift 1488199
  have htrace : WordTrace (prefixWord ++ tailWord_1488199) baseStart_1488199 baseEnd_1488199 := by
    simpa [prefixWord, tailWord_1488199, baseEnd_1488199] using wordTrace_append hprefix tailTrace_1488199
  have hstable : (prefixWord ++ tailWord_1488199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488199).length < 2 ^ (prefixWord ++ tailWord_1488199).sum := by decide
  have hdescent : baseEnd_1488199 < baseStart_1488199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488210 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 8]
def baseStart_1488210 : Nat := 118140960795 + 1488210 * 2 ^ 59
def prefixEnd_1488210 : Nat := 4983230072969 + 3 ^ 40 * 1488210 * 2
def baseEnd_1488210 : Nat := 169814898850606134495745

theorem tailTrace_1488210 : CollatzResearch.WordTrace tailWord_1488210 prefixEnd_1488210 169814898850606134495745 := by
  unfold tailWord_1488210
  simp only [CollatzResearch.WordTrace]
  refine ⟨13569869484619202719479521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36186318625651207251945389 13569869484619202719479521)
  ·
    refine ⟨10177402113464402039609641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13569869484619202719479521 10177402113464402039609641)
    ·
      refine ⟨7633051585098301529707231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10177402113464402039609641 7633051585098301529707231)
      ·
        refine ⟨11449577377647452294560847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7633051585098301529707231 11449577377647452294560847)
        ·
          refine ⟨17174366066471178441841271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11449577377647452294560847 17174366066471178441841271)
          ·
            refine ⟨25761549099706767662761907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17174366066471178441841271 25761549099706767662761907)
            ·
              refine ⟨38642323649560151494142861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25761549099706767662761907 38642323649560151494142861)
              ·
                refine ⟨14490871368585056810303573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38642323649560151494142861 14490871368585056810303573)
                ·
                  refine ⟨169814898850606134495745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14490871368585056810303573 169814898850606134495745)
                  ·
                    rfl

theorem cell22_1488210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_1488210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488210 prefixEnd_1488210 := by exact prefixLift 1488210
  have htrace : WordTrace (prefixWord ++ tailWord_1488210) baseStart_1488210 baseEnd_1488210 := by
    simpa [prefixWord, tailWord_1488210, baseEnd_1488210] using wordTrace_append hprefix tailTrace_1488210
  have hstable : (prefixWord ++ tailWord_1488210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488210).length < 2 ^ (prefixWord ++ tailWord_1488210).sum := by decide
  have hdescent : baseEnd_1488210 < baseStart_1488210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488212 : List Nat := [2, 4, 1, 1, 2, 1, 3, 1, 3, 4]
def baseStart_1488212 : Nat := 118140960795 + 1488212 * 2 ^ 59
def prefixEnd_1488212 : Nat := 4983230072969 + 3 ^ 40 * 1488212 * 2
def baseEnd_1488212 : Nat := 509445381192691064937229

theorem tailTrace_1488212 : CollatzResearch.WordTrace tailWord_1488212 prefixEnd_1488212 509445381192691064937229 := by
  unfold tailWord_1488212
  simp only [CollatzResearch.WordTrace]
  refine ⟨27139775442234782609745445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36186367256313043479660593 27139775442234782609745445)
  ·
    refine ⟨5088707895419021739327271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27139775442234782609745445 5088707895419021739327271)
    ·
      refine ⟨7633061843128532608990907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5088707895419021739327271 7633061843128532608990907)
      ·
        refine ⟨11449592764692798913486361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7633061843128532608990907 11449592764692798913486361)
        ·
          refine ⟨8587194573519599185114771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11449592764692798913486361 8587194573519599185114771)
          ·
            refine ⟨12880791860279398777672157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8587194573519599185114771 12880791860279398777672157)
            ·
              refine ⟨4830296947604774541627059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12880791860279398777672157 4830296947604774541627059)
              ·
                refine ⟨7245445421407161812440589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4830296947604774541627059 7245445421407161812440589)
                ·
                  refine ⟨2717042033027685679665221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7245445421407161812440589 2717042033027685679665221)
                  ·
                    refine ⟨509445381192691064937229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2717042033027685679665221 509445381192691064937229)
                    ·
                      rfl

theorem cell22_1488212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_1488212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488212 prefixEnd_1488212 := by exact prefixLift 1488212
  have htrace : WordTrace (prefixWord ++ tailWord_1488212) baseStart_1488212 baseEnd_1488212 := by
    simpa [prefixWord, tailWord_1488212, baseEnd_1488212] using wordTrace_append hprefix tailTrace_1488212
  have hstable : (prefixWord ++ tailWord_1488212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488212).length < 2 ^ (prefixWord ++ tailWord_1488212).sum := by decide
  have hdescent : baseEnd_1488212 < baseStart_1488212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488229 : List Nat := [1, 3, 1, 3, 1, 2, 5, 1, 1, 4]
def baseStart_1488229 : Nat := 118140960795 + 1488229 * 2 ^ 59
def prefixEnd_1488229 : Nat := 4983230072969 + 3 ^ 40 * 1488229 * 2
def baseEnd_1488229 : Nat := 509451200640108687262177

theorem tailTrace_1488229 : CollatzResearch.WordTrace tailWord_1488229 prefixEnd_1488229 509451200640108687262177 := by
  unfold tailWord_1488229
  simp only [CollatzResearch.WordTrace]
  refine ⟨54280170925407977122859741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36186780616938651415239827 54280170925407977122859741)
  ·
    refine ⟨20355064097027991421072403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54280170925407977122859741 20355064097027991421072403)
    ·
      refine ⟨30532596145541987131608605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20355064097027991421072403 30532596145541987131608605)
      ·
        refine ⟨11449723554578245174353227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30532596145541987131608605 11449723554578245174353227)
        ·
          refine ⟨17174585331867367761529841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11449723554578245174353227 17174585331867367761529841)
          ·
            refine ⟨12880938998900525821147381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17174585331867367761529841 12880938998900525821147381)
            ·
              refine ⟨1207588031146924295732567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12880938998900525821147381 1207588031146924295732567)
              ·
                refine ⟨1811382046720386443598851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1207588031146924295732567 1811382046720386443598851)
                ·
                  refine ⟨2717073070080579665398277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1811382046720386443598851 2717073070080579665398277)
                  ·
                    refine ⟨509451200640108687262177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2717073070080579665398277 509451200640108687262177)
                    ·
                      rfl

theorem cell22_1488229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 1, 4].length) (baseStart_1488229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488229 prefixEnd_1488229 := by exact prefixLift 1488229
  have htrace : WordTrace (prefixWord ++ tailWord_1488229) baseStart_1488229 baseEnd_1488229 := by
    simpa [prefixWord, tailWord_1488229, baseEnd_1488229] using wordTrace_append hprefix tailTrace_1488229
  have hstable : (prefixWord ++ tailWord_1488229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488229).length < 2 ^ (prefixWord ++ tailWord_1488229).sum := by decide
  have hdescent : baseEnd_1488229 < baseStart_1488229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488259 : List Nat := [1, 1, 1, 3, 5, 1, 2, 3, 2, 3]
def baseStart_1488259 : Nat := 118140960795 + 1488259 * 2 ^ 59
def prefixEnd_1488259 : Nat := 4983230072969 + 3 ^ 40 * 1488259 * 2
def baseEnd_1488259 : Nat := 509461470253198609012085

theorem tailTrace_1488259 : CollatzResearch.WordTrace tailWord_1488259 prefixEnd_1488259 509461470253198609012085 := by
  unfold tailWord_1488259
  simp only [CollatzResearch.WordTrace]
  refine ⟨54281265115299292246451831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36187510076866194830967887 54281265115299292246451831)
  ·
    refine ⟨81421897672948938369677747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54281265115299292246451831 81421897672948938369677747)
    ·
      refine ⟨122132846509423407554516621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81421897672948938369677747 122132846509423407554516621)
      ·
        refine ⟨45799817441033777832943733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122132846509423407554516621 45799817441033777832943733)
        ·
          refine ⟨4293732885096916671838475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45799817441033777832943733 4293732885096916671838475)
          ·
            refine ⟨6440599327645375007757713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4293732885096916671838475 6440599327645375007757713)
            ·
              refine ⟨4830449495734031255818285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6440599327645375007757713 4830449495734031255818285)
              ·
                refine ⟨1811418560900261720931857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4830449495734031255818285 1811418560900261720931857)
                ·
                  refine ⟨1358563920675196290698893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1811418560900261720931857 1358563920675196290698893)
                  ·
                    refine ⟨509461470253198609012085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1358563920675196290698893 509461470253198609012085)
                    ·
                      rfl

theorem cell22_1488259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 2, 3].length) (baseStart_1488259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488259 prefixEnd_1488259 := by exact prefixLift 1488259
  have htrace : WordTrace (prefixWord ++ tailWord_1488259) baseStart_1488259 baseEnd_1488259 := by
    simpa [prefixWord, tailWord_1488259, baseEnd_1488259] using wordTrace_append hprefix tailTrace_1488259
  have hstable : (prefixWord ++ tailWord_1488259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488259).length < 2 ^ (prefixWord ++ tailWord_1488259).sum := by decide
  have hdescent : baseEnd_1488259 < baseStart_1488259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488377 : List Nat := [1, 2, 1, 3, 1, 2, 1, 5, 1, 5]
def baseStart_1488377 : Nat := 118140960795 + 1488377 * 2 ^ 59
def prefixEnd_1488377 : Nat := 4983230072969 + 3 ^ 40 * 1488377 * 2
def baseEnd_1488377 : Nat := 509501864064685634561723

theorem tailTrace_1488377 : CollatzResearch.WordTrace tailWord_1488377 prefixEnd_1488377 509501864064685634561723 := by
  unfold tailWord_1488377
  simp only [CollatzResearch.WordTrace]
  refine ⟨54285568928871798399247385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36190379285914532266164923 54285568928871798399247385)
  ·
    refine ⟨40714176696653848799435539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54285568928871798399247385 40714176696653848799435539)
    ·
      refine ⟨61071265044980773199153309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40714176696653848799435539 61071265044980773199153309)
      ·
        refine ⟨22901724391867789949682491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61071265044980773199153309 22901724391867789949682491)
        ·
          refine ⟨34352586587801684924523737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22901724391867789949682491 34352586587801684924523737)
          ·
            refine ⟨25764439940851263693392803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34352586587801684924523737 25764439940851263693392803)
            ·
              refine ⟨38646659911276895540089205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25764439940851263693392803 38646659911276895540089205)
              ·
                refine ⟨3623124366682208956883363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38646659911276895540089205 3623124366682208956883363)
                ·
                  refine ⟨5434686550023313435325045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3623124366682208956883363 5434686550023313435325045)
                  ·
                    refine ⟨509501864064685634561723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5434686550023313435325045 509501864064685634561723)
                    ·
                      rfl

theorem cell22_1488377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 5].length) (baseStart_1488377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488377 prefixEnd_1488377 := by exact prefixLift 1488377
  have htrace : WordTrace (prefixWord ++ tailWord_1488377) baseStart_1488377 baseEnd_1488377 := by
    simpa [prefixWord, tailWord_1488377, baseEnd_1488377] using wordTrace_append hprefix tailTrace_1488377
  have hstable : (prefixWord ++ tailWord_1488377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488377).length < 2 ^ (prefixWord ++ tailWord_1488377).sum := by decide
  have hdescent : baseEnd_1488377 < baseStart_1488377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488381 : List Nat := [1, 4, 1, 1, 1, 6, 1, 2, 1, 4]
def baseStart_1488381 : Nat := 118140960795 + 1488381 * 2 ^ 59
def prefixEnd_1488381 : Nat := 4983230072969 + 3 ^ 40 * 1488381 * 2
def baseEnd_1488381 : Nat := 509503233346430957461711

theorem tailTrace_1488381 : CollatzResearch.WordTrace tailWord_1488381 prefixEnd_1488381 509503233346430957461711 := by
  unfold tailWord_1488381
  simp only [CollatzResearch.WordTrace]
  refine ⟨54285714820857307082392997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36190476547238204721595331 54285714820857307082392997)
  ·
    refine ⟨10178571528910745077948687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54285714820857307082392997 10178571528910745077948687)
    ·
      refine ⟨15267857293366117616923031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10178571528910745077948687 15267857293366117616923031)
      ·
        refine ⟨22901785940049176425384547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15267857293366117616923031 22901785940049176425384547)
        ·
          refine ⟨34352678910073764638076821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22901785940049176425384547 34352678910073764638076821)
          ·
            refine ⟨1610281823909707717409851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34352678910073764638076821 1610281823909707717409851)
            ·
              refine ⟨2415422735864561576114777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1610281823909707717409851 2415422735864561576114777)
              ·
                refine ⟨1811567051898421182086083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2415422735864561576114777 1811567051898421182086083)
                ·
                  refine ⟨2717350577847631773129125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1811567051898421182086083 2717350577847631773129125)
                  ·
                    refine ⟨509503233346430957461711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2717350577847631773129125 509503233346430957461711)
                    ·
                      rfl

theorem cell22_1488381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_1488381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488381 prefixEnd_1488381 := by exact prefixLift 1488381
  have htrace : WordTrace (prefixWord ++ tailWord_1488381) baseStart_1488381 baseEnd_1488381 := by
    simpa [prefixWord, tailWord_1488381, baseEnd_1488381] using wordTrace_append hprefix tailTrace_1488381
  have hstable : (prefixWord ++ tailWord_1488381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488381).length < 2 ^ (prefixWord ++ tailWord_1488381).sum := by decide
  have hdescent : baseEnd_1488381 < baseStart_1488381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488392 : List Nat := [2, 1, 3, 2, 1, 1, 2, 3, 1, 6]
def baseStart_1488392 : Nat := 118140960795 + 1488392 * 2 ^ 59
def prefixEnd_1488392 : Nat := 4983230072969 + 3 ^ 40 * 1488392 * 2
def baseEnd_1488392 : Nat := 509506998871230595436677

theorem tailTrace_1488392 : CollatzResearch.WordTrace tailWord_1488392 prefixEnd_1488392 509506998871230595436677 := by
  unfold tailWord_1488392
  simp only [CollatzResearch.WordTrace]
  refine ⟨27143058011908727980521715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36190744015878303974028953 27143058011908727980521715)
  ·
    refine ⟨40714587017863091970782573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27143058011908727980521715 40714587017863091970782573)
    ·
      refine ⟨15267970131698659489043465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40714587017863091970782573 15267970131698659489043465)
      ·
        refine ⟨11450977598773994616782599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15267970131698659489043465 11450977598773994616782599)
        ·
          refine ⟨17176466398160991925173899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11450977598773994616782599 17176466398160991925173899)
          ·
            refine ⟨25764699597241487887760849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17176466398160991925173899 25764699597241487887760849)
            ·
              refine ⟨19323524697931115915820637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25764699597241487887760849 19323524697931115915820637)
              ·
                refine ⟨7246321761724168468432739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19323524697931115915820637 7246321761724168468432739)
                ·
                  refine ⟨10869482642586252702649109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7246321761724168468432739 10869482642586252702649109)
                  ·
                    refine ⟨509506998871230595436677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10869482642586252702649109 509506998871230595436677)
                    ·
                      rfl

theorem cell22_1488392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_1488392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488392 prefixEnd_1488392 := by exact prefixLift 1488392
  have htrace : WordTrace (prefixWord ++ tailWord_1488392) baseStart_1488392 baseEnd_1488392 := by
    simpa [prefixWord, tailWord_1488392, baseEnd_1488392] using wordTrace_append hprefix tailTrace_1488392
  have hstable : (prefixWord ++ tailWord_1488392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488392).length < 2 ^ (prefixWord ++ tailWord_1488392).sum := by decide
  have hdescent : baseEnd_1488392 < baseStart_1488392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488394 : List Nat := [3, 1, 2, 2, 2, 3, 1, 2, 1, 5]
def baseStart_1488394 : Nat := 118140960795 + 1488394 * 2 ^ 59
def prefixEnd_1488394 : Nat := 4983230072969 + 3 ^ 40 * 1488394 * 2
def baseEnd_1488394 : Nat := 509507683512103256886671

theorem tailTrace_1488394 : CollatzResearch.WordTrace tailWord_1488394 prefixEnd_1488394 509507683512103256886671 := by
  unfold tailWord_1488394
  simp only [CollatzResearch.WordTrace]
  refine ⟨13571547242452552575654059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36190792646540140201744157 13571547242452552575654059)
  ·
    refine ⟨20357320863678828863481089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13571547242452552575654059 20357320863678828863481089)
    ·
      refine ⟨15267990647759121647610817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20357320863678828863481089 15267990647759121647610817)
      ·
        refine ⟨11450992985819341235708113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15267990647759121647610817 11450992985819341235708113)
        ·
          refine ⟨8588244739364505926781085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11450992985819341235708113 8588244739364505926781085)
          ·
            refine ⟨3220591777261689722542907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8588244739364505926781085 3220591777261689722542907)
            ·
              refine ⟨4830887665892534583814361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3220591777261689722542907 4830887665892534583814361)
              ·
                refine ⟨3623165749419400937860771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4830887665892534583814361 3623165749419400937860771)
                ·
                  refine ⟨5434748624129101406791157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3623165749419400937860771 5434748624129101406791157)
                  ·
                    refine ⟨509507683512103256886671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5434748624129101406791157 509507683512103256886671)
                    ·
                      rfl

theorem cell22_1488394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_1488394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488394 prefixEnd_1488394 := by exact prefixLift 1488394
  have htrace : WordTrace (prefixWord ++ tailWord_1488394) baseStart_1488394 baseEnd_1488394 := by
    simpa [prefixWord, tailWord_1488394, baseEnd_1488394] using wordTrace_append hprefix tailTrace_1488394
  have hstable : (prefixWord ++ tailWord_1488394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488394).length < 2 ^ (prefixWord ++ tailWord_1488394).sum := by decide
  have hdescent : baseEnd_1488394 < baseStart_1488394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488398 : List Nat := [4, 1, 1, 2, 4, 1, 3, 1, 1, 4]
def baseStart_1488398 : Nat := 118140960795 + 1488398 * 2 ^ 59
def prefixEnd_1488398 : Nat := 4983230072969 + 3 ^ 40 * 1488398 * 2
def baseEnd_1488398 : Nat := 509509052793848579786659

theorem tailTrace_1488398 : CollatzResearch.WordTrace tailWord_1488398 prefixEnd_1488398 509509052793848579786659 := by
  unfold tailWord_1488398
  simp only [CollatzResearch.WordTrace]
  refine ⟨6785791857724464873220231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36190889907863812657174565 6785791857724464873220231)
  ·
    refine ⟨10178687786586697309830347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6785791857724464873220231 10178687786586697309830347)
    ·
      refine ⟨15268031679880045964745521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10178687786586697309830347 15268031679880045964745521)
      ·
        refine ⟨11451023759910034473559141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15268031679880045964745521 11451023759910034473559141)
        ·
          refine ⟨2147066954983131463792339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11451023759910034473559141 2147066954983131463792339)
          ·
            refine ⟨3220600432474697195688509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2147066954983131463792339 3220600432474697195688509)
            ·
              refine ⟨1207725162178011448383191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3220600432474697195688509 1207725162178011448383191)
              ·
                refine ⟨1811587743267017172574787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1207725162178011448383191 1811587743267017172574787)
                ·
                  refine ⟨2717381614900525758862181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1811587743267017172574787 2717381614900525758862181)
                  ·
                    refine ⟨509509052793848579786659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2717381614900525758862181 509509052793848579786659)
                    ·
                      rfl

theorem cell22_1488398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_1488398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488398 prefixEnd_1488398 := by exact prefixLift 1488398
  have htrace : WordTrace (prefixWord ++ tailWord_1488398) baseStart_1488398 baseEnd_1488398 := by
    simpa [prefixWord, tailWord_1488398, baseEnd_1488398] using wordTrace_append hprefix tailTrace_1488398
  have hstable : (prefixWord ++ tailWord_1488398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488398).length < 2 ^ (prefixWord ++ tailWord_1488398).sum := by decide
  have hdescent : baseEnd_1488398 < baseStart_1488398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488439 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 5, 3]
def baseStart_1488439 : Nat := 118140960795 + 1488439 * 2 ^ 59
def prefixEnd_1488439 : Nat := 4983230072969 + 3 ^ 40 * 1488439 * 2
def baseEnd_1488439 : Nat := 509523087931738139511533

theorem tailTrace_1488439 : CollatzResearch.WordTrace tailWord_1488439 prefixEnd_1488439 509523087931738139511533 := by
  unfold tailWord_1488439
  simp only [CollatzResearch.WordTrace]
  refine ⟨54287830254647182988004371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36191886836431455325336247 54287830254647182988004371)
  ·
    refine ⟨81431745381970774482006557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54287830254647182988004371 81431745381970774482006557)
    ·
      refine ⟨30536904518239040430752459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81431745381970774482006557 30536904518239040430752459)
      ·
        refine ⟨45805356777358560646128689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30536904518239040430752459 45805356777358560646128689)
        ·
          refine ⟨34354017583018920484596517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45805356777358560646128689 34354017583018920484596517)
          ·
            refine ⟨6441378296816047590861847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34354017583018920484596517 6441378296816047590861847)
            ·
              refine ⟨9662067445224071386292771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6441378296816047590861847 9662067445224071386292771)
              ·
                refine ⟨14493101167836107079439157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9662067445224071386292771 14493101167836107079439157)
                ·
                  refine ⟨1358728234484635038697421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14493101167836107079439157 1358728234484635038697421)
                  ·
                    refine ⟨509523087931738139511533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1358728234484635038697421 509523087931738139511533)
                    ·
                      rfl

theorem cell22_1488439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 5, 3].length) (baseStart_1488439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488439 prefixEnd_1488439 := by exact prefixLift 1488439
  have htrace : WordTrace (prefixWord ++ tailWord_1488439) baseStart_1488439 baseEnd_1488439 := by
    simpa [prefixWord, tailWord_1488439, baseEnd_1488439] using wordTrace_append hprefix tailTrace_1488439
  have hstable : (prefixWord ++ tailWord_1488439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488439).length < 2 ^ (prefixWord ++ tailWord_1488439).sum := by decide
  have hdescent : baseEnd_1488439 < baseStart_1488439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488484 : List Nat := [2, 3, 1, 1, 2, 3, 2, 1, 2, 5]
def baseStart_1488484 : Nat := 118140960795 + 1488484 * 2 ^ 59
def prefixEnd_1488484 : Nat := 4983230072969 + 3 ^ 40 * 1488484 * 2
def baseEnd_1488484 : Nat := 509538492351373022136395

theorem tailTrace_1488484 : CollatzResearch.WordTrace tailWord_1488484 prefixEnd_1488484 509538492351373022136395 := by
  unfold tailWord_1488484
  simp only [CollatzResearch.WordTrace]
  refine ⟨27144735769742077836696253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36192981026322770448928337 27144735769742077836696253)
  ·
    refine ⟨10179275913653279188761095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27144735769742077836696253 10179275913653279188761095)
    ·
      refine ⟨15268913870479918783141643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10179275913653279188761095 15268913870479918783141643)
      ·
        refine ⟨22903370805719878174712465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15268913870479918783141643 22903370805719878174712465)
        ·
          refine ⟨17177528104289908631034349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22903370805719878174712465 17177528104289908631034349)
          ·
            refine ⟨6441573039108715736637881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17177528104289908631034349 6441573039108715736637881)
            ·
              refine ⟨4831179779331536802478411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6441573039108715736637881 4831179779331536802478411)
              ·
                refine ⟨7246769668997305203717617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4831179779331536802478411 7246769668997305203717617)
                ·
                  refine ⟨5435077251747978902788213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7246769668997305203717617 5435077251747978902788213)
                  ·
                    refine ⟨509538492351373022136395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5435077251747978902788213 509538492351373022136395)
                    ·
                      rfl

theorem cell22_1488484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_1488484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488484 prefixEnd_1488484 := by exact prefixLift 1488484
  have htrace : WordTrace (prefixWord ++ tailWord_1488484) baseStart_1488484 baseEnd_1488484 := by
    simpa [prefixWord, tailWord_1488484, baseEnd_1488484] using wordTrace_append hprefix tailTrace_1488484
  have hstable : (prefixWord ++ tailWord_1488484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488484).length < 2 ^ (prefixWord ++ tailWord_1488484).sum := by decide
  have hdescent : baseEnd_1488484 < baseStart_1488484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488582 : List Nat := [6, 1, 2, 1, 1, 2, 1, 4, 4]
def baseStart_1488582 : Nat := 118140960795 + 1488582 * 2 ^ 59
def prefixEnd_1488582 : Nat := 4983230072969 + 3 ^ 40 * 1488582 * 2
def baseEnd_1488582 : Nat := 169857346584711144395365

theorem tailTrace_1488582 : CollatzResearch.WordTrace tailWord_1488582 prefixEnd_1488582 169857346584711144395365 := by
  unfold tailWord_1488582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1696657684160284950326875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36195363928752745606973333 1696657684160284950326875)
  ·
    refine ⟨2544986526240427425490313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1696657684160284950326875 2544986526240427425490313)
    ·
      refine ⟨1908739894680320569117735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2544986526240427425490313 1908739894680320569117735)
      ·
        refine ⟨2863109842020480853676603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1908739894680320569117735 2863109842020480853676603)
        ·
          refine ⟨4294664763030721280514905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2863109842020480853676603 4294664763030721280514905)
          ·
            refine ⟨3220998572273040960386179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4294664763030721280514905 3220998572273040960386179)
            ·
              refine ⟨4831497858409561440579269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3220998572273040960386179 4831497858409561440579269)
              ·
                refine ⟨905905848451792770108613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4831497858409561440579269 905905848451792770108613)
                ·
                  refine ⟨169857346584711144395365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 905905848451792770108613 169857346584711144395365)
                  ·
                    rfl

theorem cell22_1488582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_1488582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488582 prefixEnd_1488582 := by exact prefixLift 1488582
  have htrace : WordTrace (prefixWord ++ tailWord_1488582) baseStart_1488582 baseEnd_1488582 := by
    simpa [prefixWord, tailWord_1488582, baseEnd_1488582] using wordTrace_append hprefix tailTrace_1488582
  have hstable : (prefixWord ++ tailWord_1488582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488582).length < 2 ^ (prefixWord ++ tailWord_1488582).sum := by decide
  have hdescent : baseEnd_1488582 < baseStart_1488582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488625 : List Nat := [1, 2, 2, 2, 2, 4, 2, 3, 1, 3]
def baseStart_1488625 : Nat := 118140960795 + 1488625 * 2 ^ 59
def prefixEnd_1488625 : Nat := 4983230072969 + 3 ^ 40 * 1488625 * 2
def baseEnd_1488625 : Nat := 509586759532895654360963

theorem tailTrace_1488625 : CollatzResearch.WordTrace tailWord_1488625 prefixEnd_1488625 509586759532895654360963 := by
  unfold tailWord_1488625
  simp only [CollatzResearch.WordTrace]
  refine ⟨54294614231973336754275329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36196409487982224502850219 54294614231973336754275329)
  ·
    refine ⟨40720960673980002565706497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54294614231973336754275329 40720960673980002565706497)
    ·
      refine ⟨30540720505485001924279873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40720960673980002565706497 30540720505485001924279873)
      ·
        refine ⟨22905540379113751443209905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30540720505485001924279873 22905540379113751443209905)
        ·
          refine ⟨17179155284335313582407429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22905540379113751443209905 17179155284335313582407429)
          ·
            refine ⟨3221091615812871296701393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17179155284335313582407429 3221091615812871296701393)
            ·
              refine ⟨2415818711859653472526045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3221091615812871296701393 2415818711859653472526045)
              ·
                refine ⟨905932016947370052197267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2415818711859653472526045 905932016947370052197267)
                ·
                  refine ⟨1358898025421055078295901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 905932016947370052197267 1358898025421055078295901)
                  ·
                    refine ⟨509586759532895654360963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1358898025421055078295901 509586759532895654360963)
                    ·
                      rfl

theorem cell22_1488625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 3, 1, 3].length) (baseStart_1488625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488625 prefixEnd_1488625 := by exact prefixLift 1488625
  have htrace : WordTrace (prefixWord ++ tailWord_1488625) baseStart_1488625 baseEnd_1488625 := by
    simpa [prefixWord, tailWord_1488625, baseEnd_1488625] using wordTrace_append hprefix tailTrace_1488625
  have hstable : (prefixWord ++ tailWord_1488625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488625).length < 2 ^ (prefixWord ++ tailWord_1488625).sum := by decide
  have hdescent : baseEnd_1488625 < baseStart_1488625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488638 : List Nat := [4, 2, 2, 1, 3, 1, 1, 1, 7]
def baseStart_1488638 : Nat := 118140960795 + 1488638 * 2 ^ 59
def prefixEnd_1488638 : Nat := 4983230072969 + 3 ^ 40 * 1488638 * 2
def baseEnd_1488638 : Nat := 169863736566189317928641

theorem tailTrace_1488638 : CollatzResearch.WordTrace tailWord_1488638 prefixEnd_1488638 169863736566189317928641 := by
  unfold tailWord_1488638
  simp only [CollatzResearch.WordTrace]
  refine ⟨6786886047615779996812321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36196725587284159982999045 6786886047615779996812321)
  ·
    refine ⟨5090164535711834997609241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6786886047615779996812321 5090164535711834997609241)
    ·
      refine ⟨3817623401783876248206931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5090164535711834997609241 3817623401783876248206931)
      ·
        refine ⟨5726435102675814372310397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3817623401783876248206931 5726435102675814372310397)
        ·
          refine ⟨2147413163503430389616399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5726435102675814372310397 2147413163503430389616399)
          ·
            refine ⟨3221119745255145584424599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2147413163503430389616399 3221119745255145584424599)
            ·
              refine ⟨4831679617882718376636899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3221119745255145584424599 4831679617882718376636899)
              ·
                refine ⟨7247519426824077564955349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4831679617882718376636899 7247519426824077564955349)
                ·
                  refine ⟨169863736566189317928641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7247519426824077564955349 169863736566189317928641)
                  ·
                    rfl

theorem cell22_1488638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_1488638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488638 prefixEnd_1488638 := by exact prefixLift 1488638
  have htrace : WordTrace (prefixWord ++ tailWord_1488638) baseStart_1488638 baseEnd_1488638 := by
    simpa [prefixWord, tailWord_1488638, baseEnd_1488638] using wordTrace_append hprefix tailTrace_1488638
  have hstable : (prefixWord ++ tailWord_1488638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488638).length < 2 ^ (prefixWord ++ tailWord_1488638).sum := by decide
  have hdescent : baseEnd_1488638 < baseStart_1488638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488666 : List Nat := [3, 1, 1, 3, 2, 2, 2, 2, 6]
def baseStart_1488666 : Nat := 118140960795 + 1488666 * 2 ^ 59
def prefixEnd_1488666 : Nat := 4983230072969 + 3 ^ 40 * 1488666 * 2
def baseEnd_1488666 : Nat := 169866931556928404695279

theorem tailTrace_1488666 : CollatzResearch.WordTrace tailWord_1488666 prefixEnd_1488666 169866931556928404695279 := by
  unfold tailWord_1488666
  simp only [CollatzResearch.WordTrace]
  refine ⟨13574027406206200189129463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36197406416549867171011901 13574027406206200189129463)
  ·
    refine ⟨20361041109309300283694195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13574027406206200189129463 20361041109309300283694195)
    ·
      refine ⟨30541561663963950425541293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20361041109309300283694195 30541561663963950425541293)
      ·
        refine ⟨11453085623986481409577985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30541561663963950425541293 11453085623986481409577985)
        ·
          refine ⟨8589814217989861057183489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11453085623986481409577985 8589814217989861057183489)
          ·
            refine ⟨6442360663492395792887617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8589814217989861057183489 6442360663492395792887617)
            ·
              refine ⟨4831770497619296844665713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6442360663492395792887617 4831770497619296844665713)
              ·
                refine ⟨3623827873214472633499285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4831770497619296844665713 3623827873214472633499285)
                ·
                  refine ⟨169866931556928404695279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3623827873214472633499285 169866931556928404695279)
                  ·
                    rfl

theorem cell22_1488666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 6].length) (baseStart_1488666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488666 prefixEnd_1488666 := by exact prefixLift 1488666
  have htrace : WordTrace (prefixWord ++ tailWord_1488666) baseStart_1488666 baseEnd_1488666 := by
    simpa [prefixWord, tailWord_1488666, baseEnd_1488666] using wordTrace_append hprefix tailTrace_1488666
  have hstable : (prefixWord ++ tailWord_1488666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488666).length < 2 ^ (prefixWord ++ tailWord_1488666).sum := by decide
  have hdescent : baseEnd_1488666 < baseStart_1488666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488668 : List Nat := [2, 2, 3, 1, 1, 2, 4, 2, 1, 4]
def baseStart_1488668 : Nat := 118140960795 + 1488668 * 2 ^ 59
def prefixEnd_1488668 : Nat := 4983230072969 + 3 ^ 40 * 1488668 * 2
def baseEnd_1488668 : Nat := 509601479311657875535831

theorem tailTrace_1488668 : CollatzResearch.WordTrace tailWord_1488668 prefixEnd_1488668 509601479311657875535831 := by
  unfold tailWord_1488668
  simp only [CollatzResearch.WordTrace]
  refine ⟨27148091285408777549045329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36197455047211703398727105 27148091285408777549045329)
  ·
    refine ⟨20361068464056583161783997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27148091285408777549045329 20361068464056583161783997)
    ·
      refine ⟨7635400674021218685668999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20361068464056583161783997 7635400674021218685668999)
      ·
        refine ⟨11453101011031828028503499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7635400674021218685668999 11453101011031828028503499)
        ·
          refine ⟨17179651516547742042755249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11453101011031828028503499 17179651516547742042755249)
          ·
            refine ⟨12884738637410806532066437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17179651516547742042755249 12884738637410806532066437)
            ·
              refine ⟨2415888494514526224762457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12884738637410806532066437 2415888494514526224762457)
              ·
                refine ⟨1811916370885894668571843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2415888494514526224762457 1811916370885894668571843)
                ·
                  refine ⟨2717874556328842002857765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1811916370885894668571843 2717874556328842002857765)
                  ·
                    refine ⟨509601479311657875535831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2717874556328842002857765 509601479311657875535831)
                    ·
                      rfl

theorem cell22_1488668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_1488668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488668 prefixEnd_1488668 := by exact prefixLift 1488668
  have htrace : WordTrace (prefixWord ++ tailWord_1488668) baseStart_1488668 baseEnd_1488668 := by
    simpa [prefixWord, tailWord_1488668, baseEnd_1488668] using wordTrace_append hprefix tailTrace_1488668
  have hstable : (prefixWord ++ tailWord_1488668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488668).length < 2 ^ (prefixWord ++ tailWord_1488668).sum := by decide
  have hdescent : baseEnd_1488668 < baseStart_1488668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488696 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 4, 4]
def baseStart_1488696 : Nat := 118140960795 + 1488696 * 2 ^ 59
def prefixEnd_1488696 : Nat := 4983230072969 + 3 ^ 40 * 1488696 * 2
def baseEnd_1488696 : Nat := 509611064283875135835745

theorem tailTrace_1488696 : CollatzResearch.WordTrace tailWord_1488696 prefixEnd_1488696 509611064283875135835745 := by
  unfold tailWord_1488696
  simp only [CollatzResearch.WordTrace]
  refine ⟨27148601907358057940054971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36198135876477410586739961 27148601907358057940054971)
  ·
    refine ⟨40722902861037086910082457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27148601907358057940054971 40722902861037086910082457)
    ·
      refine ⟨30542177145777815182561843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40722902861037086910082457 30542177145777815182561843)
      ·
        refine ⟨45813265718666722773842765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30542177145777815182561843 45813265718666722773842765)
        ·
          refine ⟨17179974644500021040191037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45813265718666722773842765 17179974644500021040191037)
          ·
            refine ⟨6442490491687507890071639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17179974644500021040191037 6442490491687507890071639)
            ·
              refine ⟨9663735737531261835107459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6442490491687507890071639 9663735737531261835107459)
              ·
                refine ⟨14495603606296892752661189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9663735737531261835107459 14495603606296892752661189)
                ·
                  refine ⟨2717925676180667391123973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14495603606296892752661189 2717925676180667391123973)
                  ·
                    refine ⟨509611064283875135835745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2717925676180667391123973 509611064283875135835745)
                    ·
                      rfl

theorem cell22_1488696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_1488696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488696 prefixEnd_1488696 := by exact prefixLift 1488696
  have htrace : WordTrace (prefixWord ++ tailWord_1488696) baseStart_1488696 baseEnd_1488696 := by
    simpa [prefixWord, tailWord_1488696, baseEnd_1488696] using wordTrace_append hprefix tailTrace_1488696
  have hstable : (prefixWord ++ tailWord_1488696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488696).length < 2 ^ (prefixWord ++ tailWord_1488696).sum := by decide
  have hdescent : baseEnd_1488696 < baseStart_1488696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488698 : List Nat := [3, 1, 1, 1, 5, 1, 2, 1, 4, 3]
def baseStart_1488698 : Nat := 118140960795 + 1488698 * 2 ^ 59
def prefixEnd_1488698 : Nat := 4983230072969 + 3 ^ 40 * 1488698 * 2
def baseEnd_1488698 : Nat := 509611748924747797285739

theorem tailTrace_1488698 : CollatzResearch.WordTrace tailWord_1488698 prefixEnd_1488698 509611748924747797285739 := by
  unfold tailWord_1488698
  simp only [CollatzResearch.WordTrace]
  refine ⟨13574319190177217555420687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36198184507139246814455165 13574319190177217555420687)
  ·
    refine ⟨20361478785265826333131031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13574319190177217555420687 20361478785265826333131031)
    ·
      refine ⟨30542218177898739499696547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20361478785265826333131031 30542218177898739499696547)
      ·
        refine ⟨45813327266848109249544821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30542218177898739499696547 45813327266848109249544821)
        ·
          refine ⟨4294999431267010242144827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45813327266848109249544821 4294999431267010242144827)
          ·
            refine ⟨6442499146900515363217241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4294999431267010242144827 6442499146900515363217241)
            ·
              refine ⟨4831874360175386522412931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6442499146900515363217241 4831874360175386522412931)
              ·
                refine ⟨7247811540263079783619397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4831874360175386522412931 7247811540263079783619397)
                ·
                  refine ⟨1358964663799327459428637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7247811540263079783619397 1358964663799327459428637)
                  ·
                    refine ⟨509611748924747797285739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1358964663799327459428637 509611748924747797285739)
                    ·
                      rfl

theorem cell22_1488698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 4, 3].length) (baseStart_1488698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488698 prefixEnd_1488698 := by exact prefixLift 1488698
  have htrace : WordTrace (prefixWord ++ tailWord_1488698) baseStart_1488698 baseEnd_1488698 := by
    simpa [prefixWord, tailWord_1488698, baseEnd_1488698] using wordTrace_append hprefix tailTrace_1488698
  have hstable : (prefixWord ++ tailWord_1488698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488698).length < 2 ^ (prefixWord ++ tailWord_1488698).sum := by decide
  have hdescent : baseEnd_1488698 < baseStart_1488698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488771 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 1, 7]
def baseStart_1488771 : Nat := 118140960795 + 1488771 * 2 ^ 59
def prefixEnd_1488771 : Nat := 4983230072969 + 3 ^ 40 * 1488771 * 2
def baseEnd_1488771 : Nat := 509636738316599940210515

theorem tailTrace_1488771 : CollatzResearch.WordTrace tailWord_1488771 prefixEnd_1488771 509636738316599940210515 := by
  unfold tailWord_1488771
  simp only [CollatzResearch.WordTrace]
  refine ⟨54299939289444403689090167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36199959526296269126060111 54299939289444403689090167)
  ·
    refine ⟨81449908934166605533635251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54299939289444403689090167 81449908934166605533635251)
    ·
      refine ⟨122174863401249908300452877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81449908934166605533635251 122174863401249908300452877)
      ·
        refine ⟨45815573775468715612669829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122174863401249908300452877 45815573775468715612669829)
        ·
          refine ⟨8590420082900384177375593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45815573775468715612669829 8590420082900384177375593)
          ·
            refine ⟨6442815062175288133031695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8590420082900384177375593 6442815062175288133031695)
            ·
              refine ⟨9664222593262932199547543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6442815062175288133031695 9664222593262932199547543)
              ·
                refine ⟨14496333889894398299321315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9664222593262932199547543 14496333889894398299321315)
                ·
                  refine ⟨21744500834841597448981973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14496333889894398299321315 21744500834841597448981973)
                  ·
                    refine ⟨509636738316599940210515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21744500834841597448981973 509636738316599940210515)
                    ·
                      rfl

theorem cell22_1488771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 7].length) (baseStart_1488771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488771 prefixEnd_1488771 := by exact prefixLift 1488771
  have htrace : WordTrace (prefixWord ++ tailWord_1488771) baseStart_1488771 baseEnd_1488771 := by
    simpa [prefixWord, tailWord_1488771, baseEnd_1488771] using wordTrace_append hprefix tailTrace_1488771
  have hstable : (prefixWord ++ tailWord_1488771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488771).length < 2 ^ (prefixWord ++ tailWord_1488771).sum := by decide
  have hdescent : baseEnd_1488771 < baseStart_1488771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488831 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 3, 6]
def baseStart_1488831 : Nat := 118140960795 + 1488831 * 2 ^ 59
def prefixEnd_1488831 : Nat := 4983230072969 + 3 ^ 40 * 1488831 * 2
def baseEnd_1488831 : Nat := 509657277542779783710331

theorem tailTrace_1488831 : CollatzResearch.WordTrace tailWord_1488831 prefixEnd_1488831 509657277542779783710331 := by
  unfold tailWord_1488831
  simp only [CollatzResearch.WordTrace]
  refine ⟨54302127669227033936274347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36201418446151355957516231 54302127669227033936274347)
  ·
    refine ⟨81453191503840550904411521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54302127669227033936274347 81453191503840550904411521)
    ·
      refine ⟨61089893627880413178308641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81453191503840550904411521 61089893627880413178308641)
      ·
        refine ⟨45817420220910309883731481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61089893627880413178308641 45817420220910309883731481)
        ·
          refine ⟨34363065165682732412798611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45817420220910309883731481 34363065165682732412798611)
          ·
            refine ⟨51544597748524098619197917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34363065165682732412798611 51544597748524098619197917)
            ·
              refine ⟨19329224155696536982199219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51544597748524098619197917 19329224155696536982199219)
              ·
                refine ⟨28993836233544805473298829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19329224155696536982199219 28993836233544805473298829)
                ·
                  refine ⟨10872688587579302052487061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28993836233544805473298829 10872688587579302052487061)
                  ·
                    refine ⟨509657277542779783710331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10872688587579302052487061 509657277542779783710331)
                    ·
                      rfl

theorem cell22_1488831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 6].length) (baseStart_1488831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488831 prefixEnd_1488831 := by exact prefixLift 1488831
  have htrace : WordTrace (prefixWord ++ tailWord_1488831) baseStart_1488831 baseEnd_1488831 := by
    simpa [prefixWord, tailWord_1488831, baseEnd_1488831] using wordTrace_append hprefix tailTrace_1488831
  have hstable : (prefixWord ++ tailWord_1488831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488831).length < 2 ^ (prefixWord ++ tailWord_1488831).sum := by decide
  have hdescent : baseEnd_1488831 < baseStart_1488831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488863 : List Nat := [1, 1, 2, 3, 4, 3, 8]
def baseStart_1488863 : Nat := 118140960795 + 1488863 * 2 ^ 59
def prefixEnd_1488863 : Nat := 4983230072969 + 3 ^ 40 * 1488863 * 2
def baseEnd_1488863 : Nat := 18876601177657124700379

theorem tailTrace_1488863 : CollatzResearch.WordTrace tailWord_1488863 prefixEnd_1488863 18876601177657124700379 := by
  unfold tailWord_1488863
  simp only [CollatzResearch.WordTrace]
  refine ⟨54303294805111103401439243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36202196536740735600959495 54303294805111103401439243)
  ·
    refine ⟨81454942207666655102158865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54303294805111103401439243 81454942207666655102158865)
    ·
      refine ⟨61091206655749991326619149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81454942207666655102158865 61091206655749991326619149)
      ·
        refine ⟨22909202495906246747482181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61091206655749991326619149 22909202495906246747482181)
        ·
          refine ⟨4295475467982421265152909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22909202495906246747482181 4295475467982421265152909)
          ·
            refine ⟨1610803300493407974432341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4295475467982421265152909 1610803300493407974432341)
            ·
              refine ⟨18876601177657124700379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1610803300493407974432341 18876601177657124700379)
              ·
                rfl

theorem cell22_1488863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 8].length) (baseStart_1488863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488863 prefixEnd_1488863 := by exact prefixLift 1488863
  have htrace : WordTrace (prefixWord ++ tailWord_1488863) baseStart_1488863 baseEnd_1488863 := by
    simpa [prefixWord, tailWord_1488863, baseEnd_1488863] using wordTrace_append hprefix tailTrace_1488863
  have hstable : (prefixWord ++ tailWord_1488863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488863).length < 2 ^ (prefixWord ++ tailWord_1488863).sum := by decide
  have hdescent : baseEnd_1488863 < baseStart_1488863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488925 : List Nat := [1, 4, 2, 2, 2, 1, 1, 4, 5]
def baseStart_1488925 : Nat := 118140960795 + 1488925 * 2 ^ 59
def prefixEnd_1488925 : Nat := 4983230072969 + 3 ^ 40 * 1488925 * 2
def baseEnd_1488925 : Nat := 169896485221264957286681

theorem tailTrace_1488925 : CollatzResearch.WordTrace tailWord_1488925 prefixEnd_1488925 169896485221264957286681 := by
  unfold tailWord_1488925
  simp only [CollatzResearch.WordTrace]
  refine ⟨54305556130886487990196229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36203704087257658660130819 54305556130886487990196229)
  ·
    refine ⟨10182291774541216498161793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54305556130886487990196229 10182291774541216498161793)
    ·
      refine ⟨7636718830905912373621345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10182291774541216498161793 7636718830905912373621345)
      ·
        refine ⟨5727539123179434280216009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7636718830905912373621345 5727539123179434280216009)
        ·
          refine ⟨4295654342384575710162007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5727539123179434280216009 4295654342384575710162007)
          ·
            refine ⟨6443481513576863565243011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4295654342384575710162007 6443481513576863565243011)
            ·
              refine ⟨9665222270365295347864517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6443481513576863565243011 9665222270365295347864517)
              ·
                refine ⟨1812229175693492877724597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9665222270365295347864517 1812229175693492877724597)
                ·
                  refine ⟨169896485221264957286681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1812229175693492877724597 169896485221264957286681)
                  ·
                    rfl

theorem cell22_1488925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_1488925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488925 prefixEnd_1488925 := by exact prefixLift 1488925
  have htrace : WordTrace (prefixWord ++ tailWord_1488925) baseStart_1488925 baseEnd_1488925 := by
    simpa [prefixWord, tailWord_1488925, baseEnd_1488925] using wordTrace_append hprefix tailTrace_1488925
  have hstable : (prefixWord ++ tailWord_1488925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488925).length < 2 ^ (prefixWord ++ tailWord_1488925).sum := by decide
  have hdescent : baseEnd_1488925 < baseStart_1488925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488929 : List Nat := [1, 2, 3, 2, 4, 1, 1, 4, 1, 3]
def baseStart_1488929 : Nat := 118140960795 + 1488929 * 2 ^ 59
def prefixEnd_1488929 : Nat := 4983230072969 + 3 ^ 40 * 1488929 * 2
def baseEnd_1488929 : Nat := 509690824945540194760031

theorem tailTrace_1488929 : CollatzResearch.WordTrace tailWord_1488929 prefixEnd_1488929 509690824945540194760031 := by
  unfold tailWord_1488929
  simp only [CollatzResearch.WordTrace]
  refine ⟨54305702022871996673341841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36203801348581331115561227 54305702022871996673341841)
  ·
    refine ⟨40729276517153997505006381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54305702022871996673341841 40729276517153997505006381)
    ·
      refine ⟨15273478693932749064377393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40729276517153997505006381 15273478693932749064377393)
      ·
        refine ⟨11455109020449561798283045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15273478693932749064377393 11455109020449561798283045)
        ·
          refine ⟨2147832941334292837178071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11455109020449561798283045 2147832941334292837178071)
          ·
            refine ⟨3221749412001439255767107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2147832941334292837178071 3221749412001439255767107)
            ·
              refine ⟨4832624118002158883650661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3221749412001439255767107 4832624118002158883650661)
              ·
                refine ⟨906117022125404790684499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4832624118002158883650661 906117022125404790684499)
                ·
                  refine ⟨1359175533188107186026749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 906117022125404790684499 1359175533188107186026749)
                  ·
                    refine ⟨509690824945540194760031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1359175533188107186026749 509690824945540194760031)
                    ·
                      rfl

theorem cell22_1488929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 4, 1, 3].length) (baseStart_1488929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488929 prefixEnd_1488929 := by exact prefixLift 1488929
  have htrace : WordTrace (prefixWord ++ tailWord_1488929) baseStart_1488929 baseEnd_1488929 := by
    simpa [prefixWord, tailWord_1488929, baseEnd_1488929] using wordTrace_append hprefix tailTrace_1488929
  have hstable : (prefixWord ++ tailWord_1488929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488929).length < 2 ^ (prefixWord ++ tailWord_1488929).sum := by decide
  have hdescent : baseEnd_1488929 < baseStart_1488929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488968 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 3, 5]
def baseStart_1488968 : Nat := 118140960795 + 1488968 * 2 ^ 59
def prefixEnd_1488968 : Nat := 4983230072969 + 3 ^ 40 * 1488968 * 2
def baseEnd_1488968 : Nat := 509704175442557093034911

theorem tailTrace_1488968 : CollatzResearch.WordTrace tailWord_1488968 prefixEnd_1488968 509704175442557093034911 := by
  unfold tailWord_1488968
  simp only [CollatzResearch.WordTrace]
  refine ⟨27153562234865353167005779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36204749646487137556007705 27153562234865353167005779)
  ·
    refine ⟨40730343352298029750508669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27153562234865353167005779 40730343352298029750508669)
    ·
      refine ⟨15273878757111761156440751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40730343352298029750508669 15273878757111761156440751)
      ·
        refine ⟨22910818135667641734661127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15273878757111761156440751 22910818135667641734661127)
        ·
          refine ⟨34366227203501462601991691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22910818135667641734661127 34366227203501462601991691)
          ·
            refine ⟨51549340805252193902987537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34366227203501462601991691 51549340805252193902987537)
            ·
              refine ⟨38662005603939145427240653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51549340805252193902987537 38662005603939145427240653)
              ·
                refine ⟨14498252101477179535215245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38662005603939145427240653 14498252101477179535215245)
                ·
                  refine ⟨5436844538053942325705717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14498252101477179535215245 5436844538053942325705717)
                  ·
                    refine ⟨509704175442557093034911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5436844538053942325705717 509704175442557093034911)
                    ·
                      rfl

theorem cell22_1488968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_1488968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488968 prefixEnd_1488968 := by exact prefixLift 1488968
  have htrace : WordTrace (prefixWord ++ tailWord_1488968) baseStart_1488968 baseEnd_1488968 := by
    simpa [prefixWord, tailWord_1488968, baseEnd_1488968] using wordTrace_append hprefix tailTrace_1488968
  have hstable : (prefixWord ++ tailWord_1488968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488968).length < 2 ^ (prefixWord ++ tailWord_1488968).sum := by decide
  have hdescent : baseEnd_1488968 < baseStart_1488968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488972 : List Nat := [2, 2, 1, 3, 1, 1, 6, 1, 1, 4]
def baseStart_1488972 : Nat := 118140960795 + 1488972 * 2 ^ 59
def prefixEnd_1488972 : Nat := 4983230072969 + 3 ^ 40 * 1488972 * 2
def baseEnd_1488972 : Nat := 509705544724302415934899

theorem tailTrace_1488972 : CollatzResearch.WordTrace tailWord_1488972 prefixEnd_1488972 509705544724302415934899 := by
  unfold tailWord_1488972
  simp only [CollatzResearch.WordTrace]
  refine ⟨27153635180858107508578585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36204846907810810011438113 27153635180858107508578585)
  ·
    refine ⟨20365226385643580631433939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27153635180858107508578585 20365226385643580631433939)
    ·
      refine ⟨30547839578465370947150909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20365226385643580631433939 30547839578465370947150909)
      ·
        refine ⟨11455439841924514105181591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30547839578465370947150909 11455439841924514105181591)
        ·
          refine ⟨17183159762886771157772387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11455439841924514105181591 17183159762886771157772387)
          ·
            refine ⟨25774739644330156736658581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17183159762886771157772387 25774739644330156736658581)
            ·
              refine ⟨1208190920827976097030871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25774739644330156736658581 1208190920827976097030871)
              ·
                refine ⟨1812286381241964145546307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1208190920827976097030871 1812286381241964145546307)
                ·
                  refine ⟨2718429571862946218319461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1812286381241964145546307 2718429571862946218319461)
                  ·
                    refine ⟨509705544724302415934899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2718429571862946218319461 509705544724302415934899)
                    ·
                      rfl

theorem cell22_1488972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 1, 4].length) (baseStart_1488972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488972 prefixEnd_1488972 := by exact prefixLift 1488972
  have htrace : WordTrace (prefixWord ++ tailWord_1488972) baseStart_1488972 baseEnd_1488972 := by
    simpa [prefixWord, tailWord_1488972, baseEnd_1488972] using wordTrace_append hprefix tailTrace_1488972
  have hstable : (prefixWord ++ tailWord_1488972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488972).length < 2 ^ (prefixWord ++ tailWord_1488972).sum := by decide
  have hdescent : baseEnd_1488972 < baseStart_1488972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1488985 : List Nat := [1, 2, 1, 2, 2, 1, 5, 1, 4, 3]
def baseStart_1488985 : Nat := 118140960795 + 1488985 * 2 ^ 59
def prefixEnd_1488985 : Nat := 4983230072969 + 3 ^ 40 * 1488985 * 2
def baseEnd_1488985 : Nat := 509709994889974715359859

theorem tailTrace_1488985 : CollatzResearch.WordTrace tailWord_1488985 prefixEnd_1488985 509709994889974715359859 := by
  unfold tailWord_1488985
  simp only [CollatzResearch.WordTrace]
  refine ⟨54307744510669118237380409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36205163007112745491586939 54307744510669118237380409)
  ·
    refine ⟨40730808383001838678035307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54307744510669118237380409 40730808383001838678035307)
    ·
      refine ⟨61096212574502758017052961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40730808383001838678035307 61096212574502758017052961)
      ·
        refine ⟨45822159430877068512789721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61096212574502758017052961 45822159430877068512789721)
        ·
          refine ⟨34366619573157801384592291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45822159430877068512789721 34366619573157801384592291)
          ·
            refine ⟨51549929359736702076888437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34366619573157801384592291 51549929359736702076888437)
            ·
              refine ⟨4832805877475315819708291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51549929359736702076888437 4832805877475315819708291)
              ·
                refine ⟨7249208816212973729562437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4832805877475315819708291 7249208816212973729562437)
                ·
                  refine ⟨1359226653039932574292957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7249208816212973729562437 1359226653039932574292957)
                  ·
                    refine ⟨509709994889974715359859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1359226653039932574292957 509709994889974715359859)
                    ·
                      rfl

theorem cell22_1488985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 4, 3].length) (baseStart_1488985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1488985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1488985 prefixEnd_1488985 := by exact prefixLift 1488985
  have htrace : WordTrace (prefixWord ++ tailWord_1488985) baseStart_1488985 baseEnd_1488985 := by
    simpa [prefixWord, tailWord_1488985, baseEnd_1488985] using wordTrace_append hprefix tailTrace_1488985
  have hstable : (prefixWord ++ tailWord_1488985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1488985).length < 2 ^ (prefixWord ++ tailWord_1488985).sum := by decide
  have hdescent : baseEnd_1488985 < baseStart_1488985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1488985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489015 : List Nat := [1, 1, 3, 1, 1, 5, 4, 6]
def baseStart_1489015 : Nat := 118140960795 + 1489015 * 2 ^ 59
def prefixEnd_1489015 : Nat := 4983230072969 + 3 ^ 40 * 1489015 * 2
def baseEnd_1489015 : Nat := 56635584944784959678863

theorem tailTrace_1489015 : CollatzResearch.WordTrace tailWord_1489015 prefixEnd_1489015 56635584944784959678863 := by
  unfold tailWord_1489015
  simp only [CollatzResearch.WordTrace]
  refine ⟨54308838700560433360972499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36205892467040288907314999 54308838700560433360972499)
  ·
    refine ⟨81463258050840650041458749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54308838700560433360972499 81463258050840650041458749)
    ·
      refine ⟨30548721769065243765547031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81463258050840650041458749 30548721769065243765547031)
      ·
        refine ⟨45823082653597865648320547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30548721769065243765547031 45823082653597865648320547)
        ·
          refine ⟨68734623980396798472480821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45823082653597865648320547 68734623980396798472480821)
          ·
            refine ⟨6443870998162199856795077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68734623980396798472480821 6443870998162199856795077)
            ·
              refine ⟨1208225812155412473149077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6443870998162199856795077 1208225812155412473149077)
              ·
                refine ⟨56635584944784959678863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1208225812155412473149077 56635584944784959678863)
                ·
                  rfl

theorem cell22_1489015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 6].length) (baseStart_1489015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1489015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1489015 prefixEnd_1489015 := by exact prefixLift 1489015
  have htrace : WordTrace (prefixWord ++ tailWord_1489015) baseStart_1489015 baseEnd_1489015 := by
    simpa [prefixWord, tailWord_1489015, baseEnd_1489015] using wordTrace_append hprefix tailTrace_1489015
  have hstable : (prefixWord ++ tailWord_1489015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489015).length < 2 ^ (prefixWord ++ tailWord_1489015).sum := by decide
  have hdescent : baseEnd_1489015 < baseStart_1489015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489184 : List Nat := [2, 1, 1, 5, 2, 3, 2, 6]
def baseStart_1489184 : Nat := 118140960795 + 1489184 * 2 ^ 59
def prefixEnd_1489184 : Nat := 4983230072969 + 3 ^ 40 * 1489184 * 2
def baseEnd_1489184 : Nat := 56642012961867169959361

theorem tailTrace_1489184 : CollatzResearch.WordTrace tailWord_1489184 prefixEnd_1489184 56642012961867169959361 := by
  unfold tailWord_1489184
  simp only [CollatzResearch.WordTrace]
  refine ⟨27157501318474087611937303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36210001757965450149249737 27157501318474087611937303)
  ·
    refine ⟨40736251977711131417905955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27157501318474087611937303 40736251977711131417905955)
    ·
      refine ⟨61104377966566697126858933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40736251977711131417905955 61104377966566697126858933)
      ·
        refine ⟨5728535434365627855643025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61104377966566697126858933 5728535434365627855643025)
        ·
          refine ⟨4296401575774220891732269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5728535434365627855643025 4296401575774220891732269)
          ·
            refine ⟨1611150590915332834399601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4296401575774220891732269 1611150590915332834399601)
            ·
              refine ⟨1208362943186499625799701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1611150590915332834399601 1208362943186499625799701)
              ·
                refine ⟨56642012961867169959361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1208362943186499625799701 56642012961867169959361)
                ·
                  rfl

theorem cell22_1489184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 6].length) (baseStart_1489184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1489184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1489184 prefixEnd_1489184 := by exact prefixLift 1489184
  have htrace : WordTrace (prefixWord ++ tailWord_1489184) baseStart_1489184 baseEnd_1489184 := by
    simpa [prefixWord, tailWord_1489184, baseEnd_1489184] using wordTrace_append hprefix tailTrace_1489184
  have hstable : (prefixWord ++ tailWord_1489184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489184).length < 2 ^ (prefixWord ++ tailWord_1489184).sum := by decide
  have hdescent : baseEnd_1489184 < baseStart_1489184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489212 : List Nat := [2, 2, 2, 2, 1, 2, 2, 4, 5]
def baseStart_1489212 : Nat := 118140960795 + 1489212 * 2 ^ 59
def prefixEnd_1489212 : Nat := 4983230072969 + 3 ^ 40 * 1489212 * 2
def baseEnd_1489212 : Nat := 169929233876340596644721

theorem tailTrace_1489212 : CollatzResearch.WordTrace tailWord_1489212 prefixEnd_1489212 169929233876340596644721 := by
  unfold tailWord_1489212
  simp only [CollatzResearch.WordTrace]
  refine ⟨27158011940423368002946945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36210682587231157337262593 27158011940423368002946945)
  ·
    refine ⟨20368508955317526002210209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27158011940423368002946945 20368508955317526002210209)
    ·
      refine ⟨15276381716488144501657657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20368508955317526002210209 15276381716488144501657657)
      ·
        refine ⟨11457286287366108376243243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15276381716488144501657657 11457286287366108376243243)
        ·
          refine ⟨17185929431049162564364865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11457286287366108376243243 17185929431049162564364865)
          ·
            refine ⟨12889447073286871923273649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17185929431049162564364865 12889447073286871923273649)
            ·
              refine ⟨9667085304965153942455237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12889447073286871923273649 9667085304965153942455237)
              ·
                refine ⟨1812578494680966364210357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9667085304965153942455237 1812578494680966364210357)
                ·
                  refine ⟨169929233876340596644721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1812578494680966364210357 169929233876340596644721)
                  ·
                    rfl

theorem cell22_1489212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 5].length) (baseStart_1489212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1489212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1489212 prefixEnd_1489212 := by exact prefixLift 1489212
  have htrace : WordTrace (prefixWord ++ tailWord_1489212) baseStart_1489212 baseEnd_1489212 := by
    simpa [prefixWord, tailWord_1489212, baseEnd_1489212] using wordTrace_append hprefix tailTrace_1489212
  have hstable : (prefixWord ++ tailWord_1489212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489212).length < 2 ^ (prefixWord ++ tailWord_1489212).sum := by decide
  have hdescent : baseEnd_1489212 < baseStart_1489212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489225 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 2, 8]
def baseStart_1489225 : Nat := 118140960795 + 1489225 * 2 ^ 59
def prefixEnd_1489225 : Nat := 4983230072969 + 3 ^ 40 * 1489225 * 2
def baseEnd_1489225 : Nat := 509792151794694089359123

theorem tailTrace_1489225 : CollatzResearch.WordTrace tailWord_1489225 prefixEnd_1489225 509792151794694089359123 := by
  unfold tailWord_1489225
  simp only [CollatzResearch.WordTrace]
  refine ⟨54316498029799639226117129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36210998686533092817411419 54316498029799639226117129)
  ·
    refine ⟨40737373522349729419587847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54316498029799639226117129 40737373522349729419587847)
    ·
      refine ⟨61106060283524594129381771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40737373522349729419587847 61106060283524594129381771)
      ·
        refine ⟨91659090425286891194072657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61106060283524594129381771 91659090425286891194072657)
        ·
          refine ⟨68744317818965168395554493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91659090425286891194072657 68744317818965168395554493)
          ·
            refine ⟨25779119182111938148332935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68744317818965168395554493 25779119182111938148332935)
            ·
              refine ⟨38668678773167907222499403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25779119182111938148332935 38668678773167907222499403)
              ·
                refine ⟨58003018159751860833749105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38668678773167907222499403 58003018159751860833749105)
                ·
                  refine ⟨43502263619813895625311829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58003018159751860833749105 43502263619813895625311829)
                  ·
                    refine ⟨509792151794694089359123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 43502263619813895625311829 509792151794694089359123)
                    ·
                      rfl

theorem cell22_1489225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 8].length) (baseStart_1489225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1489225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1489225 prefixEnd_1489225 := by exact prefixLift 1489225
  have htrace : WordTrace (prefixWord ++ tailWord_1489225) baseStart_1489225 baseEnd_1489225 := by
    simpa [prefixWord, tailWord_1489225, baseEnd_1489225] using wordTrace_append hprefix tailTrace_1489225
  have hstable : (prefixWord ++ tailWord_1489225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489225).length < 2 ^ (prefixWord ++ tailWord_1489225).sum := by decide
  have hdescent : baseEnd_1489225 < baseStart_1489225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489287 : List Nat := [1, 1, 4, 2, 2, 1, 2, 2, 1, 6]
def baseStart_1489287 : Nat := 118140960795 + 1489287 * 2 ^ 59
def prefixEnd_1489287 : Nat := 4983230072969 + 3 ^ 40 * 1489287 * 2
def baseEnd_1489287 : Nat := 509813375661746594308933

theorem tailTrace_1489287 : CollatzResearch.WordTrace tailWord_1489287 prefixEnd_1489287 509813375661746594308933 := by
  unfold tailWord_1489287
  simp only [CollatzResearch.WordTrace]
  refine ⟨54318759355575023814874115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36212506237050015876582743 54318759355575023814874115)
  ·
    refine ⟨81478139033362535722311173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54318759355575023814874115 81478139033362535722311173)
    ·
      refine ⟨15277151068755475447933345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81478139033362535722311173 15277151068755475447933345)
      ·
        refine ⟨11457863301566606585950009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15277151068755475447933345 11457863301566606585950009)
        ·
          refine ⟨8593397476174954939462507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11457863301566606585950009 8593397476174954939462507)
          ·
            refine ⟨12890096214262432409193761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8593397476174954939462507 12890096214262432409193761)
            ·
              refine ⟨9667572160696824306895321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12890096214262432409193761 9667572160696824306895321)
              ·
                refine ⟨7250679120522618230171491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9667572160696824306895321 7250679120522618230171491)
                ·
                  refine ⟨10876018680783927345257237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7250679120522618230171491 10876018680783927345257237)
                  ·
                    refine ⟨509813375661746594308933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10876018680783927345257237 509813375661746594308933)
                    ·
                      rfl

theorem cell22_1489287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_1489287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1489287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1489287 prefixEnd_1489287 := by exact prefixLift 1489287
  have htrace : WordTrace (prefixWord ++ tailWord_1489287) baseStart_1489287 baseEnd_1489287 := by
    simpa [prefixWord, tailWord_1489287, baseEnd_1489287] using wordTrace_append hprefix tailTrace_1489287
  have hstable : (prefixWord ++ tailWord_1489287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489287).length < 2 ^ (prefixWord ++ tailWord_1489287).sum := by decide
  have hdescent : baseEnd_1489287 < baseStart_1489287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489289 : List Nat := [1, 2, 1, 1, 6, 2, 2, 1, 1, 5]
def baseStart_1489289 : Nat := 118140960795 + 1489289 * 2 ^ 59
def prefixEnd_1489289 : Nat := 4983230072969 + 3 ^ 40 * 1489289 * 2
def baseEnd_1489289 : Nat := 509814060302619255758927

theorem tailTrace_1489289 : CollatzResearch.WordTrace tailWord_1489289 prefixEnd_1489289 509814060302619255758927 := by
  unfold tailWord_1489289
  simp only [CollatzResearch.WordTrace]
  refine ⟨54318832301567778156446921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36212554867711852104297947 54318832301567778156446921)
  ·
    refine ⟨40739124226175833617335191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54318832301567778156446921 40739124226175833617335191)
    ·
      refine ⟨61108686339263750426002787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40739124226175833617335191 61108686339263750426002787)
      ·
        refine ⟨91663029508895625639004181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61108686339263750426002787 91663029508895625639004181)
        ·
          refine ⟨4296704508229482451828321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 91663029508895625639004181 4296704508229482451828321)
          ·
            refine ⟨3222528381172111838871241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4296704508229482451828321 3222528381172111838871241)
            ·
              refine ⟨2416896285879083879153431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3222528381172111838871241 2416896285879083879153431)
              ·
                refine ⟨3625344428818625818730147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2416896285879083879153431 3625344428818625818730147)
                ·
                  refine ⟨5438016643227938728095221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3625344428818625818730147 5438016643227938728095221)
                  ·
                    refine ⟨509814060302619255758927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5438016643227938728095221 509814060302619255758927)
                    ·
                      rfl

theorem cell22_1489289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 5].length) (baseStart_1489289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1489289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1489289 prefixEnd_1489289 := by exact prefixLift 1489289
  have htrace : WordTrace (prefixWord ++ tailWord_1489289) baseStart_1489289 baseEnd_1489289 := by
    simpa [prefixWord, tailWord_1489289, baseEnd_1489289] using wordTrace_append hprefix tailTrace_1489289
  have hstable : (prefixWord ++ tailWord_1489289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489289).length < 2 ^ (prefixWord ++ tailWord_1489289).sum := by decide
  have hdescent : baseEnd_1489289 < baseStart_1489289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489304 : List Nat := [2, 1, 2, 5, 1, 2, 1, 1, 1, 6]
def baseStart_1489304 : Nat := 118140960795 + 1489304 * 2 ^ 59
def prefixEnd_1489304 : Nat := 4983230072969 + 3 ^ 40 * 1489304 * 2
def baseEnd_1489304 : Nat := 509819195109164216633881

theorem tailTrace_1489304 : CollatzResearch.WordTrace tailWord_1489304 prefixEnd_1489304 509819195109164216633881 := by
  unfold tailWord_1489304
  simp only [CollatzResearch.WordTrace]
  refine ⟨27159689698256717859121483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36212919597675623812161977 27159689698256717859121483)
  ·
    refine ⟨40739534547385076788682225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27159689698256717859121483 40739534547385076788682225)
    ·
      refine ⟨30554650910538807591511669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40739534547385076788682225 30554650910538807591511669)
      ·
        refine ⟨2864498522863013211704219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30554650910538807591511669 2864498522863013211704219)
        ·
          refine ⟨4296747784294519817556329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2864498522863013211704219 4296747784294519817556329)
          ·
            refine ⟨3222560838220889863167247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4296747784294519817556329 3222560838220889863167247)
            ·
              refine ⟨4833841257331334794750871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3222560838220889863167247 4833841257331334794750871)
              ·
                refine ⟨7250761885997002192126307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4833841257331334794750871 7250761885997002192126307)
                ·
                  refine ⟨10876142828995503288189461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7250761885997002192126307 10876142828995503288189461)
                  ·
                    refine ⟨509819195109164216633881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10876142828995503288189461 509819195109164216633881)
                    ·
                      rfl

theorem cell22_1489304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_1489304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1489304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1489304 prefixEnd_1489304 := by exact prefixLift 1489304
  have htrace : WordTrace (prefixWord ++ tailWord_1489304) baseStart_1489304 baseEnd_1489304 := by
    simpa [prefixWord, tailWord_1489304, baseEnd_1489304] using wordTrace_append hprefix tailTrace_1489304
  have hstable : (prefixWord ++ tailWord_1489304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489304).length < 2 ^ (prefixWord ++ tailWord_1489304).sum := by decide
  have hdescent : baseEnd_1489304 < baseStart_1489304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489310 : List Nat := [4, 3, 1, 2, 1, 3, 2, 1, 1, 4]
def baseStart_1489310 : Nat := 118140960795 + 1489310 * 2 ^ 59
def prefixEnd_1489310 : Nat := 4983230072969 + 3 ^ 40 * 1489310 * 2
def baseEnd_1489310 : Nat := 509821249031782200983863

theorem tailTrace_1489310 : CollatzResearch.WordTrace tailWord_1489310 prefixEnd_1489310 509821249031782200983863 := by
  unfold tailWord_1489310
  simp only [CollatzResearch.WordTrace]
  refine ⟨6789949779311462342870173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36213065489661132495307589 6789949779311462342870173)
  ·
    refine ⟨2546231167241798378576315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6789949779311462342870173 2546231167241798378576315)
    ·
      refine ⟨3819346750862697567864473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2546231167241798378576315 3819346750862697567864473)
      ·
        refine ⟨2864510063147023175898355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3819346750862697567864473 2864510063147023175898355)
        ·
          refine ⟨4296765094720534763847533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2864510063147023175898355 4296765094720534763847533)
          ·
            refine ⟨1611286910520200536442825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4296765094720534763847533 1611286910520200536442825)
            ·
              refine ⟨1208465182890150402332119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1611286910520200536442825 1208465182890150402332119)
              ·
                refine ⟨1812697774335225603498179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1208465182890150402332119 1812697774335225603498179)
                ·
                  refine ⟨2719046661502838405247269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1812697774335225603498179 2719046661502838405247269)
                  ·
                    refine ⟨509821249031782200983863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2719046661502838405247269 509821249031782200983863)
                    ·
                      rfl

theorem cell22_1489310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_1489310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1489310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1489310 prefixEnd_1489310 := by exact prefixLift 1489310
  have htrace : WordTrace (prefixWord ++ tailWord_1489310) baseStart_1489310 baseEnd_1489310 := by
    simpa [prefixWord, tailWord_1489310, baseEnd_1489310] using wordTrace_append hprefix tailTrace_1489310
  have hstable : (prefixWord ++ tailWord_1489310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489310).length < 2 ^ (prefixWord ++ tailWord_1489310).sum := by decide
  have hdescent : baseEnd_1489310 < baseStart_1489310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489364 : List Nat := [2, 4, 1, 2, 2, 1, 1, 2, 7]
def baseStart_1489364 : Nat := 118140960795 + 1489364 * 2 ^ 59
def prefixEnd_1489364 : Nat := 4983230072969 + 3 ^ 40 * 1489364 * 2
def baseEnd_1489364 : Nat := 169946578111781353377899

theorem tailTrace_1489364 : CollatzResearch.WordTrace tailWord_1489364 prefixEnd_1489364 169946578111781353377899 := by
  unfold tailWord_1489364
  simp only [CollatzResearch.WordTrace]
  refine ⟨27160783888148032982713573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36214378517530710643618097 27160783888148032982713573)
  ·
    refine ⟨5092646979027756184258795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27160783888148032982713573 5092646979027756184258795)
    ·
      refine ⟨7638970468541634276388193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5092646979027756184258795 7638970468541634276388193)
      ·
        refine ⟨5729227851406225707291145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7638970468541634276388193 5729227851406225707291145)
        ·
          refine ⟨4296920888554669280468359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5729227851406225707291145 4296920888554669280468359)
          ·
            refine ⟨6445381332832003920702539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4296920888554669280468359 6445381332832003920702539)
            ·
              refine ⟨9668071999248005881053809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6445381332832003920702539 9668071999248005881053809)
              ·
                refine ⟨7251053999436004410790357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9668071999248005881053809 7251053999436004410790357)
                ·
                  refine ⟨169946578111781353377899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7251053999436004410790357 169946578111781353377899)
                  ·
                    rfl

theorem cell22_1489364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_1489364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1489364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1489364 prefixEnd_1489364 := by exact prefixLift 1489364
  have htrace : WordTrace (prefixWord ++ tailWord_1489364) baseStart_1489364 baseEnd_1489364 := by
    simpa [prefixWord, tailWord_1489364, baseEnd_1489364] using wordTrace_append hprefix tailTrace_1489364
  have hstable : (prefixWord ++ tailWord_1489364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489364).length < 2 ^ (prefixWord ++ tailWord_1489364).sum := by decide
  have hdescent : baseEnd_1489364 < baseStart_1489364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489443 : List Nat := [1, 1, 1, 4, 4, 1, 4, 2, 4]
def baseStart_1489443 : Nat := 118140960795 + 1489443 * 2 ^ 59
def prefixEnd_1489443 : Nat := 4983230072969 + 3 ^ 40 * 1489443 * 2
def baseEnd_1489443 : Nat := 169955592549938062469485

theorem tailTrace_1489443 : CollatzResearch.WordTrace tailWord_1489443 prefixEnd_1489443 169955592549938062469485 := by
  unfold tailWord_1489443
  simp only [CollatzResearch.WordTrace]
  refine ⟨54324449143009862457552983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36216299428673241638368655 54324449143009862457552983)
  ·
    refine ⟨81486673714514793686329475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54324449143009862457552983 81486673714514793686329475)
    ·
      refine ⟨122230010571772190529494213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81486673714514793686329475 122230010571772190529494213)
      ·
        refine ⟨22918126982207285724280165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122230010571772190529494213 22918126982207285724280165)
        ·
          refine ⟨4297148809163866073302531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22918126982207285724280165 4297148809163866073302531)
          ·
            refine ⟨6445723213745799109953797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4297148809163866073302531 6445723213745799109953797)
            ·
              refine ⟨1208573102577337333116337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6445723213745799109953797 1208573102577337333116337)
              ·
                refine ⟨906429826933002999837253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1208573102577337333116337 906429826933002999837253)
                ·
                  refine ⟨169955592549938062469485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 906429826933002999837253 169955592549938062469485)
                  ·
                    rfl

theorem cell22_1489443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 2, 4].length) (baseStart_1489443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1489443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1489443 prefixEnd_1489443 := by exact prefixLift 1489443
  have htrace : WordTrace (prefixWord ++ tailWord_1489443) baseStart_1489443 baseEnd_1489443 := by
    simpa [prefixWord, tailWord_1489443, baseEnd_1489443] using wordTrace_append hprefix tailTrace_1489443
  have hstable : (prefixWord ++ tailWord_1489443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489443).length < 2 ^ (prefixWord ++ tailWord_1489443).sum := by decide
  have hdescent : baseEnd_1489443 < baseStart_1489443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489473 : List Nat := [1, 2, 5, 1, 1, 4, 1, 1, 2, 4]
def baseStart_1489473 : Nat := 118140960795 + 1489473 * 2 ^ 59
def prefixEnd_1489473 : Nat := 4983230072969 + 3 ^ 40 * 1489473 * 2
def baseEnd_1489473 : Nat := 509877047262904109158363

theorem tailTrace_1489473 : CollatzResearch.WordTrace tailWord_1489473 prefixEnd_1489473 509877047262904109158363 := by
  unfold tailWord_1489473
  simp only [CollatzResearch.WordTrace]
  refine ⟨54325543332901177581145073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36217028888600785054096715 54325543332901177581145073)
  ·
    refine ⟨40744157499675883185858805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54325543332901177581145073 40744157499675883185858805)
    ·
      refine ⟨3819764765594614048674263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40744157499675883185858805 3819764765594614048674263)
      ·
        refine ⟨5729647148391921073011395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3819764765594614048674263 5729647148391921073011395)
        ·
          refine ⟨8594470722587881609517093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5729647148391921073011395 8594470722587881609517093)
          ·
            refine ⟨1611463260485227801784455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8594470722587881609517093 1611463260485227801784455)
            ·
              refine ⟨2417194890727841702676683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1611463260485227801784455 2417194890727841702676683)
              ·
                refine ⟨3625792336091762554015025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2417194890727841702676683 3625792336091762554015025)
                ·
                  refine ⟨2719344252068821915511269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3625792336091762554015025 2719344252068821915511269)
                  ·
                    refine ⟨509877047262904109158363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2719344252068821915511269 509877047262904109158363)
                    ·
                      rfl

theorem cell22_1489473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_1489473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1489473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1489473 prefixEnd_1489473 := by exact prefixLift 1489473
  have htrace : WordTrace (prefixWord ++ tailWord_1489473) baseStart_1489473 baseEnd_1489473 := by
    simpa [prefixWord, tailWord_1489473, baseEnd_1489473] using wordTrace_append hprefix tailTrace_1489473
  have hstable : (prefixWord ++ tailWord_1489473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489473).length < 2 ^ (prefixWord ++ tailWord_1489473).sum := by decide
  have hdescent : baseEnd_1489473 < baseStart_1489473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489610 : List Nat := [3, 1, 2, 1, 4, 2, 2, 2, 2, 3]
def baseStart_1489610 : Nat := 118140960795 + 1489610 * 2 ^ 59
def prefixEnd_1489610 : Nat := 4983230072969 + 3 ^ 40 * 1489610 * 2
def baseEnd_1489610 : Nat := 509923945162681418482943

theorem tailTrace_1489610 : CollatzResearch.WordTrace tailWord_1489610 prefixEnd_1489610 509923945162681418482943 := by
  unfold tailWord_1489610
  simp only [CollatzResearch.WordTrace]
  refine ⟨13582635033351212494720571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36220360088936566652588189 13582635033351212494720571)
  ·
    refine ⟨20373952550026818742080857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13582635033351212494720571 20373952550026818742080857)
    ·
      refine ⟨15280464412520114056560643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20373952550026818742080857 15280464412520114056560643)
      ·
        refine ⟨22920696618780171084840965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15280464412520114056560643 22920696618780171084840965)
        ·
          refine ⟨4297630616021282078407681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22920696618780171084840965 4297630616021282078407681)
          ·
            refine ⟨3223222962015961558805761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4297630616021282078407681 3223222962015961558805761)
            ·
              refine ⟨2417417221511971169104321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3223222962015961558805761 2417417221511971169104321)
              ·
                refine ⟨1813062916133978376828241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2417417221511971169104321 1813062916133978376828241)
                ·
                  refine ⟨1359797187100483782621181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1813062916133978376828241 1359797187100483782621181)
                  ·
                    refine ⟨509923945162681418482943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1359797187100483782621181 509923945162681418482943)
                    ·
                      rfl

theorem cell22_1489610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_1489610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1489610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1489610 prefixEnd_1489610 := by exact prefixLift 1489610
  have htrace : WordTrace (prefixWord ++ tailWord_1489610) baseStart_1489610 baseEnd_1489610 := by
    simpa [prefixWord, tailWord_1489610, baseEnd_1489610] using wordTrace_append hprefix tailTrace_1489610
  have hstable : (prefixWord ++ tailWord_1489610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489610).length < 2 ^ (prefixWord ++ tailWord_1489610).sum := by decide
  have hdescent : baseEnd_1489610 < baseStart_1489610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489612 : List Nat := [2, 2, 1, 5, 1, 3, 2, 2, 4]
def baseStart_1489612 : Nat := 118140960795 + 1489612 * 2 ^ 59
def prefixEnd_1489612 : Nat := 4983230072969 + 3 ^ 40 * 1489612 * 2
def baseEnd_1489612 : Nat := 169974876601184693310979

theorem tailTrace_1489612 : CollatzResearch.WordTrace tailWord_1489612 prefixEnd_1489612 169974876601184693310979 := by
  unfold tailWord_1489612
  simp only [CollatzResearch.WordTrace]
  refine ⟨27165306539698802160227545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36220408719598402880303393 27165306539698802160227545)
  ·
    refine ⟨20373979904774101620170659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27165306539698802160227545 20373979904774101620170659)
    ·
      refine ⟨30560969857161152430255989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20373979904774101620170659 30560969857161152430255989)
      ·
        refine ⟨2865090924108858040336499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30560969857161152430255989 2865090924108858040336499)
        ·
          refine ⟨4297636386163287060504749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2865090924108858040336499 4297636386163287060504749)
          ·
            refine ⟨1611613644811232647689281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4297636386163287060504749 1611613644811232647689281)
            ·
              refine ⟨1208710233608424485766961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1611613644811232647689281 1208710233608424485766961)
              ·
                refine ⟨906532675206318364325221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1208710233608424485766961 906532675206318364325221)
                ·
                  refine ⟨169974876601184693310979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 906532675206318364325221 169974876601184693310979)
                  ·
                    rfl

theorem cell22_1489612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 2, 4].length) (baseStart_1489612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1489612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1489612 prefixEnd_1489612 := by exact prefixLift 1489612
  have htrace : WordTrace (prefixWord ++ tailWord_1489612) baseStart_1489612 baseEnd_1489612 := by
    simpa [prefixWord, tailWord_1489612, baseEnd_1489612] using wordTrace_append hprefix tailTrace_1489612
  have hstable : (prefixWord ++ tailWord_1489612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489612).length < 2 ^ (prefixWord ++ tailWord_1489612).sum := by decide
  have hdescent : baseEnd_1489612 < baseStart_1489612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489681 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 5, 4]
def baseStart_1489681 : Nat := 118140960795 + 1489681 * 2 ^ 59
def prefixEnd_1489681 : Nat := 4983230072969 + 3 ^ 40 * 1489681 * 2
def baseEnd_1489681 : Nat := 509948249913660899957725

theorem tailTrace_1489681 : CollatzResearch.WordTrace tailWord_1489681 prefixEnd_1489681 509948249913660899957725 := by
  unfold tailWord_1489681
  simp only [CollatzResearch.WordTrace]
  refine ⟨54333129716147629104716897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36222086477431752736477931 54333129716147629104716897)
  ·
    refine ⟨40749847287110721828537673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54333129716147629104716897 40749847287110721828537673)
    ·
      refine ⟨30562385465333041371403255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40749847287110721828537673 30562385465333041371403255)
      ·
        refine ⟨45843578197999562057104883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30562385465333041371403255 45843578197999562057104883)
        ·
          refine ⟨68765367296999343085657325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45843578197999562057104883 68765367296999343085657325)
          ·
            refine ⟨25787012736374753657121497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68765367296999343085657325 25787012736374753657121497)
            ·
              refine ⟨19340259552281065242841123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25787012736374753657121497 19340259552281065242841123)
              ·
                refine ⟨29010389328421597864261685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19340259552281065242841123 29010389328421597864261685)
                ·
                  refine ⟨2719723999539524799774533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29010389328421597864261685 2719723999539524799774533)
                  ·
                    refine ⟨509948249913660899957725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2719723999539524799774533 509948249913660899957725)
                    ·
                      rfl

theorem cell22_1489681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_1489681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1489681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1489681 prefixEnd_1489681 := by exact prefixLift 1489681
  have htrace : WordTrace (prefixWord ++ tailWord_1489681) baseStart_1489681 baseEnd_1489681 := by
    simpa [prefixWord, tailWord_1489681, baseEnd_1489681] using wordTrace_append hprefix tailTrace_1489681
  have hstable : (prefixWord ++ tailWord_1489681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489681).length < 2 ^ (prefixWord ++ tailWord_1489681).sum := by decide
  have hdescent : baseEnd_1489681 < baseStart_1489681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489706 : List Nat := [3, 1, 4, 3, 1, 2, 1, 3, 1, 3]
def baseStart_1489706 : Nat := 118140960795 + 1489706 * 2 ^ 59
def prefixEnd_1489706 : Nat := 4983230072969 + 3 ^ 40 * 1489706 * 2
def baseEnd_1489706 : Nat := 509956807924569168082649

theorem tailTrace_1489706 : CollatzResearch.WordTrace tailWord_1489706 prefixEnd_1489706 509956807924569168082649 := by
  unfold tailWord_1489706
  simp only [CollatzResearch.WordTrace]
  refine ⟨13583510385264264593594243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36222694360704705582917981 13583510385264264593594243)
  ·
    refine ⟨20375265577896396890391365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13583510385264264593594243 20375265577896396890391365)
    ·
      refine ⟨3820362295855574416948381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20375265577896396890391365 3820362295855574416948381)
      ·
        refine ⟨1432635860945840406355643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3820362295855574416948381 1432635860945840406355643)
        ·
          refine ⟨2148953791418760609533465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1432635860945840406355643 2148953791418760609533465)
          ·
            refine ⟨1611715343564070457150099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2148953791418760609533465 1611715343564070457150099)
            ·
              refine ⟨2417573015346105685725149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1611715343564070457150099 2417573015346105685725149)
              ·
                refine ⟨906589880754789632146931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2417573015346105685725149 906589880754789632146931)
                ·
                  refine ⟨1359884821132184448220397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 906589880754789632146931 1359884821132184448220397)
                  ·
                    refine ⟨509956807924569168082649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1359884821132184448220397 509956807924569168082649)
                    ·
                      rfl

theorem cell22_1489706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_1489706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1489706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1489706 prefixEnd_1489706 := by exact prefixLift 1489706
  have htrace : WordTrace (prefixWord ++ tailWord_1489706) baseStart_1489706 baseEnd_1489706 := by
    simpa [prefixWord, tailWord_1489706, baseEnd_1489706] using wordTrace_append hprefix tailTrace_1489706
  have hstable : (prefixWord ++ tailWord_1489706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489706).length < 2 ^ (prefixWord ++ tailWord_1489706).sum := by decide
  have hdescent : baseEnd_1489706 < baseStart_1489706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489803 : List Nat := [1, 1, 1, 1, 4, 2, 4, 3, 5]
def baseStart_1489803 : Nat := 118140960795 + 1489803 * 2 ^ 59
def prefixEnd_1489803 : Nat := 4983230072969 + 3 ^ 40 * 1489803 * 2
def baseEnd_1489803 : Nat := 169996671002297749469117

theorem tailTrace_1489803 : CollatzResearch.WordTrace tailWord_1489803 prefixEnd_1489803 169996671002297749469117 := by
  unfold tailWord_1489803
  simp only [CollatzResearch.WordTrace]
  refine ⟨54337579421705643940658063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36225052947803762627105375 54337579421705643940658063)
  ·
    refine ⟨81506369132558465910987095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54337579421705643940658063 81506369132558465910987095)
    ·
      refine ⟨122259553698837698866480643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81506369132558465910987095 122259553698837698866480643)
      ·
        refine ⟨183389330548256548299720965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122259553698837698866480643 183389330548256548299720965)
        ·
          refine ⟨34385499477798102806197681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 183389330548256548299720965 34385499477798102806197681)
          ·
            refine ⟨25789124608348577104648261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34385499477798102806197681 25789124608348577104648261)
            ·
              refine ⟨4835460864065358207121549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25789124608348577104648261 4835460864065358207121549)
              ·
                refine ⟨1813297824024509327670581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4835460864065358207121549 1813297824024509327670581)
                ·
                  refine ⟨169996671002297749469117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1813297824024509327670581 169996671002297749469117)
                  ·
                    rfl

theorem cell22_1489803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 5].length) (baseStart_1489803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1489803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1489803 prefixEnd_1489803 := by exact prefixLift 1489803
  have htrace : WordTrace (prefixWord ++ tailWord_1489803) baseStart_1489803 baseEnd_1489803 := by
    simpa [prefixWord, tailWord_1489803, baseEnd_1489803] using wordTrace_append hprefix tailTrace_1489803
  have hstable : (prefixWord ++ tailWord_1489803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489803).length < 2 ^ (prefixWord ++ tailWord_1489803).sum := by decide
  have hdescent : baseEnd_1489803 < baseStart_1489803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489837 : List Nat := [1, 5, 2, 3, 1, 1, 1, 1, 7]
def baseStart_1489837 : Nat := 118140960795 + 1489837 * 2 ^ 59
def prefixEnd_1489837 : Nat := 4983230072969 + 3 ^ 40 * 1489837 * 2
def baseEnd_1489837 : Nat := 170000550633909497685749

theorem tailTrace_1489837 : CollatzResearch.WordTrace tailWord_1489837 prefixEnd_1489837 170000550633909497685749 := by
  unfold tailWord_1489837
  simp only [CollatzResearch.WordTrace]
  refine ⟨54338819503582467747395765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36225879669054978498263843 54338819503582467747395765)
  ·
    refine ⟨5094264328460856351318353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54338819503582467747395765 5094264328460856351318353)
    ·
      refine ⟨3820698246345642263488765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5094264328460856351318353 3820698246345642263488765)
      ·
        refine ⟨1432761842379615848808287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3820698246345642263488765 1432761842379615848808287)
        ·
          refine ⟨2149142763569423773212431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1432761842379615848808287 2149142763569423773212431)
          ·
            refine ⟨3223714145354135659818647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2149142763569423773212431 3223714145354135659818647)
            ·
              refine ⟨4835571218031203489727971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3223714145354135659818647 4835571218031203489727971)
              ·
                refine ⟨7253356827046805234591957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4835571218031203489727971 7253356827046805234591957)
                ·
                  refine ⟨170000550633909497685749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7253356827046805234591957 170000550633909497685749)
                  ·
                    rfl

theorem cell22_1489837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_1489837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1489837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1489837 prefixEnd_1489837 := by exact prefixLift 1489837
  have htrace : WordTrace (prefixWord ++ tailWord_1489837) baseStart_1489837 baseEnd_1489837 := by
    simpa [prefixWord, tailWord_1489837, baseEnd_1489837] using wordTrace_append hprefix tailTrace_1489837
  have hstable : (prefixWord ++ tailWord_1489837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489837).length < 2 ^ (prefixWord ++ tailWord_1489837).sum := by decide
  have hdescent : baseEnd_1489837 < baseStart_1489837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489848 : List Nat := [2, 1, 2, 1, 2, 4, 1, 3, 6]
def baseStart_1489848 : Nat := 118140960795 + 1489848 * 2 ^ 59
def prefixEnd_1489848 : Nat := 4983230072969 + 3 ^ 40 * 1489848 * 2
def baseEnd_1489848 : Nat := 170001805808842710344071

theorem tailTrace_1489848 : CollatzResearch.WordTrace tailWord_1489848 prefixEnd_1489848 170001805808842710344071 := by
  unfold tailWord_1489848
  simp only [CollatzResearch.WordTrace]
  refine ⟨27169610353271308313023099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36226147137695077750697465 27169610353271308313023099)
  ·
    refine ⟨40754415529906962469534649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27169610353271308313023099 40754415529906962469534649)
    ·
      refine ⟨30565811647430221852150987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40754415529906962469534649 30565811647430221852150987)
      ·
        refine ⟨45848717471145332778226481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30565811647430221852150987 45848717471145332778226481)
        ·
          refine ⟨34386538103358999583669861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45848717471145332778226481 34386538103358999583669861)
          ·
            refine ⟨6447475894379812421938099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34386538103358999583669861 6447475894379812421938099)
            ·
              refine ⟨9671213841569718632907149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6447475894379812421938099 9671213841569718632907149)
              ·
                refine ⟨3626705190588644487340181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9671213841569718632907149 3626705190588644487340181)
                ·
                  refine ⟨170001805808842710344071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3626705190588644487340181 170001805808842710344071)
                  ·
                    rfl

theorem cell22_1489848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 6].length) (baseStart_1489848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1489848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1489848 prefixEnd_1489848 := by exact prefixLift 1489848
  have htrace : WordTrace (prefixWord ++ tailWord_1489848) baseStart_1489848 baseEnd_1489848 := by
    simpa [prefixWord, tailWord_1489848, baseEnd_1489848] using wordTrace_append hprefix tailTrace_1489848
  have hstable : (prefixWord ++ tailWord_1489848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489848).length < 2 ^ (prefixWord ++ tailWord_1489848).sum := by decide
  have hdescent : baseEnd_1489848 < baseStart_1489848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489880 : List Nat := [2, 1, 2, 2, 2, 3, 1, 2, 4, 3]
def baseStart_1489880 : Nat := 118140960795 + 1489880 * 2 ^ 59
def prefixEnd_1489880 : Nat := 4983230072969 + 3 ^ 40 * 1489880 * 2
def baseEnd_1489880 : Nat := 510016371680490714232115

theorem tailTrace_1489880 : CollatzResearch.WordTrace tailWord_1489880 prefixEnd_1489880 510016371680490714232115 := by
  unfold tailWord_1489880
  simp only [CollatzResearch.WordTrace]
  refine ⟨27170193921213343045605547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36226925228284457394140729 27170193921213343045605547)
  ·
    refine ⟨40755290881820014568408321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27170193921213343045605547 40755290881820014568408321)
    ·
      refine ⟨30566468161365010926306241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40755290881820014568408321 30566468161365010926306241)
      ·
        refine ⟨22924851121023758194729681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30566468161365010926306241 22924851121023758194729681)
        ·
          refine ⟨17193638340767818646047261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22924851121023758194729681 17193638340767818646047261)
          ·
            refine ⟨6447614377787931992267723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17193638340767818646047261 6447614377787931992267723)
            ·
              refine ⟨9671421566681897988401585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6447614377787931992267723 9671421566681897988401585)
              ·
                refine ⟨7253566175011423491301189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9671421566681897988401585 7253566175011423491301189)
                ·
                  refine ⟨1360043657814641904618973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7253566175011423491301189 1360043657814641904618973)
                  ·
                    refine ⟨510016371680490714232115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1360043657814641904618973 510016371680490714232115)
                    ·
                      rfl

theorem cell22_1489880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 4, 3].length) (baseStart_1489880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1489880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1489880 prefixEnd_1489880 := by exact prefixLift 1489880
  have htrace : WordTrace (prefixWord ++ tailWord_1489880) baseStart_1489880 baseEnd_1489880 := by
    simpa [prefixWord, tailWord_1489880, baseEnd_1489880] using wordTrace_append hprefix tailTrace_1489880
  have hstable : (prefixWord ++ tailWord_1489880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489880).length < 2 ^ (prefixWord ++ tailWord_1489880).sum := by decide
  have hdescent : baseEnd_1489880 < baseStart_1489880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489882 : List Nat := [3, 1, 1, 2, 4, 1, 3, 3, 4]
def baseStart_1489882 : Nat := 118140960795 + 1489882 * 2 ^ 59
def prefixEnd_1489882 : Nat := 4983230072969 + 3 ^ 40 * 1489882 * 2
def baseEnd_1489882 : Nat := 170005685440454458560703

theorem tailTrace_1489882 : CollatzResearch.WordTrace tailWord_1489882 prefixEnd_1489882 170005685440454458560703 := by
  unfold tailWord_1489882
  simp only [CollatzResearch.WordTrace]
  refine ⟨13585115197104860108195975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36226973858946293621855933 13585115197104860108195975)
  ·
    refine ⟨20377672795657290162293963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13585115197104860108195975 20377672795657290162293963)
    ·
      refine ⟨30566509193485935243440945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20377672795657290162293963 30566509193485935243440945)
      ·
        refine ⟨22924881895114451432580709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30566509193485935243440945 22924881895114451432580709)
        ·
          refine ⟨4298415355333959643608883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22924881895114451432580709 4298415355333959643608883)
          ·
            refine ⟨6447623033000939465413325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4298415355333959643608883 6447623033000939465413325)
            ·
              refine ⟨2417858637375352299529997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6447623033000939465413325 2417858637375352299529997)
              ·
                refine ⟨906696989015757112323749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2417858637375352299529997 906696989015757112323749)
                ·
                  refine ⟨170005685440454458560703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 906696989015757112323749 170005685440454458560703)
                  ·
                    rfl

theorem cell22_1489882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 3, 4].length) (baseStart_1489882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1489882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1489882 prefixEnd_1489882 := by exact prefixLift 1489882
  have htrace : WordTrace (prefixWord ++ tailWord_1489882) baseStart_1489882 baseEnd_1489882 := by
    simpa [prefixWord, tailWord_1489882, baseEnd_1489882] using wordTrace_append hprefix tailTrace_1489882
  have hstable : (prefixWord ++ tailWord_1489882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489882).length < 2 ^ (prefixWord ++ tailWord_1489882).sum := by decide
  have hdescent : baseEnd_1489882 < baseStart_1489882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489895 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 4, 4]
def baseStart_1489895 : Nat := 118140960795 + 1489895 * 2 ^ 59
def prefixEnd_1489895 : Nat := 4983230072969 + 3 ^ 40 * 1489895 * 2
def baseEnd_1489895 : Nat := 510021506487035675107069

theorem tailTrace_1489895 : CollatzResearch.WordTrace tailWord_1489895 prefixEnd_1489895 510021506487035675107069 := by
  unfold tailWord_1489895
  simp only [CollatzResearch.WordTrace]
  refine ⟨54340934937372343653007139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36227289958248229102004759 54340934937372343653007139)
  ·
    refine ⟨81511402406058515479510709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54340934937372343653007139 81511402406058515479510709)
    ·
      refine ⟨7641693975567985826204129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81511402406058515479510709 7641693975567985826204129)
      ·
        refine ⟨5731270481675989369653097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7641693975567985826204129 5731270481675989369653097)
        ·
          refine ⟨4298452861256992027239823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5731270481675989369653097 4298452861256992027239823)
          ·
            refine ⟨6447679291885488040859735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4298452861256992027239823 6447679291885488040859735)
            ·
              refine ⟨9671518937828232061289603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6447679291885488040859735 9671518937828232061289603)
              ·
                refine ⟨14507278406742348091934405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9671518937828232061289603 14507278406742348091934405)
                ·
                  refine ⟨2720114701264190267237701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14507278406742348091934405 2720114701264190267237701)
                  ·
                    refine ⟨510021506487035675107069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2720114701264190267237701 510021506487035675107069)
                    ·
                      rfl

theorem cell22_1489895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_1489895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1489895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1489895 prefixEnd_1489895 := by exact prefixLift 1489895
  have htrace : WordTrace (prefixWord ++ tailWord_1489895) baseStart_1489895 baseEnd_1489895 := by
    simpa [prefixWord, tailWord_1489895, baseEnd_1489895] using wordTrace_append hprefix tailTrace_1489895
  have hstable : (prefixWord ++ tailWord_1489895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489895).length < 2 ^ (prefixWord ++ tailWord_1489895).sum := by decide
  have hdescent : baseEnd_1489895 < baseStart_1489895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489910 : List Nat := [5, 1, 1, 1, 3, 1, 1, 9]
def baseStart_1489910 : Nat := 118140960795 + 1489910 * 2 ^ 59
def prefixEnd_1489910 : Nat := 4983230072969 + 3 ^ 40 * 1489910 * 2
def baseEnd_1489910 : Nat := 56669626810397848442447

theorem tailTrace_1489910 : CollatzResearch.WordTrace tailWord_1489910 prefixEnd_1489910 56669626810397848442447 := by
  unfold tailWord_1489910
  simp only [CollatzResearch.WordTrace]
  refine ⟨3396342627019875075925199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36227654688212000809868789 3396342627019875075925199)
  ·
    refine ⟨5094513940529812613887799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3396342627019875075925199 5094513940529812613887799)
    ·
      refine ⟨7641770910794718920831699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5094513940529812613887799 7641770910794718920831699)
      ·
        refine ⟨11462656366192078381247549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7641770910794718920831699 11462656366192078381247549)
        ·
          refine ⟨4298496137322029392967831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11462656366192078381247549 4298496137322029392967831)
          ·
            refine ⟨6447744205983044089451747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4298496137322029392967831 6447744205983044089451747)
            ·
              refine ⟨9671616308974566134177621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6447744205983044089451747 9671616308974566134177621)
              ·
                refine ⟨56669626810397848442447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9671616308974566134177621 56669626810397848442447)
                ·
                  rfl

theorem cell22_1489910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_1489910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1489910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1489910 prefixEnd_1489910 := by exact prefixLift 1489910
  have htrace : WordTrace (prefixWord ++ tailWord_1489910) baseStart_1489910 baseEnd_1489910 := by
    simpa [prefixWord, tailWord_1489910, baseEnd_1489910] using wordTrace_append hprefix tailTrace_1489910
  have hstable : (prefixWord ++ tailWord_1489910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489910).length < 2 ^ (prefixWord ++ tailWord_1489910).sum := by decide
  have hdescent : baseEnd_1489910 < baseStart_1489910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489925 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 5, 3]
def baseStart_1489925 : Nat := 118140960795 + 1489925 * 2 ^ 59
def prefixEnd_1489925 : Nat := 4983230072969 + 3 ^ 40 * 1489925 * 2
def baseEnd_1489925 : Nat := 510031776100125596856977

theorem tailTrace_1489925 : CollatzResearch.WordTrace tailWord_1489925 prefixEnd_1489925 510031776100125596856977 := by
  unfold tailWord_1489925
  simp only [CollatzResearch.WordTrace]
  refine ⟨54342029127263658776599229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36228019418175772517732819 54342029127263658776599229)
  ·
    refine ⟨20378260922723872041224711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54342029127263658776599229 20378260922723872041224711)
    ·
      refine ⟨30567391384085808061837067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20378260922723872041224711 30567391384085808061837067)
      ·
        refine ⟨45851087076128712092755601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30567391384085808061837067 45851087076128712092755601)
        ·
          refine ⟨34388315307096534069566701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45851087076128712092755601 34388315307096534069566701)
          ·
            refine ⟨12895618240161200276087513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34388315307096534069566701 12895618240161200276087513)
            ·
              refine ⟨9671713680120900207065635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12895618240161200276087513 9671713680120900207065635)
              ·
                refine ⟨14507570520181350310598453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9671713680120900207065635 14507570520181350310598453)
                ·
                  refine ⟨1360084736267001591618605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14507570520181350310598453 1360084736267001591618605)
                  ·
                    refine ⟨510031776100125596856977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1360084736267001591618605 510031776100125596856977)
                    ·
                      rfl

theorem cell22_1489925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 5, 3].length) (baseStart_1489925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1489925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1489925 prefixEnd_1489925 := by exact prefixLift 1489925
  have htrace : WordTrace (prefixWord ++ tailWord_1489925) baseStart_1489925 baseEnd_1489925 := by
    simpa [prefixWord, tailWord_1489925, baseEnd_1489925] using wordTrace_append hprefix tailTrace_1489925
  have hstable : (prefixWord ++ tailWord_1489925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489925).length < 2 ^ (prefixWord ++ tailWord_1489925).sum := by decide
  have hdescent : baseEnd_1489925 < baseStart_1489925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489955 : List Nat := [1, 1, 1, 4, 3, 2, 1, 4, 5]
def baseStart_1489955 : Nat := 118140960795 + 1489955 * 2 ^ 59
def prefixEnd_1489955 : Nat := 4983230072969 + 3 ^ 40 * 1489955 * 2
def baseEnd_1489955 : Nat := 170014015237738506202295

theorem tailTrace_1489955 : CollatzResearch.WordTrace tailWord_1489955 prefixEnd_1489955 170014015237738506202295 := by
  unfold tailWord_1489955
  simp only [CollatzResearch.WordTrace]
  refine ⟨54343123317154973900191319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36228748878103315933460879 54343123317154973900191319)
  ·
    refine ⟨81514684975732460850286979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54343123317154973900191319 81514684975732460850286979)
    ·
      refine ⟨122272027463598691275430469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81514684975732460850286979 122272027463598691275430469)
      ·
        refine ⟨22926005149424754614143213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122272027463598691275430469 22926005149424754614143213)
        ·
          refine ⟨8597251931034282980303705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22926005149424754614143213 8597251931034282980303705)
          ·
            refine ⟨6447938948275712235227779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8597251931034282980303705 6447938948275712235227779)
            ·
              refine ⟨9671908422413568352841669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6447938948275712235227779 9671908422413568352841669)
              ·
                refine ⟨1813482829202544066157813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9671908422413568352841669 1813482829202544066157813)
                ·
                  refine ⟨170014015237738506202295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1813482829202544066157813 170014015237738506202295)
                  ·
                    rfl

theorem cell22_1489955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 4, 5].length) (baseStart_1489955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1489955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1489955 prefixEnd_1489955 := by exact prefixLift 1489955
  have htrace : WordTrace (prefixWord ++ tailWord_1489955) baseStart_1489955 baseEnd_1489955 := by
    simpa [prefixWord, tailWord_1489955, baseEnd_1489955] using wordTrace_append hprefix tailTrace_1489955
  have hstable : (prefixWord ++ tailWord_1489955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489955).length < 2 ^ (prefixWord ++ tailWord_1489955).sum := by decide
  have hdescent : baseEnd_1489955 < baseStart_1489955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1489970 : List Nat := [3, 2, 1, 1, 2, 2, 3, 1, 2, 5]
def baseStart_1489970 : Nat := 118140960795 + 1489970 * 2 ^ 59
def prefixEnd_1489970 : Nat := 4983230072969 + 3 ^ 40 * 1489970 * 2
def baseEnd_1489970 : Nat := 510047180519760479481839

theorem tailTrace_1489970 : CollatzResearch.WordTrace tailWord_1489970 prefixEnd_1489970 510047180519760479481839 := by
  unfold tailWord_1489970
  simp only [CollatzResearch.WordTrace]
  refine ⟨13585917603025157865496841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36229113608067087641324909 13585917603025157865496841)
  ·
    refine ⟨10189438202268868399122631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13585917603025157865496841 10189438202268868399122631)
    ·
      refine ⟨15284157303403302598683947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10189438202268868399122631 15284157303403302598683947)
      ·
        refine ⟨22926235955104953898025921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15284157303403302598683947 22926235955104953898025921)
        ·
          refine ⟨17194676966328715423519441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22926235955104953898025921 17194676966328715423519441)
          ·
            refine ⟨12896007724746536567639581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17194676966328715423519441 12896007724746536567639581)
            ·
              refine ⟨4836002896779951212864843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12896007724746536567639581 4836002896779951212864843)
              ·
                refine ⟨7254004345169926819297265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4836002896779951212864843 7254004345169926819297265)
                ·
                  refine ⟨5440503258877445114472949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7254004345169926819297265 5440503258877445114472949)
                  ·
                    refine ⟨510047180519760479481839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5440503258877445114472949 510047180519760479481839)
                    ·
                      rfl

theorem cell22_1489970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_1489970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1489970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1489970 prefixEnd_1489970 := by exact prefixLift 1489970
  have htrace : WordTrace (prefixWord ++ tailWord_1489970) baseStart_1489970 baseEnd_1489970 := by
    simpa [prefixWord, tailWord_1489970, baseEnd_1489970] using wordTrace_append hprefix tailTrace_1489970
  have hstable : (prefixWord ++ tailWord_1489970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1489970).length < 2 ^ (prefixWord ++ tailWord_1489970).sum := by decide
  have hdescent : baseEnd_1489970 < baseStart_1489970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1489970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490017 : List Nat := [1, 2, 3, 1, 1, 2, 4, 4, 4]
def baseStart_1490017 : Nat := 118140960795 + 1490017 * 2 ^ 59
def prefixEnd_1490017 : Nat := 4983230072969 + 3 ^ 40 * 1490017 * 2
def baseEnd_1490017 : Nat := 170021089860089341185565

theorem tailTrace_1490017 : CollatzResearch.WordTrace tailWord_1490017 prefixEnd_1490017 170021089860089341185565 := by
  unfold tailWord_1490017
  simp only [CollatzResearch.WordTrace]
  refine ⟨54345384642930358488948305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36230256428620238992632203 54345384642930358488948305)
  ·
    refine ⟨40759038482197768866711229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54345384642930358488948305 40759038482197768866711229)
    ·
      refine ⟨15284639430824163325016711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40759038482197768866711229 15284639430824163325016711)
      ·
        refine ⟨22926959146236244987525067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15284639430824163325016711 22926959146236244987525067)
        ·
          refine ⟨34390438719354367481287601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22926959146236244987525067 34390438719354367481287601)
          ·
            refine ⟨25792829039515775610965701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34390438719354367481287601 25792829039515775610965701)
            ·
              refine ⟨4836155444909207927056069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25792829039515775610965701 4836155444909207927056069)
              ·
                refine ⟨906779145920476486323013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4836155444909207927056069 906779145920476486323013)
                ·
                  refine ⟨170021089860089341185565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 906779145920476486323013 170021089860089341185565)
                  ·
                    rfl

theorem cell22_1490017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 4, 4].length) (baseStart_1490017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1490017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1490017 prefixEnd_1490017 := by exact prefixLift 1490017
  have htrace : WordTrace (prefixWord ++ tailWord_1490017) baseStart_1490017 baseEnd_1490017 := by
    simpa [prefixWord, tailWord_1490017, baseEnd_1490017] using wordTrace_append hprefix tailTrace_1490017
  have hstable : (prefixWord ++ tailWord_1490017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490017).length < 2 ^ (prefixWord ++ tailWord_1490017).sum := by decide
  have hdescent : baseEnd_1490017 < baseStart_1490017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490045 : List Nat := [1, 4, 1, 1, 3, 1, 3, 8]
def baseStart_1490045 : Nat := 118140960795 + 1490045 * 2 ^ 59
def prefixEnd_1490045 : Nat := 4983230072969 + 3 ^ 40 * 1490045 * 2
def baseEnd_1490045 : Nat := 56674761616942809317401

theorem tailTrace_1490045 : CollatzResearch.WordTrace tailWord_1490045 prefixEnd_1490045 56674761616942809317401 := by
  unfold tailWord_1490045
  simp only [CollatzResearch.WordTrace]
  refine ⟨54346405886828919270967589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36230937257885946180645059 54346405886828919270967589)
  ·
    refine ⟨10189951103780422363306423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54346405886828919270967589 10189951103780422363306423)
    ·
      refine ⟨15284926655670633544959635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10189951103780422363306423 15284926655670633544959635)
      ·
        refine ⟨22927389983505950317439453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15284926655670633544959635 22927389983505950317439453)
        ·
          refine ⟨8597771243814731369039795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22927389983505950317439453 8597771243814731369039795)
          ·
            refine ⟨12896656865722097053559693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8597771243814731369039795 12896656865722097053559693)
            ·
              refine ⟨4836246324645786395084885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12896656865722097053559693 4836246324645786395084885)
              ·
                refine ⟨56674761616942809317401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4836246324645786395084885 56674761616942809317401)
                ·
                  rfl

theorem cell22_1490045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 8].length) (baseStart_1490045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1490045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1490045 prefixEnd_1490045 := by exact prefixLift 1490045
  have htrace : WordTrace (prefixWord ++ tailWord_1490045) baseStart_1490045 baseEnd_1490045 := by
    simpa [prefixWord, tailWord_1490045, baseEnd_1490045] using wordTrace_append hprefix tailTrace_1490045
  have hstable : (prefixWord ++ tailWord_1490045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490045).length < 2 ^ (prefixWord ++ tailWord_1490045).sum := by decide
  have hdescent : baseEnd_1490045 < baseStart_1490045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490062 : List Nat := [4, 1, 1, 3, 2, 3, 8]
def baseStart_1490062 : Nat := 118140960795 + 1490062 * 2 ^ 59
def prefixEnd_1490062 : Nat := 4983230072969 + 3 ^ 40 * 1490062 * 2
def baseEnd_1490062 : Nat := 18891802740737144673391

theorem tailTrace_1490062 : CollatzResearch.WordTrace tailWord_1490062 prefixEnd_1490062 18891802740737144673391 := by
  unfold tailWord_1490062
  simp only [CollatzResearch.WordTrace]
  refine ⟨6793378240970916396792055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36231350618511554116224293 6793378240970916396792055)
  ·
    refine ⟨10190067361456374595188083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6793378240970916396792055 10190067361456374595188083)
    ·
      refine ⟨15285101042184561892782125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10190067361456374595188083 15285101042184561892782125)
      ·
        refine ⟨5731912890819210709793297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15285101042184561892782125 5731912890819210709793297)
        ·
          refine ⟨4298934668114408032344973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5731912890819210709793297 4298934668114408032344973)
          ·
            refine ⟨1612100500542903012129365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4298934668114408032344973 1612100500542903012129365)
            ·
              refine ⟨18891802740737144673391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1612100500542903012129365 18891802740737144673391)
              ·
                rfl

theorem cell22_1490062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 8].length) (baseStart_1490062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1490062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1490062 prefixEnd_1490062 := by exact prefixLift 1490062
  have htrace : WordTrace (prefixWord ++ tailWord_1490062) baseStart_1490062 baseEnd_1490062 := by
    simpa [prefixWord, tailWord_1490062, baseEnd_1490062] using wordTrace_append hprefix tailTrace_1490062
  have hstable : (prefixWord ++ tailWord_1490062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490062).length < 2 ^ (prefixWord ++ tailWord_1490062).sum := by decide
  have hdescent : baseEnd_1490062 < baseStart_1490062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490152 : List Nat := [2, 1, 4, 1, 2, 1, 3, 2, 6]
def baseStart_1490152 : Nat := 118140960795 + 1490152 * 2 ^ 59
def prefixEnd_1490152 : Nat := 4983230072969 + 3 ^ 40 * 1490152 * 2
def baseEnd_1490152 : Nat := 170036494279724223810427

theorem tailTrace_1490152 : CollatzResearch.WordTrace tailWord_1490152 prefixEnd_1490152 170036494279724223810427 := by
  unfold tailWord_1490152
  simp only [CollatzResearch.WordTrace]
  refine ⟨27175154248720638272556355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36233538998294184363408473 27175154248720638272556355)
  ·
    refine ⟨40762731373080957408834533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27175154248720638272556355 40762731373080957408834533)
    ·
      refine ⟨7643012132452679514156475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40762731373080957408834533 7643012132452679514156475)
      ·
        refine ⟨11464518198679019271234713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7643012132452679514156475 11464518198679019271234713)
        ·
          refine ⟨8598388649009264453426035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11464518198679019271234713 8598388649009264453426035)
          ·
            refine ⟨12897582973513896680139053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8598388649009264453426035 12897582973513896680139053)
            ·
              refine ⟨4836593615067711255052145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12897582973513896680139053 4836593615067711255052145)
              ·
                refine ⟨3627445211300783441289109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4836593615067711255052145 3627445211300783441289109)
                ·
                  refine ⟨170036494279724223810427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3627445211300783441289109 170036494279724223810427)
                  ·
                    rfl

theorem cell22_1490152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 6].length) (baseStart_1490152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1490152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1490152 prefixEnd_1490152 := by exact prefixLift 1490152
  have htrace : WordTrace (prefixWord ++ tailWord_1490152) baseStart_1490152 baseEnd_1490152 := by
    simpa [prefixWord, tailWord_1490152, baseEnd_1490152] using wordTrace_append hprefix tailTrace_1490152
  have hstable : (prefixWord ++ tailWord_1490152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490152).length < 2 ^ (prefixWord ++ tailWord_1490152).sum := by decide
  have hdescent : baseEnd_1490152 < baseStart_1490152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490167 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 6, 3]
def baseStart_1490167 : Nat := 118140960795 + 1490167 * 2 ^ 59
def prefixEnd_1490167 : Nat := 4983230072969 + 3 ^ 40 * 1490167 * 2
def baseEnd_1490167 : Nat := 510114617645717632306235

theorem tailTrace_1490167 : CollatzResearch.WordTrace tailWord_1490167 prefixEnd_1490167 510114617645717632306235 := by
  unfold tailWord_1490167
  simp only [CollatzResearch.WordTrace]
  refine ⟨54350855592386934106908755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36233903728257956071272503 54350855592386934106908755)
  ·
    refine ⟨81526283388580401160363133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54350855592386934106908755 81526283388580401160363133)
    ·
      refine ⟨30572356270717650435136175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81526283388580401160363133 30572356270717650435136175)
      ·
        refine ⟨45858534406076475652704263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30572356270717650435136175 45858534406076475652704263)
        ·
          refine ⟨68787801609114713479056395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45858534406076475652704263 68787801609114713479056395)
          ·
            refine ⟨103181702413672070218584593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68787801609114713479056395 103181702413672070218584593)
            ·
              refine ⟨77386276810254052663938445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103181702413672070218584593 77386276810254052663938445)
              ·
                refine ⟨29019853803845269748976917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77386276810254052663938445 29019853803845269748976917)
                ·
                  refine ⟨1360305647055247019483293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29019853803845269748976917 1360305647055247019483293)
                  ·
                    refine ⟨510114617645717632306235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1360305647055247019483293 510114617645717632306235)
                    ·
                      rfl

theorem cell22_1490167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 6, 3].length) (baseStart_1490167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1490167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1490167 prefixEnd_1490167 := by exact prefixLift 1490167
  have htrace : WordTrace (prefixWord ++ tailWord_1490167) baseStart_1490167 baseEnd_1490167 := by
    simpa [prefixWord, tailWord_1490167, baseEnd_1490167] using wordTrace_append hprefix tailTrace_1490167
  have hstable : (prefixWord ++ tailWord_1490167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490167).length < 2 ^ (prefixWord ++ tailWord_1490167).sum := by decide
  have hdescent : baseEnd_1490167 < baseStart_1490167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490169 : List Nat := [1, 2, 1, 3, 1, 1, 6, 3, 4]
def baseStart_1490169 : Nat := 118140960795 + 1490169 * 2 ^ 59
def prefixEnd_1490169 : Nat := 4983230072969 + 3 ^ 40 * 1490169 * 2
def baseEnd_1490169 : Nat := 170038434095530097918743

theorem tailTrace_1490169 : CollatzResearch.WordTrace tailWord_1490169 prefixEnd_1490169 170038434095530097918743 := by
  unfold tailWord_1490169
  simp only [CollatzResearch.WordTrace]
  refine ⟨54350928538379688448481561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36233952358919792298987707 54350928538379688448481561)
  ·
    refine ⟨40763196403784766336361171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54350928538379688448481561 40763196403784766336361171)
    ·
      refine ⟨61144794605677149504541757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40763196403784766336361171 61144794605677149504541757)
      ·
        refine ⟨22929297977128931064203159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61144794605677149504541757 22929297977128931064203159)
        ·
          refine ⟨34393946965693396596304739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22929297977128931064203159 34393946965693396596304739)
          ·
            refine ⟨51590920448540094894457109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34393946965693396596304739 51590920448540094894457109)
            ·
              refine ⟨2418324396025316948177677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51590920448540094894457109 2418324396025316948177677)
              ·
                refine ⟨906871648509493855566629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2418324396025316948177677 906871648509493855566629)
                ·
                  refine ⟨170038434095530097918743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 906871648509493855566629 170038434095530097918743)
                  ·
                    rfl

theorem cell22_1490169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 3, 4].length) (baseStart_1490169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1490169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1490169 prefixEnd_1490169 := by exact prefixLift 1490169
  have htrace : WordTrace (prefixWord ++ tailWord_1490169) baseStart_1490169 baseEnd_1490169 := by
    simpa [prefixWord, tailWord_1490169, baseEnd_1490169] using wordTrace_append hprefix tailTrace_1490169
  have hstable : (prefixWord ++ tailWord_1490169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490169).length < 2 ^ (prefixWord ++ tailWord_1490169).sum := by decide
  have hdescent : baseEnd_1490169 < baseStart_1490169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490212 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 2, 7]
def baseStart_1490212 : Nat := 118140960795 + 1490212 * 2 ^ 59
def prefixEnd_1490212 : Nat := 4983230072969 + 3 ^ 40 * 1490212 * 2
def baseEnd_1490212 : Nat := 510130022065352514931097

theorem tailTrace_1490212 : CollatzResearch.WordTrace tailWord_1490212 prefixEnd_1490212 510130022065352514931097 := by
  unfold tailWord_1490212
  simp only [CollatzResearch.WordTrace]
  refine ⟨27176248438611953396148445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36234997918149271194864593 27176248438611953396148445)
  ·
    refine ⟨10191093164479482523555667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27176248438611953396148445 10191093164479482523555667)
    ·
      refine ⟨15286639746719223785333501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10191093164479482523555667 15286639746719223785333501)
      ·
        refine ⟨5732489905019708919500063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15286639746719223785333501 5732489905019708919500063)
        ·
          refine ⟨8598734857529563379250095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5732489905019708919500063 8598734857529563379250095)
          ·
            refine ⟨12898102286294345068875143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8598734857529563379250095 12898102286294345068875143)
            ·
              refine ⟨19347153429441517603312715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12898102286294345068875143 19347153429441517603312715)
              ·
                refine ⟨29020730144162276404969073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19347153429441517603312715 29020730144162276404969073)
                ·
                  refine ⟨21765547608121707303726805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29020730144162276404969073 21765547608121707303726805)
                  ·
                    refine ⟨510130022065352514931097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21765547608121707303726805 510130022065352514931097)
                    ·
                      rfl

theorem cell22_1490212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_1490212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1490212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1490212 prefixEnd_1490212 := by exact prefixLift 1490212
  have htrace : WordTrace (prefixWord ++ tailWord_1490212) baseStart_1490212 baseEnd_1490212 := by
    simpa [prefixWord, tailWord_1490212, baseEnd_1490212] using wordTrace_append hprefix tailTrace_1490212
  have hstable : (prefixWord ++ tailWord_1490212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490212).length < 2 ^ (prefixWord ++ tailWord_1490212).sum := by decide
  have hdescent : baseEnd_1490212 < baseStart_1490212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490257 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 1, 7]
def baseStart_1490257 : Nat := 118140960795 + 1490257 * 2 ^ 59
def prefixEnd_1490257 : Nat := 4983230072969 + 3 ^ 40 * 1490257 * 2
def baseEnd_1490257 : Nat := 510145426484987397555959

theorem tailTrace_1490257 : CollatzResearch.WordTrace tailWord_1490257 prefixEnd_1490257 510145426484987397555959 := by
  unfold tailWord_1490257
  simp only [CollatzResearch.WordTrace]
  refine ⟨54354138162060879477685025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36236092108040586318456683 54354138162060879477685025)
  ·
    refine ⟨40765603621545659608263769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54354138162060879477685025 40765603621545659608263769)
    ·
      refine ⟨30574202716159244706197827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40765603621545659608263769 30574202716159244706197827)
      ·
        refine ⟨45861304074238867059296741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30574202716159244706197827 45861304074238867059296741)
        ·
          refine ⟨8598994513919787573618139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45861304074238867059296741 8598994513919787573618139)
          ·
            refine ⟨12898491770879681360427209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8598994513919787573618139 12898491770879681360427209)
            ·
              refine ⟨9673868828159761020320407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12898491770879681360427209 9673868828159761020320407)
              ·
                refine ⟨14510803242239641530480611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9673868828159761020320407 14510803242239641530480611)
                ·
                  refine ⟨21766204863359462295720917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14510803242239641530480611 21766204863359462295720917)
                  ·
                    refine ⟨510145426484987397555959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21766204863359462295720917 510145426484987397555959)
                    ·
                      rfl

theorem cell22_1490257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_1490257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1490257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1490257 prefixEnd_1490257 := by exact prefixLift 1490257
  have htrace : WordTrace (prefixWord ++ tailWord_1490257) baseStart_1490257 baseEnd_1490257 := by
    simpa [prefixWord, tailWord_1490257, baseEnd_1490257] using wordTrace_append hprefix tailTrace_1490257
  have hstable : (prefixWord ++ tailWord_1490257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490257).length < 2 ^ (prefixWord ++ tailWord_1490257).sum := by decide
  have hdescent : baseEnd_1490257 < baseStart_1490257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490289 : List Nat := [1, 2, 2, 2, 1, 2, 2, 5, 1, 4]
def baseStart_1490289 : Nat := 118140960795 + 1490289 * 2 ^ 59
def prefixEnd_1490289 : Nat := 4983230072969 + 3 ^ 40 * 1490289 * 2
def baseEnd_1490289 : Nat := 510156380738949980755861

theorem tailTrace_1490289 : CollatzResearch.WordTrace tailWord_1490289 prefixEnd_1490289 510156380738949980755861 := by
  unfold tailWord_1490289
  simp only [CollatzResearch.WordTrace]
  refine ⟨54355305297944948942849921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36236870198629965961899947 54355305297944948942849921)
  ·
    refine ⟨40766478973458711707137441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54355305297944948942849921 40766478973458711707137441)
    ·
      refine ⟨30574859230094033780353081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40766478973458711707137441 30574859230094033780353081)
      ·
        refine ⟨22931144422570525335264811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30574859230094033780353081 22931144422570525335264811)
        ·
          refine ⟨34396716633855788002897217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22931144422570525335264811 34396716633855788002897217)
          ·
            refine ⟨25797537475391841002172913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34396716633855788002897217 25797537475391841002172913)
            ·
              refine ⟨19348153106543880751629685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25797537475391841002172913 19348153106543880751629685)
              ·
                refine ⟨1813889353738488820465283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19348153106543880751629685 1813889353738488820465283)
                ·
                  refine ⟨2720834030607733230697925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1813889353738488820465283 2720834030607733230697925)
                  ·
                    refine ⟨510156380738949980755861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2720834030607733230697925 510156380738949980755861)
                    ·
                      rfl

theorem cell22_1490289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 4].length) (baseStart_1490289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1490289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1490289 prefixEnd_1490289 := by exact prefixLift 1490289
  have htrace : WordTrace (prefixWord ++ tailWord_1490289) baseStart_1490289 baseEnd_1490289 := by
    simpa [prefixWord, tailWord_1490289, baseEnd_1490289] using wordTrace_append hprefix tailTrace_1490289
  have hstable : (prefixWord ++ tailWord_1490289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490289).length < 2 ^ (prefixWord ++ tailWord_1490289).sum := by decide
  have hdescent : baseEnd_1490289 < baseStart_1490289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490338 : List Nat := [3, 3, 1, 2, 1, 3, 2, 3, 4]
def baseStart_1490338 : Nat := 118140960795 + 1490338 * 2 ^ 59
def prefixEnd_1490338 : Nat := 4983230072969 + 3 ^ 40 * 1490338 * 2
def baseEnd_1490338 : Nat := 170057718146776728760237

theorem tailTrace_1490338 : CollatzResearch.WordTrace tailWord_1490338 prefixEnd_1490338 170057718146776728760237 := by
  unfold tailWord_1490338
  simp only [CollatzResearch.WordTrace]
  refine ⟨13589273118691857577845917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36238061649844953540922445 13589273118691857577845917)
  ·
    refine ⟨5095977419509446591692219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13589273118691857577845917 5095977419509446591692219)
    ·
      refine ⟨7643966129264169887538329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5095977419509446591692219 7643966129264169887538329)
      ·
        refine ⟨5732974596948127415653747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7643966129264169887538329 5732974596948127415653747)
        ·
          refine ⟨8599461895422191123480621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5732974596948127415653747 8599461895422191123480621)
          ·
            refine ⟨3224798210783321671305233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8599461895422191123480621 3224798210783321671305233)
            ·
              refine ⟨2418598658087491253478925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3224798210783321671305233 2418598658087491253478925)
              ·
                refine ⟨906974496782809220054597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2418598658087491253478925 906974496782809220054597)
                ·
                  refine ⟨170057718146776728760237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 906974496782809220054597 170057718146776728760237)
                  ·
                    rfl

theorem cell22_1490338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_1490338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1490338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1490338 prefixEnd_1490338 := by exact prefixLift 1490338
  have htrace : WordTrace (prefixWord ++ tailWord_1490338) baseStart_1490338 baseEnd_1490338 := by
    simpa [prefixWord, tailWord_1490338, baseEnd_1490338] using wordTrace_append hprefix tailTrace_1490338
  have hstable : (prefixWord ++ tailWord_1490338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490338).length < 2 ^ (prefixWord ++ tailWord_1490338).sum := by decide
  have hdescent : baseEnd_1490338 < baseStart_1490338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490394 : List Nat := [3, 1, 1, 2, 3, 2, 1, 2, 7]
def baseStart_1490394 : Nat := 118140960795 + 1490394 * 2 ^ 59
def prefixEnd_1490394 : Nat := 4983230072969 + 3 ^ 40 * 1490394 * 2
def baseEnd_1490394 : Nat := 170064108128254902293513

theorem tailTrace_1490394 : CollatzResearch.WordTrace tailWord_1490394 prefixEnd_1490394 170064108128254902293513 := by
  unfold tailWord_1490394
  simp only [CollatzResearch.WordTrace]
  refine ⟨13589783740641137968855559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36239423308376367916948157 13589783740641137968855559)
  ·
    refine ⟨20384675610961706953283339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13589783740641137968855559 20384675610961706953283339)
    ·
      refine ⟨30577013416442560429925009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20384675610961706953283339 30577013416442560429925009)
      ·
        refine ⟨22932760062331920322443757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30577013416442560429925009 22932760062331920322443757)
        ·
          refine ⟨8599785023374470120916409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22932760062331920322443757 8599785023374470120916409)
          ·
            refine ⟨6449838767530852590687307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8599785023374470120916409 6449838767530852590687307)
            ·
              refine ⟨9674758151296278886030961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6449838767530852590687307 9674758151296278886030961)
              ·
                refine ⟨7256068613472209164523221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9674758151296278886030961 7256068613472209164523221)
                ·
                  refine ⟨170064108128254902293513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7256068613472209164523221 170064108128254902293513)
                  ·
                    rfl

theorem cell22_1490394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 7].length) (baseStart_1490394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1490394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1490394 prefixEnd_1490394 := by exact prefixLift 1490394
  have htrace : WordTrace (prefixWord ++ tailWord_1490394) baseStart_1490394 baseEnd_1490394 := by
    simpa [prefixWord, tailWord_1490394, baseEnd_1490394] using wordTrace_append hprefix tailTrace_1490394
  have hstable : (prefixWord ++ tailWord_1490394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490394).length < 2 ^ (prefixWord ++ tailWord_1490394).sum := by decide
  have hdescent : baseEnd_1490394 < baseStart_1490394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1490469 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 3, 6]
def baseStart_1490469 : Nat := 118140960795 + 1490469 * 2 ^ 59
def prefixEnd_1490469 : Nat := 4983230072969 + 3 ^ 40 * 1490469 * 2
def baseEnd_1490469 : Nat := 510217998417489511255309

theorem tailTrace_1490469 : CollatzResearch.WordTrace tailWord_1490469 prefixEnd_1490469 510217998417489511255309 := by
  unfold tailWord_1490469
  simp only [CollatzResearch.WordTrace]
  refine ⟨54361870437292839684402461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36241246958195226456268307 54361870437292839684402461)
  ·
    refine ⟨20385701413984814881650923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54361870437292839684402461 20385701413984814881650923)
    ·
      refine ⟨30578552120977222322476385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20385701413984814881650923 30578552120977222322476385)
      ·
        refine ⟨22933914090732916741857289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30578552120977222322476385 22933914090732916741857289)
        ·
          refine ⟨17200435568049687556392967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22933914090732916741857289 17200435568049687556392967)
          ·
            refine ⟨25800653352074531334589451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17200435568049687556392967 25800653352074531334589451)
            ·
              refine ⟨38700980028111797001884177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25800653352074531334589451 38700980028111797001884177)
              ·
                refine ⟨29025735021083847751413133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38700980028111797001884177 29025735021083847751413133)
                ·
                  refine ⟨10884650632906442906779925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29025735021083847751413133 10884650632906442906779925)
                  ·
                    refine ⟨510217998417489511255309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10884650632906442906779925 510217998417489511255309)
                    ·
                      rfl

theorem cell22_1490469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_1490469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1490469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1490469 prefixEnd_1490469 := by exact prefixLift 1490469
  have htrace : WordTrace (prefixWord ++ tailWord_1490469) baseStart_1490469 baseEnd_1490469 := by
    simpa [prefixWord, tailWord_1490469, baseEnd_1490469] using wordTrace_append hprefix tailTrace_1490469
  have hstable : (prefixWord ++ tailWord_1490469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1490469).length < 2 ^ (prefixWord ++ tailWord_1490469).sum := by decide
  have hdescent : baseEnd_1490469 < baseStart_1490469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1490469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
