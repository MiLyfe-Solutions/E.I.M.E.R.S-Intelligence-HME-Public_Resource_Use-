import V185TrunkScan23Chunk0100

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_597822 : List Nat := [4, 2, 1, 2, 2, 2, 2, 2, 1, 2, 3]
def baseStart_597822 : Nat := 118140960795 + 597822 * 2 ^ 59
def prefixEnd_597822 : Nat := 4983230072969 + 3 ^ 40 * 597822 * 2
def baseEnd_597822 : Nat := 306970031832265252375673

theorem tailTrace_597822 : CollatzResearch.WordTrace tailWord_597822 prefixEnd_597822 306970031832265252375673 := by
  unfold tailWord_597822
  simp only [CollatzResearch.WordTrace]
  refine ⟨2725544955025058589265465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14536239760133645809415813 2725544955025058589265465)
  ·
    refine ⟨2044158716268793941949099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2725544955025058589265465 2044158716268793941949099)
    ·
      refine ⟨3066238074403190912923649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2044158716268793941949099 3066238074403190912923649)
      ·
        refine ⟨2299678555802393184692737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3066238074403190912923649 2299678555802393184692737)
        ·
          refine ⟨1724758916851794888519553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2299678555802393184692737 1724758916851794888519553)
          ·
            refine ⟨1293569187638846166389665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1724758916851794888519553 1293569187638846166389665)
            ·
              refine ⟨970176890729134624792249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1293569187638846166389665 970176890729134624792249)
              ·
                refine ⟨727632668046850968594187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 970176890729134624792249 727632668046850968594187)
                ·
                  refine ⟨1091449002070276452891281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 727632668046850968594187 1091449002070276452891281)
                  ·
                    refine ⟨818586751552707339668461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1091449002070276452891281 818586751552707339668461)
                    ·
                      refine ⟨306970031832265252375673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 818586751552707339668461 306970031832265252375673)
                      ·
                        rfl

theorem cell23_597822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_597822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597822 prefixEnd_597822 := by exact prefixLift 597822
  have htrace : WordTrace (prefixWord ++ tailWord_597822) baseStart_597822 baseEnd_597822 := by
    simpa [prefixWord, tailWord_597822, baseEnd_597822] using wordTrace_append hprefix tailTrace_597822
  have hstable : (prefixWord ++ tailWord_597822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597822).length < 2 ^ (prefixWord ++ tailWord_597822).sum := by decide
  have hdescent : baseEnd_597822 < baseStart_597822 := by decide
  rcases family_descends (prefixWord ++ tailWord_597822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597831 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 5]
def baseStart_597831 : Nat := 118140960795 + 597831 * 2 ^ 59
def prefixEnd_597831 : Nat := 4983230072969 + 3 ^ 40 * 597831 * 2
def baseEnd_597831 : Nat := 306974653158155717163131

theorem tailTrace_597831 : CollatzResearch.WordTrace tailWord_597831 prefixEnd_597831 306974653158155717163131 := by
  unfold tailWord_597831
  simp only [CollatzResearch.WordTrace]
  refine ⟨21804687897167863251201347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14536458598111908834134231 21804687897167863251201347)
  ·
    refine ⟨32707031845751794876802021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21804687897167863251201347 32707031845751794876802021)
    ·
      refine ⟨6132568471078461539400379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32707031845751794876802021 6132568471078461539400379)
      ·
        refine ⟨9198852706617692309100569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6132568471078461539400379 9198852706617692309100569)
        ·
          refine ⟨6899139529963269231825427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9198852706617692309100569 6899139529963269231825427)
          ·
            refine ⟨10348709294944903847738141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6899139529963269231825427 10348709294944903847738141)
            ·
              refine ⟨3880765985604338942901803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10348709294944903847738141 3880765985604338942901803)
              ·
                refine ⟨5821148978406508414352705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3880765985604338942901803 5821148978406508414352705)
                ·
                  refine ⟨4365861733804881310764529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5821148978406508414352705 4365861733804881310764529)
                  ·
                    refine ⟨3274396300353660983073397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4365861733804881310764529 3274396300353660983073397)
                    ·
                      refine ⟨306974653158155717163131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3274396300353660983073397 306974653158155717163131)
                      ·
                        rfl

theorem cell23_597831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_597831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597831 prefixEnd_597831 := by exact prefixLift 597831
  have htrace : WordTrace (prefixWord ++ tailWord_597831) baseStart_597831 baseEnd_597831 := by
    simpa [prefixWord, tailWord_597831, baseEnd_597831] using wordTrace_append hprefix tailTrace_597831
  have hstable : (prefixWord ++ tailWord_597831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597831).length < 2 ^ (prefixWord ++ tailWord_597831).sum := by decide
  have hdescent : baseEnd_597831 < baseStart_597831 := by decide
  rcases family_descends (prefixWord ++ tailWord_597831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597836 : List Nat := [2, 2, 1, 3, 4, 2, 1, 3, 1, 2, 2]
def baseStart_597836 : Nat := 118140960795 + 597836 * 2 ^ 59
def prefixEnd_597836 : Nat := 4983230072969 + 3 ^ 40 * 597836 * 2
def baseEnd_597836 : Nat := 306977220561428197600609

theorem tailTrace_597836 : CollatzResearch.WordTrace tailWord_597836 prefixEnd_597836 306977220561428197600609 := by
  unfold tailWord_597836
  simp only [CollatzResearch.WordTrace]
  refine ⟨10902435131074874552566681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14536580174766499403422241 10902435131074874552566681)
  ·
    refine ⟨8176826348306155914425011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10902435131074874552566681 8176826348306155914425011)
    ·
      refine ⟨12265239522459233871637517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8176826348306155914425011 12265239522459233871637517)
      ·
        refine ⟨4599464820922212701864069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12265239522459233871637517 4599464820922212701864069)
        ·
          refine ⟨862399653922914881599513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4599464820922212701864069 862399653922914881599513)
          ·
            refine ⟨646799740442186161199635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 862399653922914881599513 646799740442186161199635)
            ·
              refine ⟨970199610663279241799453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 646799740442186161199635 970199610663279241799453)
              ·
                refine ⟨363824853998729715674795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 970199610663279241799453 363824853998729715674795)
                ·
                  refine ⟨545737280998094573512193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 363824853998729715674795 545737280998094573512193)
                  ·
                    refine ⟨409302960748570930134145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 545737280998094573512193 409302960748570930134145)
                    ·
                      refine ⟨306977220561428197600609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 409302960748570930134145 306977220561428197600609)
                      ·
                        rfl

theorem cell23_597836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_597836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597836 prefixEnd_597836 := by exact prefixLift 597836
  have htrace : WordTrace (prefixWord ++ tailWord_597836) baseStart_597836 baseEnd_597836 := by
    simpa [prefixWord, tailWord_597836, baseEnd_597836] using wordTrace_append hprefix tailTrace_597836
  have hstable : (prefixWord ++ tailWord_597836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597836).length < 2 ^ (prefixWord ++ tailWord_597836).sum := by decide
  have hdescent : baseEnd_597836 < baseStart_597836 := by decide
  rcases family_descends (prefixWord ++ tailWord_597836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597861 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 3, 3, 5]
def baseStart_597861 : Nat := 118140960795 + 597861 * 2 ^ 59
def prefixEnd_597861 : Nat := 4983230072969 + 3 ^ 40 * 597861 * 2
def baseEnd_597861 : Nat := 306990057577790599787993

theorem tailTrace_597861 : CollatzResearch.WordTrace tailWord_597861 prefixEnd_597861 306990057577790599787993 := by
  unfold tailWord_597861
  simp only [CollatzResearch.WordTrace]
  refine ⟨21805782087059178374793437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14537188058039452249862291 21805782087059178374793437)
  ·
    refine ⟨8177168282647191890547539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21805782087059178374793437 8177168282647191890547539)
    ·
      refine ⟨12265752423970787835821309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8177168282647191890547539 12265752423970787835821309)
      ·
        refine ⟨4599657158989045438432991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12265752423970787835821309 4599657158989045438432991)
        ·
          refine ⟨6899485738483568157649487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4599657158989045438432991 6899485738483568157649487)
          ·
            refine ⟨10349228607725352236474231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6899485738483568157649487 10349228607725352236474231)
            ·
              refine ⟨15523842911588028354711347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10349228607725352236474231 15523842911588028354711347)
              ·
                refine ⟨23285764367382042532067021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15523842911588028354711347 23285764367382042532067021)
                ·
                  refine ⟨8732161637768265949525133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23285764367382042532067021 8732161637768265949525133)
                  ·
                    refine ⟨3274560614163099731071925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8732161637768265949525133 3274560614163099731071925)
                    ·
                      refine ⟨306990057577790599787993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3274560614163099731071925 306990057577790599787993)
                      ·
                        rfl

theorem cell23_597861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_597861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597861 prefixEnd_597861 := by exact prefixLift 597861
  have htrace : WordTrace (prefixWord ++ tailWord_597861) baseStart_597861 baseEnd_597861 := by
    simpa [prefixWord, tailWord_597861, baseEnd_597861] using wordTrace_append hprefix tailTrace_597861
  have hstable : (prefixWord ++ tailWord_597861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597861).length < 2 ^ (prefixWord ++ tailWord_597861).sum := by decide
  have hdescent : baseEnd_597861 < baseStart_597861 := by decide
  rcases family_descends (prefixWord ++ tailWord_597861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597881 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 9]
def baseStart_597881 : Nat := 118140960795 + 597881 * 2 ^ 59
def prefixEnd_597881 : Nat := 4983230072969 + 3 ^ 40 * 597881 * 2
def baseEnd_597881 : Nat := 34111147465653391281989

theorem tailTrace_597881 : CollatzResearch.WordTrace tailWord_597881 prefixEnd_597881 34111147465653391281989 := by
  unfold tailWord_597881
  simp only [CollatzResearch.WordTrace]
  refine ⟨21806511546986721790521497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14537674364657814527014331 21806511546986721790521497)
  ·
    refine ⟨16354883660240041342891123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21806511546986721790521497 16354883660240041342891123)
    ·
      refine ⟨24532325490360062014336685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16354883660240041342891123 24532325490360062014336685)
      ·
        refine ⟨9199622058885023255376257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24532325490360062014336685 9199622058885023255376257)
        ·
          refine ⟨6899716544163767441532193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9199622058885023255376257 6899716544163767441532193)
          ·
            refine ⟨5174787408122825581149145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6899716544163767441532193 5174787408122825581149145)
            ·
              refine ⟨3881090556092119185861859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5174787408122825581149145 3881090556092119185861859)
              ·
                refine ⟨5821635834138178778792789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3881090556092119185861859 5821635834138178778792789)
                ·
                  refine ⟨34111147465653391281989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5821635834138178778792789 34111147465653391281989)
                  ·
                    rfl

theorem cell23_597881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 9].length) (baseStart_597881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597881 prefixEnd_597881 := by exact prefixLift 597881
  have htrace : WordTrace (prefixWord ++ tailWord_597881) baseStart_597881 baseEnd_597881 := by
    simpa [prefixWord, tailWord_597881, baseEnd_597881] using wordTrace_append hprefix tailTrace_597881
  have hstable : (prefixWord ++ tailWord_597881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597881).length < 2 ^ (prefixWord ++ tailWord_597881).sum := by decide
  have hdescent : baseEnd_597881 < baseStart_597881 := by decide
  rcases family_descends (prefixWord ++ tailWord_597881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_597975 : List Nat := [1, 1, 3, 2, 1, 1, 6, 1, 3, 4]
def baseStart_597975 : Nat := 118140960795 + 597975 * 2 ^ 59
def prefixEnd_597975 : Nat := 4983230072969 + 3 ^ 40 * 597975 * 2
def baseEnd_597975 : Nat := 102349531457467717920823

theorem tailTrace_597975 : CollatzResearch.WordTrace tailWord_597975 prefixEnd_597975 102349531457467717920823 := by
  unfold tailWord_597975
  simp only [CollatzResearch.WordTrace]
  refine ⟨21809940008646175844443379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14539960005764117229628919 21809940008646175844443379)
  ·
    refine ⟨32714910012969263766665069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21809940008646175844443379 32714910012969263766665069)
    ·
      refine ⟨12268091254863473912499401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32714910012969263766665069 12268091254863473912499401)
      ·
        refine ⟨9201068441147605434374551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12268091254863473912499401 9201068441147605434374551)
        ·
          refine ⟨13801602661721408151561827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9201068441147605434374551 13801602661721408151561827)
          ·
            refine ⟨20702403992582112227342741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13801602661721408151561827 20702403992582112227342741)
            ·
              refine ⟨970425187152286510656691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20702403992582112227342741 970425187152286510656691)
              ·
                refine ⟨1455637780728429765985037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 970425187152286510656691 1455637780728429765985037)
                ·
                  refine ⟨545864167773161162244389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1455637780728429765985037 545864167773161162244389)
                  ·
                    refine ⟨102349531457467717920823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 545864167773161162244389 102349531457467717920823)
                    ·
                      rfl

theorem cell23_597975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 3, 4].length) (baseStart_597975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_597975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_597975 prefixEnd_597975 := by exact prefixLift 597975
  have htrace : WordTrace (prefixWord ++ tailWord_597975) baseStart_597975 baseEnd_597975 := by
    simpa [prefixWord, tailWord_597975, baseEnd_597975] using wordTrace_append hprefix tailTrace_597975
  have hstable : (prefixWord ++ tailWord_597975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_597975).length < 2 ^ (prefixWord ++ tailWord_597975).sum := by decide
  have hdescent : baseEnd_597975 < baseStart_597975 := by decide
  rcases family_descends (prefixWord ++ tailWord_597975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598009 : List Nat := [1, 2, 1, 3, 1, 6, 1, 3, 1, 4]
def baseStart_598009 : Nat := 118140960795 + 598009 * 2 ^ 59
def prefixEnd_598009 : Nat := 4983230072969 + 3 ^ 40 * 598009 * 2
def baseEnd_598009 : Nat := 102355350904885340245771

theorem tailTrace_598009 : CollatzResearch.WordTrace tailWord_598009 prefixEnd_598009 102355350904885340245771 := by
  unfold tailWord_598009
  simp only [CollatzResearch.WordTrace]
  refine ⟨21811180090522999651181081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14540786727015333100787387 21811180090522999651181081)
  ·
    refine ⟨16358385067892249738385811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21811180090522999651181081 16358385067892249738385811)
    ·
      refine ⟨24537577601838374607578717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16358385067892249738385811 24537577601838374607578717)
      ·
        refine ⟨9201591600689390477842019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24537577601838374607578717 9201591600689390477842019)
        ·
          refine ⟨13802387401034085716763029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9201591600689390477842019 13802387401034085716763029)
          ·
            refine ⟨646986909423472767973267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13802387401034085716763029 646986909423472767973267)
            ·
              refine ⟨970480364135209151959901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 646986909423472767973267 970480364135209151959901)
              ·
                refine ⟨363930136550703431984963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 970480364135209151959901 363930136550703431984963)
                ·
                  refine ⟨545895204826055147977445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 363930136550703431984963 545895204826055147977445)
                  ·
                    refine ⟨102355350904885340245771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 545895204826055147977445 102355350904885340245771)
                    ·
                      rfl

theorem cell23_598009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 3, 1, 4].length) (baseStart_598009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598009 prefixEnd_598009 := by exact prefixLift 598009
  have htrace : WordTrace (prefixWord ++ tailWord_598009) baseStart_598009 baseEnd_598009 := by
    simpa [prefixWord, tailWord_598009, baseEnd_598009] using wordTrace_append hprefix tailTrace_598009
  have hstable : (prefixWord ++ tailWord_598009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598009).length < 2 ^ (prefixWord ++ tailWord_598009).sum := by decide
  have hdescent : baseEnd_598009 < baseStart_598009 := by decide
  rcases family_descends (prefixWord ++ tailWord_598009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598015 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 5, 1, 3]
def baseStart_598015 : Nat := 118140960795 + 598015 * 2 ^ 59
def prefixEnd_598015 : Nat := 4983230072969 + 3 ^ 40 * 598015 * 2
def baseEnd_598015 : Nat := 307069133598582997262285

theorem tailTrace_598015 : CollatzResearch.WordTrace tailWord_598015 prefixEnd_598015 307069133598582997262285 := by
  unfold tailWord_598015
  simp only [CollatzResearch.WordTrace]
  refine ⟨21811398928501262675899499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14540932619000841783932999 21811398928501262675899499)
  ·
    refine ⟨32717098392751894013849249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21811398928501262675899499 32717098392751894013849249)
    ·
      refine ⟨24537823794563920510386937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32717098392751894013849249 24537823794563920510386937)
      ·
        refine ⟨18403367845922940382790203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24537823794563920510386937 18403367845922940382790203)
        ·
          refine ⟨27605051768884410574185305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18403367845922940382790203 27605051768884410574185305)
          ·
            refine ⟨20703788826663307930638979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27605051768884410574185305 20703788826663307930638979)
            ·
              refine ⟨31055683239994961895958469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20703788826663307930638979 31055683239994961895958469)
              ·
                refine ⟨5822940607499055355492213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31055683239994961895958469 5822940607499055355492213)
                ·
                  refine ⟨545900681953036439577395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5822940607499055355492213 545900681953036439577395)
                  ·
                    refine ⟨818851022929554659366093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 545900681953036439577395 818851022929554659366093)
                    ·
                      refine ⟨307069133598582997262285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 818851022929554659366093 307069133598582997262285)
                      ·
                        rfl

theorem cell23_598015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 5, 1, 3].length) (baseStart_598015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598015 prefixEnd_598015 := by exact prefixLift 598015
  have htrace : WordTrace (prefixWord ++ tailWord_598015) baseStart_598015 baseEnd_598015 := by
    simpa [prefixWord, tailWord_598015, baseEnd_598015] using wordTrace_append hprefix tailTrace_598015
  have hstable : (prefixWord ++ tailWord_598015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598015).length < 2 ^ (prefixWord ++ tailWord_598015).sum := by decide
  have hdescent : baseEnd_598015 < baseStart_598015 := by decide
  rcases family_descends (prefixWord ++ tailWord_598015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598026 : List Nat := [3, 1, 2, 2, 4, 1, 3, 2, 1, 4]
def baseStart_598026 : Nat := 118140960795 + 598026 * 2 ^ 59
def prefixEnd_598026 : Nat := 4983230072969 + 3 ^ 40 * 598026 * 2
def baseEnd_598026 : Nat := 102358260628594151408245

theorem tailTrace_598026 : CollatzResearch.WordTrace tailWord_598026 prefixEnd_598026 102358260628594151408245 := by
  unfold tailWord_598026
  simp only [CollatzResearch.WordTrace]
  refine ⟨5452950032865352888637483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14541200087640941036366621 5452950032865352888637483)
  ·
    refine ⟨8179425049298029332956225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5452950032865352888637483 8179425049298029332956225)
    ·
      refine ⟨6134568786973521999717169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8179425049298029332956225 6134568786973521999717169)
      ·
        refine ⟨4600926590230141499787877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6134568786973521999717169 4600926590230141499787877)
        ·
          refine ⟨862673735668151531210227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4600926590230141499787877 862673735668151531210227)
          ·
            refine ⟨1294010603502227296815341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 862673735668151531210227 1294010603502227296815341)
            ·
              refine ⟨485253976313335236305753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1294010603502227296815341 485253976313335236305753)
              ·
                refine ⟨363940482235001427229315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 485253976313335236305753 363940482235001427229315)
                ·
                  refine ⟨545910723352502140843973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 363940482235001427229315 545910723352502140843973)
                  ·
                    refine ⟨102358260628594151408245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 545910723352502140843973 102358260628594151408245)
                    ·
                      rfl

theorem cell23_598026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 2, 1, 4].length) (baseStart_598026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598026 prefixEnd_598026 := by exact prefixLift 598026
  have htrace : WordTrace (prefixWord ++ tailWord_598026) baseStart_598026 baseEnd_598026 := by
    simpa [prefixWord, tailWord_598026, baseEnd_598026] using wordTrace_append hprefix tailTrace_598026
  have hstable : (prefixWord ++ tailWord_598026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598026).length < 2 ^ (prefixWord ++ tailWord_598026).sum := by decide
  have hdescent : baseEnd_598026 < baseStart_598026 := by decide
  rcases family_descends (prefixWord ++ tailWord_598026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598039 : List Nat := [1, 1, 3, 5, 2, 2, 2, 1, 6]
def baseStart_598039 : Nat := 118140960795 + 598039 * 2 ^ 59
def prefixEnd_598039 : Nat := 4983230072969 + 3 ^ 40 * 598039 * 2
def baseEnd_598039 : Nat := 34120161903810100373575

theorem tailTrace_598039 : CollatzResearch.WordTrace tailWord_598039 prefixEnd_598039 34120161903810100373575 := by
  unfold tailWord_598039
  simp only [CollatzResearch.WordTrace]
  refine ⟨21812274280414314774773171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14541516186942876516515447 21812274280414314774773171)
  ·
    refine ⟨32718411420621472162159757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21812274280414314774773171 32718411420621472162159757)
    ·
      refine ⟨12269404282733052060809909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32718411420621472162159757 12269404282733052060809909)
      ·
        refine ⟨1150256651506223630700929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12269404282733052060809909 1150256651506223630700929)
        ·
          refine ⟨862692488629667723025697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1150256651506223630700929 862692488629667723025697)
          ·
            refine ⟨647019366472250792269273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 862692488629667723025697 647019366472250792269273)
            ·
              refine ⟨485264524854188094201955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 647019366472250792269273 485264524854188094201955)
              ·
                refine ⟨727896787281282141302933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 485264524854188094201955 727896787281282141302933)
                ·
                  refine ⟨34120161903810100373575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 727896787281282141302933 34120161903810100373575)
                  ·
                    rfl

theorem cell23_598039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 6].length) (baseStart_598039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598039 prefixEnd_598039 := by exact prefixLift 598039
  have htrace : WordTrace (prefixWord ++ tailWord_598039) baseStart_598039 baseEnd_598039 := by
    simpa [prefixWord, tailWord_598039, baseEnd_598039] using wordTrace_append hprefix tailTrace_598039
  have hstable : (prefixWord ++ tailWord_598039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598039).length < 2 ^ (prefixWord ++ tailWord_598039).sum := by decide
  have hdescent : baseEnd_598039 < baseStart_598039 := by decide
  rcases family_descends (prefixWord ++ tailWord_598039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598052 : List Nat := [2, 3, 1, 4, 2, 1, 1, 1, 3, 5]
def baseStart_598052 : Nat := 118140960795 + 598052 * 2 ^ 59
def prefixEnd_598052 : Nat := 4983230072969 + 3 ^ 40 * 598052 * 2
def baseEnd_598052 : Nat := 102362710794266450833205

theorem tailTrace_598052 : CollatzResearch.WordTrace tailWord_598052 prefixEnd_598052 102362710794266450833205 := by
  unfold tailWord_598052
  simp only [CollatzResearch.WordTrace]
  refine ⟨10906374214683608997498205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14541832286244811996664273 10906374214683608997498205)
  ·
    refine ⟨4089890330506353374061827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10906374214683608997498205 4089890330506353374061827)
    ·
      refine ⟨6134835495759530061092741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4089890330506353374061827 6134835495759530061092741)
      ·
        refine ⟨1150281655454911886454889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6134835495759530061092741 1150281655454911886454889)
        ·
          refine ⟨862711241591183914841167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1150281655454911886454889 862711241591183914841167)
          ·
            refine ⟨1294066862386775872261751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 862711241591183914841167 1294066862386775872261751)
            ·
              refine ⟨1941100293580163808392627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1294066862386775872261751 1941100293580163808392627)
              ·
                refine ⟨2911650440370245712588941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1941100293580163808392627 2911650440370245712588941)
                ·
                  refine ⟨1091868915138842142220853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2911650440370245712588941 1091868915138842142220853)
                  ·
                    refine ⟨102362710794266450833205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1091868915138842142220853 102362710794266450833205)
                    ·
                      rfl

theorem cell23_598052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_598052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598052 prefixEnd_598052 := by exact prefixLift 598052
  have htrace : WordTrace (prefixWord ++ tailWord_598052) baseStart_598052 baseEnd_598052 := by
    simpa [prefixWord, tailWord_598052, baseEnd_598052] using wordTrace_append hprefix tailTrace_598052
  have hstable : (prefixWord ++ tailWord_598052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598052).length < 2 ^ (prefixWord ++ tailWord_598052).sum := by decide
  have hdescent : baseEnd_598052 < baseStart_598052 := by decide
  rcases family_descends (prefixWord ++ tailWord_598052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598065 : List Nat := [1, 2, 2, 3, 1, 4, 1, 2, 1, 6]
def baseStart_598065 : Nat := 118140960795 + 598065 * 2 ^ 59
def prefixEnd_598065 : Nat := 4983230072969 + 3 ^ 40 * 598065 * 2
def baseEnd_598065 : Nat := 102364935877102600545685

theorem tailTrace_598065 : CollatzResearch.WordTrace tailWord_598065 prefixEnd_598065 102364935877102600545685 := by
  unfold tailWord_598065
  simp only [CollatzResearch.WordTrace]
  refine ⟨21813222578320121215219649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14542148385546747476813099 21813222578320121215219649)
  ·
    refine ⟨16359916933740090911414737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21813222578320121215219649 16359916933740090911414737)
    ·
      refine ⟨12269937700305068183561053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16359916933740090911414737 12269937700305068183561053)
      ·
        refine ⟨4601226637614400568835395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12269937700305068183561053 4601226637614400568835395)
        ·
          refine ⟨6901839956421600853253093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4601226637614400568835395 6901839956421600853253093)
          ·
            refine ⟨1294094991829050159984955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6901839956421600853253093 1294094991829050159984955)
            ·
              refine ⟨1941142487743575239977433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1294094991829050159984955 1941142487743575239977433)
              ·
                refine ⟨1455856865807681429983075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1941142487743575239977433 1455856865807681429983075)
                ·
                  refine ⟨2183785298711522144974613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1455856865807681429983075 2183785298711522144974613)
                  ·
                    refine ⟨102364935877102600545685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2183785298711522144974613 102364935877102600545685)
                    ·
                      rfl

theorem cell23_598065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 6].length) (baseStart_598065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598065 prefixEnd_598065 := by exact prefixLift 598065
  have htrace : WordTrace (prefixWord ++ tailWord_598065) baseStart_598065 baseEnd_598065 := by
    simpa [prefixWord, tailWord_598065, baseEnd_598065] using wordTrace_append hprefix tailTrace_598065
  have hstable : (prefixWord ++ tailWord_598065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598065).length < 2 ^ (prefixWord ++ tailWord_598065).sum := by decide
  have hdescent : baseEnd_598065 < baseStart_598065 := by decide
  rcases family_descends (prefixWord ++ tailWord_598065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598088 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 2, 2, 7]
def baseStart_598088 : Nat := 118140960795 + 598088 * 2 ^ 59
def prefixEnd_598088 : Nat := 4983230072969 + 3 ^ 40 * 598088 * 2
def baseEnd_598088 : Nat := 307106617686361211649449

theorem tailTrace_598088 : CollatzResearch.WordTrace tailWord_598088 prefixEnd_598088 307106617686361211649449 := by
  unfold tailWord_598088
  simp only [CollatzResearch.WordTrace]
  refine ⟨10907030728618398071653459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14542707638157864095537945 10907030728618398071653459)
  ·
    refine ⟨16360546092927597107480189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10907030728618398071653459 16360546092927597107480189)
    ·
      refine ⟨6135204784847848915305071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16360546092927597107480189 6135204784847848915305071)
      ·
        refine ⟨9202807177271773372957607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6135204784847848915305071 9202807177271773372957607)
        ·
          refine ⟨13804210765907660059436411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9202807177271773372957607 13804210765907660059436411)
          ·
            refine ⟨20706316148861490089154617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13804210765907660059436411 20706316148861490089154617)
            ·
              refine ⟨15529737111646117566865963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20706316148861490089154617 15529737111646117566865963)
              ·
                refine ⟨23294605667469176350298945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15529737111646117566865963 23294605667469176350298945)
                ·
                  refine ⟨17470954250601882262724209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23294605667469176350298945 17470954250601882262724209)
                  ·
                    refine ⟨13103215687951411697043157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17470954250601882262724209 13103215687951411697043157)
                    ·
                      refine ⟨307106617686361211649449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 13103215687951411697043157 307106617686361211649449)
                      ·
                        rfl

theorem cell23_598088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_598088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598088 prefixEnd_598088 := by exact prefixLift 598088
  have htrace : WordTrace (prefixWord ++ tailWord_598088) baseStart_598088 baseEnd_598088 := by
    simpa [prefixWord, tailWord_598088, baseEnd_598088] using wordTrace_append hprefix tailTrace_598088
  have hstable : (prefixWord ++ tailWord_598088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598088).length < 2 ^ (prefixWord ++ tailWord_598088).sum := by decide
  have hdescent : baseEnd_598088 < baseStart_598088 := by decide
  rcases family_descends (prefixWord ++ tailWord_598088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598109 : List Nat := [1, 4, 4, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_598109 : Nat := 118140960795 + 598109 * 2 ^ 59
def prefixEnd_598109 : Nat := 4983230072969 + 3 ^ 40 * 598109 * 2
def baseEnd_598109 : Nat := 307117400780105629486853

theorem tailTrace_598109 : CollatzResearch.WordTrace tailWord_598109 prefixEnd_598109 307117400780105629486853 := by
  unfold tailWord_598109
  simp only [CollatzResearch.WordTrace]
  refine ⟨21814827390160716729821381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14543218260107144486547587 21814827390160716729821381)
  ·
    refine ⟨4090280135655134386841509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21814827390160716729821381 4090280135655134386841509)
    ·
      refine ⟨766927525435337697532783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4090280135655134386841509 766927525435337697532783)
      ·
        refine ⟨1150391288153006546299175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 766927525435337697532783 1150391288153006546299175)
        ·
          refine ⟨1725586932229509819448763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1150391288153006546299175 1725586932229509819448763)
          ·
            refine ⟨2588380398344264729173145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1725586932229509819448763 2588380398344264729173145)
            ·
              refine ⟨1941285298758198546879859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2588380398344264729173145 1941285298758198546879859)
              ·
                refine ⟨2911927948137297820319789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1941285298758198546879859 2911927948137297820319789)
                ·
                  refine ⟨1091972980551486682619921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2911927948137297820319789 1091972980551486682619921)
                  ·
                    refine ⟨818979735413615011964941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1091972980551486682619921 818979735413615011964941)
                    ·
                      refine ⟨307117400780105629486853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 818979735413615011964941 307117400780105629486853)
                      ·
                        rfl

theorem cell23_598109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_598109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598109 prefixEnd_598109 := by exact prefixLift 598109
  have htrace : WordTrace (prefixWord ++ tailWord_598109) baseStart_598109 baseEnd_598109 := by
    simpa [prefixWord, tailWord_598109, baseEnd_598109] using wordTrace_append hprefix tailTrace_598109
  have hstable : (prefixWord ++ tailWord_598109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598109).length < 2 ^ (prefixWord ++ tailWord_598109).sum := by decide
  have hdescent : baseEnd_598109 < baseStart_598109 := by decide
  rcases family_descends (prefixWord ++ tailWord_598109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598110 : List Nat := [4, 4, 1, 1, 2, 2, 1, 1, 2, 3, 2]
def baseStart_598110 : Nat := 118140960795 + 598110 * 2 ^ 59
def prefixEnd_598110 : Nat := 4983230072969 + 3 ^ 40 * 598110 * 2
def baseEnd_598110 : Nat := 307117914260760125574349

theorem tailTrace_598110 : CollatzResearch.WordTrace tailWord_598110 prefixEnd_598110 307117914260760125574349 := by
  unfold tailWord_598110
  simp only [CollatzResearch.WordTrace]
  refine ⟨2726857982894636737575973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14543242575438062600405189 2726857982894636737575973)
  ·
    refine ⟨511285871792744388295495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2726857982894636737575973 511285871792744388295495)
    ·
      refine ⟨766928807689116582443243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 511285871792744388295495 766928807689116582443243)
      ·
        refine ⟨1150393211533674873664865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 766928807689116582443243 1150393211533674873664865)
        ·
          refine ⟨862794908650256155248649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1150393211533674873664865 862794908650256155248649)
          ·
            refine ⟨647096181487692116436487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 862794908650256155248649 647096181487692116436487)
            ·
              refine ⟨970644272231538174654731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 647096181487692116436487 970644272231538174654731)
              ·
                refine ⟨1455966408347307261982097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 970644272231538174654731 1455966408347307261982097)
                ·
                  refine ⟨1091974806260480446486573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1455966408347307261982097 1091974806260480446486573)
                  ·
                    refine ⟨409490552347680167432465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1091974806260480446486573 409490552347680167432465)
                    ·
                      refine ⟨307117914260760125574349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 409490552347680167432465 307117914260760125574349)
                      ·
                        rfl

theorem cell23_598110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_598110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598110 prefixEnd_598110 := by exact prefixLift 598110
  have htrace : WordTrace (prefixWord ++ tailWord_598110) baseStart_598110 baseEnd_598110 := by
    simpa [prefixWord, tailWord_598110, baseEnd_598110] using wordTrace_append hprefix tailTrace_598110
  have hstable : (prefixWord ++ tailWord_598110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598110).length < 2 ^ (prefixWord ++ tailWord_598110).sum := by decide
  have hdescent : baseEnd_598110 < baseStart_598110 := by decide
  rcases family_descends (prefixWord ++ tailWord_598110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598165 : List Nat := [1, 3, 2, 1, 1, 1, 4, 2, 2, 1, 5]
def baseStart_598165 : Nat := 118140960795 + 598165 * 2 ^ 59
def prefixEnd_598165 : Nat := 4983230072969 + 3 ^ 40 * 598165 * 2
def baseEnd_598165 : Nat := 307146155696757410386595

theorem tailTrace_598165 : CollatzResearch.WordTrace tailWord_598165 prefixEnd_598165 307146155696757410386595 := by
  unfold tailWord_598165
  simp only [CollatzResearch.WordTrace]
  refine ⟨21816869877957838293859949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14544579918638558862573299 21816869877957838293859949)
  ·
    refine ⟨8181326204234189360197481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21816869877957838293859949 8181326204234189360197481)
    ·
      refine ⟨6135994653175642020148111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8181326204234189360197481 6135994653175642020148111)
      ·
        refine ⟨9203991979763463030222167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6135994653175642020148111 9203991979763463030222167)
        ·
          refine ⟨13805987969645194545333251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9203991979763463030222167 13805987969645194545333251)
          ·
            refine ⟨20708981954467791817999877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13805987969645194545333251 20708981954467791817999877)
            ·
              refine ⟨3882934116462710965874977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20708981954467791817999877 3882934116462710965874977)
              ·
                refine ⟨2912200587347033224406233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3882934116462710965874977 2912200587347033224406233)
                ·
                  refine ⟨2184150440510274918304675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2912200587347033224406233 2184150440510274918304675)
                  ·
                    refine ⟨3276225660765412377457013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2184150440510274918304675 3276225660765412377457013)
                    ·
                      refine ⟨307146155696757410386595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3276225660765412377457013 307146155696757410386595)
                      ·
                        rfl

theorem cell23_598165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_598165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598165 prefixEnd_598165 := by exact prefixLift 598165
  have htrace : WordTrace (prefixWord ++ tailWord_598165) baseStart_598165 baseEnd_598165 := by
    simpa [prefixWord, tailWord_598165, baseEnd_598165] using wordTrace_append hprefix tailTrace_598165
  have hstable : (prefixWord ++ tailWord_598165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598165).length < 2 ^ (prefixWord ++ tailWord_598165).sum := by decide
  have hdescent : baseEnd_598165 < baseStart_598165 := by decide
  rcases family_descends (prefixWord ++ tailWord_598165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598202 : List Nat := [3, 1, 1, 1, 2, 2, 2, 6, 5]
def baseStart_598202 : Nat := 118140960795 + 598202 * 2 ^ 59
def prefixEnd_598202 : Nat := 4983230072969 + 3 ^ 40 * 598202 * 2
def baseEnd_598202 : Nat := 34129461608997085069325

theorem tailTrace_598202 : CollatzResearch.WordTrace tailWord_598202 prefixEnd_598202 34129461608997085069325 := by
  unfold tailWord_598202
  simp only [CollatzResearch.WordTrace]
  refine ⟨5454554844705948403239215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14545479585882529075304573 5454554844705948403239215)
  ·
    refine ⟨8181832267058922604858823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5454554844705948403239215 8181832267058922604858823)
    ·
      refine ⟨12272748400588383907288235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8181832267058922604858823 12272748400588383907288235)
      ·
        refine ⟨18409122600882575860932353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12272748400588383907288235 18409122600882575860932353)
        ·
          refine ⟨13806841950661931895699265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18409122600882575860932353 13806841950661931895699265)
          ·
            refine ⟨10355131462996448921774449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13806841950661931895699265 10355131462996448921774449)
            ·
              refine ⟨7766348597247336691330837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10355131462996448921774449 7766348597247336691330837)
              ·
                refine ⟨364047590495968907406133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7766348597247336691330837 364047590495968907406133)
                ·
                  refine ⟨34129461608997085069325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 364047590495968907406133 34129461608997085069325)
                  ·
                    rfl

theorem cell23_598202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 6, 5].length) (baseStart_598202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598202 prefixEnd_598202 := by exact prefixLift 598202
  have htrace : WordTrace (prefixWord ++ tailWord_598202) baseStart_598202 baseEnd_598202 := by
    simpa [prefixWord, tailWord_598202, baseEnd_598202] using wordTrace_append hprefix tailTrace_598202
  have hstable : (prefixWord ++ tailWord_598202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598202).length < 2 ^ (prefixWord ++ tailWord_598202).sum := by decide
  have hdescent : baseEnd_598202 < baseStart_598202 := by decide
  rcases family_descends (prefixWord ++ tailWord_598202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598232 : List Nat := [2, 1, 2, 2, 4, 1, 1, 3, 2, 5]
def baseStart_598232 : Nat := 118140960795 + 598232 * 2 ^ 59
def prefixEnd_598232 : Nat := 4983230072969 + 3 ^ 40 * 598232 * 2
def baseEnd_598232 : Nat := 102393519633536216082929

theorem tailTrace_598232 : CollatzResearch.WordTrace tailWord_598232 prefixEnd_598232 102393519633536216082929 := by
  unfold tailWord_598232
  simp only [CollatzResearch.WordTrace]
  refine ⟨10909656784357554368274475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14546209045810072491032633 10909656784357554368274475)
  ·
    refine ⟨16364485176536331552411713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10909656784357554368274475 16364485176536331552411713)
    ·
      refine ⟨12273363882402248664308785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16364485176536331552411713 12273363882402248664308785)
      ·
        refine ⟨9205022911801686498231589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12273363882402248664308785 9205022911801686498231589)
        ·
          refine ⟨1725941795962816218418423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9205022911801686498231589 1725941795962816218418423)
          ·
            refine ⟨2588912693944224327627635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1725941795962816218418423 2588912693944224327627635)
            ·
              refine ⟨3883369040916336491441453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2588912693944224327627635 3883369040916336491441453)
              ·
                refine ⟨1456263390343626184290545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3883369040916336491441453 1456263390343626184290545)
                ·
                  refine ⟨1092197542757719638217909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1456263390343626184290545 1092197542757719638217909)
                  ·
                    refine ⟨102393519633536216082929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1092197542757719638217909 102393519633536216082929)
                    ·
                      rfl

theorem cell23_598232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 2, 5].length) (baseStart_598232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598232 prefixEnd_598232 := by exact prefixLift 598232
  have htrace : WordTrace (prefixWord ++ tailWord_598232) baseStart_598232 baseEnd_598232 := by
    simpa [prefixWord, tailWord_598232, baseEnd_598232] using wordTrace_append hprefix tailTrace_598232
  have hstable : (prefixWord ++ tailWord_598232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598232).length < 2 ^ (prefixWord ++ tailWord_598232).sum := by decide
  have hdescent : baseEnd_598232 < baseStart_598232 := by decide
  rcases family_descends (prefixWord ++ tailWord_598232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598252 : List Nat := [2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 4]
def baseStart_598252 : Nat := 118140960795 + 598252 * 2 ^ 59
def prefixEnd_598252 : Nat := 4983230072969 + 3 ^ 40 * 598252 * 2
def baseEnd_598252 : Nat := 307190828513698569998695

theorem tailTrace_598252 : CollatzResearch.WordTrace tailWord_598252 prefixEnd_598252 307190828513698569998695 := by
  unfold tailWord_598252
  simp only [CollatzResearch.WordTrace]
  refine ⟨10910021514321326076138505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14546695352428434768184673 10910021514321326076138505)
  ·
    refine ⟨8182516135740994557103879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10910021514321326076138505 8182516135740994557103879)
    ·
      refine ⟨12273774203611491835655819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8182516135740994557103879 12273774203611491835655819)
      ·
        refine ⟨18410661305417237753483729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12273774203611491835655819 18410661305417237753483729)
        ·
          refine ⟨13807995979062928315112797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18410661305417237753483729 13807995979062928315112797)
          ·
            refine ⟨5177998492148598118167299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13807995979062928315112797 5177998492148598118167299)
            ·
              refine ⟨7766997738222897177250949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5177998492148598118167299 7766997738222897177250949)
              ·
                refine ⟨1456312075916793220734553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7766997738222897177250949 1456312075916793220734553)
                ·
                  refine ⟨1092234056937594915550915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1456312075916793220734553 1092234056937594915550915)
                  ·
                    refine ⟨1638351085406392373326373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1092234056937594915550915 1638351085406392373326373)
                    ·
                      refine ⟨307190828513698569998695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1638351085406392373326373 307190828513698569998695)
                      ·
                        rfl

theorem cell23_598252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 4].length) (baseStart_598252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598252 prefixEnd_598252 := by exact prefixLift 598252
  have htrace : WordTrace (prefixWord ++ tailWord_598252) baseStart_598252 baseEnd_598252 := by
    simpa [prefixWord, tailWord_598252, baseEnd_598252] using wordTrace_append hprefix tailTrace_598252
  have hstable : (prefixWord ++ tailWord_598252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598252).length < 2 ^ (prefixWord ++ tailWord_598252).sum := by decide
  have hdescent : baseEnd_598252 < baseStart_598252 := by decide
  rcases family_descends (prefixWord ++ tailWord_598252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598253 : List Nat := [1, 5, 1, 2, 3, 2, 2, 2, 5]
def baseStart_598253 : Nat := 118140960795 + 598253 * 2 ^ 59
def prefixEnd_598253 : Nat := 4983230072969 + 3 ^ 40 * 598253 * 2
def baseEnd_598253 : Nat := 34132371332705896231799

theorem tailTrace_598253 : CollatzResearch.WordTrace tailWord_598253 prefixEnd_598253 34132371332705896231799 := by
  unfold tailWord_598253
  simp only [CollatzResearch.WordTrace]
  refine ⟨21820079501639029323063413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14546719667759352882042275 21820079501639029323063413)
  ·
    refine ⟨2045632453278658999037195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21820079501639029323063413 2045632453278658999037195)
    ·
      refine ⟨3068448679917988498555793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2045632453278658999037195 3068448679917988498555793)
      ·
        refine ⟨2301336509938491373916845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3068448679917988498555793 2301336509938491373916845)
        ·
          refine ⟨863001191226934265218817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2301336509938491373916845 863001191226934265218817)
          ·
            refine ⟨647250893420200698914113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 863001191226934265218817 647250893420200698914113)
            ·
              refine ⟨485438170065150524185585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 647250893420200698914113 485438170065150524185585)
              ·
                refine ⟨364078627548862893139189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 485438170065150524185585 364078627548862893139189)
                ·
                  refine ⟨34132371332705896231799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 364078627548862893139189 34132371332705896231799)
                  ·
                    rfl

theorem cell23_598253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_598253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598253 prefixEnd_598253 := by exact prefixLift 598253
  have htrace : WordTrace (prefixWord ++ tailWord_598253) baseStart_598253 baseEnd_598253 := by
    simpa [prefixWord, tailWord_598253, baseEnd_598253] using wordTrace_append hprefix tailTrace_598253
  have hstable : (prefixWord ++ tailWord_598253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598253).length < 2 ^ (prefixWord ++ tailWord_598253).sum := by decide
  have hdescent : baseEnd_598253 < baseStart_598253 := by decide
  rcases family_descends (prefixWord ++ tailWord_598253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598265 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 4, 1, 6]
def baseStart_598265 : Nat := 118140960795 + 598265 * 2 ^ 59
def prefixEnd_598265 : Nat := 4983230072969 + 3 ^ 40 * 598265 * 2
def baseEnd_598265 : Nat := 307197503762207019136135

theorem tailTrace_598265 : CollatzResearch.WordTrace tailWord_598265 prefixEnd_598265 307197503762207019136135 := by
  unfold tailWord_598265
  simp only [CollatzResearch.WordTrace]
  refine ⟨21820517177595555372500249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14547011451730370248333499 21820517177595555372500249)
  ·
    refine ⟨16365387883196666529375187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21820517177595555372500249 16365387883196666529375187)
    ·
      refine ⟨24548081824794999794062781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16365387883196666529375187 24548081824794999794062781)
      ·
        refine ⟨9205530684298124922773543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24548081824794999794062781 9205530684298124922773543)
        ·
          refine ⟨13808296026447187384160315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9205530684298124922773543 13808296026447187384160315)
          ·
            refine ⟨20712444039670781076240473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13808296026447187384160315 20712444039670781076240473)
            ·
              refine ⟨15534333029753085807180355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20712444039670781076240473 15534333029753085807180355)
              ·
                refine ⟨23301499544629628710770533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15534333029753085807180355 23301499544629628710770533)
                ·
                  refine ⟨4369031164618055383269475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23301499544629628710770533 4369031164618055383269475)
                  ·
                    refine ⟨6553546746927083074904213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4369031164618055383269475 6553546746927083074904213)
                    ·
                      refine ⟨307197503762207019136135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6553546746927083074904213 307197503762207019136135)
                      ·
                        rfl

theorem cell23_598265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_598265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598265 prefixEnd_598265 := by exact prefixLift 598265
  have htrace : WordTrace (prefixWord ++ tailWord_598265) baseStart_598265 baseEnd_598265 := by
    simpa [prefixWord, tailWord_598265, baseEnd_598265] using wordTrace_append hprefix tailTrace_598265
  have hstable : (prefixWord ++ tailWord_598265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598265).length < 2 ^ (prefixWord ++ tailWord_598265).sum := by decide
  have hdescent : baseEnd_598265 < baseStart_598265 := by decide
  rcases family_descends (prefixWord ++ tailWord_598265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598272 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 3]
def baseStart_598272 : Nat := 118140960795 + 598272 * 2 ^ 59
def prefixEnd_598272 : Nat := 4983230072969 + 3 ^ 40 * 598272 * 2
def baseEnd_598272 : Nat := 307201098126788491748603

theorem tailTrace_598272 : CollatzResearch.WordTrace tailWord_598272 prefixEnd_598272 307201098126788491748603 := by
  unfold tailWord_598272
  simp only [CollatzResearch.WordTrace]
  refine ⟨10910386244285097784002535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14547181659046797045336713 10910386244285097784002535)
  ·
    refine ⟨16365579366427646676003803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10910386244285097784002535 16365579366427646676003803)
    ·
      refine ⟨24548369049641470014005705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16365579366427646676003803 24548369049641470014005705)
      ·
        refine ⟨18411276787231102510504279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24548369049641470014005705 18411276787231102510504279)
        ·
          refine ⟨27616915180846653765756419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18411276787231102510504279 27616915180846653765756419)
          ·
            refine ⟨41425372771269980648634629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27616915180846653765756419 41425372771269980648634629)
            ·
              refine ⟨7767257394613121371618993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41425372771269980648634629 7767257394613121371618993)
              ·
                refine ⟨5825443045959841028714245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7767257394613121371618993 5825443045959841028714245)
                ·
                  refine ⟨1092270571117470192883921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5825443045959841028714245 1092270571117470192883921)
                  ·
                    refine ⟨819202928338102644662941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1092270571117470192883921 819202928338102644662941)
                    ·
                      refine ⟨307201098126788491748603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 819202928338102644662941 307201098126788491748603)
                      ·
                        rfl

theorem cell23_598272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 3].length) (baseStart_598272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598272 prefixEnd_598272 := by exact prefixLift 598272
  have htrace : WordTrace (prefixWord ++ tailWord_598272) baseStart_598272 baseEnd_598272 := by
    simpa [prefixWord, tailWord_598272, baseEnd_598272] using wordTrace_append hprefix tailTrace_598272
  have hstable : (prefixWord ++ tailWord_598272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598272).length < 2 ^ (prefixWord ++ tailWord_598272).sum := by decide
  have hdescent : baseEnd_598272 < baseStart_598272 := by decide
  rcases family_descends (prefixWord ++ tailWord_598272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598289 : List Nat := [1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 3]
def baseStart_598289 : Nat := 118140960795 + 598289 * 2 ^ 59
def prefixEnd_598289 : Nat := 4983230072969 + 3 ^ 40 * 598289 * 2
def baseEnd_598289 : Nat := 307209827297914925236025

theorem tailTrace_598289 : CollatzResearch.WordTrace tailWord_598289 prefixEnd_598289 307209827297914925236025 := by
  unfold tailWord_598289
  simp only [CollatzResearch.WordTrace]
  refine ⟨21821392529508607471373921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14547595019672404980915947 21821392529508607471373921)
  ·
    refine ⟨16366044397131455603530441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21821392529508607471373921 16366044397131455603530441)
    ·
      refine ⟨12274533297848591702647831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16366044397131455603530441 12274533297848591702647831)
      ·
        refine ⟨18411799946772887553971747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12274533297848591702647831 18411799946772887553971747)
        ·
          refine ⟨27617699920159331330957621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18411799946772887553971747 27617699920159331330957621)
          ·
            refine ⟨2589159367514937312277277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27617699920159331330957621 2589159367514937312277277)
            ·
              refine ⟨970934762818101492103979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2589159367514937312277277 970934762818101492103979)
              ·
                refine ⟨1456402144227152238155969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 970934762818101492103979 1456402144227152238155969)
                ·
                  refine ⟨1092301608170364178616977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1456402144227152238155969 1092301608170364178616977)
                  ·
                    refine ⟨819226206127773133962733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1092301608170364178616977 819226206127773133962733)
                    ·
                      refine ⟨307209827297914925236025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 819226206127773133962733 307209827297914925236025)
                      ·
                        rfl

theorem cell23_598289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 3].length) (baseStart_598289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598289 prefixEnd_598289 := by exact prefixLift 598289
  have htrace : WordTrace (prefixWord ++ tailWord_598289) baseStart_598289 baseEnd_598289 := by
    simpa [prefixWord, tailWord_598289, baseEnd_598289] using wordTrace_append hprefix tailTrace_598289
  have hstable : (prefixWord ++ tailWord_598289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598289).length < 2 ^ (prefixWord ++ tailWord_598289).sum := by decide
  have hdescent : baseEnd_598289 < baseStart_598289 := by decide
  rcases family_descends (prefixWord ++ tailWord_598289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598296 : List Nat := [2, 1, 2, 3, 1, 2, 4, 3, 1, 4]
def baseStart_598296 : Nat := 118140960795 + 598296 * 2 ^ 59
def prefixEnd_598296 : Nat := 4983230072969 + 3 ^ 40 * 598296 * 2
def baseEnd_598296 : Nat := 102404473887498799282831

theorem tailTrace_598296 : CollatzResearch.WordTrace tailWord_598296 prefixEnd_598296 102404473887498799282831 := by
  unfold tailWord_598296
  simp only [CollatzResearch.WordTrace]
  refine ⟨10910823920241623833439371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14547765226988831777919161 10910823920241623833439371)
  ·
    refine ⟨16366235880362435750159057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10910823920241623833439371 16366235880362435750159057)
    ·
      refine ⟨12274676910271826812619293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16366235880362435750159057 12274676910271826812619293)
      ·
        refine ⟨4603003841351935054732235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12274676910271826812619293 4603003841351935054732235)
        ·
          refine ⟨6904505762027902582098353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4603003841351935054732235 6904505762027902582098353)
          ·
            refine ⟨5178379321520926936573765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6904505762027902582098353 5178379321520926936573765)
            ·
              refine ⟨970946122785173800607581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5178379321520926936573765 970946122785173800607581)
              ·
                refine ⟨364104796044440175227843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 970946122785173800607581 364104796044440175227843)
                ·
                  refine ⟨546157194066660262841765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 364104796044440175227843 546157194066660262841765)
                  ·
                    refine ⟨102404473887498799282831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 546157194066660262841765 102404473887498799282831)
                    ·
                      rfl

theorem cell23_598296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 3, 1, 4].length) (baseStart_598296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598296 prefixEnd_598296 := by exact prefixLift 598296
  have htrace : WordTrace (prefixWord ++ tailWord_598296) baseStart_598296 baseEnd_598296 := by
    simpa [prefixWord, tailWord_598296, baseEnd_598296] using wordTrace_append hprefix tailTrace_598296
  have hstable : (prefixWord ++ tailWord_598296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598296).length < 2 ^ (prefixWord ++ tailWord_598296).sum := by decide
  have hdescent : baseEnd_598296 < baseStart_598296 := by decide
  rcases family_descends (prefixWord ++ tailWord_598296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598319 : List Nat := [1, 1, 2, 1, 2, 1, 5, 3, 3, 1, 3]
def baseStart_598319 : Nat := 118140960795 + 598319 * 2 ^ 59
def prefixEnd_598319 : Nat := 4983230072969 + 3 ^ 40 * 598319 * 2
def baseEnd_598319 : Nat := 307225231717549807860887

theorem tailTrace_598319 : CollatzResearch.WordTrace tailWord_598319 prefixEnd_598319 307225231717549807860887 := by
  unfold tailWord_598319
  simp only [CollatzResearch.WordTrace]
  refine ⟨21822486719399922594966011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14548324479599948396644007 21822486719399922594966011)
  ·
    refine ⟨32733730079099883892449017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21822486719399922594966011 32733730079099883892449017)
    ·
      refine ⟨24550297559324912919336763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32733730079099883892449017 24550297559324912919336763)
      ·
        refine ⟨36825446338987369379005145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24550297559324912919336763 36825446338987369379005145)
        ·
          refine ⟨27619084754240527034253859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36825446338987369379005145 27619084754240527034253859)
          ·
            refine ⟨41428627131360790551380789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27619084754240527034253859 41428627131360790551380789)
            ·
              refine ⟨3883933793565074114191949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41428627131360790551380789 3883933793565074114191949)
              ·
                refine ⟨1456475172586902792821981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3883933793565074114191949 1456475172586902792821981)
                ·
                  refine ⟨546178189720088547308243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1456475172586902792821981 546178189720088547308243)
                  ·
                    refine ⟨819267284580132820962365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 546178189720088547308243 819267284580132820962365)
                    ·
                      refine ⟨307225231717549807860887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 819267284580132820962365 307225231717549807860887)
                      ·
                        rfl

theorem cell23_598319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 3, 1, 3].length) (baseStart_598319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598319 prefixEnd_598319 := by exact prefixLift 598319
  have htrace : WordTrace (prefixWord ++ tailWord_598319) baseStart_598319 baseEnd_598319 := by
    simpa [prefixWord, tailWord_598319, baseEnd_598319] using wordTrace_append hprefix tailTrace_598319
  have hstable : (prefixWord ++ tailWord_598319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598319).length < 2 ^ (prefixWord ++ tailWord_598319).sum := by decide
  have hdescent : baseEnd_598319 < baseStart_598319 := by decide
  rcases family_descends (prefixWord ++ tailWord_598319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598353 : List Nat := [1, 2, 2, 1, 4, 2, 3, 3, 1, 1, 3]
def baseStart_598353 : Nat := 118140960795 + 598353 * 2 ^ 59
def prefixEnd_598353 : Nat := 4983230072969 + 3 ^ 40 * 598353 * 2
def baseEnd_598353 : Nat := 307242690059802674835731

theorem tailTrace_598353 : CollatzResearch.WordTrace tailWord_598353 prefixEnd_598353 307242690059802674835731 := by
  unfold tailWord_598353
  simp only [CollatzResearch.WordTrace]
  refine ⟨21823726801276746401703713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14549151200851164267802475 21823726801276746401703713)
  ·
    refine ⟨16367795100957559801277785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21823726801276746401703713 16367795100957559801277785)
    ·
      refine ⟨12275846325718169850958339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16367795100957559801277785 12275846325718169850958339)
      ·
        refine ⟨18413769488577254776437509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12275846325718169850958339 18413769488577254776437509)
        ·
          refine ⟨3452581779108235270582033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18413769488577254776437509 3452581779108235270582033)
          ·
            refine ⟨2589436334331176452936525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3452581779108235270582033 2589436334331176452936525)
            ·
              refine ⟨971038625374191169851197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2589436334331176452936525 971038625374191169851197)
              ·
                refine ⟨364139484515321688694199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 971038625374191169851197 364139484515321688694199)
                ·
                  refine ⟨546209226772982533041299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 364139484515321688694199 546209226772982533041299)
                  ·
                    refine ⟨819313840159473799561949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 546209226772982533041299 819313840159473799561949)
                    ·
                      refine ⟨307242690059802674835731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 819313840159473799561949 307242690059802674835731)
                      ·
                        rfl

theorem cell23_598353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 3, 1, 1, 3].length) (baseStart_598353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598353 prefixEnd_598353 := by exact prefixLift 598353
  have htrace : WordTrace (prefixWord ++ tailWord_598353) baseStart_598353 baseEnd_598353 := by
    simpa [prefixWord, tailWord_598353, baseEnd_598353] using wordTrace_append hprefix tailTrace_598353
  have hstable : (prefixWord ++ tailWord_598353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598353).length < 2 ^ (prefixWord ++ tailWord_598353).sum := by decide
  have hdescent : baseEnd_598353 < baseStart_598353 := by decide
  rcases family_descends (prefixWord ++ tailWord_598353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598359 : List Nat := [1, 1, 3, 2, 3, 1, 1, 5, 1, 1, 4]
def baseStart_598359 : Nat := 118140960795 + 598359 * 2 ^ 59
def prefixEnd_598359 : Nat := 4983230072969 + 3 ^ 40 * 598359 * 2
def baseEnd_598359 : Nat := 307245770943729651360703

theorem tailTrace_598359 : CollatzResearch.WordTrace tailWord_598359 prefixEnd_598359 307245770943729651360703 := by
  unfold tailWord_598359
  simp only [CollatzResearch.WordTrace]
  refine ⟨21823945639255009426422131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14549297092836672950948087 21823945639255009426422131)
  ·
    refine ⟨32735918458882514139633197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21823945639255009426422131 32735918458882514139633197)
    ·
      refine ⟨12275969422080942802362449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32735918458882514139633197 12275969422080942802362449)
      ·
        refine ⟨9206977066560707101771837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12275969422080942802362449 9206977066560707101771837)
        ·
          refine ⟨3452616399960265163164439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9206977066560707101771837 3452616399960265163164439)
          ·
            refine ⟨5178924599940397744746659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3452616399960265163164439 5178924599940397744746659)
            ·
              refine ⟨7768386899910596617119989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5178924599940397744746659 7768386899910596617119989)
              ·
                refine ⟨728286271866618432854999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7768386899910596617119989 728286271866618432854999)
                ·
                  refine ⟨1092429407799927649282499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 728286271866618432854999 1092429407799927649282499)
                  ·
                    refine ⟨1638644111699891473923749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1092429407799927649282499 1638644111699891473923749)
                    ·
                      refine ⟨307245770943729651360703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1638644111699891473923749 307245770943729651360703)
                      ·
                        rfl

theorem cell23_598359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_598359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598359 prefixEnd_598359 := by exact prefixLift 598359
  have htrace : WordTrace (prefixWord ++ tailWord_598359) baseStart_598359 baseEnd_598359 := by
    simpa [prefixWord, tailWord_598359, baseEnd_598359] using wordTrace_append hprefix tailTrace_598359
  have hstable : (prefixWord ++ tailWord_598359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598359).length < 2 ^ (prefixWord ++ tailWord_598359).sum := by decide
  have hdescent : baseEnd_598359 < baseStart_598359 := by decide
  rcases family_descends (prefixWord ++ tailWord_598359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598372 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 3, 1, 6]
def baseStart_598372 : Nat := 118140960795 + 598372 * 2 ^ 59
def prefixEnd_598372 : Nat := 4983230072969 + 3 ^ 40 * 598372 * 2
def baseEnd_598372 : Nat := 307252446192238100498143

theorem tailTrace_598372 : CollatzResearch.WordTrace tailWord_598372 prefixEnd_598372 307252446192238100498143 := by
  unfold tailWord_598372
  simp only [CollatzResearch.WordTrace]
  refine ⟨10912209894103956323322685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14549613192138608431096913 10912209894103956323322685)
  ·
    refine ⟨4092078710288983621246007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10912209894103956323322685 4092078710288983621246007)
    ·
      refine ⟨6138118065433475431869011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4092078710288983621246007 6138118065433475431869011)
      ·
        refine ⟨9207177098150213147803517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6138118065433475431869011 9207177098150213147803517)
        ·
          refine ⟨3452691411806329930426319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9207177098150213147803517 3452691411806329930426319)
          ·
            refine ⟨5179037117709494895639479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3452691411806329930426319 5179037117709494895639479)
            ·
              refine ⟨7768555676564242343459219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5179037117709494895639479 7768555676564242343459219)
              ·
                refine ⟨11652833514846363515188829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7768555676564242343459219 11652833514846363515188829)
                ·
                  refine ⟨4369812568067386318195811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11652833514846363515188829 4369812568067386318195811)
                  ·
                    refine ⟨6554718852101079477293717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4369812568067386318195811 6554718852101079477293717)
                    ·
                      refine ⟨307252446192238100498143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6554718852101079477293717 307252446192238100498143)
                      ·
                        rfl

theorem cell23_598372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_598372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598372 prefixEnd_598372 := by exact prefixLift 598372
  have htrace : WordTrace (prefixWord ++ tailWord_598372) baseStart_598372 baseEnd_598372 := by
    simpa [prefixWord, tailWord_598372, baseEnd_598372] using wordTrace_append hprefix tailTrace_598372
  have hstable : (prefixWord ++ tailWord_598372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598372).length < 2 ^ (prefixWord ++ tailWord_598372).sum := by decide
  have hdescent : baseEnd_598372 < baseStart_598372 := by decide
  rcases family_descends (prefixWord ++ tailWord_598372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598386 : List Nat := [3, 2, 1, 2, 1, 4, 1, 3, 2, 4]
def baseStart_598386 : Nat := 118140960795 + 598386 * 2 ^ 59
def prefixEnd_598386 : Nat := 4983230072969 + 3 ^ 40 * 598386 * 2
def baseEnd_598386 : Nat := 102419878307133681907693

theorem tailTrace_598386 : CollatzResearch.WordTrace tailWord_598386 prefixEnd_598386 102419878307133681907693 := by
  unfold tailWord_598386
  simp only [CollatzResearch.WordTrace]
  refine ⟨5456232602539298259413753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14549953606771462025103341 5456232602539298259413753)
  ·
    refine ⟨4092174451904473694560315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5456232602539298259413753 4092174451904473694560315)
    ·
      refine ⟨6138261677856710541840473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4092174451904473694560315 6138261677856710541840473)
      ·
        refine ⟨4603696258392532906380355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6138261677856710541840473 4603696258392532906380355)
        ·
          refine ⟨6905544387588799359570533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4603696258392532906380355 6905544387588799359570533)
          ·
            refine ⟨1294789572672899879919475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6905544387588799359570533 1294789572672899879919475)
            ·
              refine ⟨1942184359009349819879213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1294789572672899879919475 1942184359009349819879213)
              ·
                refine ⟨728319134628506182454705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1942184359009349819879213 728319134628506182454705)
                ·
                  refine ⟨546239350971379636841029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 728319134628506182454705 546239350971379636841029)
                  ·
                    refine ⟨102419878307133681907693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 546239350971379636841029 102419878307133681907693)
                    ·
                      rfl

theorem cell23_598386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_598386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598386 prefixEnd_598386 := by exact prefixLift 598386
  have htrace : WordTrace (prefixWord ++ tailWord_598386) baseStart_598386 baseEnd_598386 := by
    simpa [prefixWord, tailWord_598386, baseEnd_598386] using wordTrace_append hprefix tailTrace_598386
  have hstable : (prefixWord ++ tailWord_598386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598386).length < 2 ^ (prefixWord ++ tailWord_598386).sum := by decide
  have hdescent : baseEnd_598386 < baseStart_598386 := by decide
  rcases family_descends (prefixWord ++ tailWord_598386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598389 : List Nat := [1, 3, 4, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_598389 : Nat := 118140960795 + 598389 * 2 ^ 59
def prefixEnd_598389 : Nat := 4983230072969 + 3 ^ 40 * 598389 * 2
def baseEnd_598389 : Nat := 307261175363364533985565

theorem tailTrace_598389 : CollatzResearch.WordTrace tailWord_598389 prefixEnd_598389 307261175363364533985565 := by
  unfold tailWord_598389
  simp only [CollatzResearch.WordTrace]
  refine ⟨21825039829146324550014221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14550026552764216366676147 21825039829146324550014221)
  ·
    refine ⟨8184389935929871706255333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21825039829146324550014221 8184389935929871706255333)
    ·
      refine ⟨1534573112986850944922875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8184389935929871706255333 1534573112986850944922875)
      ·
        refine ⟨2301859669480276417384313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1534573112986850944922875 2301859669480276417384313)
        ·
          refine ⟨1726394752110207313038235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2301859669480276417384313 1726394752110207313038235)
          ·
            refine ⟨2589592128165310969557353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1726394752110207313038235 2589592128165310969557353)
            ·
              refine ⟨1942194096123983227168015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2589592128165310969557353 1942194096123983227168015)
              ·
                refine ⟨2913291144185974840752023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1942194096123983227168015 2913291144185974840752023)
                ·
                  refine ⟨4369936716278962261128035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2913291144185974840752023 4369936716278962261128035)
                  ·
                    refine ⟨6554905074418443391692053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4369936716278962261128035 6554905074418443391692053)
                    ·
                      refine ⟨307261175363364533985565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6554905074418443391692053 307261175363364533985565)
                      ·
                        rfl

theorem cell23_598389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_598389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598389 prefixEnd_598389 := by exact prefixLift 598389
  have htrace : WordTrace (prefixWord ++ tailWord_598389) baseStart_598389 baseEnd_598389 := by
    simpa [prefixWord, tailWord_598389, baseEnd_598389] using wordTrace_append hprefix tailTrace_598389
  have hstable : (prefixWord ++ tailWord_598389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598389).length < 2 ^ (prefixWord ++ tailWord_598389).sum := by decide
  have hdescent : baseEnd_598389 < baseStart_598389 := by decide
  rcases family_descends (prefixWord ++ tailWord_598389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598390 : List Nat := [5, 1, 1, 4, 1, 2, 1, 2, 1, 5]
def baseStart_598390 : Nat := 118140960795 + 598390 * 2 ^ 59
def prefixEnd_598390 : Nat := 4983230072969 + 3 ^ 40 * 598390 * 2
def baseEnd_598390 : Nat := 102420562948006343357687

theorem tailTrace_598390 : CollatzResearch.WordTrace tailWord_598390 prefixEnd_598390 102420562948006343357687 := by
  unfold tailWord_598390
  simp only [CollatzResearch.WordTrace]
  refine ⟨1364067268883918857550039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14550050868095134480533749 1364067268883918857550039)
  ·
    refine ⟨2046100903325878286325059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1364067268883918857550039 2046100903325878286325059)
    ·
      refine ⟨3069151354988817429487589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2046100903325878286325059 3069151354988817429487589)
      ·
        refine ⟨575465879060403268028923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3069151354988817429487589 575465879060403268028923)
        ·
          refine ⟨863198818590604902043385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 575465879060403268028923 863198818590604902043385)
          ·
            refine ⟨647399113942953676532539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 863198818590604902043385 647399113942953676532539)
            ·
              refine ⟨971098670914430514798809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 647399113942953676532539 971098670914430514798809)
              ·
                refine ⟨728324003185822886099107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 971098670914430514798809 728324003185822886099107)
                ·
                  refine ⟨1092486004778734329148661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 728324003185822886099107 1092486004778734329148661)
                  ·
                    refine ⟨102420562948006343357687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1092486004778734329148661 102420562948006343357687)
                    ·
                      rfl

theorem cell23_598390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_598390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598390 prefixEnd_598390 := by exact prefixLift 598390
  have htrace : WordTrace (prefixWord ++ tailWord_598390) baseStart_598390 baseEnd_598390 := by
    simpa [prefixWord, tailWord_598390, baseEnd_598390] using wordTrace_append hprefix tailTrace_598390
  have hstable : (prefixWord ++ tailWord_598390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598390).length < 2 ^ (prefixWord ++ tailWord_598390).sum := by decide
  have hdescent : baseEnd_598390 < baseStart_598390 := by decide
  rcases family_descends (prefixWord ++ tailWord_598390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598409 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 3, 3, 3]
def baseStart_598409 : Nat := 118140960795 + 598409 * 2 ^ 59
def prefixEnd_598409 : Nat := 4983230072969 + 3 ^ 40 * 598409 * 2
def baseEnd_598409 : Nat := 307271444976454455735473

theorem tailTrace_598409 : CollatzResearch.WordTrace tailWord_598409 prefixEnd_598409 307271444976454455735473 := by
  unfold tailWord_598409
  simp only [CollatzResearch.WordTrace]
  refine ⟨21825769289073867965742281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14550512859382578643828187 21825769289073867965742281)
  ·
    refine ⟨16369326966805400974306711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21825769289073867965742281 16369326966805400974306711)
    ·
      refine ⟨24553990450208101461460067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16369326966805400974306711 24553990450208101461460067)
      ·
        refine ⟨36830985675312152192190101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24553990450208101461460067 36830985675312152192190101)
        ·
          refine ⟨1726452453530257134008911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36830985675312152192190101 1726452453530257134008911)
          ·
            refine ⟨2589678680295385701013367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1726452453530257134008911 2589678680295385701013367)
            ·
              refine ⟨3884518020443078551520051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2589678680295385701013367 3884518020443078551520051)
              ·
                refine ⟨5826777030664617827280077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3884518020443078551520051 5826777030664617827280077)
                ·
                  refine ⟨2185041386499231685230029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5826777030664617827280077 2185041386499231685230029)
                  ·
                    refine ⟨819390519937211881961261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2185041386499231685230029 819390519937211881961261)
                    ·
                      refine ⟨307271444976454455735473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 819390519937211881961261 307271444976454455735473)
                      ·
                        rfl

theorem cell23_598409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 3, 3].length) (baseStart_598409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598409 prefixEnd_598409 := by exact prefixLift 598409
  have htrace : WordTrace (prefixWord ++ tailWord_598409) baseStart_598409 baseEnd_598409 := by
    simpa [prefixWord, tailWord_598409, baseEnd_598409] using wordTrace_append hprefix tailTrace_598409
  have hstable : (prefixWord ++ tailWord_598409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598409).length < 2 ^ (prefixWord ++ tailWord_598409).sum := by decide
  have hdescent : baseEnd_598409 < baseStart_598409 := by decide
  rcases family_descends (prefixWord ++ tailWord_598409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598410 : List Nat := [3, 1, 2, 5, 1, 1, 3, 1, 1, 1, 4]
def baseStart_598410 : Nat := 118140960795 + 598410 * 2 ^ 59
def prefixEnd_598410 : Nat := 4983230072969 + 3 ^ 40 * 598410 * 2
def baseEnd_598410 : Nat := 307271958457108951822969

theorem tailTrace_598410 : CollatzResearch.WordTrace tailWord_598410 prefixEnd_598410 307271958457108951822969 := by
  unfold tailWord_598410
  simp only [CollatzResearch.WordTrace]
  refine ⟨5456451440517561284132171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14550537174713496757685789 5456451440517561284132171)
  ·
    refine ⟨8184677160776341926198257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5456451440517561284132171 8184677160776341926198257)
    ·
      refine ⟨6138507870582256444648693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8184677160776341926198257 6138507870582256444648693)
      ·
        refine ⟨575485112867086541685815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6138507870582256444648693 575485112867086541685815)
        ·
          refine ⟨863227669300629812528723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 575485112867086541685815 863227669300629812528723)
          ·
            refine ⟨1294841503950944718793085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 863227669300629812528723 1294841503950944718793085)
            ·
              refine ⟨485565563981604269547407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1294841503950944718793085 485565563981604269547407)
              ·
                refine ⟨728348345972406404321111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 485565563981604269547407 728348345972406404321111)
                ·
                  refine ⟨1092522518958609606481667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 728348345972406404321111 1092522518958609606481667)
                  ·
                    refine ⟨1638783778437914409722501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1092522518958609606481667 1638783778437914409722501)
                    ·
                      refine ⟨307271958457108951822969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1638783778437914409722501 307271958457108951822969)
                      ·
                        rfl

theorem cell23_598410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_598410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598410 prefixEnd_598410 := by exact prefixLift 598410
  have htrace : WordTrace (prefixWord ++ tailWord_598410) baseStart_598410 baseEnd_598410 := by
    simpa [prefixWord, tailWord_598410, baseEnd_598410] using wordTrace_append hprefix tailTrace_598410
  have hstable : (prefixWord ++ tailWord_598410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598410).length < 2 ^ (prefixWord ++ tailWord_598410).sum := by decide
  have hdescent : baseEnd_598410 < baseStart_598410 := by decide
  rcases family_descends (prefixWord ++ tailWord_598410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598433 : List Nat := [1, 2, 3, 5, 2, 1, 1, 8]
def baseStart_598433 : Nat := 118140960795 + 598433 * 2 ^ 59
def prefixEnd_598433 : Nat := 4983230072969 + 3 ^ 40 * 598433 * 2
def baseEnd_598433 : Nat := 11380880315265272660569

theorem tailTrace_598433 : CollatzResearch.WordTrace tailWord_598433 prefixEnd_598433 11380880315265272660569 := by
  unfold tailWord_598433
  simp only [CollatzResearch.WordTrace]
  refine ⟨21826644640986920064615953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14551096427324613376410635 21826644640986920064615953)
  ·
    refine ⟨16369983480740190048461965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21826644640986920064615953 16369983480740190048461965)
    ·
      refine ⟨6138743805277571268173237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16369983480740190048461965 6138743805277571268173237)
      ·
        refine ⟨575507231744772306391241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6138743805277571268173237 575507231744772306391241)
        ·
          refine ⟨431630423808579229793431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 575507231744772306391241 431630423808579229793431)
          ·
            refine ⟨647445635712868844690147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431630423808579229793431 647445635712868844690147)
            ·
              refine ⟨971168453569303267035221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 647445635712868844690147 971168453569303267035221)
              ·
                refine ⟨11380880315265272660569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 971168453569303267035221 11380880315265272660569)
                ·
                  rfl

theorem cell23_598433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 8].length) (baseStart_598433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598433 prefixEnd_598433 := by exact prefixLift 598433
  have htrace : WordTrace (prefixWord ++ tailWord_598433) baseStart_598433 baseEnd_598433 := by
    simpa [prefixWord, tailWord_598433, baseEnd_598433] using wordTrace_append hprefix tailTrace_598433
  have hstable : (prefixWord ++ tailWord_598433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598433).length < 2 ^ (prefixWord ++ tailWord_598433).sum := by decide
  have hdescent : baseEnd_598433 < baseStart_598433 := by decide
  rcases family_descends (prefixWord ++ tailWord_598433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598436 : List Nat := [2, 3, 1, 2, 1, 1, 3, 2, 3, 3, 2]
def baseStart_598436 : Nat := 118140960795 + 598436 * 2 ^ 59
def prefixEnd_598436 : Nat := 4983230072969 + 3 ^ 40 * 598436 * 2
def baseEnd_598436 : Nat := 307285308954125850097849

theorem tailTrace_598436 : CollatzResearch.WordTrace tailWord_598436 prefixEnd_598436 307285308954125850097849 := by
  unfold tailWord_598436
  simp only [CollatzResearch.WordTrace]
  refine ⟨10913377029988025788487581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14551169373317367717983441 10913377029988025788487581)
  ·
    refine ⟨4092516386245509670682843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10913377029988025788487581 4092516386245509670682843)
    ·
      refine ⟨6138774579368264506024265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4092516386245509670682843 6138774579368264506024265)
      ·
        refine ⟨4604080934526198379518199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6138774579368264506024265 4604080934526198379518199)
        ·
          refine ⟨6906121401789297569277299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4604080934526198379518199 6906121401789297569277299)
          ·
            refine ⟨10359182102683946353915949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6906121401789297569277299 10359182102683946353915949)
            ·
              refine ⟨3884693288506479882718481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10359182102683946353915949 3884693288506479882718481)
              ·
                refine ⟨2913519966379859912038861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3884693288506479882718481 2913519966379859912038861)
                ·
                  refine ⟨1092569987392447467014573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2913519966379859912038861 1092569987392447467014573)
                  ·
                    refine ⟨409713745272167800130465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1092569987392447467014573 409713745272167800130465)
                    ·
                      refine ⟨307285308954125850097849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 409713745272167800130465 307285308954125850097849)
                      ·
                        rfl

theorem cell23_598436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_598436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598436 prefixEnd_598436 := by exact prefixLift 598436
  have htrace : WordTrace (prefixWord ++ tailWord_598436) baseStart_598436 baseEnd_598436 := by
    simpa [prefixWord, tailWord_598436, baseEnd_598436] using wordTrace_append hprefix tailTrace_598436
  have hstable : (prefixWord ++ tailWord_598436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598436).length < 2 ^ (prefixWord ++ tailWord_598436).sum := by decide
  have hdescent : baseEnd_598436 < baseStart_598436 := by decide
  rcases family_descends (prefixWord ++ tailWord_598436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598489 : List Nat := [1, 2, 1, 2, 4, 1, 4, 1, 7]
def baseStart_598489 : Nat := 118140960795 + 598489 * 2 ^ 59
def prefixEnd_598489 : Nat := 4983230072969 + 3 ^ 40 * 598489 * 2
def baseEnd_598489 : Nat := 34145835936534904748345

theorem tailTrace_598489 : CollatzResearch.WordTrace tailWord_598489 prefixEnd_598489 34145835936534904748345 := by
  unfold tailWord_598489
  simp only [CollatzResearch.WordTrace]
  refine ⟨21828687128784041628654521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14552458085856027752436347 21828687128784041628654521)
  ·
    refine ⟨16371515346588031221490891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21828687128784041628654521 16371515346588031221490891)
    ·
      refine ⟨24557273019882046832236337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16371515346588031221490891 24557273019882046832236337)
      ·
        refine ⟨18417954764911535124177253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24557273019882046832236337 18417954764911535124177253)
        ·
          refine ⟨3453366518420912835783235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18417954764911535124177253 3453366518420912835783235)
          ·
            refine ⟨5180049777631369253674853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3453366518420912835783235 5180049777631369253674853)
            ·
              refine ⟨971259333305881735064035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5180049777631369253674853 971259333305881735064035)
              ·
                refine ⟨1456888999958822602596053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 971259333305881735064035 1456888999958822602596053)
                ·
                  refine ⟨34145835936534904748345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1456888999958822602596053 34145835936534904748345)
                  ·
                    rfl

theorem cell23_598489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 7].length) (baseStart_598489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598489 prefixEnd_598489 := by exact prefixLift 598489
  have htrace : WordTrace (prefixWord ++ tailWord_598489) baseStart_598489 baseEnd_598489 := by
    simpa [prefixWord, tailWord_598489, baseEnd_598489] using wordTrace_append hprefix tailTrace_598489
  have hstable : (prefixWord ++ tailWord_598489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598489).length < 2 ^ (prefixWord ++ tailWord_598489).sum := by decide
  have hdescent : baseEnd_598489 < baseStart_598489 := by decide
  rcases family_descends (prefixWord ++ tailWord_598489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598534 : List Nat := [6, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2]
def baseStart_598534 : Nat := 118140960795 + 598534 * 2 ^ 59
def prefixEnd_598534 : Nat := 4983230072969 + 3 ^ 40 * 598534 * 2
def baseEnd_598534 : Nat := 307335630058266466672399

theorem tailTrace_598534 : CollatzResearch.WordTrace tailWord_598534 prefixEnd_598534 307335630058266466672399 := by
  unfold tailWord_598534
  simp only [CollatzResearch.WordTrace]
  refine ⟨682197762925656697313833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14553552275747342876028437 682197762925656697313833)
  ·
    refine ⟨511648322194242522985375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 682197762925656697313833 511648322194242522985375)
    ·
      refine ⟨767472483291363784478063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 511648322194242522985375 767472483291363784478063)
      ·
        refine ⟨1151208724937045676717095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 767472483291363784478063 1151208724937045676717095)
        ·
          refine ⟨1726813087405568515075643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1151208724937045676717095 1726813087405568515075643)
          ·
            refine ⟨2590219631108352772613465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1726813087405568515075643 2590219631108352772613465)
            ·
              refine ⟨1942664723331264579460099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2590219631108352772613465 1942664723331264579460099)
              ·
                refine ⟨2913997084996896869190149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1942664723331264579460099 2913997084996896869190149)
                ·
                  refine ⟨546374453436918162973153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2913997084996896869190149 546374453436918162973153)
                  ·
                    refine ⟨409780840077688622229865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 546374453436918162973153 409780840077688622229865)
                    ·
                      refine ⟨307335630058266466672399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 409780840077688622229865 307335630058266466672399)
                      ·
                        rfl

theorem cell23_598534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_598534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598534 prefixEnd_598534 := by exact prefixLift 598534
  have htrace : WordTrace (prefixWord ++ tailWord_598534) baseStart_598534 baseEnd_598534 := by
    simpa [prefixWord, tailWord_598534, baseEnd_598534] using wordTrace_append hprefix tailTrace_598534
  have hstable : (prefixWord ++ tailWord_598534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598534).length < 2 ^ (prefixWord ++ tailWord_598534).sum := by decide
  have hdescent : baseEnd_598534 < baseStart_598534 := by decide
  rcases family_descends (prefixWord ++ tailWord_598534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598551 : List Nat := [1, 1, 3, 6, 2, 1, 2, 1, 2, 2, 2]
def baseStart_598551 : Nat := 118140960795 + 598551 * 2 ^ 59
def prefixEnd_598551 : Nat := 4983230072969 + 3 ^ 40 * 598551 * 2
def baseEnd_598551 : Nat := 307344359229392900159821

theorem tailTrace_598551 : CollatzResearch.WordTrace tailWord_598551 prefixEnd_598551 307344359229392900159821 := by
  unfold tailWord_598551
  simp only [CollatzResearch.WordTrace]
  refine ⟨21830948454559426217411507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14553965636372950811607671 21830948454559426217411507)
  ·
    refine ⟨32746422681839139326117261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21830948454559426217411507 32746422681839139326117261)
    ·
      refine ⟨12279908505689677247293973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32746422681839139326117261 12279908505689677247293973)
      ·
        refine ⟨575620711204203620966905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12279908505689677247293973 575620711204203620966905)
        ·
          refine ⟨431715533403152715725179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 575620711204203620966905 431715533403152715725179)
          ·
            refine ⟨647573300104729073587769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431715533403152715725179 647573300104729073587769)
            ·
              refine ⟨485679975078546805190827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 647573300104729073587769 485679975078546805190827)
              ·
                refine ⟨728519962617820207786241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 485679975078546805190827 728519962617820207786241)
                ·
                  refine ⟨546389971963365155839681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 728519962617820207786241 546389971963365155839681)
                  ·
                    refine ⟨409792478972523866879761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 546389971963365155839681 409792478972523866879761)
                    ·
                      refine ⟨307344359229392900159821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 409792478972523866879761 307344359229392900159821)
                      ·
                        rfl

theorem cell23_598551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_598551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598551 prefixEnd_598551 := by exact prefixLift 598551
  have htrace : WordTrace (prefixWord ++ tailWord_598551) baseStart_598551 baseEnd_598551 := by
    simpa [prefixWord, tailWord_598551, baseEnd_598551] using wordTrace_append hprefix tailTrace_598551
  have hstable : (prefixWord ++ tailWord_598551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598551).length < 2 ^ (prefixWord ++ tailWord_598551).sum := by decide
  have hdescent : baseEnd_598551 < baseStart_598551 := by decide
  rcases family_descends (prefixWord ++ tailWord_598551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598576 : List Nat := [2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 3]
def baseStart_598576 : Nat := 118140960795 + 598576 * 2 ^ 59
def prefixEnd_598576 : Nat := 4983230072969 + 3 ^ 40 * 598576 * 2
def baseEnd_598576 : Nat := 307357196245755302347205

theorem tailTrace_598576 : CollatzResearch.WordTrace tailWord_598576 prefixEnd_598576 307357196245755302347205 := by
  unfold tailWord_598576
  simp only [CollatzResearch.WordTrace]
  refine ⟨10915930139734427743535791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14554573519645903658047721 10915930139734427743535791)
  ·
    refine ⟨16373895209601641615303687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10915930139734427743535791 16373895209601641615303687)
    ·
      refine ⟨24560842814402462422955531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16373895209601641615303687 24560842814402462422955531)
      ·
        refine ⟨36841264221603693634433297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24560842814402462422955531 36841264221603693634433297)
        ·
          refine ⟨27630948166202770225824973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36841264221603693634433297 27630948166202770225824973)
          ·
            refine ⟨10361605562326038834684365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27630948166202770225824973 10361605562326038834684365)
            ·
              refine ⟨3885602085872264563006637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10361605562326038834684365 3885602085872264563006637)
              ·
                refine ⟨1457100782202099211127489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3885602085872264563006637 1457100782202099211127489)
                ·
                  refine ⟨1092825586651574408345617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1457100782202099211127489 1092825586651574408345617)
                  ·
                    refine ⟨819619189988680806259213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1092825586651574408345617 819619189988680806259213)
                    ·
                      refine ⟨307357196245755302347205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 819619189988680806259213 307357196245755302347205)
                      ·
                        rfl

theorem cell23_598576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 3].length) (baseStart_598576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598576 prefixEnd_598576 := by exact prefixLift 598576
  have htrace : WordTrace (prefixWord ++ tailWord_598576) baseStart_598576 baseEnd_598576 := by
    simpa [prefixWord, tailWord_598576, baseEnd_598576] using wordTrace_append hprefix tailTrace_598576
  have hstable : (prefixWord ++ tailWord_598576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598576).length < 2 ^ (prefixWord ++ tailWord_598576).sum := by decide
  have hdescent : baseEnd_598576 < baseStart_598576 := by decide
  rcases family_descends (prefixWord ++ tailWord_598576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598583 : List Nat := [1, 1, 3, 1, 2, 3, 2, 5, 1, 4]
def baseStart_598583 : Nat := 118140960795 + 598583 * 2 ^ 59
def prefixEnd_598583 : Nat := 4983230072969 + 3 ^ 40 * 598583 * 2
def baseEnd_598583 : Nat := 102453596870112258319891

theorem tailTrace_598583 : CollatzResearch.WordTrace tailWord_598583 prefixEnd_598583 102453596870112258319891 := by
  unfold tailWord_598583
  simp only [CollatzResearch.WordTrace]
  refine ⟨21832115590443495682576403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14554743726962330455050935 21832115590443495682576403)
  ·
    refine ⟨32748173385665243523864605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21832115590443495682576403 32748173385665243523864605)
    ·
      refine ⟨12280565019624466321449227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32748173385665243523864605 12280565019624466321449227)
      ·
        refine ⟨18420847529436699482173841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12280565019624466321449227 18420847529436699482173841)
        ·
          refine ⟨13815635647077524611630381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18420847529436699482173841 13815635647077524611630381)
          ·
            refine ⟨5180863367654071729361393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13815635647077524611630381 5180863367654071729361393)
            ·
              refine ⟨3885647525740553797021045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5180863367654071729361393 3885647525740553797021045)
              ·
                refine ⟨364279455538176918470723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3885647525740553797021045 364279455538176918470723)
                ·
                  refine ⟨546419183307265377706085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 364279455538176918470723 546419183307265377706085)
                  ·
                    refine ⟨102453596870112258319891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 546419183307265377706085 102453596870112258319891)
                    ·
                      rfl

theorem cell23_598583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 5, 1, 4].length) (baseStart_598583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598583 prefixEnd_598583 := by exact prefixLift 598583
  have htrace : WordTrace (prefixWord ++ tailWord_598583) baseStart_598583 baseEnd_598583 := by
    simpa [prefixWord, tailWord_598583, baseEnd_598583] using wordTrace_append hprefix tailTrace_598583
  have hstable : (prefixWord ++ tailWord_598583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598583).length < 2 ^ (prefixWord ++ tailWord_598583).sum := by decide
  have hdescent : baseEnd_598583 < baseStart_598583 := by decide
  rcases family_descends (prefixWord ++ tailWord_598583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598593 : List Nat := [1, 2, 5, 1, 1, 2, 2, 2, 2, 2, 3]
def baseStart_598593 : Nat := 118140960795 + 598593 * 2 ^ 59
def prefixEnd_598593 : Nat := 4983230072969 + 3 ^ 40 * 598593 * 2
def baseEnd_598593 : Nat := 307365925416881735834627

theorem tailTrace_598593 : CollatzResearch.WordTrace tailWord_598593 prefixEnd_598593 307365925416881735834627 := by
  unfold tailWord_598593
  simp only [CollatzResearch.WordTrace]
  refine ⟨21832480320407267390440433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14554986880271511593626955 21832480320407267390440433)
  ·
    refine ⟨16374360240305450542830325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21832480320407267390440433 16374360240305450542830325)
    ·
      refine ⟨1535096272528635988390343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16374360240305450542830325 1535096272528635988390343)
      ·
        refine ⟨2302644408792953982585515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1535096272528635988390343 2302644408792953982585515)
        ·
          refine ⟨3453966613189430973878273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2302644408792953982585515 3453966613189430973878273)
          ·
            refine ⟨2590474959892073230408705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3453966613189430973878273 2590474959892073230408705)
            ·
              refine ⟨1942856219919054922806529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2590474959892073230408705 1942856219919054922806529)
              ·
                refine ⟨1457142164939291192104897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1942856219919054922806529 1457142164939291192104897)
                ·
                  refine ⟨1092856623704468394078673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1457142164939291192104897 1092856623704468394078673)
                  ·
                    refine ⟨819642467778351295559005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1092856623704468394078673 819642467778351295559005)
                    ·
                      refine ⟨307365925416881735834627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 819642467778351295559005 307365925416881735834627)
                      ·
                        rfl

theorem cell23_598593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_598593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598593 prefixEnd_598593 := by exact prefixLift 598593
  have htrace : WordTrace (prefixWord ++ tailWord_598593) baseStart_598593 baseEnd_598593 := by
    simpa [prefixWord, tailWord_598593, baseEnd_598593] using wordTrace_append hprefix tailTrace_598593
  have hstable : (prefixWord ++ tailWord_598593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598593).length < 2 ^ (prefixWord ++ tailWord_598593).sum := by decide
  have hdescent : baseEnd_598593 < baseStart_598593 := by decide
  rcases family_descends (prefixWord ++ tailWord_598593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598680 : List Nat := [2, 1, 2, 4, 1, 1, 1, 4, 3, 2, 2]
def baseStart_598680 : Nat := 118140960795 + 598680 * 2 ^ 59
def prefixEnd_598680 : Nat := 4983230072969 + 3 ^ 40 * 598680 * 2
def baseEnd_598680 : Nat := 307410598233822895446727

theorem tailTrace_598680 : CollatzResearch.WordTrace tailWord_598680 prefixEnd_598680 307410598233822895446727 := by
  unfold tailWord_598680
  simp only [CollatzResearch.WordTrace]
  refine ⟨10917826735546040624428747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14557102314061387499238329 10917826735546040624428747)
  ·
    refine ⟨16376740103319060936643121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10917826735546040624428747 16376740103319060936643121)
    ·
      refine ⟨12282555077489295702482341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16376740103319060936643121 12282555077489295702482341)
      ·
        refine ⟨2302979077029242944215439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12282555077489295702482341 2302979077029242944215439)
        ·
          refine ⟨3454468615543864416323159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2302979077029242944215439 3454468615543864416323159)
          ·
            refine ⟨5181702923315796624484739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3454468615543864416323159 5181702923315796624484739)
            ·
              refine ⟨7772554384973694936727109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5181702923315796624484739 7772554384973694936727109)
              ·
                refine ⟨1457353947182567800636333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7772554384973694936727109 1457353947182567800636333)
                ·
                  refine ⟨546507730193462925238625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1457353947182567800636333 546507730193462925238625)
                  ·
                    refine ⟨409880797645097193928969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 546507730193462925238625 409880797645097193928969)
                    ·
                      refine ⟨307410598233822895446727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 409880797645097193928969 307410598233822895446727)
                      ·
                        rfl

theorem cell23_598680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_598680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598680 prefixEnd_598680 := by exact prefixLift 598680
  have htrace : WordTrace (prefixWord ++ tailWord_598680) baseStart_598680 baseEnd_598680 := by
    simpa [prefixWord, tailWord_598680, baseEnd_598680] using wordTrace_append hprefix tailTrace_598680
  have hstable : (prefixWord ++ tailWord_598680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598680).length < 2 ^ (prefixWord ++ tailWord_598680).sum := by decide
  have hdescent : baseEnd_598680 < baseStart_598680 := by decide
  rcases family_descends (prefixWord ++ tailWord_598680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598714 : List Nat := [3, 1, 1, 1, 2, 3, 5, 2, 1, 2, 2]
def baseStart_598714 : Nat := 118140960795 + 598714 * 2 ^ 59
def prefixEnd_598714 : Nat := 4983230072969 + 3 ^ 40 * 598714 * 2
def baseEnd_598714 : Nat := 307428056576075762421571

theorem tailTrace_598714 : CollatzResearch.WordTrace tailWord_598714 prefixEnd_598714 307428056576075762421571 := by
  unfold tailWord_598714
  simp only [CollatzResearch.WordTrace]
  refine ⟨5459223388242226263898799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14557929035312603370396797 5459223388242226263898799)
  ·
    refine ⟨8188835082363339395848199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5459223388242226263898799 8188835082363339395848199)
    ·
      refine ⟨12283252623545009093772299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8188835082363339395848199 12283252623545009093772299)
      ·
        refine ⟨18424878935317513640658449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12283252623545009093772299 18424878935317513640658449)
        ·
          refine ⟨13818659201488135230493837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18424878935317513640658449 13818659201488135230493837)
          ·
            refine ⟨5181997200558050711435189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13818659201488135230493837 5181997200558050711435189)
            ·
              refine ⟨485812237552317254197049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5181997200558050711435189 485812237552317254197049)
              ·
                refine ⟨364359178164237940647787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 485812237552317254197049 364359178164237940647787)
                ·
                  refine ⟨546538767246356910971681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 364359178164237940647787 546538767246356910971681)
                  ·
                    refine ⟨409904075434767683228761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 546538767246356910971681 409904075434767683228761)
                    ·
                      refine ⟨307428056576075762421571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 409904075434767683228761 307428056576075762421571)
                      ·
                        rfl

theorem cell23_598714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 2, 1, 2, 2].length) (baseStart_598714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598714 prefixEnd_598714 := by exact prefixLift 598714
  have htrace : WordTrace (prefixWord ++ tailWord_598714) baseStart_598714 baseEnd_598714 := by
    simpa [prefixWord, tailWord_598714, baseEnd_598714] using wordTrace_append hprefix tailTrace_598714
  have hstable : (prefixWord ++ tailWord_598714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598714).length < 2 ^ (prefixWord ++ tailWord_598714).sum := by decide
  have hdescent : baseEnd_598714 < baseStart_598714 := by decide
  rcases family_descends (prefixWord ++ tailWord_598714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598716 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 2, 7]
def baseStart_598716 : Nat := 118140960795 + 598716 * 2 ^ 59
def prefixEnd_598716 : Nat := 4983230072969 + 3 ^ 40 * 598716 * 2
def baseEnd_598716 : Nat := 102476361179128251532187

theorem tailTrace_598716 : CollatzResearch.WordTrace tailWord_598716 prefixEnd_598716 102476361179128251532187 := by
  unfold tailWord_598716
  simp only [CollatzResearch.WordTrace]
  refine ⟨10918483249480829698584001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14557977665974439598112001 10918483249480829698584001)
  ·
    refine ⟨8188862437110622273938001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10918483249480829698584001 8188862437110622273938001)
    ·
      refine ⟨6141646827832966705453501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8188862437110622273938001 6141646827832966705453501)
      ·
        refine ⟨2303117560437362514545063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6141646827832966705453501 2303117560437362514545063)
        ·
          refine ⟨3454676340656043771817595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2303117560437362514545063 3454676340656043771817595)
          ·
            refine ⟨5182014510984065657726393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3454676340656043771817595 5182014510984065657726393)
            ·
              refine ⟨3886510883238049243294795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5182014510984065657726393 3886510883238049243294795)
              ·
                refine ⟨5829766324857073864942193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3886510883238049243294795 5829766324857073864942193)
                ·
                  refine ⟨4372324743642805398706645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5829766324857073864942193 4372324743642805398706645)
                  ·
                    refine ⟨102476361179128251532187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4372324743642805398706645 102476361179128251532187)
                    ·
                      rfl

theorem cell23_598716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_598716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598716 prefixEnd_598716 := by exact prefixLift 598716
  have htrace : WordTrace (prefixWord ++ tailWord_598716) baseStart_598716 baseEnd_598716 := by
    simpa [prefixWord, tailWord_598716, baseEnd_598716] using wordTrace_append hprefix tailTrace_598716
  have hstable : (prefixWord ++ tailWord_598716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598716).length < 2 ^ (prefixWord ++ tailWord_598716).sum := by decide
  have hdescent : baseEnd_598716 < baseStart_598716 := by decide
  rcases family_descends (prefixWord ++ tailWord_598716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598776 : List Nat := [2, 1, 2, 1, 1, 2, 4, 3, 7]
def baseStart_598776 : Nat := 118140960795 + 598776 * 2 ^ 59
def prefixEnd_598776 : Nat := 4983230072969 + 3 ^ 40 * 598776 * 2
def baseEnd_598776 : Nat := 34162210264072724427365

theorem tailTrace_598776 : CollatzResearch.WordTrace tailWord_598776 prefixEnd_598776 34162210264072724427365 := by
  unfold tailWord_598776
  simp only [CollatzResearch.WordTrace]
  refine ⟨10919577439372144822176091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14559436585829526429568121 10919577439372144822176091)
  ·
    refine ⟨16379366159058217233264137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10919577439372144822176091 16379366159058217233264137)
    ·
      refine ⟨12284524619293662924948103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16379366159058217233264137 12284524619293662924948103)
      ·
        refine ⟨18426786928940494387422155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12284524619293662924948103 18426786928940494387422155)
        ·
          refine ⟨27640180393410741581133233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18426786928940494387422155 27640180393410741581133233)
          ·
            refine ⟨20730135295058056185849925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27640180393410741581133233 20730135295058056185849925)
            ·
              refine ⟨3886900367823385534846861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20730135295058056185849925 3886900367823385534846861)
              ·
                refine ⟨1457587637933769575567573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3886900367823385534846861 1457587637933769575567573)
                ·
                  refine ⟨34162210264072724427365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1457587637933769575567573 34162210264072724427365)
                  ·
                    rfl

theorem cell23_598776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 7].length) (baseStart_598776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598776 prefixEnd_598776 := by exact prefixLift 598776
  have htrace : WordTrace (prefixWord ++ tailWord_598776) baseStart_598776 baseEnd_598776 := by
    simpa [prefixWord, tailWord_598776, baseEnd_598776] using wordTrace_append hprefix tailTrace_598776
  have hstable : (prefixWord ++ tailWord_598776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598776).length < 2 ^ (prefixWord ++ tailWord_598776).sum := by decide
  have hdescent : baseEnd_598776 < baseStart_598776 := by decide
  rcases family_descends (prefixWord ++ tailWord_598776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598810 : List Nat := [3, 1, 1, 3, 2, 1, 4, 3, 5]
def baseStart_598810 : Nat := 118140960795 + 598810 * 2 ^ 59
def prefixEnd_598810 : Nat := 4983230072969 + 3 ^ 40 * 598810 * 2
def baseEnd_598810 : Nat := 34164150079878598535681

theorem tailTrace_598810 : CollatzResearch.WordTrace tailWord_598810 prefixEnd_598810 34164150079878598535681 := by
  unfold tailWord_598810
  simp only [CollatzResearch.WordTrace]
  refine ⟨5460098740155278362772471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14560263307080742300726589 5460098740155278362772471)
  ·
    refine ⟨8190148110232917544158707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5460098740155278362772471 8190148110232917544158707)
    ·
      refine ⟨12285222165349376316238061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8190148110232917544158707 12285222165349376316238061)
      ·
        refine ⟨4606958312006016118589273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12285222165349376316238061 4606958312006016118589273)
        ·
          refine ⟨3455218734004512088941955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4606958312006016118589273 3455218734004512088941955)
          ·
            refine ⟨5182828101006768133412933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3455218734004512088941955 5182828101006768133412933)
            ·
              refine ⟨971780268938769025014925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5182828101006768133412933 971780268938769025014925)
              ·
                refine ⟨364417600852038384380597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 971780268938769025014925 364417600852038384380597)
                ·
                  refine ⟨34164150079878598535681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 364417600852038384380597 34164150079878598535681)
                  ·
                    rfl

theorem cell23_598810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 3, 5].length) (baseStart_598810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598810 prefixEnd_598810 := by exact prefixLift 598810
  have htrace : WordTrace (prefixWord ++ tailWord_598810) baseStart_598810 baseEnd_598810 := by
    simpa [prefixWord, tailWord_598810, baseEnd_598810] using wordTrace_append hprefix tailTrace_598810
  have hstable : (prefixWord ++ tailWord_598810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598810).length < 2 ^ (prefixWord ++ tailWord_598810).sum := by decide
  have hdescent : baseEnd_598810 < baseStart_598810 := by decide
  rcases family_descends (prefixWord ++ tailWord_598810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598838 : List Nat := [5, 1, 2, 2, 2, 1, 3, 1, 2, 2, 2]
def baseStart_598838 : Nat := 118140960795 + 598838 * 2 ^ 59
def prefixEnd_598838 : Nat := 4983230072969 + 3 ^ 40 * 598838 * 2
def baseEnd_598838 : Nat := 307491728177233277271001

theorem tailTrace_598838 : CollatzResearch.WordTrace tailWord_598838 prefixEnd_598838 307491728177233277271001 := by
  unfold tailWord_598838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1365088512782479639569323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14560944136346449488739445 1365088512782479639569323)
  ·
    refine ⟨2047632769173719459353985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1365088512782479639569323 2047632769173719459353985)
    ·
      refine ⟨1535724576880289594515489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2047632769173719459353985 1535724576880289594515489)
      ·
        refine ⟨1151793432660217195886617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1535724576880289594515489 1151793432660217195886617)
        ·
          refine ⟨863845074495162896914963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1151793432660217195886617 863845074495162896914963)
          ·
            refine ⟨1295767611742744345372445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 863845074495162896914963 1295767611742744345372445)
            ·
              refine ⟨485912854403529129514667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1295767611742744345372445 485912854403529129514667)
              ·
                refine ⟨728869281605293694272001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 485912854403529129514667 728869281605293694272001)
                ·
                  refine ⟨546651961203970270704001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 728869281605293694272001 546651961203970270704001)
                  ·
                    refine ⟨409988970902977703028001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 546651961203970270704001 409988970902977703028001)
                    ·
                      refine ⟨307491728177233277271001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 409988970902977703028001 307491728177233277271001)
                      ·
                        rfl

theorem cell23_598838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_598838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598838 prefixEnd_598838 := by exact prefixLift 598838
  have htrace : WordTrace (prefixWord ++ tailWord_598838) baseStart_598838 baseEnd_598838 := by
    simpa [prefixWord, tailWord_598838, baseEnd_598838] using wordTrace_append hprefix tailTrace_598838
  have hstable : (prefixWord ++ tailWord_598838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598838).length < 2 ^ (prefixWord ++ tailWord_598838).sum := by decide
  have hdescent : baseEnd_598838 < baseStart_598838 := by decide
  rcases family_descends (prefixWord ++ tailWord_598838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598853 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 5, 4]
def baseStart_598853 : Nat := 118140960795 + 598853 * 2 ^ 59
def prefixEnd_598853 : Nat := 4983230072969 + 3 ^ 40 * 598853 * 2
def baseEnd_598853 : Nat := 102499810129016906194477

theorem tailTrace_598853 : CollatzResearch.WordTrace tailWord_598853 prefixEnd_598853 102499810129016906194477 := by
  unfold tailWord_598853
  simp only [CollatzResearch.WordTrace]
  refine ⟨21841963299465331794905213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14561308866310221196603475 21841963299465331794905213)
  ·
    refine ⟨8190736237299499423089455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21841963299465331794905213 8190736237299499423089455)
    ·
      refine ⟨12286104355949249134634183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8190736237299499423089455 12286104355949249134634183)
      ·
        refine ⟨18429156533923873701951275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12286104355949249134634183 18429156533923873701951275)
        ·
          refine ⟨27643734800885810552926913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18429156533923873701951275 27643734800885810552926913)
          ·
            refine ⟨20732801100664357914695185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27643734800885810552926913 20732801100664357914695185)
            ·
              refine ⟨15549600825498268436021389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20732801100664357914695185 15549600825498268436021389)
              ·
                refine ⟨5831100309561850663508021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15549600825498268436021389 5831100309561850663508021)
                ·
                  refine ⟨546665654021423499703877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5831100309561850663508021 546665654021423499703877)
                  ·
                    refine ⟨102499810129016906194477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 546665654021423499703877 102499810129016906194477)
                    ·
                      rfl

theorem cell23_598853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 5, 4].length) (baseStart_598853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598853 prefixEnd_598853 := by exact prefixLift 598853
  have htrace : WordTrace (prefixWord ++ tailWord_598853) baseStart_598853 baseEnd_598853 := by
    simpa [prefixWord, tailWord_598853, baseEnd_598853] using wordTrace_append hprefix tailTrace_598853
  have hstable : (prefixWord ++ tailWord_598853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598853).length < 2 ^ (prefixWord ++ tailWord_598853).sum := by decide
  have hdescent : baseEnd_598853 < baseStart_598853 := by decide
  rcases family_descends (prefixWord ++ tailWord_598853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598861 : List Nat := [1, 6, 1, 2, 3, 1, 1, 3, 5]
def baseStart_598861 : Nat := 118140960795 + 598861 * 2 ^ 59
def prefixEnd_598861 : Nat := 4983230072969 + 3 ^ 40 * 598861 * 2
def baseEnd_598861 : Nat := 34167059803587409698155

theorem tailTrace_598861 : CollatzResearch.WordTrace tailWord_598861 prefixEnd_598861 34167059803587409698155 := by
  unfold tailWord_598861
  simp only [CollatzResearch.WordTrace]
  refine ⟨21842255083436349161196437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14561503388957566107464291 21842255083436349161196437)
  ·
    refine ⟨1023855707036078866931083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21842255083436349161196437 1023855707036078866931083)
    ·
      refine ⟨1535783560554118300396625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1023855707036078866931083 1535783560554118300396625)
      ·
        refine ⟨1151837670415588725297469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1535783560554118300396625 1151837670415588725297469)
        ·
          refine ⟨431939126405845771986551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1151837670415588725297469 431939126405845771986551)
          ·
            refine ⟨647908689608768657979827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431939126405845771986551 647908689608768657979827)
            ·
              refine ⟨971863034413152986969741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 647908689608768657979827 971863034413152986969741)
              ·
                refine ⟨364448637904932370113653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 971863034413152986969741 364448637904932370113653)
                ·
                  refine ⟨34167059803587409698155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 364448637904932370113653 34167059803587409698155)
                  ·
                    rfl

theorem cell23_598861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_598861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598861 prefixEnd_598861 := by exact prefixLift 598861
  have htrace : WordTrace (prefixWord ++ tailWord_598861) baseStart_598861 baseEnd_598861 := by
    simpa [prefixWord, tailWord_598861, baseEnd_598861] using wordTrace_append hprefix tailTrace_598861
  have hstable : (prefixWord ++ tailWord_598861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598861).length < 2 ^ (prefixWord ++ tailWord_598861).sum := by decide
  have hdescent : baseEnd_598861 < baseStart_598861 := by decide
  rcases family_descends (prefixWord ++ tailWord_598861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598863 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 8, 2, 3]
def baseStart_598863 : Nat := 118140960795 + 598863 * 2 ^ 59
def prefixEnd_598863 : Nat := 4983230072969 + 3 ^ 40 * 598863 * 2
def baseEnd_598863 : Nat := 307504565193595679458385

theorem tailTrace_598863 : CollatzResearch.WordTrace tailWord_598863 prefixEnd_598863 307504565193595679458385 := by
  unfold tailWord_598863
  simp only [CollatzResearch.WordTrace]
  refine ⟨21842328029429103502769243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14561552019619402335179495 21842328029429103502769243)
  ·
    refine ⟨32763492044143655254153865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21842328029429103502769243 32763492044143655254153865)
    ·
      refine ⟨24572619033107741440615399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32763492044143655254153865 24572619033107741440615399)
      ·
        refine ⟨36858928549661612160923099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24572619033107741440615399 36858928549661612160923099)
        ·
          refine ⟨55288392824492418241384649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36858928549661612160923099 55288392824492418241384649)
          ·
            refine ⟨41466294618369313681038487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55288392824492418241384649 41466294618369313681038487)
            ·
              refine ⟨62199441927553970521557731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41466294618369313681038487 62199441927553970521557731)
              ·
                refine ⟨93299162891330955782336597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62199441927553970521557731 93299162891330955782336597)
                ·
                  refine ⟨1093349565132784638074257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 93299162891330955782336597 1093349565132784638074257)
                  ·
                    refine ⟨820012173849588478555693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1093349565132784638074257 820012173849588478555693)
                    ·
                      refine ⟨307504565193595679458385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 820012173849588478555693 307504565193595679458385)
                      ·
                        rfl

theorem cell23_598863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 2, 3].length) (baseStart_598863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598863 prefixEnd_598863 := by exact prefixLift 598863
  have htrace : WordTrace (prefixWord ++ tailWord_598863) baseStart_598863 baseEnd_598863 := by
    simpa [prefixWord, tailWord_598863, baseEnd_598863] using wordTrace_append hprefix tailTrace_598863
  have hstable : (prefixWord ++ tailWord_598863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598863).length < 2 ^ (prefixWord ++ tailWord_598863).sum := by decide
  have hdescent : baseEnd_598863 < baseStart_598863 := by decide
  rcases family_descends (prefixWord ++ tailWord_598863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598880 : List Nat := [2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 3]
def baseStart_598880 : Nat := 118140960795 + 598880 * 2 ^ 59
def prefixEnd_598880 : Nat := 4983230072969 + 3 ^ 40 * 598880 * 2
def baseEnd_598880 : Nat := 307513294364722112945807

theorem tailTrace_598880 : CollatzResearch.WordTrace tailWord_598880 prefixEnd_598880 307513294364722112945807 := by
  unfold tailWord_598880
  simp only [CollatzResearch.WordTrace]
  refine ⟨10921474035183757703069047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14561965380245010270758729 10921474035183757703069047)
  ·
    refine ⟨16382211052775636554603571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10921474035183757703069047 16382211052775636554603571)
    ·
      refine ⟨24573316579163454831905357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16382211052775636554603571 24573316579163454831905357)
      ·
        refine ⟨9214993717186295561964509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24573316579163454831905357 9214993717186295561964509)
        ·
          refine ⟨3455622643944860835736691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9214993717186295561964509 3455622643944860835736691)
          ·
            refine ⟨5183433965917291253605037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3455622643944860835736691 5183433965917291253605037)
            ·
              refine ⟨1943787737218984220101889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5183433965917291253605037 1943787737218984220101889)
              ·
                refine ⟨1457840802914238165076417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1943787737218984220101889 1457840802914238165076417)
                ·
                  refine ⟨1093380602185678623807313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1457840802914238165076417 1093380602185678623807313)
                  ·
                    refine ⟨820035451639258967855485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1093380602185678623807313 820035451639258967855485)
                    ·
                      refine ⟨307513294364722112945807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 820035451639258967855485 307513294364722112945807)
                      ·
                        rfl

theorem cell23_598880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_598880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598880 prefixEnd_598880 := by exact prefixLift 598880
  have htrace : WordTrace (prefixWord ++ tailWord_598880) baseStart_598880 baseEnd_598880 := by
    simpa [prefixWord, tailWord_598880, baseEnd_598880] using wordTrace_append hprefix tailTrace_598880
  have hstable : (prefixWord ++ tailWord_598880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598880).length < 2 ^ (prefixWord ++ tailWord_598880).sum := by decide
  have hdescent : baseEnd_598880 < baseStart_598880 := by decide
  rcases family_descends (prefixWord ++ tailWord_598880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598883 : List Nat := [1, 1, 1, 5, 3, 1, 2, 1, 8]
def baseStart_598883 : Nat := 118140960795 + 598883 * 2 ^ 59
def prefixEnd_598883 : Nat := 4983230072969 + 3 ^ 40 * 598883 * 2
def baseEnd_598883 : Nat := 34168314978520622356477

theorem tailTrace_598883 : CollatzResearch.WordTrace tailWord_598883 prefixEnd_598883 34168314978520622356477 := by
  unfold tailWord_598883
  simp only [CollatzResearch.WordTrace]
  refine ⟨21843057489356646918497303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14562038326237764612331535 21843057489356646918497303)
  ·
    refine ⟨32764586234034970377745955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21843057489356646918497303 32764586234034970377745955)
    ·
      refine ⟨49146879351052455566618933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32764586234034970377745955 49146879351052455566618933)
      ·
        refine ⟨4607519939161167709370525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49146879351052455566618933 4607519939161167709370525)
        ·
          refine ⟨1727819977185437891013947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4607519939161167709370525 1727819977185437891013947)
          ·
            refine ⟨2591729965778156836520921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1727819977185437891013947 2591729965778156836520921)
            ·
              refine ⟨1943797474333617627390691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2591729965778156836520921 1943797474333617627390691)
              ·
                refine ⟨2915696211500426441086037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1943797474333617627390691 2915696211500426441086037)
                ·
                  refine ⟨34168314978520622356477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2915696211500426441086037 34168314978520622356477)
                  ·
                    rfl

theorem cell23_598883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 8].length) (baseStart_598883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598883 prefixEnd_598883 := by exact prefixLift 598883
  have htrace : WordTrace (prefixWord ++ tailWord_598883) baseStart_598883 baseEnd_598883 := by
    simpa [prefixWord, tailWord_598883, baseEnd_598883] using wordTrace_append hprefix tailTrace_598883
  have hstable : (prefixWord ++ tailWord_598883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598883).length < 2 ^ (prefixWord ++ tailWord_598883).sum := by decide
  have hdescent : baseEnd_598883 < baseStart_598883 := by decide
  rcases family_descends (prefixWord ++ tailWord_598883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598887 : List Nat := [1, 1, 5, 1, 2, 4, 1, 1, 3, 4]
def baseStart_598887 : Nat := 118140960795 + 598887 * 2 ^ 59
def prefixEnd_598887 : Nat := 4983230072969 + 3 ^ 40 * 598887 * 2
def baseEnd_598887 : Nat := 102505629576434528519425

theorem tailTrace_598887 : CollatzResearch.WordTrace tailWord_598887 prefixEnd_598887 102505629576434528519425 := by
  unfold tailWord_598887
  simp only [CollatzResearch.WordTrace]
  refine ⟨21843203381342155601642915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14562135587561437067761943 21843203381342155601642915)
  ·
    refine ⟨32764805072013233402464373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21843203381342155601642915 32764805072013233402464373)
    ·
      refine ⟨3071700475501240631481035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32764805072013233402464373 3071700475501240631481035)
      ·
        refine ⟨4607550713251860947221553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3071700475501240631481035 4607550713251860947221553)
        ·
          refine ⟨3455663034938895710416165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4607550713251860947221553 3455663034938895710416165)
          ·
            refine ⟨647936819051042945703031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3455663034938895710416165 647936819051042945703031)
            ·
              refine ⟨971905228576564418554547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 647936819051042945703031 971905228576564418554547)
              ·
                refine ⟨1457857842864846627831821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 971905228576564418554547 1457857842864846627831821)
                ·
                  refine ⟨546696691074317485436933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1457857842864846627831821 546696691074317485436933)
                  ·
                    refine ⟨102505629576434528519425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 546696691074317485436933 102505629576434528519425)
                    ·
                      rfl

theorem cell23_598887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_598887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598887 prefixEnd_598887 := by exact prefixLift 598887
  have htrace : WordTrace (prefixWord ++ tailWord_598887) baseStart_598887 baseEnd_598887 := by
    simpa [prefixWord, tailWord_598887, baseEnd_598887] using wordTrace_append hprefix tailTrace_598887
  have hstable : (prefixWord ++ tailWord_598887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598887).length < 2 ^ (prefixWord ++ tailWord_598887).sum := by decide
  have hdescent : baseEnd_598887 < baseStart_598887 := by decide
  rcases family_descends (prefixWord ++ tailWord_598887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598934 : List Nat := [5, 3, 1, 1, 1, 1, 1, 4, 6]
def baseStart_598934 : Nat := 118140960795 + 598934 * 2 ^ 59
def prefixEnd_598934 : Nat := 4983230072969 + 3 ^ 40 * 598934 * 2
def baseEnd_598934 : Nat := 34171224702229433518951

theorem tailTrace_598934 : CollatzResearch.WordTrace tailWord_598934 prefixEnd_598934 34171224702229433518951 := by
  unfold tailWord_598934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1365307350760742664287741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14563278408114588419069237 1365307350760742664287741)
  ·
    refine ⟨511990256535278499107903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1365307350760742664287741 511990256535278499107903)
    ·
      refine ⟨767985384802917748661855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 511990256535278499107903 767985384802917748661855)
      ·
        refine ⟨1151978077204376622992783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 767985384802917748661855 1151978077204376622992783)
        ·
          refine ⟨1727967115806564934489175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1151978077204376622992783 1727967115806564934489175)
          ·
            refine ⟨2591950673709847401733763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1727967115806564934489175 2591950673709847401733763)
            ·
              refine ⟨3887926010564771102600645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2591950673709847401733763 3887926010564771102600645)
              ·
                refine ⟨728986126980894581737621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3887926010564771102600645 728986126980894581737621)
                ·
                  refine ⟨34171224702229433518951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 728986126980894581737621 34171224702229433518951)
                  ·
                    rfl

theorem cell23_598934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_598934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598934 prefixEnd_598934 := by exact prefixLift 598934
  have htrace : WordTrace (prefixWord ++ tailWord_598934) baseStart_598934 baseEnd_598934 := by
    simpa [prefixWord, tailWord_598934, baseEnd_598934] using wordTrace_append hprefix tailTrace_598934
  have hstable : (prefixWord ++ tailWord_598934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598934).length < 2 ^ (prefixWord ++ tailWord_598934).sum := by decide
  have hdescent : baseEnd_598934 < baseStart_598934 := by decide
  rcases family_descends (prefixWord ++ tailWord_598934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598938 : List Nat := [3, 1, 1, 4, 4, 1, 2, 2, 1, 4]
def baseStart_598938 : Nat := 118140960795 + 598938 * 2 ^ 59
def prefixEnd_598938 : Nat := 4983230072969 + 3 ^ 40 * 598938 * 2
def baseEnd_598938 : Nat := 102514358747560962006847

theorem tailTrace_598938 : CollatzResearch.WordTrace tailWord_598938 prefixEnd_598938 102514358747560962006847 := by
  unfold tailWord_598938
  simp only [CollatzResearch.WordTrace]
  refine ⟨5461265876039347827937367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14563375669438260874499645 5461265876039347827937367)
  ·
    refine ⟨8191898814059021741906051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5461265876039347827937367 8191898814059021741906051)
    ·
      refine ⟨12287848221088532612859077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8191898814059021741906051 12287848221088532612859077)
      ·
        refine ⟨2303971541454099864911077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12287848221088532612859077 2303971541454099864911077)
        ·
          refine ⟨431994664022643724670827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2303971541454099864911077 431994664022643724670827)
          ·
            refine ⟨647991996033965587006241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431994664022643724670827 647991996033965587006241)
            ·
              refine ⟨485993997025474190254681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 647991996033965587006241 485993997025474190254681)
              ·
                refine ⟨364495497769105642691011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 485993997025474190254681 364495497769105642691011)
                ·
                  refine ⟨546743246653658464036517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 364495497769105642691011 546743246653658464036517)
                  ·
                    refine ⟨102514358747560962006847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 546743246653658464036517 102514358747560962006847)
                    ·
                      rfl

theorem cell23_598938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 2, 1, 4].length) (baseStart_598938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598938 prefixEnd_598938 := by exact prefixLift 598938
  have htrace : WordTrace (prefixWord ++ tailWord_598938) baseStart_598938 baseEnd_598938 := by
    simpa [prefixWord, tailWord_598938, baseEnd_598938] using wordTrace_append hprefix tailTrace_598938
  have hstable : (prefixWord ++ tailWord_598938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598938).length < 2 ^ (prefixWord ++ tailWord_598938).sum := by decide
  have hdescent : baseEnd_598938 < baseStart_598938 := by decide
  rcases family_descends (prefixWord ++ tailWord_598938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598953 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 3, 1, 5]
def baseStart_598953 : Nat := 118140960795 + 598953 * 2 ^ 59
def prefixEnd_598953 : Nat := 4983230072969 + 3 ^ 40 * 598953 * 2
def baseEnd_598953 : Nat := 307550778452500327332971

theorem tailTrace_598953 : CollatzResearch.WordTrace tailWord_598953 prefixEnd_598953 307550778452500327332971 := by
  unfold tailWord_598953
  simp only [CollatzResearch.WordTrace]
  refine ⟨21845610599103048873545513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14563740399402032582363675 21845610599103048873545513)
  ·
    refine ⟨16384207949327286655159135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21845610599103048873545513 16384207949327286655159135)
    ·
      refine ⟨24576311923990929982738703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16384207949327286655159135 24576311923990929982738703)
      ·
        refine ⟨36864467885986394974108055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24576311923990929982738703 36864467885986394974108055)
        ·
          refine ⟨55296701828979592461162083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36864467885986394974108055 55296701828979592461162083)
          ·
            refine ⟨82945052743469388691743125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55296701828979592461162083 82945052743469388691743125)
            ·
              refine ⟨3888049347350127594925459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 82945052743469388691743125 3888049347350127594925459)
              ·
                refine ⟨5832074021025191392388189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3888049347350127594925459 5832074021025191392388189)
                ·
                  refine ⟨2187027757884446772145571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5832074021025191392388189 2187027757884446772145571)
                  ·
                    refine ⟨3280541636826670158218357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2187027757884446772145571 3280541636826670158218357)
                    ·
                      refine ⟨307550778452500327332971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3280541636826670158218357 307550778452500327332971)
                      ·
                        rfl

theorem cell23_598953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 1, 5].length) (baseStart_598953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598953 prefixEnd_598953 := by exact prefixLift 598953
  have htrace : WordTrace (prefixWord ++ tailWord_598953) baseStart_598953 baseEnd_598953 := by
    simpa [prefixWord, tailWord_598953, baseEnd_598953] using wordTrace_append hprefix tailTrace_598953
  have hstable : (prefixWord ++ tailWord_598953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598953).length < 2 ^ (prefixWord ++ tailWord_598953).sum := by decide
  have hdescent : baseEnd_598953 < baseStart_598953 := by decide
  rcases family_descends (prefixWord ++ tailWord_598953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598967 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 5, 2, 2]
def baseStart_598967 : Nat := 118140960795 + 598967 * 2 ^ 59
def prefixEnd_598967 : Nat := 4983230072969 + 3 ^ 40 * 598967 * 2
def baseEnd_598967 : Nat := 307557967181663272557907

theorem tailTrace_598967 : CollatzResearch.WordTrace tailWord_598967 prefixEnd_598967 307557967181663272557907 := by
  unfold tailWord_598967
  simp only [CollatzResearch.WordTrace]
  refine ⟨21846121221052329264555155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14564080814034886176370103 21846121221052329264555155)
  ·
    refine ⟨32769181831578493896832733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21846121221052329264555155 32769181831578493896832733)
    ·
      refine ⟨12288443186841935211312275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32769181831578493896832733 12288443186841935211312275)
      ·
        refine ⟨18432664780262902816968413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12288443186841935211312275 18432664780262902816968413)
        ·
          refine ⟨6912249292598588556363155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18432664780262902816968413 6912249292598588556363155)
          ·
            refine ⟨10368373938897882834544733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6912249292598588556363155 10368373938897882834544733)
            ·
              refine ⟨3888140227086706062954275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10368373938897882834544733 3888140227086706062954275)
              ·
                refine ⟨5832210340630059094431413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3888140227086706062954275 5832210340630059094431413)
                ·
                  refine ⟨546769719434068040102945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5832210340630059094431413 546769719434068040102945)
                  ·
                    refine ⟨410077289575551030077209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 546769719434068040102945 410077289575551030077209)
                    ·
                      refine ⟨307557967181663272557907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 410077289575551030077209 307557967181663272557907)
                      ·
                        rfl

theorem cell23_598967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 5, 2, 2].length) (baseStart_598967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598967 prefixEnd_598967 := by exact prefixLift 598967
  have htrace : WordTrace (prefixWord ++ tailWord_598967) baseStart_598967 baseEnd_598967 := by
    simpa [prefixWord, tailWord_598967, baseEnd_598967] using wordTrace_append hprefix tailTrace_598967
  have hstable : (prefixWord ++ tailWord_598967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598967).length < 2 ^ (prefixWord ++ tailWord_598967).sum := by decide
  have hdescent : baseEnd_598967 < baseStart_598967 := by decide
  rcases family_descends (prefixWord ++ tailWord_598967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598970 : List Nat := [3, 1, 1, 1, 2, 1, 3, 3, 3, 2, 3]
def baseStart_598970 : Nat := 118140960795 + 598970 * 2 ^ 59
def prefixEnd_598970 : Nat := 4983230072969 + 3 ^ 40 * 598970 * 2
def baseEnd_598970 : Nat := 307559507623626760820393

theorem tailTrace_598970 : CollatzResearch.WordTrace tailWord_598970 prefixEnd_598970 307559507623626760820393 := by
  unfold tailWord_598970
  simp only [CollatzResearch.WordTrace]
  refine ⟨5461557660010365194228591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14564153760027640517942909 5461557660010365194228591)
  ·
    refine ⟨8192336490015547791342887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5461557660010365194228591 8192336490015547791342887)
    ·
      refine ⟨12288504735023321687014331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8192336490015547791342887 12288504735023321687014331)
      ·
        refine ⟨18432757102534982530521497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12288504735023321687014331 18432757102534982530521497)
        ·
          refine ⟨13824567826901236897891123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18432757102534982530521497 13824567826901236897891123)
          ·
            refine ⟨20736851740351855346836685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13824567826901236897891123 20736851740351855346836685)
            ·
              refine ⟨7776319402631945755063757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20736851740351855346836685 7776319402631945755063757)
              ·
                refine ⟨2916119775986979658148909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7776319402631945755063757 2916119775986979658148909)
                ·
                  refine ⟨1093544915995117371805841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2916119775986979658148909 1093544915995117371805841)
                  ·
                    refine ⟨820158686996338028854381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1093544915995117371805841 820158686996338028854381)
                    ·
                      refine ⟨307559507623626760820393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 820158686996338028854381 307559507623626760820393)
                      ·
                        rfl

theorem cell23_598970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 3, 2, 3].length) (baseStart_598970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598970 prefixEnd_598970 := by exact prefixLift 598970
  have htrace : WordTrace (prefixWord ++ tailWord_598970) baseStart_598970 baseEnd_598970 := by
    simpa [prefixWord, tailWord_598970, baseEnd_598970] using wordTrace_append hprefix tailTrace_598970
  have hstable : (prefixWord ++ tailWord_598970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598970).length < 2 ^ (prefixWord ++ tailWord_598970).sum := by decide
  have hdescent : baseEnd_598970 < baseStart_598970 := by decide
  rcases family_descends (prefixWord ++ tailWord_598970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598987 : List Nat := [1, 1, 1, 1, 3, 6, 1, 3, 1, 2, 3]
def baseStart_598987 : Nat := 118140960795 + 598987 * 2 ^ 59
def prefixEnd_598987 : Nat := 4983230072969 + 3 ^ 40 * 598987 * 2
def baseEnd_598987 : Nat := 307568236794753194307815

theorem tailTrace_598987 : CollatzResearch.WordTrace tailWord_598987 prefixEnd_598987 307568236794753194307815 := by
  unfold tailWord_598987
  simp only [CollatzResearch.WordTrace]
  refine ⟨21846850680979872680283215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14564567120653248453522143 21846850680979872680283215)
  ·
    refine ⟨32770276021469809020424823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21846850680979872680283215 32770276021469809020424823)
    ·
      refine ⟨49155414032204713530637235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32770276021469809020424823 49155414032204713530637235)
      ·
        refine ⟨73733121048307070295955853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49155414032204713530637235 73733121048307070295955853)
        ·
          refine ⟨27649920393115151360983445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73733121048307070295955853 27649920393115151360983445)
          ·
            refine ⟨1296090018427272720046099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 27649920393115151360983445 1296090018427272720046099)
            ·
              refine ⟨1944135027640909080069149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1296090018427272720046099 1944135027640909080069149)
              ·
                refine ⟨729050635365340905025931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1944135027640909080069149 729050635365340905025931)
                ·
                  refine ⟨1093575953048011357538897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 729050635365340905025931 1093575953048011357538897)
                  ·
                    refine ⟨820181964786008518154173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1093575953048011357538897 820181964786008518154173)
                    ·
                      refine ⟨307568236794753194307815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 820181964786008518154173 307568236794753194307815)
                      ·
                        rfl

theorem cell23_598987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 2, 3].length) (baseStart_598987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598987 prefixEnd_598987 := by exact prefixLift 598987
  have htrace : WordTrace (prefixWord ++ tailWord_598987) baseStart_598987 baseEnd_598987 := by
    simpa [prefixWord, tailWord_598987, baseEnd_598987] using wordTrace_append hprefix tailTrace_598987
  have hstable : (prefixWord ++ tailWord_598987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598987).length < 2 ^ (prefixWord ++ tailWord_598987).sum := by decide
  have hdescent : baseEnd_598987 < baseStart_598987 := by decide
  rcases family_descends (prefixWord ++ tailWord_598987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_598994 : List Nat := [3, 2, 2, 3, 1, 1, 3, 2, 2, 4]
def baseStart_598994 : Nat := 118140960795 + 598994 * 2 ^ 59
def prefixEnd_598994 : Nat := 4983230072969 + 3 ^ 40 * 598994 * 2
def baseEnd_598994 : Nat := 102523943719778222306761

theorem tailTrace_598994 : CollatzResearch.WordTrace tailWord_598994 prefixEnd_598994 102523943719778222306761 := by
  unfold tailWord_598994
  simp only [CollatzResearch.WordTrace]
  refine ⟨5461776497988628218947009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14564737327969675250525357 5461776497988628218947009)
  ·
    refine ⟨4096332373491471164210257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5461776497988628218947009 4096332373491471164210257)
    ·
      refine ⟨3072249280118603373157693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4096332373491471164210257 3072249280118603373157693)
      ·
        refine ⟨1152093480044476264934135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3072249280118603373157693 1152093480044476264934135)
        ·
          refine ⟨1728140220066714397401203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1152093480044476264934135 1728140220066714397401203)
          ·
            refine ⟨2592210330100071596101805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1728140220066714397401203 2592210330100071596101805)
            ·
              refine ⟨972078873787526848538177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2592210330100071596101805 972078873787526848538177)
              ·
                refine ⟨729059155340645136403633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 972078873787526848538177 729059155340645136403633)
                ·
                  refine ⟨546794366505483852302725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 729059155340645136403633 546794366505483852302725)
                  ·
                    refine ⟨102523943719778222306761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 546794366505483852302725 102523943719778222306761)
                    ·
                      rfl

theorem cell23_598994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_598994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_598994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_598994 prefixEnd_598994 := by exact prefixLift 598994
  have htrace : WordTrace (prefixWord ++ tailWord_598994) baseStart_598994 baseEnd_598994 := by
    simpa [prefixWord, tailWord_598994, baseEnd_598994] using wordTrace_append hprefix tailTrace_598994
  have hstable : (prefixWord ++ tailWord_598994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_598994).length < 2 ^ (prefixWord ++ tailWord_598994).sum := by decide
  have hdescent : baseEnd_598994 < baseStart_598994 := by decide
  rcases family_descends (prefixWord ++ tailWord_598994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599001 : List Nat := [1, 2, 1, 2, 5, 1, 2, 4, 1, 2, 2]
def baseStart_599001 : Nat := 118140960795 + 599001 * 2 ^ 59
def prefixEnd_599001 : Nat := 4983230072969 + 3 ^ 40 * 599001 * 2
def baseEnd_599001 : Nat := 307575425523916139532751

theorem tailTrace_599001 : CollatzResearch.WordTrace tailWord_599001 prefixEnd_599001 307575425523916139532751 := by
  unfold tailWord_599001
  simp only [CollatzResearch.WordTrace]
  refine ⟨21847361302929153071292857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14564907535286102047528571 21847361302929153071292857)
  ·
    refine ⟨16385520977196864803469643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21847361302929153071292857 16385520977196864803469643)
    ·
      refine ⟨24578281465795297205204465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16385520977196864803469643 24578281465795297205204465)
      ·
        refine ⟨18433711099346472903903349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24578281465795297205204465 18433711099346472903903349)
        ·
          refine ⟨1728160415563731834740939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18433711099346472903903349 1728160415563731834740939)
          ·
            refine ⟨2592240623345597752111409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1728160415563731834740939 2592240623345597752111409)
            ·
              refine ⟨1944180467509198314083557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2592240623345597752111409 1944180467509198314083557)
              ·
                refine ⟨364533837657974683890667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1944180467509198314083557 364533837657974683890667)
                ·
                  refine ⟨546800756486962025836001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 364533837657974683890667 546800756486962025836001)
                  ·
                    refine ⟨410100567365221519377001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 546800756486962025836001 410100567365221519377001)
                    ·
                      refine ⟨307575425523916139532751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 410100567365221519377001 307575425523916139532751)
                      ·
                        rfl

theorem cell23_599001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 4, 1, 2, 2].length) (baseStart_599001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599001 prefixEnd_599001 := by exact prefixLift 599001
  have htrace : WordTrace (prefixWord ++ tailWord_599001) baseStart_599001 baseEnd_599001 := by
    simpa [prefixWord, tailWord_599001, baseEnd_599001] using wordTrace_append hprefix tailTrace_599001
  have hstable : (prefixWord ++ tailWord_599001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599001).length < 2 ^ (prefixWord ++ tailWord_599001).sum := by decide
  have hdescent : baseEnd_599001 < baseStart_599001 := by decide
  rcases family_descends (prefixWord ++ tailWord_599001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599068 : List Nat := [2, 2, 3, 1, 4, 2, 2, 1, 2, 1, 3]
def baseStart_599068 : Nat := 118140960795 + 599068 * 2 ^ 59
def prefixEnd_599068 : Nat := 4983230072969 + 3 ^ 40 * 599068 * 2
def baseEnd_599068 : Nat := 307609828727767377394943

theorem tailTrace_599068 : CollatzResearch.WordTrace tailWord_599068 prefixEnd_599068 307609828727767377394943 := by
  unfold tailWord_599068
  simp only [CollatzResearch.WordTrace]
  refine ⟨10924902496843211756990929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14566536662457615675987905 10924902496843211756990929)
  ·
    refine ⟨8193676872632408817743197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10924902496843211756990929 8193676872632408817743197)
    ·
      refine ⟨3072628827237153306653699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8193676872632408817743197 3072628827237153306653699)
      ·
        refine ⟨4608943240855729959980549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3072628827237153306653699 4608943240855729959980549)
        ·
          refine ⟨864176857660449367496353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4608943240855729959980549 864176857660449367496353)
          ·
            refine ⟨648132643245337025622265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 864176857660449367496353 648132643245337025622265)
            ·
              refine ⟨486099482434002769216699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 648132643245337025622265 486099482434002769216699)
              ·
                refine ⟨729149223651004153825049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 486099482434002769216699 729149223651004153825049)
                ·
                  refine ⟨546861917738253115368787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 729149223651004153825049 546861917738253115368787)
                  ·
                    refine ⟨820292876607379673053181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 546861917738253115368787 820292876607379673053181)
                    ·
                      refine ⟨307609828727767377394943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 820292876607379673053181 307609828727767377394943)
                      ·
                        rfl

theorem cell23_599068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_599068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599068 prefixEnd_599068 := by exact prefixLift 599068
  have htrace : WordTrace (prefixWord ++ tailWord_599068) baseStart_599068 baseEnd_599068 := by
    simpa [prefixWord, tailWord_599068, baseEnd_599068] using wordTrace_append hprefix tailTrace_599068
  have hstable : (prefixWord ++ tailWord_599068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599068).length < 2 ^ (prefixWord ++ tailWord_599068).sum := by decide
  have hdescent : baseEnd_599068 < baseStart_599068 := by decide
  rcases family_descends (prefixWord ++ tailWord_599068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599114 : List Nat := [3, 1, 2, 1, 1, 2, 6, 2, 5]
def baseStart_599114 : Nat := 118140960795 + 599114 * 2 ^ 59
def prefixEnd_599114 : Nat := 4983230072969 + 3 ^ 40 * 599114 * 2
def baseEnd_599114 : Nat := 34181494315319355268859

theorem tailTrace_599114 : CollatzResearch.WordTrace tailWord_599114 prefixEnd_599114 34181494315319355268859 := by
  unfold tailWord_599114
  simp only [CollatzResearch.WordTrace]
  refine ⟨5462870687879943342539099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14567655167679848913437597 5462870687879943342539099)
  ·
    refine ⟨8194306031819915013808649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5462870687879943342539099 8194306031819915013808649)
    ·
      refine ⟨6145729523864936260356487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8194306031819915013808649 6145729523864936260356487)
      ·
        refine ⟨9218594285797404390534731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6145729523864936260356487 9218594285797404390534731)
        ·
          refine ⟨13827891428696106585802097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9218594285797404390534731 13827891428696106585802097)
          ·
            refine ⟨10370918571522079939351573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13827891428696106585802097 10370918571522079939351573)
            ·
              refine ⟨486136808040097497157105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10370918571522079939351573 486136808040097497157105)
              ·
                refine ⟨364602606030073122867829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 486136808040097497157105 364602606030073122867829)
                ·
                  refine ⟨34181494315319355268859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 364602606030073122867829 34181494315319355268859)
                  ·
                    rfl

theorem cell23_599114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 2, 5].length) (baseStart_599114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599114 prefixEnd_599114 := by exact prefixLift 599114
  have htrace : WordTrace (prefixWord ++ tailWord_599114) baseStart_599114 baseEnd_599114 := by
    simpa [prefixWord, tailWord_599114, baseEnd_599114] using wordTrace_append hprefix tailTrace_599114
  have hstable : (prefixWord ++ tailWord_599114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599114).length < 2 ^ (prefixWord ++ tailWord_599114).sum := by decide
  have hdescent : baseEnd_599114 < baseStart_599114 := by decide
  rcases family_descends (prefixWord ++ tailWord_599114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599144 : List Nat := [2, 1, 4, 4, 1, 1, 1, 1, 1, 7]
def baseStart_599144 : Nat := 118140960795 + 599144 * 2 ^ 59
def prefixEnd_599144 : Nat := 4983230072969 + 3 ^ 40 * 599144 * 2
def baseEnd_599144 : Nat := 102549617752503026681531

theorem tailTrace_599144 : CollatzResearch.WordTrace tailWord_599144 prefixEnd_599144 102549617752503026681531 := by
  unfold tailWord_599144
  simp only [CollatzResearch.WordTrace]
  refine ⟨10926288470705544246874243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14568384627607392329165657 10926288470705544246874243)
  ·
    refine ⟨16389432706058316370311365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10926288470705544246874243 16389432706058316370311365)
    ·
      refine ⟨3073018632385934319433381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16389432706058316370311365 3073018632385934319433381)
      ·
        refine ⟨576190993572362684893759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3073018632385934319433381 576190993572362684893759)
        ·
          refine ⟨864286490358544027340639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 576190993572362684893759 864286490358544027340639)
          ·
            refine ⟨1296429735537816041010959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 864286490358544027340639 1296429735537816041010959)
            ·
              refine ⟨1944644603306724061516439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1296429735537816041010959 1944644603306724061516439)
              ·
                refine ⟨2916966904960086092274659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1944644603306724061516439 2916966904960086092274659)
                ·
                  refine ⟨4375450357440129138411989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2916966904960086092274659 4375450357440129138411989)
                  ·
                    refine ⟨102549617752503026681531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4375450357440129138411989 102549617752503026681531)
                    ·
                      rfl

theorem cell23_599144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_599144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599144 prefixEnd_599144 := by exact prefixLift 599144
  have htrace : WordTrace (prefixWord ++ tailWord_599144) baseStart_599144 baseEnd_599144 := by
    simpa [prefixWord, tailWord_599144, baseEnd_599144] using wordTrace_append hprefix tailTrace_599144
  have hstable : (prefixWord ++ tailWord_599144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599144).length < 2 ^ (prefixWord ++ tailWord_599144).sum := by decide
  have hdescent : baseEnd_599144 < baseStart_599144 := by decide
  rcases family_descends (prefixWord ++ tailWord_599144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599160 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 2, 1, 6]
def baseStart_599160 : Nat := 118140960795 + 599160 * 2 ^ 59
def prefixEnd_599160 : Nat := 4983230072969 + 3 ^ 40 * 599160 * 2
def baseEnd_599160 : Nat := 307657068947981017444519

theorem tailTrace_599160 : CollatzResearch.WordTrace tailWord_599160 prefixEnd_599160 307657068947981017444519 := by
  unfold tailWord_599160
  simp only [CollatzResearch.WordTrace]
  refine ⟨10926580254676561613165467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14568773672902082150887289 10926580254676561613165467)
  ·
    refine ⟨16389870382014842419748201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10926580254676561613165467 16389870382014842419748201)
    ·
      refine ⟨12292402786511131814811151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16389870382014842419748201 12292402786511131814811151)
      ·
        refine ⟨18438604179766697722216727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12292402786511131814811151 18438604179766697722216727)
        ·
          refine ⟨27657906269650046583325091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18438604179766697722216727 27657906269650046583325091)
          ·
            refine ⟨41486859404475069874987637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27657906269650046583325091 41486859404475069874987637)
            ·
              refine ⟨3889393069169537800780091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41486859404475069874987637 3889393069169537800780091)
              ·
                refine ⟨5834089603754306701170137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3889393069169537800780091 5834089603754306701170137)
                ·
                  refine ⟨4375567202815730025877603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5834089603754306701170137 4375567202815730025877603)
                  ·
                    refine ⟨6563350804223595038816405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4375567202815730025877603 6563350804223595038816405)
                    ·
                      refine ⟨307657068947981017444519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6563350804223595038816405 307657068947981017444519)
                      ·
                        rfl

theorem cell23_599160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_599160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599160 prefixEnd_599160 := by exact prefixLift 599160
  have htrace : WordTrace (prefixWord ++ tailWord_599160) baseStart_599160 baseEnd_599160 := by
    simpa [prefixWord, tailWord_599160, baseEnd_599160] using wordTrace_append hprefix tailTrace_599160
  have hstable : (prefixWord ++ tailWord_599160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599160).length < 2 ^ (prefixWord ++ tailWord_599160).sum := by decide
  have hdescent : baseEnd_599160 < baseStart_599160 := by decide
  rcases family_descends (prefixWord ++ tailWord_599160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599197 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 2, 5, 3]
def baseStart_599197 : Nat := 118140960795 + 599197 * 2 ^ 59
def prefixEnd_599197 : Nat := 4983230072969 + 3 ^ 40 * 599197 * 2
def baseEnd_599197 : Nat := 307676067732197372681849

theorem tailTrace_599197 : CollatzResearch.WordTrace tailWord_599197 prefixEnd_599197 307676067732197372681849 := by
  unfold tailWord_599197
  simp only [CollatzResearch.WordTrace]
  refine ⟨21854510010219078545427845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14569673340146052363618563 21854510010219078545427845)
  ·
    refine ⟨4097720626916077227267721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21854510010219078545427845 4097720626916077227267721)
    ·
      refine ⟨3073290470187057920450791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4097720626916077227267721 3073290470187057920450791)
      ·
        refine ⟨4609935705280586880676187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3073290470187057920450791 4609935705280586880676187)
        ·
          refine ⟨6914903557920880321014281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4609935705280586880676187 6914903557920880321014281)
          ·
            refine ⟨5186177668440660240760711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6914903557920880321014281 5186177668440660240760711)
            ·
              refine ⟨7779266502660990361141067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5186177668440660240760711 7779266502660990361141067)
              ·
                refine ⟨11668899753991485541711601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7779266502660990361141067 11668899753991485541711601)
                ·
                  refine ⟨8751674815493614156283701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11668899753991485541711601 8751674815493614156283701)
                  ·
                    refine ⟨820469513952526327151597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8751674815493614156283701 820469513952526327151597)
                    ·
                      refine ⟨307676067732197372681849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 820469513952526327151597 307676067732197372681849)
                      ·
                        rfl

theorem cell23_599197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_599197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599197 prefixEnd_599197 := by exact prefixLift 599197
  have htrace : WordTrace (prefixWord ++ tailWord_599197) baseStart_599197 baseEnd_599197 := by
    simpa [prefixWord, tailWord_599197, baseEnd_599197] using wordTrace_append hprefix tailTrace_599197
  have hstable : (prefixWord ++ tailWord_599197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599197).length < 2 ^ (prefixWord ++ tailWord_599197).sum := by decide
  have hdescent : baseEnd_599197 < baseStart_599197 := by decide
  rcases family_descends (prefixWord ++ tailWord_599197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599231 : List Nat := [1, 1, 2, 2, 2, 2, 2, 6, 1, 1, 3]
def baseStart_599231 : Nat := 118140960795 + 599231 * 2 ^ 59
def prefixEnd_599231 : Nat := 4983230072969 + 3 ^ 40 * 599231 * 2
def baseEnd_599231 : Nat := 307693526074450239656693

theorem tailTrace_599231 : CollatzResearch.WordTrace tailWord_599231 prefixEnd_599231 307693526074450239656693 := by
  unfold tailWord_599231
  simp only [CollatzResearch.WordTrace]
  refine ⟨21855750092095902352165547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14570500061397268234777031 21855750092095902352165547)
  ·
    refine ⟨32783625138143853528248321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21855750092095902352165547 32783625138143853528248321)
    ·
      refine ⟨24587718853607890146186241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32783625138143853528248321 24587718853607890146186241)
      ·
        refine ⟨18440789140205917609639681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24587718853607890146186241 18440789140205917609639681)
        ·
          refine ⟨13830591855154438207229761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18440789140205917609639681 13830591855154438207229761)
          ·
            refine ⟨10372943891365828655422321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13830591855154438207229761 10372943891365828655422321)
            ·
              refine ⟨7779707918524371491566741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10372943891365828655422321 7779707918524371491566741)
              ·
                refine ⟨364673808680829913667191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7779707918524371491566741 364673808680829913667191)
                ·
                  refine ⟨547010713021244870500787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 364673808680829913667191 547010713021244870500787)
                  ·
                    refine ⟨820516069531867305751181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 547010713021244870500787 820516069531867305751181)
                    ·
                      refine ⟨307693526074450239656693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 820516069531867305751181 307693526074450239656693)
                      ·
                        rfl

theorem cell23_599231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6, 1, 1, 3].length) (baseStart_599231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599231 prefixEnd_599231 := by exact prefixLift 599231
  have htrace : WordTrace (prefixWord ++ tailWord_599231) baseStart_599231 baseEnd_599231 := by
    simpa [prefixWord, tailWord_599231, baseEnd_599231] using wordTrace_append hprefix tailTrace_599231
  have hstable : (prefixWord ++ tailWord_599231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599231).length < 2 ^ (prefixWord ++ tailWord_599231).sum := by decide
  have hdescent : baseEnd_599231 < baseStart_599231 := by decide
  rcases family_descends (prefixWord ++ tailWord_599231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599237 : List Nat := [1, 3, 1, 1, 1, 1, 3, 4, 3, 1, 4]
def baseStart_599237 : Nat := 118140960795 + 599237 * 2 ^ 59
def prefixEnd_599237 : Nat := 4983230072969 + 3 ^ 40 * 599237 * 2
def baseEnd_599237 : Nat := 307696606958377216181665

theorem tailTrace_599237 : CollatzResearch.WordTrace tailWord_599237 prefixEnd_599237 307696606958377216181665 := by
  unfold tailWord_599237
  simp only [CollatzResearch.WordTrace]
  refine ⟨21855968930074165376883965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14570645953382776917922643 21855968930074165376883965)
  ·
    refine ⟨8195988348777812016331487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21855968930074165376883965 8195988348777812016331487)
    ·
      refine ⟨12293982523166718024497231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8195988348777812016331487 12293982523166718024497231)
      ·
        refine ⟨18440973784750077036745847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12293982523166718024497231 18440973784750077036745847)
        ·
          refine ⟨27661460677125115555118771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18440973784750077036745847 27661460677125115555118771)
          ·
            refine ⟨41492191015687673332678157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27661460677125115555118771 41492191015687673332678157)
            ·
              refine ⟨15559571630882877499754309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41492191015687673332678157 15559571630882877499754309)
              ·
                refine ⟨2917419680790539531203933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15559571630882877499754309 2917419680790539531203933)
                ·
                  refine ⟨1094032380296452324201475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2917419680790539531203933 1094032380296452324201475)
                  ·
                    refine ⟨1641048570444678486302213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1094032380296452324201475 1641048570444678486302213)
                    ·
                      refine ⟨307696606958377216181665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1641048570444678486302213 307696606958377216181665)
                      ·
                        rfl

theorem cell23_599237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 1, 4].length) (baseStart_599237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599237 prefixEnd_599237 := by exact prefixLift 599237
  have htrace : WordTrace (prefixWord ++ tailWord_599237) baseStart_599237 baseEnd_599237 := by
    simpa [prefixWord, tailWord_599237, baseEnd_599237] using wordTrace_append hprefix tailTrace_599237
  have hstable : (prefixWord ++ tailWord_599237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599237).length < 2 ^ (prefixWord ++ tailWord_599237).sum := by decide
  have hdescent : baseEnd_599237 < baseStart_599237 := by decide
  rcases family_descends (prefixWord ++ tailWord_599237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599247 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 6, 4]
def baseStart_599247 : Nat := 118140960795 + 599247 * 2 ^ 59
def prefixEnd_599247 : Nat := 4983230072969 + 3 ^ 40 * 599247 * 2
def baseEnd_599247 : Nat := 102567247254974059018873

theorem tailTrace_599247 : CollatzResearch.WordTrace tailWord_599247 prefixEnd_599247 102567247254974059018873 := by
  unfold tailWord_599247
  simp only [CollatzResearch.WordTrace]
  refine ⟨21856333660037937084747995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14570889106691958056498663 21856333660037937084747995)
  ·
    refine ⟨32784500490056905627121993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21856333660037937084747995 32784500490056905627121993)
    ·
      refine ⟨24588375367542679220341495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32784500490056905627121993 24588375367542679220341495)
      ·
        refine ⟨36882563051314018830512243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24588375367542679220341495 36882563051314018830512243)
        ·
          refine ⟨55323844576971028245768365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36882563051314018830512243 55323844576971028245768365)
          ·
            refine ⟨20746441716364135592163137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55323844576971028245768365 20746441716364135592163137)
            ·
              refine ⟨15559831287273101694122353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20746441716364135592163137 15559831287273101694122353)
              ·
                refine ⟨11669873465454826270591765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15559831287273101694122353 11669873465454826270591765)
                ·
                  refine ⟨547025318693194981433989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 11669873465454826270591765 547025318693194981433989)
                  ·
                    refine ⟨102567247254974059018873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 547025318693194981433989 102567247254974059018873)
                    ·
                      rfl

theorem cell23_599247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 6, 4].length) (baseStart_599247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599247 prefixEnd_599247 := by exact prefixLift 599247
  have htrace : WordTrace (prefixWord ++ tailWord_599247) baseStart_599247 baseEnd_599247 := by
    simpa [prefixWord, tailWord_599247, baseEnd_599247] using wordTrace_append hprefix tailTrace_599247
  have hstable : (prefixWord ++ tailWord_599247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599247).length < 2 ^ (prefixWord ++ tailWord_599247).sum := by decide
  have hdescent : baseEnd_599247 < baseStart_599247 := by decide
  rcases family_descends (prefixWord ++ tailWord_599247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599274 : List Nat := [3, 1, 3, 1, 1, 3, 3, 1, 1, 1, 5]
def baseStart_599274 : Nat := 118140960795 + 599274 * 2 ^ 59
def prefixEnd_599274 : Nat := 4983230072969 + 3 ^ 40 * 599274 * 2
def baseEnd_599274 : Nat := 307715605742593571418995

theorem tailTrace_599274 : CollatzResearch.WordTrace tailWord_599274 prefixEnd_599274 307715605742593571418995 := by
  unfold tailWord_599274
  simp only [CollatzResearch.WordTrace]
  refine ⟨5464329607735030173995219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14571545620626747130653917 5464329607735030173995219)
  ·
    refine ⟨8196494411602545260992829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5464329607735030173995219 8196494411602545260992829)
    ·
      refine ⟨3073685404350954472872311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8196494411602545260992829 3073685404350954472872311)
      ·
        refine ⟨4610528106526431709308467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3073685404350954472872311 4610528106526431709308467)
        ·
          refine ⟨6915792159789647563962701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4610528106526431709308467 6915792159789647563962701)
          ·
            refine ⟨2593422059921117836486013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6915792159789647563962701 2593422059921117836486013)
            ·
              refine ⟨972533272470419188682255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2593422059921117836486013 972533272470419188682255)
              ·
                refine ⟨1458799908705628783023383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 972533272470419188682255 1458799908705628783023383)
                ·
                  refine ⟨2188199863058443174535075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1458799908705628783023383 2188199863058443174535075)
                  ·
                    refine ⟨3282299794587664761802613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2188199863058443174535075 3282299794587664761802613)
                    ·
                      refine ⟨307715605742593571418995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3282299794587664761802613 307715605742593571418995)
                      ·
                        rfl

theorem cell23_599274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_599274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599274 prefixEnd_599274 := by exact prefixLift 599274
  have htrace : WordTrace (prefixWord ++ tailWord_599274) baseStart_599274 baseEnd_599274 := by
    simpa [prefixWord, tailWord_599274, baseEnd_599274] using wordTrace_append hprefix tailTrace_599274
  have hstable : (prefixWord ++ tailWord_599274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599274).length < 2 ^ (prefixWord ++ tailWord_599274).sum := by decide
  have hdescent : baseEnd_599274 < baseStart_599274 := by decide
  rcases family_descends (prefixWord ++ tailWord_599274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599277 : List Nat := [1, 5, 1, 2, 2, 12]
def baseStart_599277 : Nat := 118140960795 + 599277 * 2 ^ 59
def prefixEnd_599277 : Nat := 4983230072969 + 3 ^ 40 * 599277 * 2
def baseEnd_599277 : Nat := 1266325704463197776467

theorem tailTrace_599277 : CollatzResearch.WordTrace tailWord_599277 prefixEnd_599277 1266325704463197776467 := by
  unfold tailWord_599277
  simp only [CollatzResearch.WordTrace]
  refine ⟨21857427849929252208340085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14571618566619501472226723 21857427849929252208340085)
  ·
    refine ⟨2049133860930867394531883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21857427849929252208340085 2049133860930867394531883)
    ·
      refine ⟨3073700791396301091797825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2049133860930867394531883 3073700791396301091797825)
      ·
        refine ⟨2305275593547225818848369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3073700791396301091797825 2305275593547225818848369)
        ·
          refine ⟨1728956695160419364136277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2305275593547225818848369 1728956695160419364136277)
          ·
            refine ⟨1266325704463197776467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 1728956695160419364136277 1266325704463197776467)
            ·
              rfl

theorem cell23_599277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 12].length) (baseStart_599277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599277 prefixEnd_599277 := by exact prefixLift 599277
  have htrace : WordTrace (prefixWord ++ tailWord_599277) baseStart_599277 baseEnd_599277 := by
    simpa [prefixWord, tailWord_599277, baseEnd_599277] using wordTrace_append hprefix tailTrace_599277
  have hstable : (prefixWord ++ tailWord_599277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599277).length < 2 ^ (prefixWord ++ tailWord_599277).sum := by decide
  have hdescent : baseEnd_599277 < baseStart_599277 := by decide
  rcases family_descends (prefixWord ++ tailWord_599277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599282 : List Nat := [3, 2, 1, 3, 3, 2, 2, 2, 1, 1, 3]
def baseStart_599282 : Nat := 118140960795 + 599282 * 2 ^ 59
def prefixEnd_599282 : Nat := 4983230072969 + 3 ^ 40 * 599282 * 2
def baseEnd_599282 : Nat := 307719713587829540118959

theorem tailTrace_599282 : CollatzResearch.WordTrace tailWord_599282 prefixEnd_599282 307719713587829540118959 := by
  unfold tailWord_599282
  simp only [CollatzResearch.WordTrace]
  refine ⟨5464402553727784515568025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14571740143274092041514733 5464402553727784515568025)
  ·
    refine ⟨4098301915295838386676019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5464402553727784515568025 4098301915295838386676019)
    ·
      refine ⟨6147452872943757580014029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4098301915295838386676019 6147452872943757580014029)
      ·
        refine ⟨2305294827353909092505261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6147452872943757580014029 2305294827353909092505261)
        ·
          refine ⟨864485560257715909689473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2305294827353909092505261 864485560257715909689473)
          ·
            refine ⟨648364170193286932267105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 864485560257715909689473 648364170193286932267105)
            ·
              refine ⟨486273127644965199200329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 648364170193286932267105 486273127644965199200329)
              ·
                refine ⟨364704845733723899400247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 486273127644965199200329 364704845733723899400247)
                ·
                  refine ⟨547057268600585849100371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 364704845733723899400247 547057268600585849100371)
                  ·
                    refine ⟨820585902900878773650557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 547057268600585849100371 820585902900878773650557)
                    ·
                      refine ⟨307719713587829540118959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 820585902900878773650557 307719713587829540118959)
                      ·
                        rfl

theorem cell23_599282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_599282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599282 prefixEnd_599282 := by exact prefixLift 599282
  have htrace : WordTrace (prefixWord ++ tailWord_599282) baseStart_599282 baseEnd_599282 := by
    simpa [prefixWord, tailWord_599282, baseEnd_599282] using wordTrace_append hprefix tailTrace_599282
  have hstable : (prefixWord ++ tailWord_599282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599282).length < 2 ^ (prefixWord ++ tailWord_599282).sum := by decide
  have hdescent : baseEnd_599282 < baseStart_599282 := by decide
  rcases family_descends (prefixWord ++ tailWord_599282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599294 : List Nat := [4, 2, 2, 1, 1, 2, 3, 8]
def baseStart_599294 : Nat := 118140960795 + 599294 * 2 ^ 59
def prefixEnd_599294 : Nat := 4983230072969 + 3 ^ 40 * 599294 * 2
def baseEnd_599294 : Nat := 11397254642803092339589

theorem tailTrace_599294 : CollatzResearch.WordTrace tailWord_599294 prefixEnd_599294 11397254642803092339589 := by
  unfold tailWord_599294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2732255986358458013963617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14572031927245109407805957 2732255986358458013963617)
  ·
    refine ⟨2049191989768843510472713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2732255986358458013963617 2049191989768843510472713)
    ·
      refine ⟨1536893992326632632854535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2049191989768843510472713 1536893992326632632854535)
      ·
        refine ⟨2305340988489948949281803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1536893992326632632854535 2305340988489948949281803)
        ·
          refine ⟨3458011482734923423922705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2305340988489948949281803 3458011482734923423922705)
          ·
            refine ⟨2593508612051192567942029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3458011482734923423922705 2593508612051192567942029)
            ·
              refine ⟨972565729519197212978261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2593508612051192567942029 972565729519197212978261)
              ·
                refine ⟨11397254642803092339589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 972565729519197212978261 11397254642803092339589)
                ·
                  rfl

theorem cell23_599294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 8].length) (baseStart_599294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599294 prefixEnd_599294 := by exact prefixLift 599294
  have htrace : WordTrace (prefixWord ++ tailWord_599294) baseStart_599294 baseEnd_599294 := by
    simpa [prefixWord, tailWord_599294, baseEnd_599294] using wordTrace_append hprefix tailTrace_599294
  have hstable : (prefixWord ++ tailWord_599294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599294).length < 2 ^ (prefixWord ++ tailWord_599294).sum := by decide
  have hdescent : baseEnd_599294 < baseStart_599294 := by decide
  rcases family_descends (prefixWord ++ tailWord_599294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599317 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 2, 2, 5]
def baseStart_599317 : Nat := 118140960795 + 599317 * 2 ^ 59
def prefixEnd_599317 : Nat := 4983230072969 + 3 ^ 40 * 599317 * 2
def baseEnd_599317 : Nat := 307737685410736903181297

theorem tailTrace_599317 : CollatzResearch.WordTrace tailWord_599317 prefixEnd_599317 307737685410736903181297 := by
  unfold tailWord_599317
  simp only [CollatzResearch.WordTrace]
  refine ⟨21858886769784339039796205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14572591179856226026530803 21858886769784339039796205)
  ·
    refine ⟨8197082538669127139923577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21858886769784339039796205 8197082538669127139923577)
    ·
      refine ⟨6147811904001845354942683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8197082538669127139923577 6147811904001845354942683)
      ·
        refine ⟨9221717856002768032414025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6147811904001845354942683 9221717856002768032414025)
        ·
          refine ⟨6916288392002076024310519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9221717856002768032414025 6916288392002076024310519)
          ·
            refine ⟨10374432588003114036465779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6916288392002076024310519 10374432588003114036465779)
            ·
              refine ⟨15561648882004671054698669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10374432588003114036465779 15561648882004671054698669)
              ·
                refine ⟨5835618330751751645512001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15561648882004671054698669 5835618330751751645512001)
                ·
                  refine ⟨4376713748063813734134001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5835618330751751645512001 4376713748063813734134001)
                  ·
                    refine ⟨3282535311047860300600501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4376713748063813734134001 3282535311047860300600501)
                    ·
                      refine ⟨307737685410736903181297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3282535311047860300600501 307737685410736903181297)
                      ·
                        rfl

theorem cell23_599317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_599317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599317 prefixEnd_599317 := by exact prefixLift 599317
  have htrace : WordTrace (prefixWord ++ tailWord_599317) baseStart_599317 baseEnd_599317 := by
    simpa [prefixWord, tailWord_599317, baseEnd_599317] using wordTrace_append hprefix tailTrace_599317
  have hstable : (prefixWord ++ tailWord_599317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599317).length < 2 ^ (prefixWord ++ tailWord_599317).sum := by decide
  have hdescent : baseEnd_599317 < baseStart_599317 := by decide
  rcases family_descends (prefixWord ++ tailWord_599317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599325 : List Nat := [1, 4, 2, 3, 1, 3, 2, 1, 1, 2, 3]
def baseStart_599325 : Nat := 118140960795 + 599325 * 2 ^ 59
def prefixEnd_599325 : Nat := 4983230072969 + 3 ^ 40 * 599325 * 2
def baseEnd_599325 : Nat := 307741793255972871881261

theorem tailTrace_599325 : CollatzResearch.WordTrace tailWord_599325 prefixEnd_599325 307741793255972871881261 := by
  unfold tailWord_599325
  simp only [CollatzResearch.WordTrace]
  refine ⟨21859178553755356406087429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14572785702503570937391619 21859178553755356406087429)
  ·
    refine ⟨4098595978829129326141393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21859178553755356406087429 4098595978829129326141393)
    ·
      refine ⟨3073946984121846994606045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4098595978829129326141393 3073946984121846994606045)
      ·
        refine ⟨1152730119045692622977267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3073946984121846994606045 1152730119045692622977267)
        ·
          refine ⟨1729095178568538934465901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1152730119045692622977267 1729095178568538934465901)
          ·
            refine ⟨648410691963202100424713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1729095178568538934465901 648410691963202100424713)
            ·
              refine ⟨486308018972401575318535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 648410691963202100424713 486308018972401575318535)
              ·
                refine ⟨729462028458602362977803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 486308018972401575318535 729462028458602362977803)
                ·
                  refine ⟨1094193042687903544466705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 729462028458602362977803 1094193042687903544466705)
                  ·
                    refine ⟨820644782015927658350029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1094193042687903544466705 820644782015927658350029)
                    ·
                      refine ⟨307741793255972871881261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 820644782015927658350029 307741793255972871881261)
                      ·
                        rfl

theorem cell23_599325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_599325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599325 prefixEnd_599325 := by exact prefixLift 599325
  have htrace : WordTrace (prefixWord ++ tailWord_599325) baseStart_599325 baseEnd_599325 := by
    simpa [prefixWord, tailWord_599325, baseEnd_599325] using wordTrace_append hprefix tailTrace_599325
  have hstable : (prefixWord ++ tailWord_599325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599325).length < 2 ^ (prefixWord ++ tailWord_599325).sum := by decide
  have hdescent : baseEnd_599325 < baseStart_599325 := by decide
  rcases family_descends (prefixWord ++ tailWord_599325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599338 : List Nat := [3, 1, 4, 2, 1, 2, 1, 1, 4, 1, 3]
def baseStart_599338 : Nat := 118140960795 + 599338 * 2 ^ 59
def prefixEnd_599338 : Nat := 4983230072969 + 3 ^ 40 * 599338 * 2
def baseEnd_599338 : Nat := 307748468504481321018701

theorem tailTrace_599338 : CollatzResearch.WordTrace tailWord_599338 prefixEnd_599338 307748468504481321018701 := by
  unfold tailWord_599338
  simp only [CollatzResearch.WordTrace]
  refine ⟨5464913175677064906577667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14573101801805506417540445 5464913175677064906577667)
  ·
    refine ⟨8197369763515597359866501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5464913175677064906577667 8197369763515597359866501)
    ·
      refine ⟨1537006830659174504974969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8197369763515597359866501 1537006830659174504974969)
      ·
        refine ⟨1152755122994380878731227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1537006830659174504974969 1152755122994380878731227)
        ·
          refine ⟨1729132684491571318096841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1152755122994380878731227 1729132684491571318096841)
          ·
            refine ⟨1296849513368678488572631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1729132684491571318096841 1296849513368678488572631)
            ·
              refine ⟨1945274270053017732858947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1296849513368678488572631 1945274270053017732858947)
              ·
                refine ⟨2917911405079526599288421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1945274270053017732858947 2917911405079526599288421)
                ·
                  refine ⟨547108388452411237366579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2917911405079526599288421 547108388452411237366579)
                  ·
                    refine ⟨820662582678616856049869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 547108388452411237366579 820662582678616856049869)
                    ·
                      refine ⟨307748468504481321018701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 820662582678616856049869 307748468504481321018701)
                      ·
                        rfl

theorem cell23_599338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_599338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599338 prefixEnd_599338 := by exact prefixLift 599338
  have htrace : WordTrace (prefixWord ++ tailWord_599338) baseStart_599338 baseEnd_599338 := by
    simpa [prefixWord, tailWord_599338, baseEnd_599338] using wordTrace_append hprefix tailTrace_599338
  have hstable : (prefixWord ++ tailWord_599338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599338).length < 2 ^ (prefixWord ++ tailWord_599338).sum := by decide
  have hdescent : baseEnd_599338 < baseStart_599338 := by decide
  rcases family_descends (prefixWord ++ tailWord_599338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599394 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_599394 : Nat := 118140960795 + 599394 * 2 ^ 59
def prefixEnd_599394 : Nat := 4983230072969 + 3 ^ 40 * 599394 * 2
def baseEnd_599394 : Nat := 307777223421133101918443

theorem tailTrace_599394 : CollatzResearch.WordTrace tailWord_599394 prefixEnd_599394 307777223421133101918443 := by
  unfold tailWord_599394
  simp only [CollatzResearch.WordTrace]
  refine ⟨5465423797626345297587309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14574463460336920793566157 5465423797626345297587309)
  ·
    refine ⟨2049533924109879486595241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5465423797626345297587309 2049533924109879486595241)
    ·
      refine ⟨1537150443082409614946431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2049533924109879486595241 1537150443082409614946431)
      ·
        refine ⟨2305725664623614422419647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1537150443082409614946431 2305725664623614422419647)
        ·
          refine ⟨3458588496935421633629471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2305725664623614422419647 3458588496935421633629471)
          ·
            refine ⟨5187882745403132450444207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3458588496935421633629471 5187882745403132450444207)
            ·
              refine ⟨7781824118104698675666311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5187882745403132450444207 7781824118104698675666311)
              ·
                refine ⟨11672736177157048013499467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7781824118104698675666311 11672736177157048013499467)
                ·
                  refine ⟨17509104265735572020249201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11672736177157048013499467 17509104265735572020249201)
                  ·
                    refine ⟨13131828199301679015186901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17509104265735572020249201 13131828199301679015186901)
                    ·
                      refine ⟨307777223421133101918443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 13131828199301679015186901 307777223421133101918443)
                      ·
                        rfl

theorem cell23_599394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_599394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599394 prefixEnd_599394 := by exact prefixLift 599394
  have htrace : WordTrace (prefixWord ++ tailWord_599394) baseStart_599394 baseEnd_599394 := by
    simpa [prefixWord, tailWord_599394, baseEnd_599394] using wordTrace_append hprefix tailTrace_599394
  have hstable : (prefixWord ++ tailWord_599394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599394).length < 2 ^ (prefixWord ++ tailWord_599394).sum := by decide
  have hdescent : baseEnd_599394 < baseStart_599394 := by decide
  rcases family_descends (prefixWord ++ tailWord_599394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599431 : List Nat := [1, 1, 4, 2, 2, 3, 2, 1, 2, 5]
def baseStart_599431 : Nat := 118140960795 + 599431 * 2 ^ 59
def prefixEnd_599431 : Nat := 4983230072969 + 3 ^ 40 * 599431 * 2
def baseEnd_599431 : Nat := 102598740735116485718591

theorem tailTrace_599431 : CollatzResearch.WordTrace tailWord_599431 prefixEnd_599431 102598740735116485718591 := by
  unfold tailWord_599431
  simp only [CollatzResearch.WordTrace]
  refine ⟨21863044691371336509446147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14575363127580891006297431 21863044691371336509446147)
  ·
    refine ⟨32794567037057004764169221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21863044691371336509446147 32794567037057004764169221)
    ·
      refine ⟨6148981319448188393281729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32794567037057004764169221 6148981319448188393281729)
      ·
        refine ⟨4611735989586141294961297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6148981319448188393281729 4611735989586141294961297)
        ·
          refine ⟨3458801992189605971220973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4611735989586141294961297 3458801992189605971220973)
          ·
            refine ⟨1297050747071102239207865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3458801992189605971220973 1297050747071102239207865)
            ·
              refine ⟨972788060303326679405899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1297050747071102239207865 972788060303326679405899)
              ·
                refine ⟨1459182090454990019108849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 972788060303326679405899 1459182090454990019108849)
                ·
                  refine ⟨1094386567841242514331637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1459182090454990019108849 1094386567841242514331637)
                  ·
                    refine ⟨102598740735116485718591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1094386567841242514331637 102598740735116485718591)
                    ·
                      rfl

theorem cell23_599431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_599431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599431 prefixEnd_599431 := by exact prefixLift 599431
  have htrace : WordTrace (prefixWord ++ tailWord_599431) baseStart_599431 baseEnd_599431 := by
    simpa [prefixWord, tailWord_599431, baseEnd_599431] using wordTrace_append hprefix tailTrace_599431
  have hstable : (prefixWord ++ tailWord_599431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599431).length < 2 ^ (prefixWord ++ tailWord_599431).sum := by decide
  have hdescent : baseEnd_599431 < baseStart_599431 := by decide
  rcases family_descends (prefixWord ++ tailWord_599431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599452 : List Nat := [2, 2, 3, 4, 1, 2, 2, 2, 5]
def baseStart_599452 : Nat := 118140960795 + 599452 * 2 ^ 59
def prefixEnd_599452 : Nat := 4983230072969 + 3 ^ 40 * 599452 * 2
def baseEnd_599452 : Nat := 34200778366565986110353

theorem tailTrace_599452 : CollatzResearch.WordTrace tailWord_599452 prefixEnd_599452 34200778366565986110353 := by
  unfold tailWord_599452
  simp only [CollatzResearch.WordTrace]
  refine ⟨10931905312147628547980305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14575873749530171397307073 10931905312147628547980305)
  ·
    refine ⟨8198928984110721410985229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10931905312147628547980305 8198928984110721410985229)
    ·
      refine ⟨3074598369041520529119461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8198928984110721410985229 3074598369041520529119461)
      ·
        refine ⟨576487194195285099209899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3074598369041520529119461 576487194195285099209899)
        ·
          refine ⟨864730791292927648814849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 576487194195285099209899 864730791292927648814849)
          ·
            refine ⟨648548093469695736611137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 864730791292927648814849 648548093469695736611137)
            ·
              refine ⟨486411070102271802458353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 648548093469695736611137 486411070102271802458353)
              ·
                refine ⟨364808302576703851843765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 486411070102271802458353 364808302576703851843765)
                ·
                  refine ⟨34200778366565986110353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 364808302576703851843765 34200778366565986110353)
                  ·
                    rfl

theorem cell23_599452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 2, 5].length) (baseStart_599452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599452 prefixEnd_599452 := by exact prefixLift 599452
  have htrace : WordTrace (prefixWord ++ tailWord_599452) baseStart_599452 baseEnd_599452 := by
    simpa [prefixWord, tailWord_599452, baseEnd_599452] using wordTrace_append hprefix tailTrace_599452
  have hstable : (prefixWord ++ tailWord_599452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599452).length < 2 ^ (prefixWord ++ tailWord_599452).sum := by decide
  have hdescent : baseEnd_599452 < baseStart_599452 := by decide
  rcases family_descends (prefixWord ++ tailWord_599452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599538 : List Nat := [3, 2, 1, 4, 1, 1, 1, 4, 1, 5]
def baseStart_599538 : Nat := 118140960795 + 599538 * 2 ^ 59
def prefixEnd_599538 : Nat := 4983230072969 + 3 ^ 40 * 599538 * 2
def baseEnd_599538 : Nat := 102617054878460179505927

theorem tailTrace_599538 : CollatzResearch.WordTrace tailWord_599538 prefixEnd_599538 102617054878460179505927 := by
  unfold tailWord_599538
  simp only [CollatzResearch.WordTrace]
  refine ⟨5466736825495923445897817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14577964867989129189060845 5466736825495923445897817)
  ·
    refine ⟨4100052619121942584423363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5466736825495923445897817 4100052619121942584423363)
    ·
      refine ⟨6150078928682913876635045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4100052619121942584423363 6150078928682913876635045)
      ·
        refine ⟨1153139799128046351869071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6150078928682913876635045 1153139799128046351869071)
        ·
          refine ⟨1729709698692069527803607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1153139799128046351869071 1729709698692069527803607)
          ·
            refine ⟨2594564548038104291705411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1729709698692069527803607 2594564548038104291705411)
            ·
              refine ⟨3891846822057156437558117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2594564548038104291705411 3891846822057156437558117)
              ·
                refine ⟨729721279135716832042147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3891846822057156437558117 729721279135716832042147)
                ·
                  refine ⟨1094581918703575248063221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 729721279135716832042147 1094581918703575248063221)
                  ·
                    refine ⟨102617054878460179505927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1094581918703575248063221 102617054878460179505927)
                    ·
                      rfl

theorem cell23_599538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_599538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599538 prefixEnd_599538 := by exact prefixLift 599538
  have htrace : WordTrace (prefixWord ++ tailWord_599538) baseStart_599538 baseEnd_599538 := by
    simpa [prefixWord, tailWord_599538, baseEnd_599538] using wordTrace_append hprefix tailTrace_599538
  have hstable : (prefixWord ++ tailWord_599538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599538).length < 2 ^ (prefixWord ++ tailWord_599538).sum := by decide
  have hdescent : baseEnd_599538 < baseStart_599538 := by decide
  rcases family_descends (prefixWord ++ tailWord_599538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599561 : List Nat := [1, 2, 1, 1, 3, 1, 6, 1, 1, 1, 5]
def baseStart_599561 : Nat := 118140960795 + 599561 * 2 ^ 59
def prefixEnd_599561 : Nat := 4983230072969 + 3 ^ 40 * 599561 * 2
def baseEnd_599561 : Nat := 307862974690433948530175

theorem tailTrace_599561 : CollatzResearch.WordTrace tailWord_599561 prefixEnd_599561 307862974690433948530175 := by
  unfold tailWord_599561
  simp only [CollatzResearch.WordTrace]
  refine ⟨21867786180900368711678537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14578524120600245807785691 21867786180900368711678537)
  ·
    refine ⟨16400839635675276533758903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21867786180900368711678537 16400839635675276533758903)
    ·
      refine ⟨24601259453512914800638355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16400839635675276533758903 24601259453512914800638355)
      ·
        refine ⟨36901889180269372200957533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24601259453512914800638355 36901889180269372200957533)
        ·
          refine ⟨13838208442601014575359075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36901889180269372200957533 13838208442601014575359075)
          ·
            refine ⟨20757312663901521863038613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13838208442601014575359075 20757312663901521863038613)
            ·
              refine ⟨972999031120383837329935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20757312663901521863038613 972999031120383837329935)
              ·
                refine ⟨1459498546680575755994903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 972999031120383837329935 1459498546680575755994903)
                ·
                  refine ⟨2189247820020863633992355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1459498546680575755994903 2189247820020863633992355)
                  ·
                    refine ⟨3283871730031295450988533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2189247820020863633992355 3283871730031295450988533)
                    ·
                      refine ⟨307862974690433948530175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3283871730031295450988533 307862974690433948530175)
                      ·
                        rfl

theorem cell23_599561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 1, 5].length) (baseStart_599561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599561 prefixEnd_599561 := by exact prefixLift 599561
  have htrace : WordTrace (prefixWord ++ tailWord_599561) baseStart_599561 baseEnd_599561 := by
    simpa [prefixWord, tailWord_599561, baseEnd_599561] using wordTrace_append hprefix tailTrace_599561
  have hstable : (prefixWord ++ tailWord_599561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599561).length < 2 ^ (prefixWord ++ tailWord_599561).sum := by decide
  have hdescent : baseEnd_599561 < baseStart_599561 := by decide
  rcases family_descends (prefixWord ++ tailWord_599561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599581 : List Nat := [1, 4, 2, 2, 1, 1, 4, 8]
def baseStart_599581 : Nat := 118140960795 + 599581 * 2 ^ 59
def prefixEnd_599581 : Nat := 4983230072969 + 3 ^ 40 * 599581 * 2
def baseEnd_599581 : Nat := 11402712751982365565929

theorem tailTrace_599581 : CollatzResearch.WordTrace tailWord_599581 prefixEnd_599581 11402712751982365565929 := by
  unfold tailWord_599581
  simp only [CollatzResearch.WordTrace]
  refine ⟨21868515640827912127406597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14579010427218608084937731 21868515640827912127406597)
  ·
    refine ⟨4100346682655233523888737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21868515640827912127406597 4100346682655233523888737)
    ·
      refine ⟨3075260011991425142916553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4100346682655233523888737 3075260011991425142916553)
      ·
        refine ⟨2306445008993568857187415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3075260011991425142916553 2306445008993568857187415)
        ·
          refine ⟨3459667513490353285781123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2306445008993568857187415 3459667513490353285781123)
          ·
            refine ⟨5189501270235529928671685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3459667513490353285781123 5189501270235529928671685)
            ·
              refine ⟨973031488169161861625941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5189501270235529928671685 973031488169161861625941)
              ·
                refine ⟨11402712751982365565929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 973031488169161861625941 11402712751982365565929)
                ·
                  rfl

theorem cell23_599581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 8].length) (baseStart_599581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599581 prefixEnd_599581 := by exact prefixLift 599581
  have htrace : WordTrace (prefixWord ++ tailWord_599581) baseStart_599581 baseEnd_599581 := by
    simpa [prefixWord, tailWord_599581, baseEnd_599581] using wordTrace_append hprefix tailTrace_599581
  have hstable : (prefixWord ++ tailWord_599581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599581).length < 2 ^ (prefixWord ++ tailWord_599581).sum := by decide
  have hdescent : baseEnd_599581 < baseStart_599581 := by decide
  rcases family_descends (prefixWord ++ tailWord_599581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599585 : List Nat := [1, 2, 3, 2, 2, 2, 4, 1, 2, 4]
def baseStart_599585 : Nat := 118140960795 + 599585 * 2 ^ 59
def prefixEnd_599585 : Nat := 4983230072969 + 3 ^ 40 * 599585 * 2
def baseEnd_599585 : Nat := 102625099408713951543355

theorem tailTrace_599585 : CollatzResearch.WordTrace tailWord_599585 prefixEnd_599585 102625099408713951543355 := by
  unfold tailWord_599585
  simp only [CollatzResearch.WordTrace]
  refine ⟨21868661532813420810552209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14579107688542280540368139 21868661532813420810552209)
  ·
    refine ⟨16401496149610065607914157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21868661532813420810552209 16401496149610065607914157)
    ·
      refine ⟨6150561056103774602967809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16401496149610065607914157 6150561056103774602967809)
      ·
        refine ⟨4612920792077830952225857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6150561056103774602967809 4612920792077830952225857)
        ·
          refine ⟨3459690594058373214169393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4612920792077830952225857 3459690594058373214169393)
          ·
            refine ⟨2594767945543779910627045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3459690594058373214169393 2594767945543779910627045)
            ·
              refine ⟨486518989789458733242571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2594767945543779910627045 486518989789458733242571)
              ·
                refine ⟨729778484684188099863857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 486518989789458733242571 729778484684188099863857)
                ·
                  refine ⟨547333863513141074897893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 729778484684188099863857 547333863513141074897893)
                  ·
                    refine ⟨102625099408713951543355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 547333863513141074897893 102625099408713951543355)
                    ·
                      rfl

theorem cell23_599585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 2, 4].length) (baseStart_599585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599585 prefixEnd_599585 := by exact prefixLift 599585
  have htrace : WordTrace (prefixWord ++ tailWord_599585) baseStart_599585 baseEnd_599585 := by
    simpa [prefixWord, tailWord_599585, baseEnd_599585] using wordTrace_append hprefix tailTrace_599585
  have hstable : (prefixWord ++ tailWord_599585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599585).length < 2 ^ (prefixWord ++ tailWord_599585).sum := by decide
  have hdescent : baseEnd_599585 < baseStart_599585 := by decide
  rcases family_descends (prefixWord ++ tailWord_599585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599592 : List Nat := [2, 1, 5, 2, 2, 2, 1, 2, 1, 1, 4]
def baseStart_599592 : Nat := 118140960795 + 599592 * 2 ^ 59
def prefixEnd_599592 : Nat := 4983230072969 + 3 ^ 40 * 599592 * 2
def baseEnd_599592 : Nat := 307878892590723327242533

theorem tailTrace_599592 : CollatzResearch.WordTrace tailWord_599592 prefixEnd_599592 307878892590723327242533 := by
  unfold tailWord_599592
  simp only [CollatzResearch.WordTrace]
  refine ⟨10934458421894030503028515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14579277895858707337371353 10934458421894030503028515)
  ·
    refine ⟨16401687632841045754542773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10934458421894030503028515 16401687632841045754542773)
    ·
      refine ⟨1537658215578848039488385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16401687632841045754542773 1537658215578848039488385)
      ·
        refine ⟨1153243661684136029616289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1537658215578848039488385 1153243661684136029616289)
        ·
          refine ⟨864932746263102022212217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1153243661684136029616289 864932746263102022212217)
          ·
            refine ⟨648699559697326516659163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 864932746263102022212217 648699559697326516659163)
            ·
              refine ⟨973049339545989774988745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 648699559697326516659163 973049339545989774988745)
              ·
                refine ⟨729787004659492331241559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 973049339545989774988745 729787004659492331241559)
                ·
                  refine ⟨1094680506989238496862339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 729787004659492331241559 1094680506989238496862339)
                  ·
                    refine ⟨1642020760483857745293509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1094680506989238496862339 1642020760483857745293509)
                    ·
                      refine ⟨307878892590723327242533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1642020760483857745293509 307878892590723327242533)
                      ·
                        rfl

theorem cell23_599592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_599592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599592 prefixEnd_599592 := by exact prefixLift 599592
  have htrace : WordTrace (prefixWord ++ tailWord_599592) baseStart_599592 baseEnd_599592 := by
    simpa [prefixWord, tailWord_599592, baseEnd_599592] using wordTrace_append hprefix tailTrace_599592
  have hstable : (prefixWord ++ tailWord_599592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599592).length < 2 ^ (prefixWord ++ tailWord_599592).sum := by decide
  have hdescent : baseEnd_599592 < baseStart_599592 := by decide
  rcases family_descends (prefixWord ++ tailWord_599592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599608 : List Nat := [2, 1, 2, 1, 4, 3, 1, 2, 1, 3, 3]
def baseStart_599608 : Nat := 118140960795 + 599608 * 2 ^ 59
def prefixEnd_599608 : Nat := 4983230072969 + 3 ^ 40 * 599608 * 2
def baseEnd_599608 : Nat := 307887108281195264642459

theorem tailTrace_599608 : CollatzResearch.WordTrace tailWord_599608 prefixEnd_599608 307887108281195264642459 := by
  unfold tailWord_599608
  simp only [CollatzResearch.WordTrace]
  refine ⟨10934750205865047869319739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14579666941153397159092985 10934750205865047869319739)
  ·
    refine ⟨16402125308797571803979609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10934750205865047869319739 16402125308797571803979609)
    ·
      refine ⟨12301593981598178852984707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16402125308797571803979609 12301593981598178852984707)
      ·
        refine ⟨18452390972397268279477061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12301593981598178852984707 18452390972397268279477061)
        ·
          refine ⟨3459823307324487802401949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18452390972397268279477061 3459823307324487802401949)
          ·
            refine ⟨1297433740246682925900731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3459823307324487802401949 1297433740246682925900731)
            ·
              refine ⟨1946150610370024388851097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1297433740246682925900731 1946150610370024388851097)
              ·
                refine ⟨1459612957777518291638323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1946150610370024388851097 1459612957777518291638323)
                ·
                  refine ⟨2189419436666277437457485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1459612957777518291638323 2189419436666277437457485)
                  ·
                    refine ⟨821032288749854039046557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2189419436666277437457485 821032288749854039046557)
                    ·
                      refine ⟨307887108281195264642459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 821032288749854039046557 307887108281195264642459)
                      ·
                        rfl

theorem cell23_599608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 1, 3, 3].length) (baseStart_599608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599608 prefixEnd_599608 := by exact prefixLift 599608
  have htrace : WordTrace (prefixWord ++ tailWord_599608) baseStart_599608 baseEnd_599608 := by
    simpa [prefixWord, tailWord_599608, baseEnd_599608] using wordTrace_append hprefix tailTrace_599608
  have hstable : (prefixWord ++ tailWord_599608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599608).length < 2 ^ (prefixWord ++ tailWord_599608).sum := by decide
  have hdescent : baseEnd_599608 < baseStart_599608 := by decide
  rcases family_descends (prefixWord ++ tailWord_599608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599612 : List Nat := [2, 2, 2, 2, 4, 1, 3, 1, 1, 2, 3]
def baseStart_599612 : Nat := 118140960795 + 599612 * 2 ^ 59
def prefixEnd_599612 : Nat := 4983230072969 + 3 ^ 40 * 599612 * 2
def baseEnd_599612 : Nat := 307889162203813248992441

theorem tailTrace_599612 : CollatzResearch.WordTrace tailWord_599612 prefixEnd_599612 307889162203813248992441 := by
  unfold tailWord_599612
  simp only [CollatzResearch.WordTrace]
  refine ⟨10934823151857802210892545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14579764202477069614523393 10934823151857802210892545)
  ·
    refine ⟨8201117363893351658169409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10934823151857802210892545 8201117363893351658169409)
    ·
      refine ⟨6150838022920013743627057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8201117363893351658169409 6150838022920013743627057)
      ·
        refine ⟨4613128517190010307720293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6150838022920013743627057 4613128517190010307720293)
        ·
          refine ⟨864961596973126932697555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4613128517190010307720293 864961596973126932697555)
          ·
            refine ⟨1297442395459690399046333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 864961596973126932697555 1297442395459690399046333)
            ·
              refine ⟨486540898297383899642375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1297442395459690399046333 486540898297383899642375)
              ·
                refine ⟨729811347446075849463563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 486540898297383899642375 729811347446075849463563)
                ·
                  refine ⟨1094717021169113774195345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 729811347446075849463563 1094717021169113774195345)
                  ·
                    refine ⟨821037765876835330646509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1094717021169113774195345 821037765876835330646509)
                    ·
                      refine ⟨307889162203813248992441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 821037765876835330646509 307889162203813248992441)
                      ·
                        rfl

theorem cell23_599612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_599612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599612 prefixEnd_599612 := by exact prefixLift 599612
  have htrace : WordTrace (prefixWord ++ tailWord_599612) baseStart_599612 baseEnd_599612 := by
    simpa [prefixWord, tailWord_599612, baseEnd_599612] using wordTrace_append hprefix tailTrace_599612
  have hstable : (prefixWord ++ tailWord_599612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599612).length < 2 ^ (prefixWord ++ tailWord_599612).sum := by decide
  have hdescent : baseEnd_599612 < baseStart_599612 := by decide
  rcases family_descends (prefixWord ++ tailWord_599612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599669 : List Nat := [1, 3, 4, 2, 1, 1, 4, 1, 1, 3, 2]
def baseStart_599669 : Nat := 118140960795 + 599669 * 2 ^ 59
def prefixEnd_599669 : Nat := 4983230072969 + 3 ^ 40 * 599669 * 2
def baseEnd_599669 : Nat := 307918430601119525979679

theorem tailTrace_599669 : CollatzResearch.WordTrace tailWord_599669 prefixEnd_599669 307918430601119525979679 := by
  unfold tailWord_599669
  simp only [CollatzResearch.WordTrace]
  refine ⟨21871725264509103156610061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14581150176339402104406707 21871725264509103156610061)
  ·
    refine ⟨8201896974190913683728773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21871725264509103156610061 8201896974190913683728773)
    ·
      refine ⟨1537855682660796315699145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8201896974190913683728773 1537855682660796315699145)
      ·
        refine ⟨1153391761995597236774359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1537855682660796315699145 1153391761995597236774359)
        ·
          refine ⟨1730087642993395855161539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1153391761995597236774359 1730087642993395855161539)
          ·
            refine ⟨2595131464490093782742309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1730087642993395855161539 2595131464490093782742309)
            ·
              refine ⟨486587149591892584264183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2595131464490093782742309 486587149591892584264183)
              ·
                refine ⟨729880724387838876396275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 486587149591892584264183 729880724387838876396275)
                ·
                  refine ⟨1094821086581758314594413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 729880724387838876396275 1094821086581758314594413)
                  ·
                    refine ⟨410557907468159367972905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1094821086581758314594413 410557907468159367972905)
                    ·
                      refine ⟨307918430601119525979679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 410557907468159367972905 307918430601119525979679)
                      ·
                        rfl

theorem cell23_599669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_599669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599669 prefixEnd_599669 := by exact prefixLift 599669
  have htrace : WordTrace (prefixWord ++ tailWord_599669) baseStart_599669 baseEnd_599669 := by
    simpa [prefixWord, tailWord_599669, baseEnd_599669] using wordTrace_append hprefix tailTrace_599669
  have hstable : (prefixWord ++ tailWord_599669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599669).length < 2 ^ (prefixWord ++ tailWord_599669).sum := by decide
  have hdescent : baseEnd_599669 < baseStart_599669 := by decide
  rcases family_descends (prefixWord ++ tailWord_599669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599721 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 5, 3, 4]
def baseStart_599721 : Nat := 118140960795 + 599721 * 2 ^ 59
def prefixEnd_599721 : Nat := 4983230072969 + 3 ^ 40 * 599721 * 2
def baseEnd_599721 : Nat := 307945131595153322529439

theorem tailTrace_599721 : CollatzResearch.WordTrace tailWord_599721 prefixEnd_599721 307945131595153322529439 := by
  unfold tailWord_599721
  simp only [CollatzResearch.WordTrace]
  refine ⟨21873621860320716037503017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14582414573547144025002011 21873621860320716037503017)
  ·
    refine ⟨16405216395240537028127263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21873621860320716037503017 16405216395240537028127263)
    ·
      refine ⟨24607824592860805542190895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16405216395240537028127263 24607824592860805542190895)
      ·
        refine ⟨36911736889291208313286343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24607824592860805542190895 36911736889291208313286343)
        ·
          refine ⟨55367605333936812469929515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36911736889291208313286343 55367605333936812469929515)
          ·
            refine ⟨83051408000905218704894273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55367605333936812469929515 83051408000905218704894273)
            ·
              refine ⟨62288556000678914028670705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83051408000905218704894273 62288556000678914028670705)
              ·
                refine ⟨46716417000509185521503029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62288556000678914028670705 46716417000509185521503029)
                ·
                  refine ⟨4379664093797736142640909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46716417000509185521503029 4379664093797736142640909)
                  ·
                    refine ⟨1642374035174151053490341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4379664093797736142640909 1642374035174151053490341)
                    ·
                      refine ⟨307945131595153322529439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1642374035174151053490341 307945131595153322529439)
                      ·
                        rfl

theorem cell23_599721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 3, 4].length) (baseStart_599721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599721 prefixEnd_599721 := by exact prefixLift 599721
  have htrace : WordTrace (prefixWord ++ tailWord_599721) baseStart_599721 baseEnd_599721 := by
    simpa [prefixWord, tailWord_599721, baseEnd_599721] using wordTrace_append hprefix tailTrace_599721
  have hstable : (prefixWord ++ tailWord_599721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599721).length < 2 ^ (prefixWord ++ tailWord_599721).sum := by decide
  have hdescent : baseEnd_599721 < baseStart_599721 := by decide
  rcases family_descends (prefixWord ++ tailWord_599721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599738 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 4, 1, 4]
def baseStart_599738 : Nat := 118140960795 + 599738 * 2 ^ 59
def prefixEnd_599738 : Nat := 4983230072969 + 3 ^ 40 * 599738 * 2
def baseEnd_599738 : Nat := 307953860766279756016861

theorem tailTrace_599738 : CollatzResearch.WordTrace tailWord_599738 prefixEnd_599738 307953860766279756016861 := by
  unfold tailWord_599738
  simp only [CollatzResearch.WordTrace]
  refine ⟨5468560475314781985217967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14582827934172751960581245 5468560475314781985217967)
  ·
    refine ⟨8202840712972172977826951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5468560475314781985217967 8202840712972172977826951)
    ·
      refine ⟨12304261069458259466740427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8202840712972172977826951 12304261069458259466740427)
      ·
        refine ⟨18456391604187389200110641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12304261069458259466740427 18456391604187389200110641)
        ·
          refine ⟨13842293703140541900082981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18456391604187389200110641 13842293703140541900082981)
          ·
            refine ⟨2595430069338851606265559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13842293703140541900082981 2595430069338851606265559)
            ·
              refine ⟨3893145104008277409398339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2595430069338851606265559 3893145104008277409398339)
              ·
                refine ⟨5839717656012416114097509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3893145104008277409398339 5839717656012416114097509)
                ·
                  refine ⟨1094947060502328021393283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5839717656012416114097509 1094947060502328021393283)
                  ·
                    refine ⟨1642420590753492032089925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1094947060502328021393283 1642420590753492032089925)
                    ·
                      refine ⟨307953860766279756016861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1642420590753492032089925 307953860766279756016861)
                      ·
                        rfl

theorem cell23_599738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 4, 1, 4].length) (baseStart_599738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599738 prefixEnd_599738 := by exact prefixLift 599738
  have htrace : WordTrace (prefixWord ++ tailWord_599738) baseStart_599738 baseEnd_599738 := by
    simpa [prefixWord, tailWord_599738, baseEnd_599738] using wordTrace_append hprefix tailTrace_599738
  have hstable : (prefixWord ++ tailWord_599738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599738).length < 2 ^ (prefixWord ++ tailWord_599738).sum := by decide
  have hdescent : baseEnd_599738 < baseStart_599738 := by decide
  rcases family_descends (prefixWord ++ tailWord_599738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599750 : List Nat := [6, 1, 2, 1, 1, 3, 2, 1, 2, 2, 2]
def baseStart_599750 : Nat := 118140960795 + 599750 * 2 ^ 59
def prefixEnd_599750 : Nat := 4983230072969 + 3 ^ 40 * 599750 * 2
def baseEnd_599750 : Nat := 307960022534133709066807

theorem tailTrace_599750 : CollatzResearch.WordTrace tailWord_599750 prefixEnd_599750 307960022534133709066807 := by
  unfold tailWord_599750
  simp only [CollatzResearch.WordTrace]
  refine ⟨683583736787989187197147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14583119718143769326872469 683583736787989187197147)
  ·
    refine ⟨1025375605181983780795721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 683583736787989187197147 1025375605181983780795721)
    ·
      refine ⟨769031703886487835596791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1025375605181983780795721 769031703886487835596791)
      ·
        refine ⟨1153547555829731753395187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 769031703886487835596791 1153547555829731753395187)
        ·
          refine ⟨1730321333744597630092781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1153547555829731753395187 1730321333744597630092781)
          ·
            refine ⟨648870500154224111284793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1730321333744597630092781 648870500154224111284793)
            ·
              refine ⟨486652875115668083463595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 648870500154224111284793 486652875115668083463595)
              ·
                refine ⟨729979312673502125195393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 486652875115668083463595 729979312673502125195393)
                ·
                  refine ⟨547484484505126593896545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 729979312673502125195393 547484484505126593896545)
                  ·
                    refine ⟨410613363378844945422409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 547484484505126593896545 410613363378844945422409)
                    ·
                      refine ⟨307960022534133709066807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 410613363378844945422409 307960022534133709066807)
                      ·
                        rfl

theorem cell23_599750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_599750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599750 prefixEnd_599750 := by exact prefixLift 599750
  have htrace : WordTrace (prefixWord ++ tailWord_599750) baseStart_599750 baseEnd_599750 := by
    simpa [prefixWord, tailWord_599750, baseEnd_599750] using wordTrace_append hprefix tailTrace_599750
  have hstable : (prefixWord ++ tailWord_599750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599750).length < 2 ^ (prefixWord ++ tailWord_599750).sum := by decide
  have hdescent : baseEnd_599750 < baseStart_599750 := by decide
  rcases family_descends (prefixWord ++ tailWord_599750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599775 : List Nat := [1, 1, 2, 3, 2, 2, 4, 1, 2, 2, 3]
def baseStart_599775 : Nat := 118140960795 + 599775 * 2 ^ 59
def prefixEnd_599775 : Nat := 4983230072969 + 3 ^ 40 * 599775 * 2
def baseEnd_599775 : Nat := 307972859550496111254191

theorem tailTrace_599775 : CollatzResearch.WordTrace tailWord_599775 prefixEnd_599775 307972859550496111254191 := by
  unfold tailWord_599775
  simp only [CollatzResearch.WordTrace]
  refine ⟨21875591402125083259968779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14583727601416722173312519 21875591402125083259968779)
  ·
    refine ⟨32813387103187624889953169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21875591402125083259968779 32813387103187624889953169)
    ·
      refine ⟨24610040327390718667464877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32813387103187624889953169 24610040327390718667464877)
      ·
        refine ⟨9228765122771519500299329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24610040327390718667464877 9228765122771519500299329)
        ·
          refine ⟨6921573842078639625224497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9228765122771519500299329 6921573842078639625224497)
          ·
            refine ⟨5191180381558979718918373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6921573842078639625224497 5191180381558979718918373)
            ·
              refine ⟨973346321542308697297195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5191180381558979718918373 973346321542308697297195)
              ·
                refine ⟨1460019482313463045945793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 973346321542308697297195 1460019482313463045945793)
                ·
                  refine ⟨1095014611735097284459345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1460019482313463045945793 1095014611735097284459345)
                  ·
                    refine ⟨821260958801322963344509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1095014611735097284459345 821260958801322963344509)
                    ·
                      refine ⟨307972859550496111254191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 821260958801322963344509 307972859550496111254191)
                      ·
                        rfl

theorem cell23_599775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_599775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599775 prefixEnd_599775 := by exact prefixLift 599775
  have htrace : WordTrace (prefixWord ++ tailWord_599775) baseStart_599775 baseEnd_599775 := by
    simpa [prefixWord, tailWord_599775, baseEnd_599775] using wordTrace_append hprefix tailTrace_599775
  have hstable : (prefixWord ++ tailWord_599775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599775).length < 2 ^ (prefixWord ++ tailWord_599775).sum := by decide
  have hdescent : baseEnd_599775 < baseStart_599775 := by decide
  rcases family_descends (prefixWord ++ tailWord_599775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599832 : List Nat := [2, 1, 2, 3, 1, 1, 5, 1, 2, 3, 2]
def baseStart_599832 : Nat := 118140960795 + 599832 * 2 ^ 59
def prefixEnd_599832 : Nat := 4983230072969 + 3 ^ 40 * 599832 * 2
def baseEnd_599832 : Nat := 308002127947802388241429

theorem tailTrace_599832 : CollatzResearch.WordTrace tailWord_599832 prefixEnd_599832 308002127947802388241429 := by
  unfold tailWord_599832
  simp only [CollatzResearch.WordTrace]
  refine ⟨10938835181459290997396875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14585113575279054663195833 10938835181459290997396875)
  ·
    refine ⟨16408252772188936496095313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10938835181459290997396875 16408252772188936496095313)
    ·
      refine ⟨12306189579141702372071485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16408252772188936496095313 12306189579141702372071485)
      ·
        refine ⟨4614821092178138389526807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12306189579141702372071485 4614821092178138389526807)
        ·
          refine ⟨6922231638267207584290211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4614821092178138389526807 6922231638267207584290211)
          ·
            refine ⟨10383347457400811376435317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6922231638267207584290211 10383347457400811376435317)
            ·
              refine ⟨973438824131326066540811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10383347457400811376435317 973438824131326066540811)
              ·
                refine ⟨1460158236196989099811217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 973438824131326066540811 1460158236196989099811217)
                ·
                  refine ⟨1095118677147741824858413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1460158236196989099811217 1095118677147741824858413)
                  ·
                    refine ⟨410669503930403184321905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1095118677147741824858413 410669503930403184321905)
                    ·
                      refine ⟨308002127947802388241429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 410669503930403184321905 308002127947802388241429)
                      ·
                        rfl

theorem cell23_599832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_599832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599832 prefixEnd_599832 := by exact prefixLift 599832
  have htrace : WordTrace (prefixWord ++ tailWord_599832) baseStart_599832 baseEnd_599832 := by
    simpa [prefixWord, tailWord_599832, baseEnd_599832] using wordTrace_append hprefix tailTrace_599832
  have hstable : (prefixWord ++ tailWord_599832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599832).length < 2 ^ (prefixWord ++ tailWord_599832).sum := by decide
  have hdescent : baseEnd_599832 < baseStart_599832 := by decide
  rcases family_descends (prefixWord ++ tailWord_599832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599839 : List Nat := [1, 1, 2, 4, 2, 1, 4, 3, 1, 1, 3]
def baseStart_599839 : Nat := 118140960795 + 599839 * 2 ^ 59
def prefixEnd_599839 : Nat := 4983230072969 + 3 ^ 40 * 599839 * 2
def baseEnd_599839 : Nat := 308005722312383860853897

theorem tailTrace_599839 : CollatzResearch.WordTrace tailWord_599839 prefixEnd_599839 308005722312383860853897 := by
  unfold tailWord_599839
  simp only [CollatzResearch.WordTrace]
  refine ⟨21877925673893222190298571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14585283782595481460199047 21877925673893222190298571)
  ·
    refine ⟨32816888510839833285447857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21877925673893222190298571 32816888510839833285447857)
    ·
      refine ⟨24612666383129874964085893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32816888510839833285447857 24612666383129874964085893)
      ·
        refine ⟨4614874946836851555766105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24612666383129874964085893 4614874946836851555766105)
        ·
          refine ⟨3461156210127638666824579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4614874946836851555766105 3461156210127638666824579)
          ·
            refine ⟨5191734315191458000236869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3461156210127638666824579 5191734315191458000236869)
            ·
              refine ⟨973450184098398375044413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5191734315191458000236869 973450184098398375044413)
              ·
                refine ⟨365043819036899390641655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 973450184098398375044413 365043819036899390641655)
                ·
                  refine ⟨547565728555349085962483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 365043819036899390641655 547565728555349085962483)
                  ·
                    refine ⟨821348592833023628943725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 547565728555349085962483 821348592833023628943725)
                    ·
                      refine ⟨308005722312383860853897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 821348592833023628943725 308005722312383860853897)
                      ·
                        rfl

theorem cell23_599839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_599839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599839 prefixEnd_599839 := by exact prefixLift 599839
  have htrace : WordTrace (prefixWord ++ tailWord_599839) baseStart_599839 baseEnd_599839 := by
    simpa [prefixWord, tailWord_599839, baseEnd_599839] using wordTrace_append hprefix tailTrace_599839
  have hstable : (prefixWord ++ tailWord_599839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599839).length < 2 ^ (prefixWord ++ tailWord_599839).sum := by decide
  have hdescent : baseEnd_599839 < baseStart_599839 := by decide
  rcases family_descends (prefixWord ++ tailWord_599839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599875 : List Nat := [1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 4]
def baseStart_599875 : Nat := 118140960795 + 599875 * 2 ^ 59
def prefixEnd_599875 : Nat := 4983230072969 + 3 ^ 40 * 599875 * 2
def baseEnd_599875 : Nat := 308024207615945720003731

theorem tailTrace_599875 : CollatzResearch.WordTrace tailWord_599875 prefixEnd_599875 308024207615945720003731 := by
  unfold tailWord_599875
  simp only [CollatzResearch.WordTrace]
  refine ⟨21879238701762800338609079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14586159134508533559072719 21879238701762800338609079)
  ·
    refine ⟨32818858052644200507913619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21879238701762800338609079 32818858052644200507913619)
    ·
      refine ⟨49228287078966300761870429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32818858052644200507913619 49228287078966300761870429)
      ·
        refine ⟨18460607654612362785701411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49228287078966300761870429 18460607654612362785701411)
        ·
          refine ⟨27690911481918544178552117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18460607654612362785701411 27690911481918544178552117)
          ·
            refine ⟨2596022951429863516739261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27690911481918544178552117 2596022951429863516739261)
            ·
              refine ⟨973508606786198818777223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2596022951429863516739261 973508606786198818777223)
              ·
                refine ⟨1460262910179298228165835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 973508606786198818777223 1460262910179298228165835)
                ·
                  refine ⟨2190394365268947342248753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1460262910179298228165835 2190394365268947342248753)
                  ·
                    refine ⟨1642795773951710506686565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2190394365268947342248753 1642795773951710506686565)
                    ·
                      refine ⟨308024207615945720003731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1642795773951710506686565 308024207615945720003731)
                      ·
                        rfl

theorem cell23_599875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 4].length) (baseStart_599875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599875 prefixEnd_599875 := by exact prefixLift 599875
  have htrace : WordTrace (prefixWord ++ tailWord_599875) baseStart_599875 baseEnd_599875 := by
    simpa [prefixWord, tailWord_599875, baseEnd_599875] using wordTrace_append hprefix tailTrace_599875
  have hstable : (prefixWord ++ tailWord_599875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599875).length < 2 ^ (prefixWord ++ tailWord_599875).sum := by decide
  have hdescent : baseEnd_599875 < baseStart_599875 := by decide
  rcases family_descends (prefixWord ++ tailWord_599875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599882 : List Nat := [3, 1, 2, 1, 1, 1, 6, 2, 1, 2, 3]
def baseStart_599882 : Nat := 118140960795 + 599882 * 2 ^ 59
def prefixEnd_599882 : Nat := 4983230072969 + 3 ^ 40 * 599882 * 2
def baseEnd_599882 : Nat := 308027801980527192616199

theorem tailTrace_599882 : CollatzResearch.WordTrace tailWord_599882 prefixEnd_599882 308027801980527192616199 := by
  unfold tailWord_599882
  simp only [CollatzResearch.WordTrace]
  refine ⟨5469873503184360133528475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14586329341824960356075933 5469873503184360133528475)
  ·
    refine ⟨8204810254776540200292713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5469873503184360133528475 8204810254776540200292713)
    ·
      refine ⟨6153607691082405150219535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8204810254776540200292713 6153607691082405150219535)
      ·
        refine ⟨9230411536623607725329303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6153607691082405150219535 9230411536623607725329303)
        ·
          refine ⟨13845617304935411587993955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9230411536623607725329303 13845617304935411587993955)
          ·
            refine ⟨20768425957403117381990933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13845617304935411587993955 20768425957403117381990933)
            ·
              refine ⟨973519966753271127280825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20768425957403117381990933 973519966753271127280825)
              ·
                refine ⟨730139975064953345460619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 973519966753271127280825 730139975064953345460619)
                ·
                  refine ⟨1095209962597430018190929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 730139975064953345460619 1095209962597430018190929)
                  ·
                    refine ⟨821407471948072513643197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1095209962597430018190929 821407471948072513643197)
                    ·
                      refine ⟨308027801980527192616199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 821407471948072513643197 308027801980527192616199)
                      ·
                        rfl

theorem cell23_599882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_599882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599882 prefixEnd_599882 := by exact prefixLift 599882
  have htrace : WordTrace (prefixWord ++ tailWord_599882) baseStart_599882 baseEnd_599882 := by
    simpa [prefixWord, tailWord_599882, baseEnd_599882] using wordTrace_append hprefix tailTrace_599882
  have hstable : (prefixWord ++ tailWord_599882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599882).length < 2 ^ (prefixWord ++ tailWord_599882).sum := by decide
  have hdescent : baseEnd_599882 < baseStart_599882 := by decide
  rcases family_descends (prefixWord ++ tailWord_599882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599912 : List Nat := [2, 1, 4, 2, 1, 1, 1, 3, 4, 1, 3]
def baseStart_599912 : Nat := 118140960795 + 599912 * 2 ^ 59
def prefixEnd_599912 : Nat := 4983230072969 + 3 ^ 40 * 599912 * 2
def baseEnd_599912 : Nat := 308043206400162075241061

theorem tailTrace_599912 : CollatzResearch.WordTrace tailWord_599912 prefixEnd_599912 308043206400162075241061 := by
  unfold tailWord_599912
  simp only [CollatzResearch.WordTrace]
  refine ⟨10940294101314377828852995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14587058801752503771803993 10940294101314377828852995)
  ·
    refine ⟨16410441151971566743279493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10940294101314377828852995 16410441151971566743279493)
    ·
      refine ⟨3076957715994668764364905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16410441151971566743279493 3076957715994668764364905)
      ·
        refine ⟨2307718286996001573273679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3076957715994668764364905 2307718286996001573273679)
        ·
          refine ⟨3461577430494002359910519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2307718286996001573273679 3461577430494002359910519)
          ·
            refine ⟨5192366145741003539865779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3461577430494002359910519 5192366145741003539865779)
            ·
              refine ⟨7788549218611505309798669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5192366145741003539865779 7788549218611505309798669)
              ·
                refine ⟨2920705956979314491174501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7788549218611505309798669 2920705956979314491174501)
                ·
                  refine ⟨547632366933621467095219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2920705956979314491174501 547632366933621467095219)
                  ·
                    refine ⟨821448550400432200642829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 547632366933621467095219 821448550400432200642829)
                    ·
                      refine ⟨308043206400162075241061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 821448550400432200642829 308043206400162075241061)
                      ·
                        rfl

theorem cell23_599912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_599912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599912 prefixEnd_599912 := by exact prefixLift 599912
  have htrace : WordTrace (prefixWord ++ tailWord_599912) baseStart_599912 baseEnd_599912 := by
    simpa [prefixWord, tailWord_599912, baseEnd_599912] using wordTrace_append hprefix tailTrace_599912
  have hstable : (prefixWord ++ tailWord_599912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599912).length < 2 ^ (prefixWord ++ tailWord_599912).sum := by decide
  have hdescent : baseEnd_599912 < baseStart_599912 := by decide
  rcases family_descends (prefixWord ++ tailWord_599912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599922 : List Nat := [3, 2, 1, 2, 1, 1, 1, 4, 3, 3, 2]
def baseStart_599922 : Nat := 118140960795 + 599922 * 2 ^ 59
def prefixEnd_599922 : Nat := 4983230072969 + 3 ^ 40 * 599922 * 2
def baseEnd_599922 : Nat := 308048341206707036116015

theorem tailTrace_599922 : CollatzResearch.WordTrace tailWord_599922 prefixEnd_599922 308048341206707036116015 := by
  unfold tailWord_599922
  simp only [CollatzResearch.WordTrace]
  refine ⟨5470238233148131841392505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14587301955061684910380013 5470238233148131841392505)
  ·
    refine ⟨4102678674861098881044379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5470238233148131841392505 4102678674861098881044379)
    ·
      refine ⟨6154018012291648321566569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4102678674861098881044379 6154018012291648321566569)
      ·
        refine ⟨4615513509218736241174927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6154018012291648321566569 4615513509218736241174927)
        ·
          refine ⟨6923270263828104361762391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4615513509218736241174927 6923270263828104361762391)
          ·
            refine ⟨10384905395742156542643587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6923270263828104361762391 10384905395742156542643587)
            ·
              refine ⟨15577358093613234813965381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10384905395742156542643587 15577358093613234813965381)
              ·
                refine ⟨2920754642552481527618509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15577358093613234813965381 2920754642552481527618509)
                ·
                  refine ⟨1095282990957180572856941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2920754642552481527618509 1095282990957180572856941)
                  ·
                    refine ⟨410731121608942714821353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1095282990957180572856941 410731121608942714821353)
                    ·
                      refine ⟨308048341206707036116015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 410731121608942714821353 308048341206707036116015)
                      ·
                        rfl

theorem cell23_599922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_599922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599922 prefixEnd_599922 := by exact prefixLift 599922
  have htrace : WordTrace (prefixWord ++ tailWord_599922) baseStart_599922 baseEnd_599922 := by
    simpa [prefixWord, tailWord_599922, baseEnd_599922] using wordTrace_append hprefix tailTrace_599922
  have hstable : (prefixWord ++ tailWord_599922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599922).length < 2 ^ (prefixWord ++ tailWord_599922).sum := by decide
  have hdescent : baseEnd_599922 < baseStart_599922 := by decide
  rcases family_descends (prefixWord ++ tailWord_599922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599928 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 6, 6]
def baseStart_599928 : Nat := 118140960795 + 599928 * 2 ^ 59
def prefixEnd_599928 : Nat := 4983230072969 + 3 ^ 40 * 599928 * 2
def baseEnd_599928 : Nat := 102683807363544670880329

theorem tailTrace_599928 : CollatzResearch.WordTrace tailWord_599928 prefixEnd_599928 102683807363544670880329 := by
  unfold tailWord_599928
  simp only [CollatzResearch.WordTrace]
  refine ⟨10940585885285395195144219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14587447847047193593525625 10940585885285395195144219)
  ·
    refine ⟨16410878827928092792716329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10940585885285395195144219 16410878827928092792716329)
    ·
      refine ⟨12308159120946069594537247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16410878827928092792716329 12308159120946069594537247)
      ·
        refine ⟨18462238681419104391805871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12308159120946069594537247 18462238681419104391805871)
        ·
          refine ⟨27693358022128656587708807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18462238681419104391805871 27693358022128656587708807)
          ·
            refine ⟨41540037033192984881563211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27693358022128656587708807 41540037033192984881563211)
            ·
              refine ⟨62310055549789477322344817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41540037033192984881563211 62310055549789477322344817)
              ·
                refine ⟨46732541662342107991758613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62310055549789477322344817 46732541662342107991758613)
                ·
                  refine ⟨2190587890422286312113685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46732541662342107991758613 2190587890422286312113685)
                  ·
                    refine ⟨102683807363544670880329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2190587890422286312113685 102683807363544670880329)
                    ·
                      rfl

theorem cell23_599928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 6, 6].length) (baseStart_599928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599928 prefixEnd_599928 := by exact prefixLift 599928
  have htrace : WordTrace (prefixWord ++ tailWord_599928) baseStart_599928 baseEnd_599928 := by
    simpa [prefixWord, tailWord_599928, baseEnd_599928] using wordTrace_append hprefix tailTrace_599928
  have hstable : (prefixWord ++ tailWord_599928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599928).length < 2 ^ (prefixWord ++ tailWord_599928).sum := by decide
  have hdescent : baseEnd_599928 < baseStart_599928 := by decide
  rcases family_descends (prefixWord ++ tailWord_599928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_599939 : List Nat := [1, 1, 1, 3, 4, 2, 3, 2, 1, 3, 2]
def baseStart_599939 : Nat := 118140960795 + 599939 * 2 ^ 59
def prefixEnd_599939 : Nat := 4983230072969 + 3 ^ 40 * 599939 * 2
def baseEnd_599939 : Nat := 308057070377833469603437

theorem tailTrace_599939 : CollatzResearch.WordTrace tailWord_599939 prefixEnd_599939 308057070377833469603437 := by
  unfold tailWord_599939
  simp only [CollatzResearch.WordTrace]
  refine ⟨21881572973530939268938871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14587715315687292845959247 21881572973530939268938871)
  ·
    refine ⟨32822359460296408903408307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21881572973530939268938871 32822359460296408903408307)
    ·
      refine ⟨49233539190444613355112461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32822359460296408903408307 49233539190444613355112461)
      ·
        refine ⟨18462577196416730008167173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49233539190444613355112461 18462577196416730008167173)
        ·
          refine ⟨3461733224328136876531345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18462577196416730008167173 3461733224328136876531345)
          ·
            refine ⟨2596299918246102657398509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3461733224328136876531345 2596299918246102657398509)
            ·
              refine ⟨973612469342288496524441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2596299918246102657398509 973612469342288496524441)
              ·
                refine ⟨730209352006716372393331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 973612469342288496524441 730209352006716372393331)
                ·
                  refine ⟨1095314028010074558589997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 730209352006716372393331 1095314028010074558589997)
                  ·
                    refine ⟨410742760503777959471249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1095314028010074558589997 410742760503777959471249)
                    ·
                      refine ⟨308057070377833469603437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 410742760503777959471249 308057070377833469603437)
                      ·
                        rfl

theorem cell23_599939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 3, 2].length) (baseStart_599939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_599939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_599939 prefixEnd_599939 := by exact prefixLift 599939
  have htrace : WordTrace (prefixWord ++ tailWord_599939) baseStart_599939 baseEnd_599939 := by
    simpa [prefixWord, tailWord_599939, baseEnd_599939] using wordTrace_append hprefix tailTrace_599939
  have hstable : (prefixWord ++ tailWord_599939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_599939).length < 2 ^ (prefixWord ++ tailWord_599939).sum := by decide
  have hdescent : baseEnd_599939 < baseStart_599939 := by decide
  rcases family_descends (prefixWord ++ tailWord_599939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600005 : List Nat := [1, 3, 1, 1, 1, 1, 1, 7, 2, 5]
def baseStart_600005 : Nat := 118140960795 + 600005 * 2 ^ 59
def prefixEnd_600005 : Nat := 4983230072969 + 3 ^ 40 * 600005 * 2
def baseEnd_600005 : Nat := 102696986700343403792711

theorem tailTrace_600005 : CollatzResearch.WordTrace tailWord_600005 prefixEnd_600005 102696986700343403792711 := by
  unfold tailWord_600005
  simp only [CollatzResearch.WordTrace]
  refine ⟨21883980191291832540841469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14589320127527888360560979 21883980191291832540841469)
  ·
    refine ⟨8206492571734437202815551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21883980191291832540841469 8206492571734437202815551)
    ·
      refine ⟨12309738857601655804223327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8206492571734437202815551 12309738857601655804223327)
      ·
        refine ⟨18464608286402483706334991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12309738857601655804223327 18464608286402483706334991)
        ·
          refine ⟨27696912429603725559502487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18464608286402483706334991 27696912429603725559502487)
          ·
            refine ⟨41545368644405588339253731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27696912429603725559502487 41545368644405588339253731)
            ·
              refine ⟨62318052966608382508880597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41545368644405588339253731 62318052966608382508880597)
              ·
                refine ⟨1460579366404883965051889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 62318052966608382508880597 1460579366404883965051889)
                ·
                  refine ⟨1095434524803662973788917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1460579366404883965051889 1095434524803662973788917)
                  ·
                    refine ⟨102696986700343403792711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1095434524803662973788917 102696986700343403792711)
                    ·
                      rfl

theorem cell23_600005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 5].length) (baseStart_600005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600005 prefixEnd_600005 := by exact prefixLift 600005
  have htrace : WordTrace (prefixWord ++ tailWord_600005) baseStart_600005 baseEnd_600005 := by
    simpa [prefixWord, tailWord_600005, baseEnd_600005] using wordTrace_append hprefix tailTrace_600005
  have hstable : (prefixWord ++ tailWord_600005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600005).length < 2 ^ (prefixWord ++ tailWord_600005).sum := by decide
  have hdescent : baseEnd_600005 < baseStart_600005 := by decide
  rcases family_descends (prefixWord ++ tailWord_600005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600065 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 10]
def baseStart_600065 : Nat := 118140960795 + 600065 * 2 ^ 59
def prefixEnd_600065 : Nat := 4983230072969 + 3 ^ 40 * 600065 * 2
def baseEnd_600065 : Nat := 34235752104477775180873

theorem tailTrace_600065 : CollatzResearch.WordTrace tailWord_600065 prefixEnd_600065 34235752104477775180873 := by
  unfold tailWord_600065
  simp only [CollatzResearch.WordTrace]
  refine ⟨21886168571074462788025649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14590779047382975192017099 21886168571074462788025649)
  ·
    refine ⟨16414626428305847091019237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21886168571074462788025649 16414626428305847091019237)
    ·
      refine ⟨3077742455307346329566107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16414626428305847091019237 3077742455307346329566107)
      ·
        refine ⟨4616613682961019494349161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3077742455307346329566107 4616613682961019494349161)
        ·
          refine ⟨3462460262220764620761871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4616613682961019494349161 3462460262220764620761871)
          ·
            refine ⟨5193690393331146931142807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3462460262220764620761871 5193690393331146931142807)
            ·
              refine ⟨7790535589996720396714211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5193690393331146931142807 7790535589996720396714211)
              ·
                refine ⟨11685803384995080595071317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7790535589996720396714211 11685803384995080595071317)
                ·
                  refine ⟨34235752104477775180873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 11685803384995080595071317 34235752104477775180873)
                  ·
                    rfl

theorem cell23_600065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 10].length) (baseStart_600065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600065 prefixEnd_600065 := by exact prefixLift 600065
  have htrace : WordTrace (prefixWord ++ tailWord_600065) baseStart_600065 baseEnd_600065 := by
    simpa [prefixWord, tailWord_600065, baseEnd_600065] using wordTrace_append hprefix tailTrace_600065
  have hstable : (prefixWord ++ tailWord_600065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600065).length < 2 ^ (prefixWord ++ tailWord_600065).sum := by decide
  have hdescent : baseEnd_600065 < baseStart_600065 := by decide
  rcases family_descends (prefixWord ++ tailWord_600065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600112 : List Nat := [2, 1, 1, 1, 2, 6, 1, 1, 3, 5]
def baseStart_600112 : Nat := 118140960795 + 600112 * 2 ^ 59
def prefixEnd_600112 : Nat := 4983230072969 + 3 ^ 40 * 600112 * 2
def baseEnd_600112 : Nat := 102715300843687097580047

theorem tailTrace_600112 : CollatzResearch.WordTrace tailWord_600112 prefixEnd_600112 102715300843687097580047 := by
  unfold tailWord_600112
  simp only [CollatzResearch.WordTrace]
  refine ⟨10943941400952094907493295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14591921867936126543324393 10943941400952094907493295)
  ·
    refine ⟨16415912101428142361239943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10943941400952094907493295 16415912101428142361239943)
    ·
      refine ⟨24623868152142213541859915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16415912101428142361239943 24623868152142213541859915)
      ·
        refine ⟨36935802228213320312789873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24623868152142213541859915 36935802228213320312789873)
        ·
          refine ⟨27701851671159990234592405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36935802228213320312789873 27701851671159990234592405)
          ·
            refine ⟨1298524297085624542246519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 27701851671159990234592405 1298524297085624542246519)
            ·
              refine ⟨1947786445628436813369779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1298524297085624542246519 1947786445628436813369779)
              ·
                refine ⟨2921679668442655220054669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1947786445628436813369779 2921679668442655220054669)
                ·
                  refine ⟨1095629875665995707520501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2921679668442655220054669 1095629875665995707520501)
                  ·
                    refine ⟨102715300843687097580047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1095629875665995707520501 102715300843687097580047)
                    ·
                      rfl

theorem cell23_600112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 3, 5].length) (baseStart_600112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600112 prefixEnd_600112 := by exact prefixLift 600112
  have htrace : WordTrace (prefixWord ++ tailWord_600112) baseStart_600112 baseEnd_600112 := by
    simpa [prefixWord, tailWord_600112, baseEnd_600112] using wordTrace_append hprefix tailTrace_600112
  have hstable : (prefixWord ++ tailWord_600112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600112).length < 2 ^ (prefixWord ++ tailWord_600112).sum := by decide
  have hdescent : baseEnd_600112 < baseStart_600112 := by decide
  rcases family_descends (prefixWord ++ tailWord_600112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600119 : List Nat := [1, 1, 3, 1, 2, 2, 3, 3, 2, 3, 2]
def baseStart_600119 : Nat := 118140960795 + 600119 * 2 ^ 59
def prefixEnd_600119 : Nat := 4983230072969 + 3 ^ 40 * 600119 * 2
def baseEnd_600119 : Nat := 308149496895642765352609

theorem tailTrace_600119 : CollatzResearch.WordTrace tailWord_600119 prefixEnd_600119 308149496895642765352609 := by
  unfold tailWord_600119
  simp only [CollatzResearch.WordTrace]
  refine ⟨21888138112878830010491411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14592092075252553340327607 21888138112878830010491411)
  ·
    refine ⟨32832207169318245015737117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21888138112878830010491411 32832207169318245015737117)
    ·
      refine ⟨12312077688494341880901419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32832207169318245015737117 12312077688494341880901419)
      ·
        refine ⟨18468116532741512821352129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12312077688494341880901419 18468116532741512821352129)
        ·
          refine ⟨13851087399556134616014097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18468116532741512821352129 13851087399556134616014097)
          ·
            refine ⟨10388315549667100962010573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13851087399556134616014097 10388315549667100962010573)
            ·
              refine ⟨3895618331125162860753965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10388315549667100962010573 3895618331125162860753965)
              ·
                refine ⟨1460856874171936072782737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3895618331125162860753965 1460856874171936072782737)
                ·
                  refine ⟨1095642655628952054587053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1460856874171936072782737 1095642655628952054587053)
                  ·
                    refine ⟨410865995860857020470145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1095642655628952054587053 410865995860857020470145)
                    ·
                      refine ⟨308149496895642765352609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 410865995860857020470145 308149496895642765352609)
                      ·
                        rfl

theorem cell23_600119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 3, 2].length) (baseStart_600119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600119 prefixEnd_600119 := by exact prefixLift 600119
  have htrace : WordTrace (prefixWord ++ tailWord_600119) baseStart_600119 baseEnd_600119 := by
    simpa [prefixWord, tailWord_600119, baseEnd_600119] using wordTrace_append hprefix tailTrace_600119
  have hstable : (prefixWord ++ tailWord_600119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600119).length < 2 ^ (prefixWord ++ tailWord_600119).sum := by decide
  have hdescent : baseEnd_600119 < baseStart_600119 := by decide
  rcases family_descends (prefixWord ++ tailWord_600119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600169 : List Nat := [1, 2, 1, 1, 1, 5, 2, 4, 1, 2, 3]
def baseStart_600169 : Nat := 118140960795 + 600169 * 2 ^ 59
def prefixEnd_600169 : Nat := 4983230072969 + 3 ^ 40 * 600169 * 2
def baseEnd_600169 : Nat := 308175170928367569727379

theorem tailTrace_600169 : CollatzResearch.WordTrace tailWord_600169 prefixEnd_600169 308175170928367569727379 := by
  unfold tailWord_600169
  simp only [CollatzResearch.WordTrace]
  refine ⟨21889961762697688549811561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14593307841798459033207707 21889961762697688549811561)
  ·
    refine ⟨16417471322023266412358671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21889961762697688549811561 16417471322023266412358671)
    ·
      refine ⟨24626206983034899618538007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16417471322023266412358671 24626206983034899618538007)
      ·
        refine ⟨36939310474552349427807011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24626206983034899618538007 36939310474552349427807011)
        ·
          refine ⟨55408965711828524141710517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36939310474552349427807011 55408965711828524141710517)
          ·
            refine ⟨5194590535483924138285361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55408965711828524141710517 5194590535483924138285361)
            ·
              refine ⟨3895942901612943103714021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5194590535483924138285361 3895942901612943103714021)
              ·
                refine ⟨730489294052426831946379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3895942901612943103714021 730489294052426831946379)
                ·
                  refine ⟨1095733941078640247919569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 730489294052426831946379 1095733941078640247919569)
                  ·
                    refine ⟨821800455808980185939677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1095733941078640247919569 821800455808980185939677)
                    ·
                      refine ⟨308175170928367569727379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 821800455808980185939677 308175170928367569727379)
                      ·
                        rfl

theorem cell23_600169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 2, 3].length) (baseStart_600169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600169 prefixEnd_600169 := by exact prefixLift 600169
  have htrace : WordTrace (prefixWord ++ tailWord_600169) baseStart_600169 baseEnd_600169 := by
    simpa [prefixWord, tailWord_600169, baseEnd_600169] using wordTrace_append hprefix tailTrace_600169
  have hstable : (prefixWord ++ tailWord_600169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600169).length < 2 ^ (prefixWord ++ tailWord_600169).sum := by decide
  have hdescent : baseEnd_600169 < baseStart_600169 := by decide
  rcases family_descends (prefixWord ++ tailWord_600169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600170 : List Nat := [3, 1, 3, 2, 4, 1, 1, 1, 2, 3, 2]
def baseStart_600170 : Nat := 118140960795 + 600170 * 2 ^ 59
def prefixEnd_600170 : Nat := 4983230072969 + 3 ^ 40 * 600170 * 2
def baseEnd_600170 : Nat := 308175684409022065814875

theorem tailTrace_600170 : CollatzResearch.WordTrace tailWord_600170 prefixEnd_600170 308175684409022065814875 := by
  unfold tailWord_600170
  simp only [CollatzResearch.WordTrace]
  refine ⟨5472499558923516430149491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14593332157129377147065309 5472499558923516430149491)
  ·
    refine ⟨8208749338385274645224237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5472499558923516430149491 8208749338385274645224237)
    ·
      refine ⟨3078281001894477991959089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8208749338385274645224237 3078281001894477991959089)
      ·
        refine ⟨2308710751420858493969317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3078281001894477991959089 2308710751420858493969317)
        ·
          refine ⟨432883265891410967619247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2308710751420858493969317 432883265891410967619247)
          ·
            refine ⟨649324898837116451428871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432883265891410967619247 649324898837116451428871)
            ·
              refine ⟨973987348255674677143307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 649324898837116451428871 973987348255674677143307)
              ·
                refine ⟨1460981022383512015714961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 973987348255674677143307 1460981022383512015714961)
                ·
                  refine ⟨1095735766787634011786221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1460981022383512015714961 1095735766787634011786221)
                  ·
                    refine ⟨410900912545362754419833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1095735766787634011786221 410900912545362754419833)
                    ·
                      refine ⟨308175684409022065814875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 410900912545362754419833 308175684409022065814875)
                      ·
                        rfl

theorem cell23_600170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_600170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600170 prefixEnd_600170 := by exact prefixLift 600170
  have htrace : WordTrace (prefixWord ++ tailWord_600170) baseStart_600170 baseEnd_600170 := by
    simpa [prefixWord, tailWord_600170, baseEnd_600170] using wordTrace_append hprefix tailTrace_600170
  have hstable : (prefixWord ++ tailWord_600170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600170).length < 2 ^ (prefixWord ++ tailWord_600170).sum := by decide
  have hdescent : baseEnd_600170 < baseStart_600170 := by decide
  rcases family_descends (prefixWord ++ tailWord_600170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600183 : List Nat := [1, 1, 3, 1, 1, 5, 1, 5, 1, 2, 2]
def baseStart_600183 : Nat := 118140960795 + 600183 * 2 ^ 59
def prefixEnd_600183 : Nat := 4983230072969 + 3 ^ 40 * 600183 * 2
def baseEnd_600183 : Nat := 308182359657530514952315

theorem tailTrace_600183 : CollatzResearch.WordTrace tailWord_600183 prefixEnd_600183 308182359657530514952315 := by
  unfold tailWord_600183
  simp only [CollatzResearch.WordTrace]
  refine ⟨21890472384646968940821203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14593648256431312627214135 21890472384646968940821203)
  ·
    refine ⟨32835708576970453411231805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21890472384646968940821203 32835708576970453411231805)
    ·
      refine ⟨12313390716363920029211927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32835708576970453411231805 12313390716363920029211927)
      ·
        refine ⟨18470086074545880043817891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12313390716363920029211927 18470086074545880043817891)
        ·
          refine ⟨27705129111818820065726837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18470086074545880043817891 27705129111818820065726837)
          ·
            refine ⟨2597355854233014381161891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27705129111818820065726837 2597355854233014381161891)
            ·
              refine ⟨3896033781349521571742837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2597355854233014381161891 3896033781349521571742837)
              ·
                refine ⟨365253167001517647350891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3896033781349521571742837 365253167001517647350891)
                ·
                  refine ⟨547879750502276471026337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 365253167001517647350891 547879750502276471026337)
                  ·
                    refine ⟨410909812876707353269753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 547879750502276471026337 410909812876707353269753)
                    ·
                      refine ⟨308182359657530514952315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 410909812876707353269753 308182359657530514952315)
                      ·
                        rfl

theorem cell23_600183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 5, 1, 2, 2].length) (baseStart_600183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600183 prefixEnd_600183 := by exact prefixLift 600183
  have htrace : WordTrace (prefixWord ++ tailWord_600183) baseStart_600183 baseEnd_600183 := by
    simpa [prefixWord, tailWord_600183, baseEnd_600183] using wordTrace_append hprefix tailTrace_600183
  have hstable : (prefixWord ++ tailWord_600183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600183).length < 2 ^ (prefixWord ++ tailWord_600183).sum := by decide
  have hdescent : baseEnd_600183 < baseStart_600183 := by decide
  rcases family_descends (prefixWord ++ tailWord_600183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600193 : List Nat := [1, 2, 4, 2, 3, 2, 1, 2, 2, 4]
def baseStart_600193 : Nat := 118140960795 + 600193 * 2 ^ 59
def prefixEnd_600193 : Nat := 4983230072969 + 3 ^ 40 * 600193 * 2
def baseEnd_600193 : Nat := 102729164821358491942423

theorem tailTrace_600193 : CollatzResearch.WordTrace tailWord_600193 prefixEnd_600193 102729164821358491942423 := by
  unfold tailWord_600193
  simp only [CollatzResearch.WordTrace]
  refine ⟨21890837114610740648685233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14593891409740493765790155 21890837114610740648685233)
  ·
    refine ⟨16418127835958055486513925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21890837114610740648685233 16418127835958055486513925)
    ·
      refine ⟨3078398969242135403721361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16418127835958055486513925 3078398969242135403721361)
      ·
        refine ⟨2308799226931601552791021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3078398969242135403721361 2308799226931601552791021)
        ·
          refine ⟨865799710099350582296633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2308799226931601552791021 865799710099350582296633)
          ·
            refine ⟨649349782574512936722475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 865799710099350582296633 649349782574512936722475)
            ·
              refine ⟨974024673861769405083713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 649349782574512936722475 974024673861769405083713)
              ·
                refine ⟨730518505396327053812785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 974024673861769405083713 730518505396327053812785)
                ·
                  refine ⟨547888879047245290359589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 730518505396327053812785 547888879047245290359589)
                  ·
                    refine ⟨102729164821358491942423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 547888879047245290359589 102729164821358491942423)
                    ·
                      rfl

theorem cell23_600193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_600193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600193 prefixEnd_600193 := by exact prefixLift 600193
  have htrace : WordTrace (prefixWord ++ tailWord_600193) baseStart_600193 baseEnd_600193 := by
    simpa [prefixWord, tailWord_600193, baseEnd_600193] using wordTrace_append hprefix tailTrace_600193
  have hstable : (prefixWord ++ tailWord_600193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600193).length < 2 ^ (prefixWord ++ tailWord_600193).sum := by decide
  have hdescent : baseEnd_600193 < baseStart_600193 := by decide
  rcases family_descends (prefixWord ++ tailWord_600193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600200 : List Nat := [2, 1, 3, 4, 1, 1, 2, 4, 1, 2, 2]
def baseStart_600200 : Nat := 118140960795 + 600200 * 2 ^ 59
def prefixEnd_600200 : Nat := 4983230072969 + 3 ^ 40 * 600200 * 2
def baseEnd_600200 : Nat := 308191088828656948439737

theorem tailTrace_600200 : CollatzResearch.WordTrace tailWord_600200 prefixEnd_600200 308191088828656948439737 := by
  unfold tailWord_600200
  simp only [CollatzResearch.WordTrace]
  refine ⟨10945546212792690422095027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14594061617056920562793369 10945546212792690422095027)
  ·
    refine ⟨16418319319189035633142541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10945546212792690422095027 16418319319189035633142541)
    ·
      refine ⟨6156869744695888362428453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16418319319189035633142541 6156869744695888362428453)
      ·
        refine ⟨1154413077130479067955335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6156869744695888362428453 1154413077130479067955335)
        ·
          refine ⟨1731619615695718601933003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1154413077130479067955335 1731619615695718601933003)
          ·
            refine ⟨2597429423543577902899505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1731619615695718601933003 2597429423543577902899505)
            ·
              refine ⟨1948072067657683427174629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2597429423543577902899505 1948072067657683427174629)
              ·
                refine ⟨365263512685815642595243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1948072067657683427174629 365263512685815642595243)
                ·
                  refine ⟨547895269028723463892865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 365263512685815642595243 547895269028723463892865)
                  ·
                    refine ⟨410921451771542597919649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 547895269028723463892865 410921451771542597919649)
                    ·
                      refine ⟨308191088828656948439737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 410921451771542597919649 308191088828656948439737)
                      ·
                        rfl

theorem cell23_600200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_600200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600200 prefixEnd_600200 := by exact prefixLift 600200
  have htrace : WordTrace (prefixWord ++ tailWord_600200) baseStart_600200 baseEnd_600200 := by
    simpa [prefixWord, tailWord_600200, baseEnd_600200] using wordTrace_append hprefix tailTrace_600200
  have hstable : (prefixWord ++ tailWord_600200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600200).length < 2 ^ (prefixWord ++ tailWord_600200).sum := by decide
  have hdescent : baseEnd_600200 < baseStart_600200 := by decide
  rcases family_descends (prefixWord ++ tailWord_600200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600234 : List Nat := [3, 1, 5, 1, 2, 2, 1, 3, 1, 2, 2]
def baseStart_600234 : Nat := 118140960795 + 600234 * 2 ^ 59
def prefixEnd_600234 : Nat := 4983230072969 + 3 ^ 40 * 600234 * 2
def baseEnd_600234 : Nat := 308208547170909815414581

theorem tailTrace_600234 : CollatzResearch.WordTrace tailWord_600234 prefixEnd_600234 308208547170909815414581 := by
  unfold tailWord_600234
  simp only [CollatzResearch.WordTrace]
  refine ⟨5473083126865551162731939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14594888338308136433951837 5473083126865551162731939)
  ·
    refine ⟨8209624690298326744097909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5473083126865551162731939 8209624690298326744097909)
    ·
      refine ⟨769652314715468132259179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8209624690298326744097909 769652314715468132259179)
      ·
        refine ⟨1154478472073202198388769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 769652314715468132259179 1154478472073202198388769)
        ·
          refine ⟨865858854054901648791577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1154478472073202198388769 865858854054901648791577)
          ·
            refine ⟨649394140541176236593683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 865858854054901648791577 649394140541176236593683)
            ·
              refine ⟨974091210811764354890525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 649394140541176236593683 974091210811764354890525)
              ·
                refine ⟨365284204054411633083947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 974091210811764354890525 365284204054411633083947)
                ·
                  refine ⟨547926306081617449625921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 365284204054411633083947 547926306081617449625921)
                  ·
                    refine ⟨410944729561213087219441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 547926306081617449625921 410944729561213087219441)
                    ·
                      refine ⟨308208547170909815414581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 410944729561213087219441 308208547170909815414581)
                      ·
                        rfl

theorem cell23_600234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_600234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600234 prefixEnd_600234 := by exact prefixLift 600234
  have htrace : WordTrace (prefixWord ++ tailWord_600234) baseStart_600234 baseEnd_600234 := by
    simpa [prefixWord, tailWord_600234, baseEnd_600234] using wordTrace_append hprefix tailTrace_600234
  have hstable : (prefixWord ++ tailWord_600234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600234).length < 2 ^ (prefixWord ++ tailWord_600234).sum := by decide
  have hdescent : baseEnd_600234 < baseStart_600234 := by decide
  rcases family_descends (prefixWord ++ tailWord_600234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600239 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 3, 4, 2]
def baseStart_600239 : Nat := 118140960795 + 600239 * 2 ^ 59
def prefixEnd_600239 : Nat := 4983230072969 + 3 ^ 40 * 600239 * 2
def baseEnd_600239 : Nat := 308211114574182295852057

theorem tailTrace_600239 : CollatzResearch.WordTrace tailWord_600239 prefixEnd_600239 308211114574182295852057 := by
  unfold tailWord_600239
  simp only [CollatzResearch.WordTrace]
  refine ⟨21892514872444090504859771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14595009914962727003239847 21892514872444090504859771)
  ·
    refine ⟨32838772308666135757289657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21892514872444090504859771 32838772308666135757289657)
    ·
      refine ⟨24629079231499601817967243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32838772308666135757289657 24629079231499601817967243)
      ·
        refine ⟨36943618847249402726950865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24629079231499601817967243 36943618847249402726950865)
        ·
          refine ⟨27707714135437052045213149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36943618847249402726950865 27707714135437052045213149)
          ·
            refine ⟨10390392800788894516954931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27707714135437052045213149 10390392800788894516954931)
            ·
              refine ⟨15585589201183341775432397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10390392800788894516954931 15585589201183341775432397)
              ·
                refine ⟨5844595950443753165787149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15585589201183341775432397 5844595950443753165787149)
                ·
                  refine ⟨2191723481416407437170181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5844595950443753165787149 2191723481416407437170181)
                  ·
                    refine ⟨410948152765576394469409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2191723481416407437170181 410948152765576394469409)
                    ·
                      refine ⟨308211114574182295852057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 410948152765576394469409 308211114574182295852057)
                      ·
                        rfl

theorem cell23_600239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 4, 2].length) (baseStart_600239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600239 prefixEnd_600239 := by exact prefixLift 600239
  have htrace : WordTrace (prefixWord ++ tailWord_600239) baseStart_600239 baseEnd_600239 := by
    simpa [prefixWord, tailWord_600239, baseEnd_600239] using wordTrace_append hprefix tailTrace_600239
  have hstable : (prefixWord ++ tailWord_600239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600239).length < 2 ^ (prefixWord ++ tailWord_600239).sum := by decide
  have hdescent : baseEnd_600239 < baseStart_600239 := by decide
  rcases family_descends (prefixWord ++ tailWord_600239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600277 : List Nat := [1, 3, 2, 4, 3, 1, 1, 2, 1, 3, 2]
def baseStart_600277 : Nat := 118140960795 + 600277 * 2 ^ 59
def prefixEnd_600277 : Nat := 4983230072969 + 3 ^ 40 * 600277 * 2
def baseEnd_600277 : Nat := 308230626839053147176883

theorem tailTrace_600277 : CollatzResearch.WordTrace tailWord_600277 prefixEnd_600277 308230626839053147176883 := by
  unfold tailWord_600277
  simp only [CollatzResearch.WordTrace]
  refine ⟨21893900846306422994743085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14595933897537615329828723 21893900846306422994743085)
  ·
    refine ⟨8210212817364908623028657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21893900846306422994743085 8210212817364908623028657)
    ·
      refine ⟨6157659613023681467271493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8210212817364908623028657 6157659613023681467271493)
      ·
        refine ⟨1154561177441940275113405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6157659613023681467271493 1154561177441940275113405)
        ·
          refine ⟨432960441540727603167527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1154561177441940275113405 432960441540727603167527)
          ·
            refine ⟨649440662311091404751291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 432960441540727603167527 649440662311091404751291)
            ·
              refine ⟨974160993466637107126937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 649440662311091404751291 974160993466637107126937)
              ·
                refine ⟨730620745099977830345203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 974160993466637107126937 730620745099977830345203)
                ·
                  refine ⟨1095931117649966745517805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 730620745099977830345203 1095931117649966745517805)
                  ·
                    refine ⟨410974169118737529569177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1095931117649966745517805 410974169118737529569177)
                    ·
                      refine ⟨308230626839053147176883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 410974169118737529569177 308230626839053147176883)
                      ·
                        rfl

theorem cell23_600277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_600277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600277 prefixEnd_600277 := by exact prefixLift 600277
  have htrace : WordTrace (prefixWord ++ tailWord_600277) baseStart_600277 baseEnd_600277 := by
    simpa [prefixWord, tailWord_600277, baseEnd_600277] using wordTrace_append hprefix tailTrace_600277
  have hstable : (prefixWord ++ tailWord_600277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600277).length < 2 ^ (prefixWord ++ tailWord_600277).sum := by decide
  have hdescent : baseEnd_600277 < baseStart_600277 := by decide
  rcases family_descends (prefixWord ++ tailWord_600277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600316 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 2, 5, 2]
def baseStart_600316 : Nat := 118140960795 + 600316 * 2 ^ 59
def prefixEnd_600316 : Nat := 4983230072969 + 3 ^ 40 * 600316 * 2
def baseEnd_600316 : Nat := 308250652584578494589203

theorem tailTrace_600316 : CollatzResearch.WordTrace tailWord_600316 prefixEnd_600316 308250652584578494589203 := by
  unfold tailWord_600316
  simp only [CollatzResearch.WordTrace]
  refine ⟨10947661646582566327706401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14596882195443421770275201 10947661646582566327706401)
  ·
    refine ⟨8210746234936924745779801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10947661646582566327706401 8210746234936924745779801)
    ·
      refine ⟨6158059676202693559334851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8210746234936924745779801 6158059676202693559334851)
      ·
        refine ⟨9237089514304040339002277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6158059676202693559334851 9237089514304040339002277)
        ·
          refine ⟨1731954283932007563562927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9237089514304040339002277 1731954283932007563562927)
          ·
            refine ⟨2597931425898011345344391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1731954283932007563562927 2597931425898011345344391)
            ·
              refine ⟨3896897138847017018016587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2597931425898011345344391 3896897138847017018016587)
              ·
                refine ⟨5845345708270525527024881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3896897138847017018016587 5845345708270525527024881)
                ·
                  refine ⟨4384009281202894145268661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5845345708270525527024881 4384009281202894145268661)
                  ·
                    refine ⟨411000870112771326118937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4384009281202894145268661 411000870112771326118937)
                    ·
                      refine ⟨308250652584578494589203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 411000870112771326118937 308250652584578494589203)
                      ·
                        rfl

theorem cell23_600316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 2, 5, 2].length) (baseStart_600316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600316 prefixEnd_600316 := by exact prefixLift 600316
  have htrace : WordTrace (prefixWord ++ tailWord_600316) baseStart_600316 baseEnd_600316 := by
    simpa [prefixWord, tailWord_600316, baseEnd_600316] using wordTrace_append hprefix tailTrace_600316
  have hstable : (prefixWord ++ tailWord_600316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600316).length < 2 ^ (prefixWord ++ tailWord_600316).sum := by decide
  have hdescent : baseEnd_600316 < baseStart_600316 := by decide
  rcases family_descends (prefixWord ++ tailWord_600316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600346 : List Nat := [3, 1, 1, 3, 4, 1, 1, 1, 1, 3, 4]
def baseStart_600346 : Nat := 118140960795 + 600346 * 2 ^ 59
def prefixEnd_600346 : Nat := 4983230072969 + 3 ^ 40 * 600346 * 2
def baseEnd_600346 : Nat := 308266057004213377214065

theorem tailTrace_600346 : CollatzResearch.WordTrace tailWord_600346 prefixEnd_600346 308266057004213377214065 := by
  unfold tailWord_600346
  simp only [CollatzResearch.WordTrace]
  refine ⟨5474104370764111944751223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14597611655370965186003261 5474104370764111944751223)
  ·
    refine ⟨8211156556146167917126835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5474104370764111944751223 8211156556146167917126835)
    ·
      refine ⟨12316734834219251875690253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8211156556146167917126835 12316734834219251875690253)
      ·
        refine ⟨4618775562832219453383845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12316734834219251875690253 4618775562832219453383845)
        ·
          refine ⟨866020418031041147509471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4618775562832219453383845 866020418031041147509471)
          ·
            refine ⟨1299030627046561721264207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 866020418031041147509471 1299030627046561721264207)
            ·
              refine ⟨1948545940569842581896311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1299030627046561721264207 1948545940569842581896311)
              ·
                refine ⟨2922818910854763872844467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1948545940569842581896311 2922818910854763872844467)
                ·
                  refine ⟨4384228366282145809266701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2922818910854763872844467 4384228366282145809266701)
                  ·
                    refine ⟨1644085637355804678475013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4384228366282145809266701 1644085637355804678475013)
                    ·
                      refine ⟨308266057004213377214065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1644085637355804678475013 308266057004213377214065)
                      ·
                        rfl

theorem cell23_600346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_600346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600346 prefixEnd_600346 := by exact prefixLift 600346
  have htrace : WordTrace (prefixWord ++ tailWord_600346) baseStart_600346 baseEnd_600346 := by
    simpa [prefixWord, tailWord_600346, baseEnd_600346] using wordTrace_append hprefix tailTrace_600346
  have hstable : (prefixWord ++ tailWord_600346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600346).length < 2 ^ (prefixWord ++ tailWord_600346).sum := by decide
  have hdescent : baseEnd_600346 < baseStart_600346 := by decide
  rcases family_descends (prefixWord ++ tailWord_600346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600373 : List Nat := [1, 3, 3, 1, 2, 1, 1, 6, 1, 4]
def baseStart_600373 : Nat := 118140960795 + 600373 * 2 ^ 59
def prefixEnd_600373 : Nat := 4983230072969 + 3 ^ 40 * 600373 * 2
def baseEnd_600373 : Nat := 102759973660628257192147

theorem tailTrace_600373 : CollatzResearch.WordTrace tailWord_600373 prefixEnd_600373 102759973660628257192147 := by
  unfold tailWord_600373
  simp only [CollatzResearch.WordTrace]
  refine ⟨21897402253958631390237773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14598268169305754260158515 21897402253958631390237773)
  ·
    refine ⟨8211525845234486771339165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21897402253958631390237773 8211525845234486771339165)
    ·
      refine ⟨3079322191962932539252187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8211525845234486771339165 3079322191962932539252187)
      ·
        refine ⟨4618983287944398808878281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3079322191962932539252187 4618983287944398808878281)
        ·
          refine ⟨3464237465958299106658711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4618983287944398808878281 3464237465958299106658711)
          ·
            refine ⟨5196356198937448659988067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3464237465958299106658711 5196356198937448659988067)
            ·
              refine ⟨7794534298406172989982101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5196356198937448659988067 7794534298406172989982101)
              ·
                refine ⟨365368795237789358905411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7794534298406172989982101 365368795237789358905411)
                ·
                  refine ⟨548053192856684038358117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 365368795237789358905411 548053192856684038358117)
                  ·
                    refine ⟨102759973660628257192147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 548053192856684038358117 102759973660628257192147)
                    ·
                      rfl

theorem cell23_600373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_600373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600373 prefixEnd_600373 := by exact prefixLift 600373
  have htrace : WordTrace (prefixWord ++ tailWord_600373) baseStart_600373 baseEnd_600373 := by
    simpa [prefixWord, tailWord_600373, baseEnd_600373] using wordTrace_append hprefix tailTrace_600373
  have hstable : (prefixWord ++ tailWord_600373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600373).length < 2 ^ (prefixWord ++ tailWord_600373).sum := by decide
  have hdescent : baseEnd_600373 < baseStart_600373 := by decide
  rcases family_descends (prefixWord ++ tailWord_600373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600414 : List Nat := [4, 4, 2, 1, 1, 1, 1, 2, 2, 1, 4]
def baseStart_600414 : Nat := 118140960795 + 600414 * 2 ^ 59
def prefixEnd_600414 : Nat := 4983230072969 + 3 ^ 40 * 600414 * 2
def baseEnd_600414 : Nat := 308300973688719111163753

theorem tailTrace_600414 : CollatzResearch.WordTrace tailWord_600414 prefixEnd_600414 308300973688719111163753 := by
  unfold tailWord_600414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2737362205851261924060037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14599265097873396928320197 2737362205851261924060037)
  ·
    refine ⟨513255413597111610761257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2737362205851261924060037 513255413597111610761257)
    ·
      refine ⟨384941560197833708070943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 513255413597111610761257 384941560197833708070943)
      ·
        refine ⟨577412340296750562106415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384941560197833708070943 577412340296750562106415)
        ·
          refine ⟨866118510445125843159623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 577412340296750562106415 866118510445125843159623)
          ·
            refine ⟨1299177765667688764739435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 866118510445125843159623 1299177765667688764739435)
            ·
              refine ⟨1948766648501533147109153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1299177765667688764739435 1948766648501533147109153)
              ·
                refine ⟨1461574986376149860331865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1948766648501533147109153 1461574986376149860331865)
                ·
                  refine ⟨1096181239782112395248899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1461574986376149860331865 1096181239782112395248899)
                  ·
                    refine ⟨1644271859673168592873349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1096181239782112395248899 1644271859673168592873349)
                    ·
                      refine ⟨308300973688719111163753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1644271859673168592873349 308300973688719111163753)
                      ·
                        rfl

theorem cell23_600414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_600414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600414 prefixEnd_600414 := by exact prefixLift 600414
  have htrace : WordTrace (prefixWord ++ tailWord_600414) baseStart_600414 baseEnd_600414 := by
    simpa [prefixWord, tailWord_600414, baseEnd_600414] using wordTrace_append hprefix tailTrace_600414
  have hstable : (prefixWord ++ tailWord_600414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600414).length < 2 ^ (prefixWord ++ tailWord_600414).sum := by decide
  have hdescent : baseEnd_600414 < baseStart_600414 := by decide
  rcases family_descends (prefixWord ++ tailWord_600414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600423 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 4, 3, 2]
def baseStart_600423 : Nat := 118140960795 + 600423 * 2 ^ 59
def prefixEnd_600423 : Nat := 4983230072969 + 3 ^ 40 * 600423 * 2
def baseEnd_600423 : Nat := 308305595014609575951211

theorem tailTrace_600423 : CollatzResearch.WordTrace tailWord_600423 prefixEnd_600423 308305595014609575951211 := by
  unfold tailWord_600423
  simp only [CollatzResearch.WordTrace]
  refine ⟨21899225903777489929557923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14599483935851659953038615 21899225903777489929557923)
  ·
    refine ⟨32848838855666234894336885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21899225903777489929557923 32848838855666234894336885)
    ·
      refine ⟨3079578642718709521344083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32848838855666234894336885 3079578642718709521344083)
      ·
        refine ⟨4619367964078064282016125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3079578642718709521344083 4619367964078064282016125)
        ·
          refine ⟨1732262986529274105756047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4619367964078064282016125 1732262986529274105756047)
          ·
            refine ⟨2598394479793911158634071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1732262986529274105756047 2598394479793911158634071)
            ·
              refine ⟨3897591719690866737951107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2598394479793911158634071 3897591719690866737951107)
              ·
                refine ⟨5846387579536300106926661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3897591719690866737951107 5846387579536300106926661)
                ·
                  refine ⟨1096197671163056270048749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5846387579536300106926661 1096197671163056270048749)
                  ·
                    refine ⟨411074126686146101268281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1096197671163056270048749 411074126686146101268281)
                    ·
                      refine ⟨308305595014609575951211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 411074126686146101268281 308305595014609575951211)
                      ·
                        rfl

theorem cell23_600423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_600423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600423 prefixEnd_600423 := by exact prefixLift 600423
  have htrace : WordTrace (prefixWord ++ tailWord_600423) baseStart_600423 baseEnd_600423 := by
    simpa [prefixWord, tailWord_600423, baseEnd_600423] using wordTrace_append hprefix tailTrace_600423
  have hstable : (prefixWord ++ tailWord_600423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600423).length < 2 ^ (prefixWord ++ tailWord_600423).sum := by decide
  have hdescent : baseEnd_600423 < baseStart_600423 := by decide
  rcases family_descends (prefixWord ++ tailWord_600423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600439 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 5]
def baseStart_600439 : Nat := 118140960795 + 600439 * 2 ^ 59
def prefixEnd_600439 : Nat := 4983230072969 + 3 ^ 40 * 600439 * 2
def baseEnd_600439 : Nat := 308313810705081513351137

theorem tailTrace_600439 : CollatzResearch.WordTrace tailWord_600439 prefixEnd_600439 308313810705081513351137 := by
  unfold tailWord_600439
  simp only [CollatzResearch.WordTrace]
  refine ⟨21899809471719524662140371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14599872981146349774760247 21899809471719524662140371)
  ·
    refine ⟨32849714207579286993210557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21899809471719524662140371 32849714207579286993210557)
    ·
      refine ⟨12318642827842232622453959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32849714207579286993210557 12318642827842232622453959)
      ·
        refine ⟨18477964241763348933680939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12318642827842232622453959 18477964241763348933680939)
        ·
          refine ⟨27716946362645023400521409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18477964241763348933680939 27716946362645023400521409)
          ·
            refine ⟨20787709771983767550391057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27716946362645023400521409 20787709771983767550391057)
            ·
              refine ⟨15590782328987825662793293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20787709771983767550391057 15590782328987825662793293)
              ·
                refine ⟨5846543373370434623547485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15590782328987825662793293 5846543373370434623547485)
                ·
                  refine ⟨2192453765013912983830307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5846543373370434623547485 2192453765013912983830307)
                  ·
                    refine ⟨3288680647520869475745461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2192453765013912983830307 3288680647520869475745461)
                    ·
                      refine ⟨308313810705081513351137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3288680647520869475745461 308313810705081513351137)
                      ·
                        rfl

theorem cell23_600439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_600439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600439 prefixEnd_600439 := by exact prefixLift 600439
  have htrace : WordTrace (prefixWord ++ tailWord_600439) baseStart_600439 baseEnd_600439 := by
    simpa [prefixWord, tailWord_600439, baseEnd_600439] using wordTrace_append hprefix tailTrace_600439
  have hstable : (prefixWord ++ tailWord_600439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600439).length < 2 ^ (prefixWord ++ tailWord_600439).sum := by decide
  have hdescent : baseEnd_600439 < baseStart_600439 := by decide
  rcases family_descends (prefixWord ++ tailWord_600439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600450 : List Nat := [3, 4, 2, 1, 2, 1, 1, 1, 3, 5]
def baseStart_600450 : Nat := 118140960795 + 600450 * 2 ^ 59
def prefixEnd_600450 : Nat := 4983230072969 + 3 ^ 40 * 600450 * 2
def baseEnd_600450 : Nat := 102773152997426990104529

theorem tailTrace_600450 : CollatzResearch.WordTrace tailWord_600450 prefixEnd_600450 102773152997426990104529 := by
  unfold tailWord_600450
  simp only [CollatzResearch.WordTrace]
  refine ⟨5475052668669918385197701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14600140449786449027193869 5475052668669918385197701)
  ·
    refine ⟨1026572375375609697224569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5475052668669918385197701 1026572375375609697224569)
    ·
      refine ⟨769929281531707272918427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1026572375375609697224569 769929281531707272918427)
      ·
        refine ⟨1154893922297560909377641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 769929281531707272918427 1154893922297560909377641)
        ·
          refine ⟨866170441723170682033231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1154893922297560909377641 866170441723170682033231)
          ·
            refine ⟨1299255662584756023049847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 866170441723170682033231 1299255662584756023049847)
            ·
              refine ⟨1948883493877134034574771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1299255662584756023049847 1948883493877134034574771)
              ·
                refine ⟨2923325240815701051862157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1948883493877134034574771 2923325240815701051862157)
                ·
                  refine ⟨1096246965305887894448309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2923325240815701051862157 1096246965305887894448309)
                  ·
                    refine ⟨102773152997426990104529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1096246965305887894448309 102773152997426990104529)
                    ·
                      rfl

theorem cell23_600450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_600450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600450 prefixEnd_600450 := by exact prefixLift 600450
  have htrace : WordTrace (prefixWord ++ tailWord_600450) baseStart_600450 baseEnd_600450 := by
    simpa [prefixWord, tailWord_600450, baseEnd_600450] using wordTrace_append hprefix tailTrace_600450
  have hstable : (prefixWord ++ tailWord_600450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600450).length < 2 ^ (prefixWord ++ tailWord_600450).sum := by decide
  have hdescent : baseEnd_600450 < baseStart_600450 := by decide
  rcases family_descends (prefixWord ++ tailWord_600450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600453 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 5, 2, 2]
def baseStart_600453 : Nat := 118140960795 + 600453 * 2 ^ 59
def prefixEnd_600453 : Nat := 4983230072969 + 3 ^ 40 * 600453 * 2
def baseEnd_600453 : Nat := 308320999434244458576073

theorem tailTrace_600453 : CollatzResearch.WordTrace tailWord_600453 prefixEnd_600453 308320999434244458576073 := by
  unfold tailWord_600453
  simp only [CollatzResearch.WordTrace]
  refine ⟨21900320093668805053150013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14600213395779203368766675 21900320093668805053150013)
  ·
    refine ⟨8212620035125801894931255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21900320093668805053150013 8212620035125801894931255)
    ·
      refine ⟨12318930052688702842396883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8212620035125801894931255 12318930052688702842396883)
      ·
        refine ⟨18478395079033054263595325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12318930052688702842396883 18478395079033054263595325)
        ·
          refine ⟨6929398154637395348848247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18478395079033054263595325 6929398154637395348848247)
          ·
            refine ⟨10394097231956093023272371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6929398154637395348848247 10394097231956093023272371)
            ·
              refine ⟨15591145847934139534908557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10394097231956093023272371 15591145847934139534908557)
              ·
                refine ⟨5846679692975302325590709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15591145847934139534908557 5846679692975302325590709)
                ·
                  refine ⟨548126221216434593024129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5846679692975302325590709 548126221216434593024129)
                  ·
                    refine ⟨411094665912325944768097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 548126221216434593024129 411094665912325944768097)
                    ·
                      refine ⟨308320999434244458576073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 411094665912325944768097 308320999434244458576073)
                      ·
                        rfl

theorem cell23_600453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 5, 2, 2].length) (baseStart_600453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600453 prefixEnd_600453 := by exact prefixLift 600453
  have htrace : WordTrace (prefixWord ++ tailWord_600453) baseStart_600453 baseEnd_600453 := by
    simpa [prefixWord, tailWord_600453, baseEnd_600453] using wordTrace_append hprefix tailTrace_600453
  have hstable : (prefixWord ++ tailWord_600453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600453).length < 2 ^ (prefixWord ++ tailWord_600453).sum := by decide
  have hdescent : baseEnd_600453 < baseStart_600453 := by decide
  rcases family_descends (prefixWord ++ tailWord_600453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600459 : List Nat := [1, 1, 1, 1, 4, 4, 2, 9]
def baseStart_600459 : Nat := 118140960795 + 600459 * 2 ^ 59
def prefixEnd_600459 : Nat := 4983230072969 + 3 ^ 40 * 600459 * 2
def baseEnd_600459 : Nat := 11419410382154497596335

theorem tailTrace_600459 : CollatzResearch.WordTrace tailWord_600459 prefixEnd_600459 11419410382154497596335 := by
  unfold tailWord_600459
  simp only [CollatzResearch.WordTrace]
  refine ⟨21900538931647068077868431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14600359287764712051912287 21900538931647068077868431)
  ·
    refine ⟨32850808397470602116802647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21900538931647068077868431 32850808397470602116802647)
    ·
      refine ⟨49276212596205903175203971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32850808397470602116802647 49276212596205903175203971)
      ·
        refine ⟨73914318894308854762805957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49276212596205903175203971 73914318894308854762805957)
        ·
          refine ⟨13858934792682910268026117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73914318894308854762805957 13858934792682910268026117)
          ·
            refine ⟨2598550273628045675254897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13858934792682910268026117 2598550273628045675254897)
            ·
              refine ⟨1948912705221034256441173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2598550273628045675254897 1948912705221034256441173)
              ·
                refine ⟨11419410382154497596335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1948912705221034256441173 11419410382154497596335)
                ·
                  rfl

theorem cell23_600459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 9].length) (baseStart_600459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600459 prefixEnd_600459 := by exact prefixLift 600459
  have htrace : WordTrace (prefixWord ++ tailWord_600459) baseStart_600459 baseEnd_600459 := by
    simpa [prefixWord, tailWord_600459, baseEnd_600459] using wordTrace_append hprefix tailTrace_600459
  have hstable : (prefixWord ++ tailWord_600459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600459).length < 2 ^ (prefixWord ++ tailWord_600459).sum := by decide
  have hdescent : baseEnd_600459 < baseStart_600459 := by decide
  rcases family_descends (prefixWord ++ tailWord_600459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600481 : List Nat := [1, 2, 3, 5, 1, 2, 2, 2, 1, 1, 3]
def baseStart_600481 : Nat := 118140960795 + 600481 * 2 ^ 59
def prefixEnd_600481 : Nat := 4983230072969 + 3 ^ 40 * 600481 * 2
def baseEnd_600481 : Nat := 308335376892570349025945

theorem tailTrace_600481 : CollatzResearch.WordTrace tailWord_600481 prefixEnd_600481 308335376892570349025945 := by
  unfold tailWord_600481
  simp only [CollatzResearch.WordTrace]
  refine ⟨21901341337567365835169297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14600894225044910556779531 21901341337567365835169297)
  ·
    refine ⟨16426006003175524376376973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21901341337567365835169297 16426006003175524376376973)
    ·
      refine ⟨6159752251190821641141365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16426006003175524376376973 6159752251190821641141365)
      ·
        refine ⟨577476773549139528857003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6159752251190821641141365 577476773549139528857003)
        ·
          refine ⟨866215160323709293285505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 577476773549139528857003 866215160323709293285505)
          ·
            refine ⟨649661370242781969964129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 866215160323709293285505 649661370242781969964129)
            ·
              refine ⟨487246027682086477473097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 649661370242781969964129 487246027682086477473097)
              ·
                refine ⟨365434520761564858104823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 487246027682086477473097 365434520761564858104823)
                ·
                  refine ⟨548151781142347287157235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 365434520761564858104823 548151781142347287157235)
                  ·
                    refine ⟨822227671713520930735853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 548151781142347287157235 822227671713520930735853)
                    ·
                      refine ⟨308335376892570349025945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 822227671713520930735853 308335376892570349025945)
                      ·
                        rfl

theorem cell23_600481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_600481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600481 prefixEnd_600481 := by exact prefixLift 600481
  have htrace : WordTrace (prefixWord ++ tailWord_600481) baseStart_600481 baseEnd_600481 := by
    simpa [prefixWord, tailWord_600481, baseEnd_600481] using wordTrace_append hprefix tailTrace_600481
  have hstable : (prefixWord ++ tailWord_600481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600481).length < 2 ^ (prefixWord ++ tailWord_600481).sum := by decide
  have hdescent : baseEnd_600481 < baseStart_600481 := by decide
  rcases family_descends (prefixWord ++ tailWord_600481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600499 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 5]
def baseStart_600499 : Nat := 118140960795 + 600499 * 2 ^ 59
def prefixEnd_600499 : Nat := 4983230072969 + 3 ^ 40 * 600499 * 2
def baseEnd_600499 : Nat := 308344619544351278600861

theorem tailTrace_600499 : CollatzResearch.WordTrace tailWord_600499 prefixEnd_600499 308344619544351278600861 := by
  unfold tailWord_600499
  simp only [CollatzResearch.WordTrace]
  refine ⟨21901997851502154909324551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14601331901001436606216367 21901997851502154909324551)
  ·
    refine ⟨32852996777253232363986827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21901997851502154909324551 32852996777253232363986827)
    ·
      refine ⟨49279495165879848545980241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32852996777253232363986827 49279495165879848545980241)
      ·
        refine ⟨36959621374409886409485181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49279495165879848545980241 36959621374409886409485181)
        ·
          refine ⟨13859858015403707403556943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36959621374409886409485181 13859858015403707403556943)
          ·
            refine ⟨20789787023105561105335415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13859858015403707403556943 20789787023105561105335415)
            ·
              refine ⟨31184680534658341658003123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20789787023105561105335415 31184680534658341658003123)
              ·
                refine ⟨46777020801987512487004685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31184680534658341658003123 46777020801987512487004685)
                ·
                  refine ⟨17541382800745317182626757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46777020801987512487004685 17541382800745317182626757)
                  ·
                    refine ⟨3289009275139746971742517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17541382800745317182626757 3289009275139746971742517)
                    ·
                      refine ⟨308344619544351278600861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3289009275139746971742517 308344619544351278600861)
                      ·
                        rfl

theorem cell23_600499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 5].length) (baseStart_600499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600499 prefixEnd_600499 := by exact prefixLift 600499
  have htrace : WordTrace (prefixWord ++ tailWord_600499) baseStart_600499 baseEnd_600499 := by
    simpa [prefixWord, tailWord_600499, baseEnd_600499] using wordTrace_append hprefix tailTrace_600499
  have hstable : (prefixWord ++ tailWord_600499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600499).length < 2 ^ (prefixWord ++ tailWord_600499).sum := by decide
  have hdescent : baseEnd_600499 < baseStart_600499 := by decide
  rcases family_descends (prefixWord ++ tailWord_600499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600503 : List Nat := [1, 1, 3, 1, 3, 4, 2, 1, 1, 3, 3]
def baseStart_600503 : Nat := 118140960795 + 600503 * 2 ^ 59
def prefixEnd_600503 : Nat := 4983230072969 + 3 ^ 40 * 600503 * 2
def baseEnd_600503 : Nat := 308346673466969262950843

theorem tailTrace_600503 : CollatzResearch.WordTrace tailWord_600503 prefixEnd_600503 308346673466969262950843 := by
  unfold tailWord_600503
  simp only [CollatzResearch.WordTrace]
  refine ⟨21902143743487663592470163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14601429162325109061646775 21902143743487663592470163)
  ·
    refine ⟨32853215615231495388705245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21902143743487663592470163 32853215615231495388705245)
    ·
      refine ⟨12319955855711810770764467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32853215615231495388705245 12319955855711810770764467)
      ·
        refine ⟨18479933783567716156146701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12319955855711810770764467 18479933783567716156146701)
        ·
          refine ⟨6929975168837893558555013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18479933783567716156146701 6929975168837893558555013)
          ·
            refine ⟨1299370344157105042229065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6929975168837893558555013 1299370344157105042229065)
            ·
              refine ⟨974527758117828781671799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1299370344157105042229065 974527758117828781671799)
              ·
                refine ⟨1461791637176743172507699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 974527758117828781671799 1461791637176743172507699)
                ·
                  refine ⟨2192687455765114758761549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1461791637176743172507699 2192687455765114758761549)
                  ·
                    refine ⟨822257795911918034535581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2192687455765114758761549 822257795911918034535581)
                    ·
                      refine ⟨308346673466969262950843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 822257795911918034535581 308346673466969262950843)
                      ·
                        rfl

theorem cell23_600503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 3, 3].length) (baseStart_600503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600503 prefixEnd_600503 := by exact prefixLift 600503
  have htrace : WordTrace (prefixWord ++ tailWord_600503) baseStart_600503 baseEnd_600503 := by
    simpa [prefixWord, tailWord_600503, baseEnd_600503] using wordTrace_append hprefix tailTrace_600503
  have hstable : (prefixWord ++ tailWord_600503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600503).length < 2 ^ (prefixWord ++ tailWord_600503).sum := by decide
  have hdescent : baseEnd_600503 < baseStart_600503 := by decide
  rcases family_descends (prefixWord ++ tailWord_600503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600524 : List Nat := [2, 2, 1, 4, 4, 1, 2, 1, 1, 2, 3]
def baseStart_600524 : Nat := 118140960795 + 600524 * 2 ^ 59
def prefixEnd_600524 : Nat := 4983230072969 + 3 ^ 40 * 600524 * 2
def baseEnd_600524 : Nat := 308357456560713680788247

theorem tailTrace_600524 : CollatzResearch.WordTrace tailWord_600524 prefixEnd_600524 308357456560713680788247 := by
  unfold tailWord_600524
  simp only [CollatzResearch.WordTrace]
  refine ⟨10951454838205792089492313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14601939784274389452656417 10951454838205792089492313)
  ·
    refine ⟨8213591128654344067119235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10951454838205792089492313 8213591128654344067119235)
    ·
      refine ⟨12320386692981516100678853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8213591128654344067119235 12320386692981516100678853)
      ·
        refine ⟨2310072504934034268877285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12320386692981516100678853 2310072504934034268877285)
        ·
          refine ⟨433138594675131425414491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2310072504934034268877285 433138594675131425414491)
          ·
            refine ⟨649707892012697138121737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433138594675131425414491 649707892012697138121737)
            ·
              refine ⟨487280919009522853591303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 649707892012697138121737 487280919009522853591303)
              ·
                refine ⟨730921378514284280386955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 487280919009522853591303 730921378514284280386955)
                ·
                  refine ⟨1096382067771426420580433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 730921378514284280386955 1096382067771426420580433)
                  ·
                    refine ⟨822286550828569815435325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1096382067771426420580433 822286550828569815435325)
                    ·
                      refine ⟨308357456560713680788247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 822286550828569815435325 308357456560713680788247)
                      ·
                        rfl

theorem cell23_600524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_600524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600524 prefixEnd_600524 := by exact prefixLift 600524
  have htrace : WordTrace (prefixWord ++ tailWord_600524) baseStart_600524 baseEnd_600524 := by
    simpa [prefixWord, tailWord_600524, baseEnd_600524] using wordTrace_append hprefix tailTrace_600524
  have hstable : (prefixWord ++ tailWord_600524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600524).length < 2 ^ (prefixWord ++ tailWord_600524).sum := by decide
  have hdescent : baseEnd_600524 < baseStart_600524 := by decide
  rcases family_descends (prefixWord ++ tailWord_600524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600556 : List Nat := [2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 4]
def baseStart_600556 : Nat := 118140960795 + 600556 * 2 ^ 59
def prefixEnd_600556 : Nat := 4983230072969 + 3 ^ 40 * 600556 * 2
def baseEnd_600556 : Nat := 308373887941657555588099

theorem tailTrace_600556 : CollatzResearch.WordTrace tailWord_600556 prefixEnd_600556 308373887941657555588099 := by
  unfold tailWord_600556
  simp only [CollatzResearch.WordTrace]
  refine ⟨10952038406147826822074761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14602717874863769096099681 10952038406147826822074761)
  ·
    refine ⟨8214028804610870116556071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10952038406147826822074761 8214028804610870116556071)
    ·
      refine ⟨12321043206916305174834107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8214028804610870116556071 12321043206916305174834107)
      ·
        refine ⟨18481564810374457762251161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12321043206916305174834107 18481564810374457762251161)
        ·
          refine ⟨13861173607780843321688371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18481564810374457762251161 13861173607780843321688371)
          ·
            refine ⟨20791760411671264982532557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13861173607780843321688371 20791760411671264982532557)
            ·
              refine ⟨7796910154376724368449709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20791760411671264982532557 7796910154376724368449709)
              ·
                refine ⟨2923841307891271638168641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7796910154376724368449709 2923841307891271638168641)
                ·
                  refine ⟨2192880980918453728626481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2923841307891271638168641 2192880980918453728626481)
                  ·
                    refine ⟨1644660735688840296469861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2192880980918453728626481 1644660735688840296469861)
                    ·
                      refine ⟨308373887941657555588099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1644660735688840296469861 308373887941657555588099)
                      ·
                        rfl

theorem cell23_600556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_600556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600556 prefixEnd_600556 := by exact prefixLift 600556
  have htrace : WordTrace (prefixWord ++ tailWord_600556) baseStart_600556 baseEnd_600556 := by
    simpa [prefixWord, tailWord_600556, baseEnd_600556] using wordTrace_append hprefix tailTrace_600556
  have hstable : (prefixWord ++ tailWord_600556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600556).length < 2 ^ (prefixWord ++ tailWord_600556).sum := by decide
  have hdescent : baseEnd_600556 < baseStart_600556 := by decide
  rcases family_descends (prefixWord ++ tailWord_600556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600626 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 2, 8]
def baseStart_600626 : Nat := 118140960795 + 600626 * 2 ^ 59
def prefixEnd_600626 : Nat := 4983230072969 + 3 ^ 40 * 600626 * 2
def baseEnd_600626 : Nat := 102803277195824093904259

theorem tailTrace_600626 : CollatzResearch.WordTrace tailWord_600626 prefixEnd_600626 102803277195824093904259 := by
  unfold tailWord_600626
  simp only [CollatzResearch.WordTrace]
  refine ⟨5476657480510513899799433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14604419948028037066131821 5476657480510513899799433)
  ·
    refine ⟨4107493110382885424849575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5476657480510513899799433 4107493110382885424849575)
    ·
      refine ⟨6161239665574328137274363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4107493110382885424849575 6161239665574328137274363)
      ·
        refine ⟨9241859498361492205911545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6161239665574328137274363 9241859498361492205911545)
        ·
          refine ⟨6931394623771119154433659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9241859498361492205911545 6931394623771119154433659)
          ·
            refine ⟨10397091935656678731650489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6931394623771119154433659 10397091935656678731650489)
            ·
              refine ⟨7797818951742509048737867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10397091935656678731650489 7797818951742509048737867)
              ·
                refine ⟨11696728427613763573106801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7797818951742509048737867 11696728427613763573106801)
                ·
                  refine ⟨8772546320710322679830101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11696728427613763573106801 8772546320710322679830101)
                  ·
                    refine ⟨102803277195824093904259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8772546320710322679830101 102803277195824093904259)
                    ·
                      rfl

theorem cell23_600626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_600626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600626 prefixEnd_600626 := by exact prefixLift 600626
  have htrace : WordTrace (prefixWord ++ tailWord_600626) baseStart_600626 baseEnd_600626 := by
    simpa [prefixWord, tailWord_600626, baseEnd_600626] using wordTrace_append hprefix tailTrace_600626
  have hstable : (prefixWord ++ tailWord_600626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600626).length < 2 ^ (prefixWord ++ tailWord_600626).sum := by decide
  have hdescent : baseEnd_600626 < baseStart_600626 := by decide
  rcases family_descends (prefixWord ++ tailWord_600626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600630 : List Nat := [5, 1, 2, 1, 2, 1, 1, 3, 2, 5]
def baseStart_600630 : Nat := 118140960795 + 600630 * 2 ^ 59
def prefixEnd_600630 : Nat := 4983230072969 + 3 ^ 40 * 600630 * 2
def baseEnd_600630 : Nat := 102803961836696755354253

theorem tailTrace_600630 : CollatzResearch.WordTrace tailWord_600630 prefixEnd_600630 102803961836696755354253 := by
  unfold tailWord_600630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1369173488376722767646459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14604517209351709521562229 1369173488376722767646459)
  ·
    refine ⟨2053760232565084151469689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1369173488376722767646459 2053760232565084151469689)
    ·
      refine ⟨1540320174423813113602267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2053760232565084151469689 1540320174423813113602267)
      ·
        refine ⟨2310480261635719670403401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1540320174423813113602267 2310480261635719670403401)
        ·
          refine ⟨1732860196226789752802551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2310480261635719670403401 1732860196226789752802551)
          ·
            refine ⟨2599290294340184629203827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1732860196226789752802551 2599290294340184629203827)
            ·
              refine ⟨3898935441510276943805741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2599290294340184629203827 3898935441510276943805741)
              ·
                refine ⟨1462100790566353853927153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3898935441510276943805741 1462100790566353853927153)
                ·
                  refine ⟨1096575592924765390445365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1462100790566353853927153 1096575592924765390445365)
                  ·
                    refine ⟨102803961836696755354253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1096575592924765390445365 102803961836696755354253)
                    ·
                      rfl

theorem cell23_600630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_600630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600630 prefixEnd_600630 := by exact prefixLift 600630
  have htrace : WordTrace (prefixWord ++ tailWord_600630) baseStart_600630 baseEnd_600630 := by
    simpa [prefixWord, tailWord_600630, baseEnd_600630] using wordTrace_append hprefix tailTrace_600630
  have hstable : (prefixWord ++ tailWord_600630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600630).length < 2 ^ (prefixWord ++ tailWord_600630).sum := by decide
  have hdescent : baseEnd_600630 < baseStart_600630 := by decide
  rcases family_descends (prefixWord ++ tailWord_600630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600673 : List Nat := [1, 2, 3, 1, 1, 4, 2, 3, 6]
def baseStart_600673 : Nat := 118140960795 + 600673 * 2 ^ 59
def prefixEnd_600673 : Nat := 4983230072969 + 3 ^ 40 * 600673 * 2
def baseEnd_600673 : Nat := 34270440575359288647229

theorem tailTrace_600673 : CollatzResearch.WordTrace tailWord_600673 prefixEnd_600673 34270440575359288647229 := by
  unfold tailWord_600673
  simp only [CollatzResearch.WordTrace]
  refine ⟨21908344152871782626158673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14605562768581188417439115 21908344152871782626158673)
  ·
    refine ⟨16431258114653836969619005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21908344152871782626158673 16431258114653836969619005)
    ·
      refine ⟨6161721792995188863607127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16431258114653836969619005 6161721792995188863607127)
      ·
        refine ⟨9242582689492783295410691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6161721792995188863607127 9242582689492783295410691)
        ·
          refine ⟨13863874034239174943116037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9242582689492783295410691 13863874034239174943116037)
          ·
            refine ⟨2599476381419845301834257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13863874034239174943116037 2599476381419845301834257)
            ·
              refine ⟨1949607286064883976375693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2599476381419845301834257 1949607286064883976375693)
              ·
                refine ⟨731102732274331491140885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1949607286064883976375693 731102732274331491140885)
                ·
                  refine ⟨34270440575359288647229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 731102732274331491140885 34270440575359288647229)
                  ·
                    rfl

theorem cell23_600673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 6].length) (baseStart_600673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600673 prefixEnd_600673 := by exact prefixLift 600673
  have htrace : WordTrace (prefixWord ++ tailWord_600673) baseStart_600673 baseEnd_600673 := by
    simpa [prefixWord, tailWord_600673, baseEnd_600673] using wordTrace_append hprefix tailTrace_600673
  have hstable : (prefixWord ++ tailWord_600673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600673).length < 2 ^ (prefixWord ++ tailWord_600673).sum := by decide
  have hdescent : baseEnd_600673 < baseStart_600673 := by decide
  rcases family_descends (prefixWord ++ tailWord_600673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600696 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 1, 3, 7]
def baseStart_600696 : Nat := 118140960795 + 600696 * 2 ^ 59
def prefixEnd_600696 : Nat := 4983230072969 + 3 ^ 40 * 600696 * 2
def baseEnd_600696 : Nat := 308445775233287007837455

theorem tailTrace_600696 : CollatzResearch.WordTrace tailWord_600696 prefixEnd_600696 308445775233287007837455 := by
  unfold tailWord_600696
  simp only [CollatzResearch.WordTrace]
  refine ⟨10954591515894228777122971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14606122021192305036163961 10954591515894228777122971)
  ·
    refine ⟨16431887273841343165684457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10954591515894228777122971 16431887273841343165684457)
    ·
      refine ⟨12323915455381007374263343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16431887273841343165684457 12323915455381007374263343)
      ·
        refine ⟨18485873183071511061395015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12323915455381007374263343 18485873183071511061395015)
        ·
          refine ⟨27728809774607266592092523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18485873183071511061395015 27728809774607266592092523)
          ·
            refine ⟨41593214661910899888138785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27728809774607266592092523 41593214661910899888138785)
            ·
              refine ⟨31194910996433174916104089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41593214661910899888138785 31194910996433174916104089)
              ·
                refine ⟨23396183247324881187078067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31194910996433174916104089 23396183247324881187078067)
                ·
                  refine ⟨35094274870987321780617101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23396183247324881187078067 35094274870987321780617101)
                  ·
                    refine ⟨13160353076620245667731413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35094274870987321780617101 13160353076620245667731413)
                    ·
                      refine ⟨308445775233287007837455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 13160353076620245667731413 308445775233287007837455)
                      ·
                        rfl

theorem cell23_600696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_600696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600696 prefixEnd_600696 := by exact prefixLift 600696
  have htrace : WordTrace (prefixWord ++ tailWord_600696) baseStart_600696 baseEnd_600696 := by
    simpa [prefixWord, tailWord_600696, baseEnd_600696] using wordTrace_append hprefix tailTrace_600696
  have hstable : (prefixWord ++ tailWord_600696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600696).length < 2 ^ (prefixWord ++ tailWord_600696).sum := by decide
  have hdescent : baseEnd_600696 < baseStart_600696 := by decide
  rcases family_descends (prefixWord ++ tailWord_600696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600737 : List Nat := [1, 2, 3, 3, 3, 1, 2, 2, 1, 5]
def baseStart_600737 : Nat := 118140960795 + 600737 * 2 ^ 59
def prefixEnd_600737 : Nat := 4983230072969 + 3 ^ 40 * 600737 * 2
def baseEnd_600737 : Nat := 102822275980040449141589

theorem tailTrace_600737 : CollatzResearch.WordTrace tailWord_600737 prefixEnd_600737 102822275980040449141589 := by
  unfold tailWord_600737
  simp only [CollatzResearch.WordTrace]
  refine ⟨21910678424639921556488465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14607118949759947704325643 21910678424639921556488465)
  ·
    refine ⟨16433008818479941167366349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21910678424639921556488465 16433008818479941167366349)
    ·
      refine ⟨6162378306929977937762381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16433008818479941167366349 6162378306929977937762381)
      ·
        refine ⟨2310891865098741726660893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6162378306929977937762381 2310891865098741726660893)
        ·
          refine ⟨866584449412028147497835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2310891865098741726660893 866584449412028147497835)
          ·
            refine ⟨1299876674118042221246753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 866584449412028147497835 1299876674118042221246753)
            ·
              refine ⟨974907505588531665935065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1299876674118042221246753 974907505588531665935065)
              ·
                refine ⟨731180629191398749451299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 974907505588531665935065 731180629191398749451299)
                ·
                  refine ⟨1096770943787098124176949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 731180629191398749451299 1096770943787098124176949)
                  ·
                    refine ⟨102822275980040449141589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1096770943787098124176949 102822275980040449141589)
                    ·
                      rfl

theorem cell23_600737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_600737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600737 prefixEnd_600737 := by exact prefixLift 600737
  have htrace : WordTrace (prefixWord ++ tailWord_600737) baseStart_600737 baseEnd_600737 := by
    simpa [prefixWord, tailWord_600737, baseEnd_600737] using wordTrace_append hprefix tailTrace_600737
  have hstable : (prefixWord ++ tailWord_600737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600737).length < 2 ^ (prefixWord ++ tailWord_600737).sum := by decide
  have hdescent : baseEnd_600737 < baseStart_600737 := by decide
  rcases family_descends (prefixWord ++ tailWord_600737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600740 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 2, 6, 2]
def baseStart_600740 : Nat := 118140960795 + 600740 * 2 ^ 59
def prefixEnd_600740 : Nat := 4983230072969 + 3 ^ 40 * 600740 * 2
def baseEnd_600740 : Nat := 308468368382084835687253

theorem tailTrace_600740 : CollatzResearch.WordTrace tailWord_600740 prefixEnd_600740 308468368382084835687253 := by
  unfold tailWord_600740
  simp only [CollatzResearch.WordTrace]
  refine ⟨10955393921814526534423837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14607191895752702045898449 10955393921814526534423837)
  ·
    refine ⟨4108272720680447450408939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10955393921814526534423837 4108272720680447450408939)
    ·
      refine ⟨6162409081020671175613409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4108272720680447450408939 6162409081020671175613409)
      ·
        refine ⟨4621806810765503381710057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6162409081020671175613409 4621806810765503381710057)
        ·
          refine ⟨3466355108074127536282543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4621806810765503381710057 3466355108074127536282543)
          ·
            refine ⟨5199532662111191304423815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3466355108074127536282543 5199532662111191304423815)
            ·
              refine ⟨7799298993166786956635723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5199532662111191304423815 7799298993166786956635723)
              ·
                refine ⟨11698948489750180434953585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7799298993166786956635723 11698948489750180434953585)
                ·
                  refine ⟨8774211367312635326215189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11698948489750180434953585 8774211367312635326215189)
                  ·
                    refine ⟨411291157842779780916337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8774211367312635326215189 411291157842779780916337)
                    ·
                      refine ⟨308468368382084835687253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 411291157842779780916337 308468368382084835687253)
                      ·
                        rfl

theorem cell23_600740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_600740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600740 prefixEnd_600740 := by exact prefixLift 600740
  have htrace : WordTrace (prefixWord ++ tailWord_600740) baseStart_600740 baseEnd_600740 := by
    simpa [prefixWord, tailWord_600740, baseEnd_600740] using wordTrace_append hprefix tailTrace_600740
  have hstable : (prefixWord ++ tailWord_600740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600740).length < 2 ^ (prefixWord ++ tailWord_600740).sum := by decide
  have hdescent : baseEnd_600740 < baseStart_600740 := by decide
  rcases family_descends (prefixWord ++ tailWord_600740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600757 : List Nat := [1, 3, 3, 3, 1, 1, 2, 3, 1, 1, 4]
def baseStart_600757 : Nat := 118140960795 + 600757 * 2 ^ 59
def prefixEnd_600757 : Nat := 4983230072969 + 3 ^ 40 * 600757 * 2
def baseEnd_600757 : Nat := 308477097553211269174675

theorem tailTrace_600757 : CollatzResearch.WordTrace tailWord_600757 prefixEnd_600757 308477097553211269174675 := by
  unfold tailWord_600757
  simp only [CollatzResearch.WordTrace]
  refine ⟨21911407884567464972216525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14607605256378309981477683 21911407884567464972216525)
  ·
    refine ⟨8216777956712799364581197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21911407884567464972216525 8216777956712799364581197)
    ·
      refine ⟨3081291733767299761717949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8216777956712799364581197 3081291733767299761717949)
      ·
        refine ⟨1155484400162737410644231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3081291733767299761717949 1155484400162737410644231)
        ·
          refine ⟨1733226600244106115966347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1155484400162737410644231 1733226600244106115966347)
          ·
            refine ⟨2599839900366159173949521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1733226600244106115966347 2599839900366159173949521)
            ·
              refine ⟨1949879925274619380462141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2599839900366159173949521 1949879925274619380462141)
              ·
                refine ⟨731204971977982267673303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1949879925274619380462141 731204971977982267673303)
                ·
                  refine ⟨1096807457966973401509955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 731204971977982267673303 1096807457966973401509955)
                  ·
                    refine ⟨1645211186950460102264933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1096807457966973401509955 1645211186950460102264933)
                    ·
                      refine ⟨308477097553211269174675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1645211186950460102264933 308477097553211269174675)
                      ·
                        rfl

theorem cell23_600757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_600757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600757 prefixEnd_600757 := by exact prefixLift 600757
  have htrace : WordTrace (prefixWord ++ tailWord_600757) baseStart_600757 baseEnd_600757 := by
    simpa [prefixWord, tailWord_600757, baseEnd_600757] using wordTrace_append hprefix tailTrace_600757
  have hstable : (prefixWord ++ tailWord_600757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600757).length < 2 ^ (prefixWord ++ tailWord_600757).sum := by decide
  have hdescent : baseEnd_600757 < baseStart_600757 := by decide
  rcases family_descends (prefixWord ++ tailWord_600757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600773 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 2, 7, 3]
def baseStart_600773 : Nat := 118140960795 + 600773 * 2 ^ 59
def prefixEnd_600773 : Nat := 4983230072969 + 3 ^ 40 * 600773 * 2
def baseEnd_600773 : Nat := 308485313243683206574601

theorem tailTrace_600773 : CollatzResearch.WordTrace tailWord_600773 prefixEnd_600773 308485313243683206574601 := by
  unfold tailWord_600773
  simp only [CollatzResearch.WordTrace]
  refine ⟨21911991452509499704798973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14607994301672999803199315 21911991452509499704798973)
  ·
    refine ⟨8216996794691062389299615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21911991452509499704798973 8216996794691062389299615)
    ·
      refine ⟨12325495192036593583949423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8216996794691062389299615 12325495192036593583949423)
      ·
        refine ⟨18488242788054890375924135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12325495192036593583949423 18488242788054890375924135)
        ·
          refine ⟨27732364182082335563886203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18488242788054890375924135 27732364182082335563886203)
          ·
            refine ⟨41598546273123503345829305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27732364182082335563886203 41598546273123503345829305)
            ·
              refine ⟨31198909704842627509371979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41598546273123503345829305 31198909704842627509371979)
              ·
                refine ⟨46798364557263941264057969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31198909704842627509371979 46798364557263941264057969)
                ·
                  refine ⟨35098773417947955948043477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46798364557263941264057969 35098773417947955948043477)
                  ·
                    refine ⟨822627501983155217532269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35098773417947955948043477 822627501983155217532269)
                    ·
                      refine ⟨308485313243683206574601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 822627501983155217532269 308485313243683206574601)
                      ·
                        rfl

theorem cell23_600773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 7, 3].length) (baseStart_600773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600773 prefixEnd_600773 := by exact prefixLift 600773
  have htrace : WordTrace (prefixWord ++ tailWord_600773) baseStart_600773 baseEnd_600773 := by
    simpa [prefixWord, tailWord_600773, baseEnd_600773] using wordTrace_append hprefix tailTrace_600773
  have hstable : (prefixWord ++ tailWord_600773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600773).length < 2 ^ (prefixWord ++ tailWord_600773).sum := by decide
  have hdescent : baseEnd_600773 < baseStart_600773 := by decide
  rcases family_descends (prefixWord ++ tailWord_600773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600780 : List Nat := [2, 2, 1, 5, 1, 2, 2, 8]
def baseStart_600780 : Nat := 118140960795 + 600780 * 2 ^ 59
def prefixEnd_600780 : Nat := 4983230072969 + 3 ^ 40 * 600780 * 2
def baseEnd_600780 : Nat := 11425515096602395525447

theorem tailTrace_600780 : CollatzResearch.WordTrace tailWord_600780 prefixEnd_600780 11425515096602395525447 := by
  unfold tailWord_600780
  simp only [CollatzResearch.WordTrace]
  refine ⟨10956123381742069950151897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14608164508989426600202529 10956123381742069950151897)
  ·
    refine ⟨8217092536306552462613923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10956123381742069950151897 8217092536306552462613923)
    ·
      refine ⟨12325638804459828693920885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8217092536306552462613923 12325638804459828693920885)
      ·
        refine ⟨1155528637918108940055083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12325638804459828693920885 1155528637918108940055083)
        ·
          refine ⟨1733292956877163410082625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1155528637918108940055083 1733292956877163410082625)
          ·
            refine ⟨1299969717657872557561969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1733292956877163410082625 1299969717657872557561969)
            ·
              refine ⟨974977288243404418171477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1299969717657872557561969 974977288243404418171477)
              ·
                refine ⟨11425515096602395525447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 974977288243404418171477 11425515096602395525447)
                ·
                  rfl

theorem cell23_600780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 8].length) (baseStart_600780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600780 prefixEnd_600780 := by exact prefixLift 600780
  have htrace : WordTrace (prefixWord ++ tailWord_600780) baseStart_600780 baseEnd_600780 := by
    simpa [prefixWord, tailWord_600780, baseEnd_600780] using wordTrace_append hprefix tailTrace_600780
  have hstable : (prefixWord ++ tailWord_600780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600780).length < 2 ^ (prefixWord ++ tailWord_600780).sum := by decide
  have hdescent : baseEnd_600780 < baseStart_600780 := by decide
  rcases family_descends (prefixWord ++ tailWord_600780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600823 : List Nat := [1, 1, 3, 1, 1, 1, 3, 4, 2, 6]
def baseStart_600823 : Nat := 118140960795 + 600823 * 2 ^ 59
def prefixEnd_600823 : Nat := 4983230072969 + 3 ^ 40 * 600823 * 2
def baseEnd_600823 : Nat := 102836995758802670316457

theorem tailTrace_600823 : CollatzResearch.WordTrace tailWord_600823 prefixEnd_600823 102836995758802670316457 := by
  unfold tailWord_600823
  simp only [CollatzResearch.WordTrace]
  refine ⟨21913815102328358244119123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14609210068218905496079415 21913815102328358244119123)
  ·
    refine ⟨32870722653492537366178685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21913815102328358244119123 32870722653492537366178685)
    ·
      refine ⟨12326520995059701512317007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32870722653492537366178685 12326520995059701512317007)
      ·
        refine ⟨18489781492589552268475511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12326520995059701512317007 18489781492589552268475511)
        ·
          refine ⟨27734672238884328402713267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18489781492589552268475511 27734672238884328402713267)
          ·
            refine ⟨41602008358326492604069901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27734672238884328402713267 41602008358326492604069901)
            ·
              refine ⟨15600753134372434726526213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41602008358326492604069901 15600753134372434726526213)
              ·
                refine ⟨2925141212694831511223665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15600753134372434726526213 2925141212694831511223665)
                ·
                  refine ⟨2193855909521123633417749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2925141212694831511223665 2193855909521123633417749)
                  ·
                    refine ⟨102836995758802670316457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2193855909521123633417749 102836995758802670316457)
                    ·
                      rfl

theorem cell23_600823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 6].length) (baseStart_600823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600823 prefixEnd_600823 := by exact prefixLift 600823
  have htrace : WordTrace (prefixWord ++ tailWord_600823) baseStart_600823 baseEnd_600823 := by
    simpa [prefixWord, tailWord_600823, baseEnd_600823] using wordTrace_append hprefix tailTrace_600823
  have hstable : (prefixWord ++ tailWord_600823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600823).length < 2 ^ (prefixWord ++ tailWord_600823).sum := by decide
  have hdescent : baseEnd_600823 < baseStart_600823 := by decide
  rcases family_descends (prefixWord ++ tailWord_600823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600834 : List Nat := [3, 4, 1, 1, 1, 2, 1, 2, 3, 3, 2]
def baseStart_600834 : Nat := 118140960795 + 600834 * 2 ^ 59
def prefixEnd_600834 : Nat := 4983230072969 + 3 ^ 40 * 600834 * 2
def baseEnd_600834 : Nat := 308516635563607467911821

theorem tailTrace_600834 : CollatzResearch.WordTrace tailWord_600834 prefixEnd_600834 308516635563607467911821 := by
  unfold tailWord_600834
  simp only [CollatzResearch.WordTrace]
  refine ⟨5478554076322126780692389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14609477536859004748513037 5478554076322126780692389)
  ·
    refine ⟨1027228889310398771379823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5478554076322126780692389 1027228889310398771379823)
    ·
      refine ⟨1540843333965598157069735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1027228889310398771379823 1540843333965598157069735)
      ·
        refine ⟨2311265000948397235604603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1540843333965598157069735 2311265000948397235604603)
        ·
          refine ⟨3466897501422595853406905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2311265000948397235604603 3466897501422595853406905)
          ·
            refine ⟨2600173126066946890055179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3466897501422595853406905 2600173126066946890055179)
            ·
              refine ⟨3900259689100420335082769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2600173126066946890055179 3900259689100420335082769)
              ·
                refine ⟨2925194766825315251312077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3900259689100420335082769 2925194766825315251312077)
                ·
                  refine ⟨1096948037559493219242029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2925194766825315251312077 1096948037559493219242029)
                  ·
                    refine ⟨411355514084809957215761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1096948037559493219242029 411355514084809957215761)
                    ·
                      refine ⟨308516635563607467911821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 411355514084809957215761 308516635563607467911821)
                      ·
                        rfl

theorem cell23_600834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_600834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600834 prefixEnd_600834 := by exact prefixLift 600834
  have htrace : WordTrace (prefixWord ++ tailWord_600834) baseStart_600834 baseEnd_600834 := by
    simpa [prefixWord, tailWord_600834, baseEnd_600834] using wordTrace_append hprefix tailTrace_600834
  have hstable : (prefixWord ++ tailWord_600834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600834).length < 2 ^ (prefixWord ++ tailWord_600834).sum := by decide
  have hdescent : baseEnd_600834 < baseStart_600834 := by decide
  rcases family_descends (prefixWord ++ tailWord_600834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600840 : List Nat := [2, 1, 3, 2, 2, 3, 1, 1, 2, 6]
def baseStart_600840 : Nat := 118140960795 + 600840 * 2 ^ 59
def prefixEnd_600840 : Nat := 4983230072969 + 3 ^ 40 * 600840 * 2
def baseEnd_600840 : Nat := 102839905482511481478931

theorem tailTrace_600840 : CollatzResearch.WordTrace tailWord_600840 prefixEnd_600840 102839905482511481478931 := by
  unfold tailWord_600840
  simp only [CollatzResearch.WordTrace]
  refine ⟨10957217571633385073743987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14609623428844513431658649 10957217571633385073743987)
  ·
    refine ⟨16435826357450077610615981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10957217571633385073743987 16435826357450077610615981)
    ·
      refine ⟨6163434884043779103980993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16435826357450077610615981 6163434884043779103980993)
      ·
        refine ⟨4622576163032834327985745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6163434884043779103980993 4622576163032834327985745)
        ·
          refine ⟨3466932122274625745989309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4622576163032834327985745 3466932122274625745989309)
          ·
            refine ⟨1300099545852984654745991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3466932122274625745989309 1300099545852984654745991)
            ·
              refine ⟨1950149318779476982118987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1300099545852984654745991 1950149318779476982118987)
              ·
                refine ⟨2925223978169215473178481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1950149318779476982118987 2925223978169215473178481)
                ·
                  refine ⟨2193917983626911604883861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2925223978169215473178481 2193917983626911604883861)
                  ·
                    refine ⟨102839905482511481478931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2193917983626911604883861 102839905482511481478931)
                    ·
                      rfl

theorem cell23_600840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_600840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600840 prefixEnd_600840 := by exact prefixLift 600840
  have htrace : WordTrace (prefixWord ++ tailWord_600840) baseStart_600840 baseEnd_600840 := by
    simpa [prefixWord, tailWord_600840, baseEnd_600840] using wordTrace_append hprefix tailTrace_600840
  have hstable : (prefixWord ++ tailWord_600840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600840).length < 2 ^ (prefixWord ++ tailWord_600840).sum := by decide
  have hdescent : baseEnd_600840 < baseStart_600840 := by decide
  rcases family_descends (prefixWord ++ tailWord_600840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600847 : List Nat := [1, 1, 2, 1, 1, 1, 8, 1, 1, 4, 2]
def baseStart_600847 : Nat := 118140960795 + 600847 * 2 ^ 59
def prefixEnd_600847 : Nat := 4983230072969 + 3 ^ 40 * 600847 * 2
def baseEnd_600847 : Nat := 308523310812115917049261

theorem tailTrace_600847 : CollatzResearch.WordTrace tailWord_600847 prefixEnd_600847 308523310812115917049261 := by
  unfold tailWord_600847
  simp only [CollatzResearch.WordTrace]
  refine ⟨21914690454241410342992795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14609793636160940228661863 21914690454241410342992795)
  ·
    refine ⟨32872035681362115514489193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21914690454241410342992795 32872035681362115514489193)
    ·
      refine ⟨24654026761021586635866895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32872035681362115514489193 24654026761021586635866895)
      ·
        refine ⟨36981040141532379953800343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24654026761021586635866895 36981040141532379953800343)
        ·
          refine ⟨55471560212298569930700515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36981040141532379953800343 55471560212298569930700515)
          ·
            refine ⟨83207340318447854896050773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55471560212298569930700515 83207340318447854896050773)
            ·
              refine ⟨975086019356810799563095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 83207340318447854896050773 975086019356810799563095)
              ·
                refine ⟨1462629029035216199344643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 975086019356810799563095 1462629029035216199344643)
                ·
                  refine ⟨2193943543552824299016965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1462629029035216199344643 2193943543552824299016965)
                  ·
                    refine ⟨411364414416154556065681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2193943543552824299016965 411364414416154556065681)
                    ·
                      refine ⟨308523310812115917049261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 411364414416154556065681 308523310812115917049261)
                      ·
                        rfl

theorem cell23_600847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 4, 2].length) (baseStart_600847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600847 prefixEnd_600847 := by exact prefixLift 600847
  have htrace : WordTrace (prefixWord ++ tailWord_600847) baseStart_600847 baseEnd_600847 := by
    simpa [prefixWord, tailWord_600847, baseEnd_600847] using wordTrace_append hprefix tailTrace_600847
  have hstable : (prefixWord ++ tailWord_600847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600847).length < 2 ^ (prefixWord ++ tailWord_600847).sum := by decide
  have hdescent : baseEnd_600847 < baseStart_600847 := by decide
  rcases family_descends (prefixWord ++ tailWord_600847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600868 : List Nat := [2, 3, 1, 3, 3, 2, 2, 1, 1, 3, 2]
def baseStart_600868 : Nat := 118140960795 + 600868 * 2 ^ 59
def prefixEnd_600868 : Nat := 4983230072969 + 3 ^ 40 * 600868 * 2
def baseEnd_600868 : Nat := 308534093905860334886665

theorem tailTrace_600868 : CollatzResearch.WordTrace tailWord_600868 prefixEnd_600868 308534093905860334886665 := by
  unfold tailWord_600868
  simp only [CollatzResearch.WordTrace]
  refine ⟨10957728193582665464753629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14610304258110220619671505 10957728193582665464753629)
  ·
    refine ⟨4109148072593499549282611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10957728193582665464753629 4109148072593499549282611)
    ·
      refine ⟨6163722108890249323923917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4109148072593499549282611 6163722108890249323923917)
      ·
        refine ⟨2311395790833843496471469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6163722108890249323923917 2311395790833843496471469)
        ·
          refine ⟨866773421562691311176801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2311395790833843496471469 866773421562691311176801)
          ·
            refine ⟨650080066172018483382601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 866773421562691311176801 650080066172018483382601)
            ·
              refine ⟨487560049629013862536951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 650080066172018483382601 487560049629013862536951)
              ·
                refine ⟨731340074443520793805427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 487560049629013862536951 731340074443520793805427)
                ·
                  refine ⟨1097010111665281190708141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 731340074443520793805427 1097010111665281190708141)
                  ·
                    refine ⟨411378791874480446515553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1097010111665281190708141 411378791874480446515553)
                    ·
                      refine ⟨308534093905860334886665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 411378791874480446515553 308534093905860334886665)
                      ·
                        rfl

theorem cell23_600868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_600868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600868 prefixEnd_600868 := by exact prefixLift 600868
  have htrace : WordTrace (prefixWord ++ tailWord_600868) baseStart_600868 baseEnd_600868 := by
    simpa [prefixWord, tailWord_600868, baseEnd_600868] using wordTrace_append hprefix tailTrace_600868
  have hstable : (prefixWord ++ tailWord_600868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600868).length < 2 ^ (prefixWord ++ tailWord_600868).sum := by decide
  have hdescent : baseEnd_600868 < baseStart_600868 := by decide
  rcases family_descends (prefixWord ++ tailWord_600868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600920 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 6, 1, 4]
def baseStart_600920 : Nat := 118140960795 + 600920 * 2 ^ 59
def prefixEnd_600920 : Nat := 4983230072969 + 3 ^ 40 * 600920 * 2
def baseEnd_600920 : Nat := 308560794899894131436425

theorem tailTrace_600920 : CollatzResearch.WordTrace tailWord_600920 prefixEnd_600920 308560794899894131436425 := by
  unfold tailWord_600920
  simp only [CollatzResearch.WordTrace]
  refine ⟨10958676491488471905200107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14611568655317962540266809 10958676491488471905200107)
  ·
    refine ⟨16438014737232707857800161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10958676491488471905200107 16438014737232707857800161)
    ·
      refine ⟨12328511052924530893350121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16438014737232707857800161 12328511052924530893350121)
      ·
        refine ⟨9246383289693398170012591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12328511052924530893350121 9246383289693398170012591)
        ·
          refine ⟨13869574934540097255018887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9246383289693398170012591 13869574934540097255018887)
          ·
            refine ⟨20804362401810145882528331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13869574934540097255018887 20804362401810145882528331)
            ·
              refine ⟨31206543602715218823792497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20804362401810145882528331 31206543602715218823792497)
              ·
                refine ⟨23404907702036414117844373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31206543602715218823792497 23404907702036414117844373)
                ·
                  refine ⟨1097105048532956911773955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23404907702036414117844373 1097105048532956911773955)
                  ·
                    refine ⟨1645657572799435367660933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1097105048532956911773955 1645657572799435367660933)
                    ·
                      refine ⟨308560794899894131436425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1645657572799435367660933 308560794899894131436425)
                      ·
                        rfl

theorem cell23_600920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_600920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600920 prefixEnd_600920 := by exact prefixLift 600920
  have htrace : WordTrace (prefixWord ++ tailWord_600920) baseStart_600920 baseEnd_600920 := by
    simpa [prefixWord, tailWord_600920, baseEnd_600920] using wordTrace_append hprefix tailTrace_600920
  have hstable : (prefixWord ++ tailWord_600920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600920).length < 2 ^ (prefixWord ++ tailWord_600920).sum := by decide
  have hdescent : baseEnd_600920 < baseStart_600920 := by decide
  rcases family_descends (prefixWord ++ tailWord_600920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600947 : List Nat := [1, 1, 1, 2, 2, 1, 7, 1, 3, 4]
def baseStart_600947 : Nat := 118140960795 + 600947 * 2 ^ 59
def prefixEnd_600947 : Nat := 4983230072969 + 3 ^ 40 * 600947 * 2
def baseEnd_600947 : Nat := 102858219625855175266267

theorem tailTrace_600947 : CollatzResearch.WordTrace tailWord_600947 prefixEnd_600947 102858219625855175266267 := by
  unfold tailWord_600947
  simp only [CollatzResearch.WordTrace]
  refine ⟨21918337753879127421633095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14612225169252751614422063 21918337753879127421633095)
  ·
    refine ⟨32877506630818691132449643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21918337753879127421633095 32877506630818691132449643)
    ·
      refine ⟨49316259946228036698674465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32877506630818691132449643 49316259946228036698674465)
      ·
        refine ⟨36987194959671027524005849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49316259946228036698674465 36987194959671027524005849)
        ·
          refine ⟨27740396219753270643004387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36987194959671027524005849 27740396219753270643004387)
          ·
            refine ⟨41610594329629905964506581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27740396219753270643004387 41610594329629905964506581)
            ·
              refine ⟨975248304600700921043123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 41610594329629905964506581 975248304600700921043123)
              ·
                refine ⟨1462872456901051381564685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 975248304600700921043123 1462872456901051381564685)
                ·
                  refine ⟨548577171337894268086757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1462872456901051381564685 548577171337894268086757)
                  ·
                    refine ⟨102858219625855175266267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 548577171337894268086757 102858219625855175266267)
                    ·
                      rfl

theorem cell23_600947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 3, 4].length) (baseStart_600947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600947 prefixEnd_600947 := by exact prefixLift 600947
  have htrace : WordTrace (prefixWord ++ tailWord_600947) baseStart_600947 baseEnd_600947 := by
    simpa [prefixWord, tailWord_600947, baseEnd_600947] using wordTrace_append hprefix tailTrace_600947
  have hstable : (prefixWord ++ tailWord_600947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600947).length < 2 ^ (prefixWord ++ tailWord_600947).sum := by decide
  have hdescent : baseEnd_600947 < baseStart_600947 := by decide
  rcases family_descends (prefixWord ++ tailWord_600947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600994 : List Nat := [3, 3, 1, 2, 2, 2, 2, 2, 6]
def baseStart_600994 : Nat := 118140960795 + 600994 * 2 ^ 59
def prefixEnd_600994 : Nat := 4983230072969 + 3 ^ 40 * 600994 * 2
def baseEnd_600994 : Nat := 34288754718702982434565

theorem tailTrace_600994 : CollatzResearch.WordTrace tailWord_600994 prefixEnd_600994 34288754718702982434565 := by
  unfold tailWord_600994
  simp only [CollatzResearch.WordTrace]
  refine ⟨5480012996177213612148509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14613367989805902965729357 5480012996177213612148509)
  ·
    refine ⟨2055004873566455104555691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5480012996177213612148509 2055004873566455104555691)
    ·
      refine ⟨3082507310349682656833537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2055004873566455104555691 3082507310349682656833537)
      ·
        refine ⟨2311880482762261992625153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3082507310349682656833537 2311880482762261992625153)
        ·
          refine ⟨1733910362071696494468865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2311880482762261992625153 1733910362071696494468865)
          ·
            refine ⟨1300432771553772370851649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1733910362071696494468865 1300432771553772370851649)
            ·
              refine ⟨975324578665329278138737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1300432771553772370851649 975324578665329278138737)
              ·
                refine ⟨731493433998996958604053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 975324578665329278138737 731493433998996958604053)
                ·
                  refine ⟨34288754718702982434565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 731493433998996958604053 34288754718702982434565)
                  ·
                    rfl

theorem cell23_600994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_600994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600994 prefixEnd_600994 := by exact prefixLift 600994
  have htrace : WordTrace (prefixWord ++ tailWord_600994) baseStart_600994 baseEnd_600994 := by
    simpa [prefixWord, tailWord_600994, baseEnd_600994] using wordTrace_append hprefix tailTrace_600994
  have hstable : (prefixWord ++ tailWord_600994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600994).length < 2 ^ (prefixWord ++ tailWord_600994).sum := by decide
  have hdescent : baseEnd_600994 < baseStart_600994 := by decide
  rcases family_descends (prefixWord ++ tailWord_600994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_600997 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 5, 5, 2]
def baseStart_600997 : Nat := 118140960795 + 600997 * 2 ^ 59
def prefixEnd_600997 : Nat := 4983230072969 + 3 ^ 40 * 600997 * 2
def baseEnd_600997 : Nat := 308600332910290330173571

theorem tailTrace_600997 : CollatzResearch.WordTrace tailWord_600997 prefixEnd_600997 308600332910290330173571 := by
  unfold tailWord_600997
  simp only [CollatzResearch.WordTrace]
  refine ⟨21920161403697985960953245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14613440935798657307302163 21920161403697985960953245)
  ·
    refine ⟨8220060526386744735357467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21920161403697985960953245 8220060526386744735357467)
    ·
      refine ⟨12330090789580117103036201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8220060526386744735357467 12330090789580117103036201)
      ·
        refine ⟨9247568092185087827277151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12330090789580117103036201 9247568092185087827277151)
        ·
          refine ⟨13871352138277631740915727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9247568092185087827277151 13871352138277631740915727)
          ·
            refine ⟨20807028207416447611373591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13871352138277631740915727 20807028207416447611373591)
            ·
              refine ⟨31210542311124671417060387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20807028207416447611373591 31210542311124671417060387)
              ·
                refine ⟨46815813466687007125590581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31210542311124671417060387 46815813466687007125590581)
                ·
                  refine ⟨4388982512501906918024117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46815813466687007125590581 4388982512501906918024117)
                  ·
                    refine ⟨411467110547053773564761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4388982512501906918024117 411467110547053773564761)
                    ·
                      refine ⟨308600332910290330173571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 411467110547053773564761 308600332910290330173571)
                      ·
                        rfl

theorem cell23_600997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 5, 2].length) (baseStart_600997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_600997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_600997 prefixEnd_600997 := by exact prefixLift 600997
  have htrace : WordTrace (prefixWord ++ tailWord_600997) baseStart_600997 baseEnd_600997 := by
    simpa [prefixWord, tailWord_600997, baseEnd_600997] using wordTrace_append hprefix tailTrace_600997
  have hstable : (prefixWord ++ tailWord_600997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_600997).length < 2 ^ (prefixWord ++ tailWord_600997).sum := by decide
  have hdescent : baseEnd_600997 < baseStart_600997 := by decide
  rcases family_descends (prefixWord ++ tailWord_600997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601021 : List Nat := [1, 4, 1, 2, 4, 1, 1, 2, 3, 1, 3]
def baseStart_601021 : Nat := 118140960795 + 601021 * 2 ^ 59
def prefixEnd_601021 : Nat := 4983230072969 + 3 ^ 40 * 601021 * 2
def baseEnd_601021 : Nat := 308612656445998236273461

theorem tailTrace_601021 : CollatzResearch.WordTrace tailWord_601021 prefixEnd_601021 308612656445998236273461 := by
  unfold tailWord_601021
  simp only [CollatzResearch.WordTrace]
  refine ⟨21921036755611038059826917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14614024503740692039884611 21921036755611038059826917)
  ·
    refine ⟨4110194391677069636217547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21921036755611038059826917 4110194391677069636217547)
    ·
      refine ⟨6165291587515604454326321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4110194391677069636217547 6165291587515604454326321)
      ·
        refine ⟨4623968690636703340744741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6165291587515604454326321 4623968690636703340744741)
        ·
          refine ⟨866994129494381876389639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4623968690636703340744741 866994129494381876389639)
          ·
            refine ⟨1300491194241572814584459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 866994129494381876389639 1300491194241572814584459)
            ·
              refine ⟨1950736791362359221876689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1300491194241572814584459 1950736791362359221876689)
              ·
                refine ⟨1463052593521769416407517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1950736791362359221876689 1463052593521769416407517)
                ·
                  refine ⟨548644722570663531152819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1463052593521769416407517 548644722570663531152819)
                  ·
                    refine ⟨822967083855995296729229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 548644722570663531152819 822967083855995296729229)
                    ·
                      refine ⟨308612656445998236273461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 822967083855995296729229 308612656445998236273461)
                      ·
                        rfl

theorem cell23_601021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_601021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601021 prefixEnd_601021 := by exact prefixLift 601021
  have htrace : WordTrace (prefixWord ++ tailWord_601021) baseStart_601021 baseEnd_601021 := by
    simpa [prefixWord, tailWord_601021, baseEnd_601021] using wordTrace_append hprefix tailTrace_601021
  have hstable : (prefixWord ++ tailWord_601021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601021).length < 2 ^ (prefixWord ++ tailWord_601021).sum := by decide
  have hdescent : baseEnd_601021 < baseStart_601021 := by decide
  rcases family_descends (prefixWord ++ tailWord_601021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601027 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 2, 6, 2]
def baseStart_601027 : Nat := 118140960795 + 601027 * 2 ^ 59
def prefixEnd_601027 : Nat := 4983230072969 + 3 ^ 40 * 601027 * 2
def baseEnd_601027 : Nat := 308615737329925212798433

theorem tailTrace_601027 : CollatzResearch.WordTrace tailWord_601027 prefixEnd_601027 308615737329925212798433 := by
  unfold tailWord_601027
  simp only [CollatzResearch.WordTrace]
  refine ⟨21921255593589301084545335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14614170395726200723030223 21921255593589301084545335)
  ·
    refine ⟨32881883390383951626818003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21921255593589301084545335 32881883390383951626818003)
    ·
      refine ⟨49322825085575927440227005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32881883390383951626818003 49322825085575927440227005)
      ·
        refine ⟨18496059407090972790085127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49322825085575927440227005 18496059407090972790085127)
        ·
          refine ⟨27744089110636459185127691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18496059407090972790085127 27744089110636459185127691)
          ·
            refine ⟨41616133665954688777691537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27744089110636459185127691 41616133665954688777691537)
            ·
              refine ⟨31212100249466016583268653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41616133665954688777691537 31212100249466016583268653)
              ·
                refine ⟨11704537593549756218725745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31212100249466016583268653 11704537593549756218725745)
                ·
                  refine ⟨8778403195162317164044309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11704537593549756218725745 8778403195162317164044309)
                  ·
                    refine ⟨411487649773233617064577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8778403195162317164044309 411487649773233617064577)
                    ·
                      refine ⟨308615737329925212798433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 411487649773233617064577 308615737329925212798433)
                      ·
                        rfl

theorem cell23_601027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 6, 2].length) (baseStart_601027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601027 prefixEnd_601027 := by exact prefixLift 601027
  have htrace : WordTrace (prefixWord ++ tailWord_601027) baseStart_601027 baseEnd_601027 := by
    simpa [prefixWord, tailWord_601027, baseEnd_601027] using wordTrace_append hprefix tailTrace_601027
  have hstable : (prefixWord ++ tailWord_601027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601027).length < 2 ^ (prefixWord ++ tailWord_601027).sum := by decide
  have hdescent : baseEnd_601027 < baseStart_601027 := by decide
  rcases family_descends (prefixWord ++ tailWord_601027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601038 : List Nat := [4, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3]
def baseStart_601038 : Nat := 118140960795 + 601038 * 2 ^ 59
def prefixEnd_601038 : Nat := 4983230072969 + 3 ^ 40 * 601038 * 2
def baseEnd_601038 : Nat := 308621385617124669760883

theorem tailTrace_601038 : CollatzResearch.WordTrace tailWord_601038 prefixEnd_601038 308621385617124669760883 := by
  unfold tailWord_601038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2740207099568681245399471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14614437864366299975463845 2740207099568681245399471)
  ·
    refine ⟨4110310649353021868099207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2740207099568681245399471 4110310649353021868099207)
    ·
      refine ⟨6165465974029532802148811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4110310649353021868099207 6165465974029532802148811)
      ·
        refine ⟨9248198961044299203223217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6165465974029532802148811 9248198961044299203223217)
        ·
          refine ⟨6936149220783224402417413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9248198961044299203223217 6936149220783224402417413)
          ·
            refine ⟨1300527978896854575453265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6936149220783224402417413 1300527978896854575453265)
            ·
              refine ⟨975395984172640931589949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1300527978896854575453265 975395984172640931589949)
              ·
                refine ⟨365773494064740349346231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 975395984172640931589949 365773494064740349346231)
                ·
                  refine ⟨548660241097110524019347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 365773494064740349346231 548660241097110524019347)
                  ·
                    refine ⟨822990361645665786029021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 548660241097110524019347 822990361645665786029021)
                    ·
                      refine ⟨308621385617124669760883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 822990361645665786029021 308621385617124669760883)
                      ·
                        rfl

theorem cell23_601038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3].length) (baseStart_601038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601038 prefixEnd_601038 := by exact prefixLift 601038
  have htrace : WordTrace (prefixWord ++ tailWord_601038) baseStart_601038 baseEnd_601038 := by
    simpa [prefixWord, tailWord_601038, baseEnd_601038] using wordTrace_append hprefix tailTrace_601038
  have hstable : (prefixWord ++ tailWord_601038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601038).length < 2 ^ (prefixWord ++ tailWord_601038).sum := by decide
  have hdescent : baseEnd_601038 < baseStart_601038 := by decide
  rcases family_descends (prefixWord ++ tailWord_601038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601040 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 6]
def baseStart_601040 : Nat := 118140960795 + 601040 * 2 ^ 59
def prefixEnd_601040 : Nat := 4983230072969 + 3 ^ 40 * 601040 * 2
def baseEnd_601040 : Nat := 308622412578433661935873

theorem tailTrace_601040 : CollatzResearch.WordTrace tailWord_601040 prefixEnd_601040 308622412578433661935873 := by
  unfold tailWord_601040
  simp only [CollatzResearch.WordTrace]
  refine ⟨10960864871271102152384287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14614486495028136203179049 10960864871271102152384287)
  ·
    refine ⟨16441297306906653228576431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10960864871271102152384287 16441297306906653228576431)
    ·
      refine ⟨24661945960359979842864647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16441297306906653228576431 24661945960359979842864647)
      ·
        refine ⟨36992918940539969764296971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24661945960359979842864647 36992918940539969764296971)
        ·
          refine ⟨55489378410809954646445457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36992918940539969764296971 55489378410809954646445457)
          ·
            refine ⟨41617033808107465984834093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55489378410809954646445457 41617033808107465984834093)
            ·
              refine ⟨15606387678040299744312785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41617033808107465984834093 15606387678040299744312785)
              ·
                refine ⟨11704790758530224808234589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15606387678040299744312785 11704790758530224808234589)
                ·
                  refine ⟨4389296534448834303087971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11704790758530224808234589 4389296534448834303087971)
                  ·
                    refine ⟨6583944801673251454631957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4389296534448834303087971 6583944801673251454631957)
                    ·
                      refine ⟨308622412578433661935873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6583944801673251454631957 308622412578433661935873)
                      ·
                        rfl

theorem cell23_601040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 6].length) (baseStart_601040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601040 prefixEnd_601040 := by exact prefixLift 601040
  have htrace : WordTrace (prefixWord ++ tailWord_601040) baseStart_601040 baseEnd_601040 := by
    simpa [prefixWord, tailWord_601040, baseEnd_601040] using wordTrace_append hprefix tailTrace_601040
  have hstable : (prefixWord ++ tailWord_601040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601040).length < 2 ^ (prefixWord ++ tailWord_601040).sum := by decide
  have hdescent : baseEnd_601040 < baseStart_601040 := by decide
  rcases family_descends (prefixWord ++ tailWord_601040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601047 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 5, 2, 3]
def baseStart_601047 : Nat := 118140960795 + 601047 * 2 ^ 59
def prefixEnd_601047 : Nat := 4983230072969 + 3 ^ 40 * 601047 * 2
def baseEnd_601047 : Nat := 308626006943015134548341

theorem tailTrace_601047 : CollatzResearch.WordTrace tailWord_601047 prefixEnd_601047 308626006943015134548341 := by
  unfold tailWord_601047
  simp only [CollatzResearch.WordTrace]
  refine ⟨21921985053516844500273395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14614656702344563000182263 21921985053516844500273395)
  ·
    refine ⟨32882977580275266750410093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21921985053516844500273395 32882977580275266750410093)
    ·
      refine ⟨12331116592603225031403785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32882977580275266750410093 12331116592603225031403785)
      ·
        refine ⟨9248337444452418773552839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12331116592603225031403785 9248337444452418773552839)
        ·
          refine ⟨13872506166678628160329259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9248337444452418773552839 13872506166678628160329259)
          ·
            refine ⟨20808759250017942240493889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13872506166678628160329259 20808759250017942240493889)
            ·
              refine ⟨15606569437513456680370417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20808759250017942240493889 15606569437513456680370417)
              ·
                refine ⟨11704927078135092510277813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15606569437513456680370417 11704927078135092510277813)
                ·
                  refine ⟨1097336913575164922838545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11704927078135092510277813 1097336913575164922838545)
                  ·
                    refine ⟨823002685181373692128909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1097336913575164922838545 823002685181373692128909)
                    ·
                      refine ⟨308626006943015134548341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 823002685181373692128909 308626006943015134548341)
                      ·
                        rfl

theorem cell23_601047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_601047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601047 prefixEnd_601047 := by exact prefixLift 601047
  have htrace : WordTrace (prefixWord ++ tailWord_601047) baseStart_601047 baseEnd_601047 := by
    simpa [prefixWord, tailWord_601047, baseEnd_601047] using wordTrace_append hprefix tailTrace_601047
  have hstable : (prefixWord ++ tailWord_601047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601047).length < 2 ^ (prefixWord ++ tailWord_601047).sum := by decide
  have hdescent : baseEnd_601047 < baseStart_601047 := by decide
  rcases family_descends (prefixWord ++ tailWord_601047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601071 : List Nat := [1, 1, 2, 1, 4, 4, 3, 1, 2, 4]
def baseStart_601071 : Nat := 118140960795 + 601071 * 2 ^ 59
def prefixEnd_601071 : Nat := 4983230072969 + 3 ^ 40 * 601071 * 2
def baseEnd_601071 : Nat := 102879443492907680216077

theorem tailTrace_601071 : CollatzResearch.WordTrace tailWord_601071 prefixEnd_601071 102879443492907680216077 := by
  unfold tailWord_601071
  simp only [CollatzResearch.WordTrace]
  refine ⟨21922860405429896599147067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14615240270286597732764711 21922860405429896599147067)
  ·
    refine ⟨32884290608144844898720601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21922860405429896599147067 32884290608144844898720601)
    ·
      refine ⟨24663217956108633674040451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32884290608144844898720601 24663217956108633674040451)
      ·
        refine ⟨36994826934162950511060677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24663217956108633674040451 36994826934162950511060677)
        ·
          refine ⟨6936530050155553220823877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36994826934162950511060677 6936530050155553220823877)
          ·
            refine ⟨1300599384404166228904477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6936530050155553220823877 1300599384404166228904477)
            ·
              refine ⟨487724769151562335839179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1300599384404166228904477 487724769151562335839179)
              ·
                refine ⟨731587153727343503758769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 487724769151562335839179 731587153727343503758769)
                ·
                  refine ⟨548690365295507627819077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 731587153727343503758769 548690365295507627819077)
                  ·
                    refine ⟨102879443492907680216077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 548690365295507627819077 102879443492907680216077)
                    ·
                      rfl

theorem cell23_601071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 2, 4].length) (baseStart_601071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601071 prefixEnd_601071 := by exact prefixLift 601071
  have htrace : WordTrace (prefixWord ++ tailWord_601071) baseStart_601071 baseEnd_601071 := by
    simpa [prefixWord, tailWord_601071, baseEnd_601071] using wordTrace_append hprefix tailTrace_601071
  have hstable : (prefixWord ++ tailWord_601071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601071).length < 2 ^ (prefixWord ++ tailWord_601071).sum := by decide
  have hdescent : baseEnd_601071 < baseStart_601071 := by decide
  rcases family_descends (prefixWord ++ tailWord_601071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601078 : List Nat := [5, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2]
def baseStart_601078 : Nat := 118140960795 + 601078 * 2 ^ 59
def prefixEnd_601078 : Nat := 4983230072969 + 3 ^ 40 * 601078 * 2
def baseEnd_601078 : Nat := 308641924843304513260699

theorem tailTrace_601078 : CollatzResearch.WordTrace tailWord_601078 prefixEnd_601078 308641924843304513260699 := by
  unfold tailWord_601078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1370194732275283549665743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14615410477603024529767925 1370194732275283549665743)
  ·
    refine ⟨2055292098412925324498615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1370194732275283549665743 2055292098412925324498615)
    ·
      refine ⟨3082938147619387986747923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2055292098412925324498615 3082938147619387986747923)
      ·
        refine ⟨4624407221429081980121885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3082938147619387986747923 4624407221429081980121885)
        ·
          refine ⟨1734152708035905742545707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4624407221429081980121885 1734152708035905742545707)
          ·
            refine ⟨2601229062053858613818561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1734152708035905742545707 2601229062053858613818561)
            ·
              refine ⟨1950921796540393960363921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2601229062053858613818561 1950921796540393960363921)
              ·
                refine ⟨1463191347405295470272941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1950921796540393960363921 1463191347405295470272941)
                ·
                  refine ⟨548696755276985801352353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1463191347405295470272941 548696755276985801352353)
                  ·
                    refine ⟨411522566457739351014265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 548696755276985801352353 411522566457739351014265)
                    ·
                      refine ⟨308641924843304513260699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 411522566457739351014265 308641924843304513260699)
                      ·
                        rfl

theorem cell23_601078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_601078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601078 prefixEnd_601078 := by exact prefixLift 601078
  have htrace : WordTrace (prefixWord ++ tailWord_601078) baseStart_601078 baseEnd_601078 := by
    simpa [prefixWord, tailWord_601078, baseEnd_601078] using wordTrace_append hprefix tailTrace_601078
  have hstable : (prefixWord ++ tailWord_601078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601078).length < 2 ^ (prefixWord ++ tailWord_601078).sum := by decide
  have hdescent : baseEnd_601078 < baseStart_601078 := by decide
  rcases family_descends (prefixWord ++ tailWord_601078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601084 : List Nat := [2, 2, 2, 1, 2, 5, 2, 7]
def baseStart_601084 : Nat := 118140960795 + 601084 * 2 ^ 59
def prefixEnd_601084 : Nat := 4983230072969 + 3 ^ 40 * 601084 * 2
def baseEnd_601084 : Nat := 11431296508415981103173

theorem tailTrace_601084 : CollatzResearch.WordTrace tailWord_601084 prefixEnd_601084 11431296508415981103173 := by
  unfold tailWord_601084
  simp only [CollatzResearch.WordTrace]
  refine ⟨10961667277191399909685153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14615556369588533212913537 10961667277191399909685153)
  ·
    refine ⟨8221250457893549932263865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10961667277191399909685153 8221250457893549932263865)
    ·
      refine ⟨6165937843420162449197899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8221250457893549932263865 6165937843420162449197899)
      ·
        refine ⟨9248906765130243673796849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6165937843420162449197899 9248906765130243673796849)
        ·
          refine ⟨6936680073847682755347637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9248906765130243673796849 6936680073847682755347637)
          ·
            refine ⟨650313756923220258313841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6936680073847682755347637 650313756923220258313841)
            ·
              refine ⟨487735317692415193735381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 650313756923220258313841 487735317692415193735381)
              ·
                refine ⟨11431296508415981103173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 487735317692415193735381 11431296508415981103173)
                ·
                  rfl

theorem cell23_601084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 7].length) (baseStart_601084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601084 prefixEnd_601084 := by exact prefixLift 601084
  have htrace : WordTrace (prefixWord ++ tailWord_601084) baseStart_601084 baseEnd_601084 := by
    simpa [prefixWord, tailWord_601084, baseEnd_601084] using wordTrace_append hprefix tailTrace_601084
  have hstable : (prefixWord ++ tailWord_601084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601084).length < 2 ^ (prefixWord ++ tailWord_601084).sum := by decide
  have hdescent : baseEnd_601084 < baseStart_601084 := by decide
  rcases family_descends (prefixWord ++ tailWord_601084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601111 : List Nat := [1, 1, 3, 5, 1, 1, 2, 1, 4, 1, 3]
def baseStart_601111 : Nat := 118140960795 + 601111 * 2 ^ 59
def prefixEnd_601111 : Nat := 4983230072969 + 3 ^ 40 * 601111 * 2
def baseEnd_601111 : Nat := 308658869704902884148047

theorem tailTrace_601111 : CollatzResearch.WordTrace tailWord_601111 prefixEnd_601111 308658869704902884148047 := by
  unfold tailWord_601111
  simp only [CollatzResearch.WordTrace]
  refine ⟨21924319325284983430603187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14616212883523322287068791 21924319325284983430603187)
  ·
    refine ⟨32886478987927475145904781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21924319325284983430603187 32886478987927475145904781)
    ·
      refine ⟨12332429620472803179714293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32886478987927475145904781 12332429620472803179714293)
      ·
        refine ⟨1156165276919325298098215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12332429620472803179714293 1156165276919325298098215)
        ·
          refine ⟨1734247915378987947147323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1156165276919325298098215 1734247915378987947147323)
          ·
            refine ⟨2601371873068481920720985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1734247915378987947147323 2601371873068481920720985)
            ·
              refine ⟨1951028904801361440540739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2601371873068481920720985 1951028904801361440540739)
              ·
                refine ⟨2926543357202042160811109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1951028904801361440540739 2926543357202042160811109)
                ·
                  refine ⟨548726879475382905152083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2926543357202042160811109 548726879475382905152083)
                  ·
                    refine ⟨823090319213074357728125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 548726879475382905152083 823090319213074357728125)
                    ·
                      refine ⟨308658869704902884148047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 823090319213074357728125 308658869704902884148047)
                      ·
                        rfl

theorem cell23_601111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_601111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601111 prefixEnd_601111 := by exact prefixLift 601111
  have htrace : WordTrace (prefixWord ++ tailWord_601111) baseStart_601111 baseEnd_601111 := by
    simpa [prefixWord, tailWord_601111, baseEnd_601111] using wordTrace_append hprefix tailTrace_601111
  have hstable : (prefixWord ++ tailWord_601111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601111).length < 2 ^ (prefixWord ++ tailWord_601111).sum := by decide
  have hdescent : baseEnd_601111 < baseStart_601111 := by decide
  rcases family_descends (prefixWord ++ tailWord_601111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601137 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 4, 1, 5]
def baseStart_601137 : Nat := 118140960795 + 601137 * 2 ^ 59
def prefixEnd_601137 : Nat := 4983230072969 + 3 ^ 40 * 601137 * 2
def baseEnd_601137 : Nat := 308672220201919782422927

theorem tailTrace_601137 : CollatzResearch.WordTrace tailWord_601137 prefixEnd_601137 308672220201919782422927 := by
  unfold tailWord_601137
  simp only [CollatzResearch.WordTrace]
  refine ⟨21925267623190789871049665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14616845082127193247366443 21925267623190789871049665)
  ·
    refine ⟨16443950717393092403287249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21925267623190789871049665 16443950717393092403287249)
    ·
      refine ⟨12332963038044819302465437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16443950717393092403287249 12332963038044819302465437)
      ·
        refine ⟨4624861139266807238424539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12332963038044819302465437 4624861139266807238424539)
        ·
          refine ⟨6937291708900210857636809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4624861139266807238424539 6937291708900210857636809)
          ·
            refine ⟨5202968781675158143227607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6937291708900210857636809 5202968781675158143227607)
            ·
              refine ⟨7804453172512737214841411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5202968781675158143227607 7804453172512737214841411)
              ·
                refine ⟨11706679758769105822262117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7804453172512737214841411 11706679758769105822262117)
                ·
                  refine ⟨2195002454769207341674147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11706679758769105822262117 2195002454769207341674147)
                  ·
                    refine ⟨3292503682153811012511221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2195002454769207341674147 3292503682153811012511221)
                    ·
                      refine ⟨308672220201919782422927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3292503682153811012511221 308672220201919782422927)
                      ·
                        rfl

theorem cell23_601137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_601137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601137 prefixEnd_601137 := by exact prefixLift 601137
  have htrace : WordTrace (prefixWord ++ tailWord_601137) baseStart_601137 baseEnd_601137 := by
    simpa [prefixWord, tailWord_601137, baseEnd_601137] using wordTrace_append hprefix tailTrace_601137
  have hstable : (prefixWord ++ tailWord_601137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601137).length < 2 ^ (prefixWord ++ tailWord_601137).sum := by decide
  have hdescent : baseEnd_601137 < baseStart_601137 := by decide
  rcases family_descends (prefixWord ++ tailWord_601137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601184 : List Nat := [2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 3]
def baseStart_601184 : Nat := 118140960795 + 601184 * 2 ^ 59
def prefixEnd_601184 : Nat := 4983230072969 + 3 ^ 40 * 601184 * 2
def baseEnd_601184 : Nat := 308696353792681098535211

theorem tailTrace_601184 : CollatzResearch.WordTrace tailWord_601184 prefixEnd_601184 308696353792681098535211 := by
  unfold tailWord_601184
  simp only [CollatzResearch.WordTrace]
  refine ⟨10963490927010258449005303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14617987902680344598673737 10963490927010258449005303)
  ·
    refine ⟨16445236390515387673507955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10963490927010258449005303 16445236390515387673507955)
    ·
      refine ⟨24667854585773081510261933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16445236390515387673507955 24667854585773081510261933)
      ·
        refine ⟨9250445469664905566348225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24667854585773081510261933 9250445469664905566348225)
        ·
          refine ⟨6937834102248679174761169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9250445469664905566348225 6937834102248679174761169)
          ·
            refine ⟨5203375576686509381070877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6937834102248679174761169 5203375576686509381070877)
            ·
              refine ⟨1951265841257441017901579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5203375576686509381070877 1951265841257441017901579)
              ·
                refine ⟨2926898761886161526852369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1951265841257441017901579 2926898761886161526852369)
                ·
                  refine ⟨2195174071414621145139277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2926898761886161526852369 2195174071414621145139277)
                  ·
                    refine ⟨823190276780482929427229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2195174071414621145139277 823190276780482929427229)
                    ·
                      refine ⟨308696353792681098535211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 823190276780482929427229 308696353792681098535211)
                      ·
                        rfl

theorem cell23_601184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_601184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601184 prefixEnd_601184 := by exact prefixLift 601184
  have htrace : WordTrace (prefixWord ++ tailWord_601184) baseStart_601184 baseEnd_601184 := by
    simpa [prefixWord, tailWord_601184, baseEnd_601184] using wordTrace_append hprefix tailTrace_601184
  have hstable : (prefixWord ++ tailWord_601184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601184).length < 2 ^ (prefixWord ++ tailWord_601184).sum := by decide
  have hdescent : baseEnd_601184 < baseStart_601184 := by decide
  rcases family_descends (prefixWord ++ tailWord_601184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601187 : List Nat := [1, 1, 1, 5, 1, 1, 1, 4, 1, 7]
def baseStart_601187 : Nat := 118140960795 + 601187 * 2 ^ 59
def prefixEnd_601187 : Nat := 4983230072969 + 3 ^ 40 * 601187 * 2
def baseEnd_601187 : Nat := 102899298078214862265899

theorem tailTrace_601187 : CollatzResearch.WordTrace tailWord_601187 prefixEnd_601187 102899298078214862265899 := by
  unfold tailWord_601187
  simp only [CollatzResearch.WordTrace]
  refine ⟨21927091273009648410369815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14618060848673098940246543 21927091273009648410369815)
  ·
    refine ⟨32890636909514472615554723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21927091273009648410369815 32890636909514472615554723)
    ·
      refine ⟨49335955364271708923332085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32890636909514472615554723 49335955364271708923332085)
      ·
        refine ⟨4625245815400472711562383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49335955364271708923332085 4625245815400472711562383)
        ·
          refine ⟨6937868723100709067343575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4625245815400472711562383 6937868723100709067343575)
          ·
            refine ⟨10406803084651063601015363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6937868723100709067343575 10406803084651063601015363)
            ·
              refine ⟨15610204626976595401523045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10406803084651063601015363 15610204626976595401523045)
              ·
                refine ⟨2926913367558111637785571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15610204626976595401523045 2926913367558111637785571)
                ·
                  refine ⟨4390370051337167456678357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2926913367558111637785571 4390370051337167456678357)
                  ·
                    refine ⟨102899298078214862265899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4390370051337167456678357 102899298078214862265899)
                    ·
                      rfl

theorem cell23_601187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 7].length) (baseStart_601187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601187 prefixEnd_601187 := by exact prefixLift 601187
  have htrace : WordTrace (prefixWord ++ tailWord_601187) baseStart_601187 baseEnd_601187 := by
    simpa [prefixWord, tailWord_601187, baseEnd_601187] using wordTrace_append hprefix tailTrace_601187
  have hstable : (prefixWord ++ tailWord_601187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601187).length < 2 ^ (prefixWord ++ tailWord_601187).sum := by decide
  have hdescent : baseEnd_601187 < baseStart_601187 := by decide
  rcases family_descends (prefixWord ++ tailWord_601187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601227 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 5]
def baseStart_601227 : Nat := 118140960795 + 601227 * 2 ^ 59
def prefixEnd_601227 : Nat := 4983230072969 + 3 ^ 40 * 601227 * 2
def baseEnd_601227 : Nat := 308718433460824430297513

theorem tailTrace_601227 : CollatzResearch.WordTrace tailWord_601227 prefixEnd_601227 308718433460824430297513 := by
  unfold tailWord_601227
  simp only [CollatzResearch.WordTrace]
  refine ⟨21928550192864735241825935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14619033461909823494550623 21928550192864735241825935)
  ·
    refine ⟨32892825289297102862738903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21928550192864735241825935 32892825289297102862738903)
    ·
      refine ⟨49339237933945654294108355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32892825289297102862738903 49339237933945654294108355)
      ·
        refine ⟨74008856900918481441162533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49339237933945654294108355 74008856900918481441162533)
        ·
          refine ⟨13876660668922215270217975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74008856900918481441162533 13876660668922215270217975)
          ·
            refine ⟨20814991003383322905326963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13876660668922215270217975 20814991003383322905326963)
            ·
              refine ⟨31222486505074984357990445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20814991003383322905326963 31222486505074984357990445)
              ·
                refine ⟨11708432439403119134246417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31222486505074984357990445 11708432439403119134246417)
                ·
                  refine ⟨8781324329552339350684813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11708432439403119134246417 8781324329552339350684813)
                  ·
                    refine ⟨3292996623582127256506805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8781324329552339350684813 3292996623582127256506805)
                    ·
                      refine ⟨308718433460824430297513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3292996623582127256506805 308718433460824430297513)
                      ·
                        rfl

theorem cell23_601227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 5].length) (baseStart_601227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601227 prefixEnd_601227 := by exact prefixLift 601227
  have htrace : WordTrace (prefixWord ++ tailWord_601227) baseStart_601227 baseEnd_601227 := by
    simpa [prefixWord, tailWord_601227, baseEnd_601227] using wordTrace_append hprefix tailTrace_601227
  have hstable : (prefixWord ++ tailWord_601227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601227).length < 2 ^ (prefixWord ++ tailWord_601227).sum := by decide
  have hdescent : baseEnd_601227 < baseStart_601227 := by decide
  rcases family_descends (prefixWord ++ tailWord_601227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601278 : List Nat := [4, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3]
def baseStart_601278 : Nat := 118140960795 + 601278 * 2 ^ 59
def prefixEnd_601278 : Nat := 4983230072969 + 3 ^ 40 * 601278 * 2
def baseEnd_601278 : Nat := 308744620974203730759779

theorem tailTrace_601278 : CollatzResearch.WordTrace tailWord_601278 prefixEnd_601278 308744620974203730759779 := by
  unfold tailWord_601278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2741301289459996368991561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14620273543786647301288325 2741301289459996368991561)
  ·
    refine ⟨2055975967094997276743671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2741301289459996368991561 2055975967094997276743671)
    ·
      refine ⟨3083963950642495915115507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2055975967094997276743671 3083963950642495915115507)
      ·
        refine ⟨4625945925963743872673261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3083963950642495915115507 4625945925963743872673261)
        ·
          refine ⟨1734729722236403952252473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4625945925963743872673261 1734729722236403952252473)
          ·
            refine ⟨1301047291677302964189355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1734729722236403952252473 1301047291677302964189355)
            ·
              refine ⟨1951570937515954446284033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1301047291677302964189355 1951570937515954446284033)
              ·
                refine ⟨1463678203136965834713025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1951570937515954446284033 1463678203136965834713025)
                ·
                  refine ⟨1097758652352724376034769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1463678203136965834713025 1097758652352724376034769)
                  ·
                    refine ⟨823318989264543282026077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1097758652352724376034769 823318989264543282026077)
                    ·
                      refine ⟨308744620974203730759779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 823318989264543282026077 308744620974203730759779)
                      ·
                        rfl

theorem cell23_601278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_601278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601278 prefixEnd_601278 := by exact prefixLift 601278
  have htrace : WordTrace (prefixWord ++ tailWord_601278) baseStart_601278 baseEnd_601278 := by
    simpa [prefixWord, tailWord_601278, baseEnd_601278] using wordTrace_append hprefix tailTrace_601278
  have hstable : (prefixWord ++ tailWord_601278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601278).length < 2 ^ (prefixWord ++ tailWord_601278).sum := by decide
  have hdescent : baseEnd_601278 < baseStart_601278 := by decide
  rcases family_descends (prefixWord ++ tailWord_601278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601281 : List Nat := [1, 2, 6, 1, 1, 1, 2, 1, 8]
def baseStart_601281 : Nat := 118140960795 + 601281 * 2 ^ 59
def prefixEnd_601281 : Nat := 4983230072969 + 3 ^ 40 * 601281 * 2
def baseEnd_601281 : Nat := 34305129046240802113585

theorem tailTrace_601281 : CollatzResearch.WordTrace tailWord_601281 prefixEnd_601281 34305129046240802113585 := by
  unfold tailWord_601281
  simp only [CollatzResearch.WordTrace]
  refine ⟨21930519734669102464291697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14620346489779401642861131 21930519734669102464291697)
  ·
    refine ⟨16447889801001826848218773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21930519734669102464291697 16447889801001826848218773)
    ·
      refine ⟨770994834421960633510255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16447889801001826848218773 770994834421960633510255)
      ·
        refine ⟨1156492251632940950265383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 770994834421960633510255 1156492251632940950265383)
        ·
          refine ⟨1734738377449411425398075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1156492251632940950265383 1734738377449411425398075)
          ·
            refine ⟨2602107566174117138097113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1734738377449411425398075 2602107566174117138097113)
            ·
              refine ⟨1951580674630587853572835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2602107566174117138097113 1951580674630587853572835)
              ·
                refine ⟨2927371011945881780359253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1951580674630587853572835 2927371011945881780359253)
                ·
                  refine ⟨34305129046240802113585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2927371011945881780359253 34305129046240802113585)
                  ·
                    rfl

theorem cell23_601281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 8].length) (baseStart_601281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601281 prefixEnd_601281 := by exact prefixLift 601281
  have htrace : WordTrace (prefixWord ++ tailWord_601281) baseStart_601281 baseEnd_601281 := by
    simpa [prefixWord, tailWord_601281, baseEnd_601281] using wordTrace_append hprefix tailTrace_601281
  have hstable : (prefixWord ++ tailWord_601281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601281).length < 2 ^ (prefixWord ++ tailWord_601281).sum := by decide
  have hdescent : baseEnd_601281 < baseStart_601281 := by decide
  rcases family_descends (prefixWord ++ tailWord_601281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601291 : List Nat := [1, 1, 1, 1, 3, 2, 2, 5, 3, 1, 3]
def baseStart_601291 : Nat := 118140960795 + 601291 * 2 ^ 59
def prefixEnd_601291 : Nat := 4983230072969 + 3 ^ 40 * 601291 * 2
def baseEnd_601291 : Nat := 308751296222712179897219

theorem tailTrace_601291 : CollatzResearch.WordTrace tailWord_601291 prefixEnd_601291 308751296222712179897219 := by
  unfold tailWord_601291
  simp only [CollatzResearch.WordTrace]
  refine ⟨21930884464632874172155727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14620589643088582781437151 21930884464632874172155727)
  ·
    refine ⟨32896326696949311258233591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21930884464632874172155727 32896326696949311258233591)
    ·
      refine ⟨49344490045423966887350387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32896326696949311258233591 49344490045423966887350387)
      ·
        refine ⟨74016735068135950331025581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49344490045423966887350387 74016735068135950331025581)
        ·
          refine ⟨27756275650550981374134593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74016735068135950331025581 27756275650550981374134593)
          ·
            refine ⟨20817206737913236030600945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27756275650550981374134593 20817206737913236030600945)
            ·
              refine ⟨15612905053434927022950709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20817206737913236030600945 15612905053434927022950709)
              ·
                refine ⟨1463709848759524408401629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15612905053434927022950709 1463709848759524408401629)
                ·
                  refine ⟨548891193284821653150611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1463709848759524408401629 548891193284821653150611)
                  ·
                    refine ⟨823336789927232479725917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 548891193284821653150611 823336789927232479725917)
                    ·
                      refine ⟨308751296222712179897219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 823336789927232479725917 308751296222712179897219)
                      ·
                        rfl

theorem cell23_601291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 3, 1, 3].length) (baseStart_601291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601291 prefixEnd_601291 := by exact prefixLift 601291
  have htrace : WordTrace (prefixWord ++ tailWord_601291) baseStart_601291 baseEnd_601291 := by
    simpa [prefixWord, tailWord_601291, baseEnd_601291] using wordTrace_append hprefix tailTrace_601291
  have hstable : (prefixWord ++ tailWord_601291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601291).length < 2 ^ (prefixWord ++ tailWord_601291).sum := by decide
  have hdescent : baseEnd_601291 < baseStart_601291 := by decide
  rcases family_descends (prefixWord ++ tailWord_601291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601311 : List Nat := [1, 1, 2, 3, 2, 1, 5, 2, 1, 5]
def baseStart_601311 : Nat := 118140960795 + 601311 * 2 ^ 59
def prefixEnd_601311 : Nat := 4983230072969 + 3 ^ 40 * 601311 * 2
def baseEnd_601311 : Nat := 102920521945267367215709

theorem tailTrace_601311 : CollatzResearch.WordTrace tailWord_601311 prefixEnd_601311 102920521945267367215709 := by
  unfold tailWord_601311
  simp only [CollatzResearch.WordTrace]
  refine ⟨21931613924560417587883787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14621075949706945058589191 21931613924560417587883787)
  ·
    refine ⟨32897420886840626381825681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21931613924560417587883787 32897420886840626381825681)
    ·
      refine ⟨24673065665130469786369261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32897420886840626381825681 24673065665130469786369261)
      ·
        refine ⟨9252399624423926169888473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24673065665130469786369261 9252399624423926169888473)
        ·
          refine ⟨6939299718317944627416355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9252399624423926169888473 6939299718317944627416355)
          ·
            refine ⟨10408949577476916941124533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6939299718317944627416355 10408949577476916941124533)
            ·
              refine ⟨975839022888460963230425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10408949577476916941124533 975839022888460963230425)
              ·
                refine ⟨731879267166345722422819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 975839022888460963230425 731879267166345722422819)
                ·
                  refine ⟨1097818900749518583634229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 731879267166345722422819 1097818900749518583634229)
                  ·
                    refine ⟨102920521945267367215709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1097818900749518583634229 102920521945267367215709)
                    ·
                      rfl

theorem cell23_601311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 5].length) (baseStart_601311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601311 prefixEnd_601311 := by exact prefixLift 601311
  have htrace : WordTrace (prefixWord ++ tailWord_601311) baseStart_601311 baseEnd_601311 := by
    simpa [prefixWord, tailWord_601311, baseEnd_601311] using wordTrace_append hprefix tailTrace_601311
  have hstable : (prefixWord ++ tailWord_601311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601311).length < 2 ^ (prefixWord ++ tailWord_601311).sum := by decide
  have hdescent : baseEnd_601311 < baseStart_601311 := by decide
  rcases family_descends (prefixWord ++ tailWord_601311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601324 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 3, 6]
def baseStart_601324 : Nat := 118140960795 + 601324 * 2 ^ 59
def prefixEnd_601324 : Nat := 4983230072969 + 3 ^ 40 * 601324 * 2
def baseEnd_601324 : Nat := 102922747028103516928189

theorem tailTrace_601324 : CollatzResearch.WordTrace tailWord_601324 prefixEnd_601324 102922747028103516928189 := by
  unfold tailWord_601324
  simp only [CollatzResearch.WordTrace]
  refine ⟨10966044036756660404053513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14621392049008880538738017 10966044036756660404053513)
  ·
    refine ⟨8224533027567495303040135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10966044036756660404053513 8224533027567495303040135)
    ·
      refine ⟨12336799541351242954560203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8224533027567495303040135 12336799541351242954560203)
      ·
        refine ⟨18505199312026864431840305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12336799541351242954560203 18505199312026864431840305)
        ·
          refine ⟨13878899484020148323880229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18505199312026864431840305 13878899484020148323880229)
          ·
            refine ⟨2602293653253777810727543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13878899484020148323880229 2602293653253777810727543)
            ·
              refine ⟨3903440479880666716091315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2602293653253777810727543 3903440479880666716091315)
              ·
                refine ⟨5855160719821000074136973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3903440479880666716091315 5855160719821000074136973)
                ·
                  refine ⟨2195685269932875027801365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5855160719821000074136973 2195685269932875027801365)
                  ·
                    refine ⟨102922747028103516928189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2195685269932875027801365 102922747028103516928189)
                    ·
                      rfl

theorem cell23_601324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 6].length) (baseStart_601324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601324 prefixEnd_601324 := by exact prefixLift 601324
  have htrace : WordTrace (prefixWord ++ tailWord_601324) baseStart_601324 baseEnd_601324 := by
    simpa [prefixWord, tailWord_601324, baseEnd_601324] using wordTrace_append hprefix tailTrace_601324
  have hstable : (prefixWord ++ tailWord_601324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601324).length < 2 ^ (prefixWord ++ tailWord_601324).sum := by decide
  have hdescent : baseEnd_601324 < baseStart_601324 := by decide
  rcases family_descends (prefixWord ++ tailWord_601324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601332 : List Nat := [2, 6, 1, 2, 1, 1, 2, 2, 6]
def baseStart_601332 : Nat := 118140960795 + 601332 * 2 ^ 59
def prefixEnd_601332 : Nat := 4983230072969 + 3 ^ 40 * 601332 * 2
def baseEnd_601332 : Nat := 34308038769949613276059

theorem tailTrace_601332 : CollatzResearch.WordTrace tailWord_601332 prefixEnd_601332 34308038769949613276059 := by
  unfold tailWord_601332
  simp only [CollatzResearch.WordTrace]
  refine ⟨10966189928742169087199125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14621586571656225449598833 10966189928742169087199125)
  ·
    refine ⟨514040152909789175962459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10966189928742169087199125 514040152909789175962459)
    ·
      refine ⟨771060229364683763943689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 514040152909789175962459 771060229364683763943689)
      ·
        refine ⟨578295172023512822957767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 771060229364683763943689 578295172023512822957767)
        ·
          refine ⟨867442758035269234436651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 578295172023512822957767 867442758035269234436651)
          ·
            refine ⟨1301164137052903851654977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 867442758035269234436651 1301164137052903851654977)
            ·
              refine ⟨975873102789677888741233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1301164137052903851654977 975873102789677888741233)
              ·
                refine ⟨731904827092258416555925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 975873102789677888741233 731904827092258416555925)
                ·
                  refine ⟨34308038769949613276059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 731904827092258416555925 34308038769949613276059)
                  ·
                    rfl

theorem cell23_601332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_601332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601332 prefixEnd_601332 := by exact prefixLift 601332
  have htrace : WordTrace (prefixWord ++ tailWord_601332) baseStart_601332 baseEnd_601332 := by
    simpa [prefixWord, tailWord_601332, baseEnd_601332] using wordTrace_append hprefix tailTrace_601332
  have hstable : (prefixWord ++ tailWord_601332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601332).length < 2 ^ (prefixWord ++ tailWord_601332).sum := by decide
  have hdescent : baseEnd_601332 < baseStart_601332 := by decide
  rcases family_descends (prefixWord ++ tailWord_601332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601342 : List Nat := [4, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3]
def baseStart_601342 : Nat := 118140960795 + 601342 * 2 ^ 59
def prefixEnd_601342 : Nat := 4983230072969 + 3 ^ 40 * 601342 * 2
def baseEnd_601342 : Nat := 308777483736091480359485

theorem tailTrace_601342 : CollatzResearch.WordTrace tailWord_601342 prefixEnd_601342 308777483736091480359485 := by
  unfold tailWord_601342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2741593073431013735282785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14621829724965406588174853 2741593073431013735282785)
  ·
    refine ⟨2056194805073260301462089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2741593073431013735282785 2056194805073260301462089)
    ·
      refine ⟨1542146103804945226096567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2056194805073260301462089 1542146103804945226096567)
      ·
        refine ⟨2313219155707417839144851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1542146103804945226096567 2313219155707417839144851)
        ·
          refine ⟨3469828733561126758717277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2313219155707417839144851 3469828733561126758717277)
          ·
            refine ⟨1301185775085422534518979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3469828733561126758717277 1301185775085422534518979)
            ·
              refine ⟨1951778662628133801778469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1301185775085422534518979 1951778662628133801778469)
              ·
                refine ⟨365958499242775087833463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1951778662628133801778469 365958499242775087833463)
                ·
                  refine ⟨548937748864162631750195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 365958499242775087833463 548937748864162631750195)
                  ·
                    refine ⟨823406623296243947625293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 548937748864162631750195 823406623296243947625293)
                    ·
                      refine ⟨308777483736091480359485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 823406623296243947625293 308777483736091480359485)
                      ·
                        rfl

theorem cell23_601342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_601342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601342 prefixEnd_601342 := by exact prefixLift 601342
  have htrace : WordTrace (prefixWord ++ tailWord_601342) baseStart_601342 baseEnd_601342 := by
    simpa [prefixWord, tailWord_601342, baseEnd_601342] using wordTrace_append hprefix tailTrace_601342
  have hstable : (prefixWord ++ tailWord_601342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601342).length < 2 ^ (prefixWord ++ tailWord_601342).sum := by decide
  have hdescent : baseEnd_601342 < baseStart_601342 := by decide
  rcases family_descends (prefixWord ++ tailWord_601342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601344 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 4]
def baseStart_601344 : Nat := 118140960795 + 601344 * 2 ^ 59
def prefixEnd_601344 : Nat := 4983230072969 + 3 ^ 40 * 601344 * 2
def baseEnd_601344 : Nat := 308778510697400472534475

theorem tailTrace_601344 : CollatzResearch.WordTrace tailWord_601344 prefixEnd_601344 308778510697400472534475 := by
  unfold tailWord_601344
  simp only [CollatzResearch.WordTrace]
  refine ⟨10966408766720432111917543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14621878355627242815890057 10966408766720432111917543)
  ·
    refine ⟨16449613150080648167876315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10966408766720432111917543 16449613150080648167876315)
    ·
      refine ⟨24674419725120972251814473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16449613150080648167876315 24674419725120972251814473)
      ·
        refine ⟨18505814793840729188860855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24674419725120972251814473 18505814793840729188860855)
        ·
          refine ⟨27758722190761093783291283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18505814793840729188860855 27758722190761093783291283)
          ·
            refine ⟨41638083286141640674936925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27758722190761093783291283 41638083286141640674936925)
            ·
              refine ⟨15614281232303115253101347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41638083286141640674936925 15614281232303115253101347)
              ·
                refine ⟨23421421848454672879652021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15614281232303115253101347 23421421848454672879652021)
                ·
                  refine ⟨2195758298292625582467377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23421421848454672879652021 2195758298292625582467377)
                  ·
                    refine ⟨1646818723719469186850533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2195758298292625582467377 1646818723719469186850533)
                    ·
                      refine ⟨308778510697400472534475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1646818723719469186850533 308778510697400472534475)
                      ·
                        rfl

theorem cell23_601344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_601344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601344 prefixEnd_601344 := by exact prefixLift 601344
  have htrace : WordTrace (prefixWord ++ tailWord_601344) baseStart_601344 baseEnd_601344 := by
    simpa [prefixWord, tailWord_601344, baseEnd_601344] using wordTrace_append hprefix tailTrace_601344
  have hstable : (prefixWord ++ tailWord_601344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601344).length < 2 ^ (prefixWord ++ tailWord_601344).sum := by decide
  have hdescent : baseEnd_601344 < baseStart_601344 := by decide
  rcases family_descends (prefixWord ++ tailWord_601344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601358 : List Nat := [4, 1, 1, 2, 1, 3, 2, 3, 2, 4]
def baseStart_601358 : Nat := 118140960795 + 601358 * 2 ^ 59
def prefixEnd_601358 : Nat := 4983230072969 + 3 ^ 40 * 601358 * 2
def baseEnd_601358 : Nat := 102928566475521139253137

theorem tailTrace_601358 : CollatzResearch.WordTrace tailWord_601358 prefixEnd_601358 102928566475521139253137 := by
  unfold tailWord_601358
  simp only [CollatzResearch.WordTrace]
  refine ⟨2741666019423768076855591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14622218770260096409896485 2741666019423768076855591)
  ·
    refine ⟨4112499029135652115283387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2741666019423768076855591 4112499029135652115283387)
    ·
      refine ⟨6168748543703478172925081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4112499029135652115283387 6168748543703478172925081)
      ·
        refine ⟨4626561407777608629693811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6168748543703478172925081 4626561407777608629693811)
        ·
          refine ⟨6939842111666412944540717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4626561407777608629693811 6939842111666412944540717)
          ·
            refine ⟨2602440791874904854202769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6939842111666412944540717 2602440791874904854202769)
            ·
              refine ⟨1951830593906178640652077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2602440791874904854202769 1951830593906178640652077)
              ·
                refine ⟨731936472714816990244529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1951830593906178640652077 731936472714816990244529)
                ·
                  refine ⟨548952354536112742683397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 731936472714816990244529 548952354536112742683397)
                  ·
                    refine ⟨102928566475521139253137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 548952354536112742683397 102928566475521139253137)
                    ·
                      rfl

theorem cell23_601358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_601358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601358 prefixEnd_601358 := by exact prefixLift 601358
  have htrace : WordTrace (prefixWord ++ tailWord_601358) baseStart_601358 baseEnd_601358 := by
    simpa [prefixWord, tailWord_601358, baseEnd_601358] using wordTrace_append hprefix tailTrace_601358
  have hstable : (prefixWord ++ tailWord_601358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601358).length < 2 ^ (prefixWord ++ tailWord_601358).sum := by decide
  have hdescent : baseEnd_601358 < baseStart_601358 := by decide
  rcases family_descends (prefixWord ++ tailWord_601358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601361 : List Nat := [1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 4]
def baseStart_601361 : Nat := 118140960795 + 601361 * 2 ^ 59
def prefixEnd_601361 : Nat := 4983230072969 + 3 ^ 40 * 601361 * 2
def baseEnd_601361 : Nat := 308787239868526906021897

theorem tailTrace_601361 : CollatzResearch.WordTrace tailWord_601361 prefixEnd_601361 308787239868526906021897 := by
  unfold tailWord_601361
  simp only [CollatzResearch.WordTrace]
  refine ⟨21933437574379276127203937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14622291716252850751469291 21933437574379276127203937)
  ·
    refine ⟨16450078180784457095402953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21933437574379276127203937 16450078180784457095402953)
    ·
      refine ⟨12337558635588342821552215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16450078180784457095402953 12337558635588342821552215)
      ·
        refine ⟨18506337953382514232328323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12337558635588342821552215 18506337953382514232328323)
        ·
          refine ⟨27759506930073771348492485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18506337953382514232328323 27759506930073771348492485)
          ·
            refine ⟨5204907549388832127842341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27759506930073771348492485 5204907549388832127842341)
            ·
              refine ⟨975920165510406023970439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5204907549388832127842341 975920165510406023970439)
              ·
                refine ⟨1463880248265609035955659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 975920165510406023970439 1463880248265609035955659)
                ·
                  refine ⟨2195820372398413553933489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1463880248265609035955659 2195820372398413553933489)
                  ·
                    refine ⟨1646865279298810165450117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2195820372398413553933489 1646865279298810165450117)
                    ·
                      refine ⟨308787239868526906021897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1646865279298810165450117 308787239868526906021897)
                      ·
                        rfl

theorem cell23_601361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 4].length) (baseStart_601361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601361 prefixEnd_601361 := by exact prefixLift 601361
  have htrace : WordTrace (prefixWord ++ tailWord_601361) baseStart_601361 baseEnd_601361 := by
    simpa [prefixWord, tailWord_601361, baseEnd_601361] using wordTrace_append hprefix tailTrace_601361
  have hstable : (prefixWord ++ tailWord_601361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601361).length < 2 ^ (prefixWord ++ tailWord_601361).sum := by decide
  have hdescent : baseEnd_601361 < baseStart_601361 := by decide
  rcases family_descends (prefixWord ++ tailWord_601361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601425 : List Nat := [1, 2, 2, 1, 4, 1, 4, 2, 1, 3, 2]
def baseStart_601425 : Nat := 118140960795 + 601425 * 2 ^ 59
def prefixEnd_601425 : Nat := 4983230072969 + 3 ^ 40 * 601425 * 2
def baseEnd_601425 : Nat := 308820102630414655621603

theorem tailTrace_601425 : CollatzResearch.WordTrace tailWord_601425 prefixEnd_601425 308820102630414655621603 := by
  unfold tailWord_601425
  simp only [CollatzResearch.WordTrace]
  refine ⟨21935771846147415057533729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14623847897431610038355819 21935771846147415057533729)
  ·
    refine ⟨16451828884610561293150297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21935771846147415057533729 16451828884610561293150297)
    ·
      refine ⟨12338871663457920969862723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16451828884610561293150297 12338871663457920969862723)
      ·
        refine ⟨18508307495186881454794085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12338871663457920969862723 18508307495186881454794085)
        ·
          refine ⟨3470307655347540272773891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18508307495186881454794085 3470307655347540272773891)
          ·
            refine ⟨5205461483021310409160837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3470307655347540272773891 5205461483021310409160837)
            ·
              refine ⟨976024028066495701717657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5205461483021310409160837 976024028066495701717657)
              ·
                refine ⟨732018021049871776288243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 976024028066495701717657 732018021049871776288243)
                ·
                  refine ⟨1098027031574807664432365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 732018021049871776288243 1098027031574807664432365)
                  ·
                    refine ⟨411760136840552874162137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1098027031574807664432365 411760136840552874162137)
                    ·
                      refine ⟨308820102630414655621603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 411760136840552874162137 308820102630414655621603)
                      ·
                        rfl

theorem cell23_601425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 3, 2].length) (baseStart_601425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601425 prefixEnd_601425 := by exact prefixLift 601425
  have htrace : WordTrace (prefixWord ++ tailWord_601425) baseStart_601425 baseEnd_601425 := by
    simpa [prefixWord, tailWord_601425, baseEnd_601425] using wordTrace_append hprefix tailTrace_601425
  have hstable : (prefixWord ++ tailWord_601425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601425).length < 2 ^ (prefixWord ++ tailWord_601425).sum := by decide
  have hdescent : baseEnd_601425 < baseStart_601425 := by decide
  rcases family_descends (prefixWord ++ tailWord_601425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601455 : List Nat := [1, 1, 2, 1, 3, 1, 4, 4, 2, 2, 2]
def baseStart_601455 : Nat := 118140960795 + 601455 * 2 ^ 59
def prefixEnd_601455 : Nat := 4983230072969 + 3 ^ 40 * 601455 * 2
def baseEnd_601455 : Nat := 308835507050049538246465

theorem tailTrace_601455 : CollatzResearch.WordTrace tailWord_601455 prefixEnd_601455 308835507050049538246465 := by
  unfold tailWord_601455
  simp only [CollatzResearch.WordTrace]
  refine ⟨21936866036038730181125819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14624577357359153454083879 21936866036038730181125819)
  ·
    refine ⟨32905299054058095271688729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21936866036038730181125819 32905299054058095271688729)
    ·
      refine ⟨24678974290543571453766547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32905299054058095271688729 24678974290543571453766547)
      ·
        refine ⟨37018461435815357180649821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24678974290543571453766547 37018461435815357180649821)
        ·
          refine ⟨13881923038430758942743683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37018461435815357180649821 13881923038430758942743683)
          ·
            refine ⟨20822884557646138414115525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13881923038430758942743683 20822884557646138414115525)
            ·
              refine ⟨3904290854558650952646661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20822884557646138414115525 3904290854558650952646661)
              ·
                refine ⟨732054535229747053621249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3904290854558650952646661 732054535229747053621249)
                ·
                  refine ⟨549040901422310290215937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 732054535229747053621249 549040901422310290215937)
                  ·
                    refine ⟨411780676066732717661953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 549040901422310290215937 411780676066732717661953)
                    ·
                      refine ⟨308835507050049538246465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 411780676066732717661953 308835507050049538246465)
                      ·
                        rfl

theorem cell23_601455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 2, 2, 2].length) (baseStart_601455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601455 prefixEnd_601455 := by exact prefixLift 601455
  have htrace : WordTrace (prefixWord ++ tailWord_601455) baseStart_601455 baseEnd_601455 := by
    simpa [prefixWord, tailWord_601455, baseEnd_601455] using wordTrace_append hprefix tailTrace_601455
  have hstable : (prefixWord ++ tailWord_601455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601455).length < 2 ^ (prefixWord ++ tailWord_601455).sum := by decide
  have hdescent : baseEnd_601455 < baseStart_601455 := by decide
  rcases family_descends (prefixWord ++ tailWord_601455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601512 : List Nat := [2, 1, 6, 1, 2, 1, 1, 4, 5]
def baseStart_601512 : Nat := 118140960795 + 601512 * 2 ^ 59
def prefixEnd_601512 : Nat := 4983230072969 + 3 ^ 40 * 601512 * 2
def baseEnd_601512 : Nat := 34318308383039535025967

theorem tailTrace_601512 : CollatzResearch.WordTrace tailWord_601512 prefixEnd_601512 34318308383039535025967 := by
  unfold tailWord_601512
  simp only [CollatzResearch.WordTrace]
  refine ⟨10969472498416114457975395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14625963331221485943967193 10969472498416114457975395)
  ·
    refine ⟨16454208747624171686963093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10969472498416114457975395 16454208747624171686963093)
    ·
      refine ⟨771291035044883047826395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16454208747624171686963093 771291035044883047826395)
      ·
        refine ⟨1156936552567324571739593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 771291035044883047826395 1156936552567324571739593)
        ·
          refine ⟨867702414425493428804695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1156936552567324571739593 867702414425493428804695)
          ·
            refine ⟨1301553621638240143207043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 867702414425493428804695 1301553621638240143207043)
            ·
              refine ⟨1952330432457360214810565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1301553621638240143207043 1952330432457360214810565)
              ·
                refine ⟨366061956085755040276981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1952330432457360214810565 366061956085755040276981)
                ·
                  refine ⟨34318308383039535025967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 366061956085755040276981 34318308383039535025967)
                  ·
                    rfl

theorem cell23_601512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 4, 5].length) (baseStart_601512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601512 prefixEnd_601512 := by exact prefixLift 601512
  have htrace : WordTrace (prefixWord ++ tailWord_601512) baseStart_601512 baseEnd_601512 := by
    simpa [prefixWord, tailWord_601512, baseEnd_601512] using wordTrace_append hprefix tailTrace_601512
  have hstable : (prefixWord ++ tailWord_601512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601512).length < 2 ^ (prefixWord ++ tailWord_601512).sum := by decide
  have hdescent : baseEnd_601512 < baseStart_601512 := by decide
  rcases family_descends (prefixWord ++ tailWord_601512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601528 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 1, 6, 2]
def baseStart_601528 : Nat := 118140960795 + 601528 * 2 ^ 59
def prefixEnd_601528 : Nat := 4983230072969 + 3 ^ 40 * 601528 * 2
def baseEnd_601528 : Nat := 308872991137827752633629

theorem tailTrace_601528 : CollatzResearch.WordTrace tailWord_601528 prefixEnd_601528 308872991137827752633629 := by
  unfold tailWord_601528
  simp only [CollatzResearch.WordTrace]
  refine ⟨10969764282387131824266619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14626352376516175765688825 10969764282387131824266619)
  ·
    refine ⟨16454646423580697736399929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10969764282387131824266619 16454646423580697736399929)
    ·
      refine ⟨12340984817685523302299947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16454646423580697736399929 12340984817685523302299947)
      ·
        refine ⟨18511477226528284953449921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12340984817685523302299947 18511477226528284953449921)
        ·
          refine ⟨13883607919896213715087441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18511477226528284953449921 13883607919896213715087441)
          ·
            refine ⟨10412705939922160286315581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13883607919896213715087441 10412705939922160286315581)
            ·
              refine ⟨3904764727470810107368343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10412705939922160286315581 3904764727470810107368343)
              ·
                refine ⟨5857147091206215161052515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3904764727470810107368343 5857147091206215161052515)
                ·
                  refine ⟨8785720636809322741578773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5857147091206215161052515 8785720636809322741578773)
                  ·
                    refine ⟨411830654850437003511505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8785720636809322741578773 411830654850437003511505)
                    ·
                      refine ⟨308872991137827752633629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 411830654850437003511505 308872991137827752633629)
                      ·
                        rfl

theorem cell23_601528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 1, 6, 2].length) (baseStart_601528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601528 prefixEnd_601528 := by exact prefixLift 601528
  have htrace : WordTrace (prefixWord ++ tailWord_601528) baseStart_601528 baseEnd_601528 := by
    simpa [prefixWord, tailWord_601528, baseEnd_601528] using wordTrace_append hprefix tailTrace_601528
  have hstable : (prefixWord ++ tailWord_601528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601528).length < 2 ^ (prefixWord ++ tailWord_601528).sum := by decide
  have hdescent : baseEnd_601528 < baseStart_601528 := by decide
  rcases family_descends (prefixWord ++ tailWord_601528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601585 : List Nat := [1, 2, 2, 2, 3, 3, 3, 1, 6]
def baseStart_601585 : Nat := 118140960795 + 601585 * 2 ^ 59
def prefixEnd_601585 : Nat := 4983230072969 + 3 ^ 40 * 601585 * 2
def baseEnd_601585 : Nat := 34322473281681558846763

theorem tailTrace_601585 : CollatzResearch.WordTrace tailWord_601585 prefixEnd_601585 34322473281681558846763 := by
  unfold tailWord_601585
  simp only [CollatzResearch.WordTrace]
  refine ⟨21941607525567762383358209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14627738350378508255572139 21941607525567762383358209)
  ·
    refine ⟨16456205644175821787518657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21941607525567762383358209 16456205644175821787518657)
    ·
      refine ⟨12342154233131866340638993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16456205644175821787518657 12342154233131866340638993)
      ·
        refine ⟨9256615674848899755479245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12342154233131866340638993 9256615674848899755479245)
        ·
          refine ⟨3471230878068337408304717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9256615674848899755479245 3471230878068337408304717)
          ·
            refine ⟨1301711579275626528114269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3471230878068337408304717 1301711579275626528114269)
            ·
              refine ⟨488141842228359948042851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1301711579275626528114269 488141842228359948042851)
              ·
                refine ⟨732212763342539922064277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 488141842228359948042851 732212763342539922064277)
                ·
                  refine ⟨34322473281681558846763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 732212763342539922064277 34322473281681558846763)
                  ·
                    rfl

theorem cell23_601585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 6].length) (baseStart_601585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601585 prefixEnd_601585 := by exact prefixLift 601585
  have htrace : WordTrace (prefixWord ++ tailWord_601585) baseStart_601585 baseEnd_601585 := by
    simpa [prefixWord, tailWord_601585, baseEnd_601585] using wordTrace_append hprefix tailTrace_601585
  have hstable : (prefixWord ++ tailWord_601585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601585).length < 2 ^ (prefixWord ++ tailWord_601585).sum := by decide
  have hdescent : baseEnd_601585 < baseStart_601585 := by decide
  rcases family_descends (prefixWord ++ tailWord_601585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601605 : List Nat := [1, 3, 1, 1, 2, 2, 1, 5, 2, 3, 2]
def baseStart_601605 : Nat := 118140960795 + 601605 * 2 ^ 59
def prefixEnd_601605 : Nat := 4983230072969 + 3 ^ 40 * 601605 * 2
def baseEnd_601605 : Nat := 308912529148223951370775

theorem tailTrace_601605 : CollatzResearch.WordTrace tailWord_601605 prefixEnd_601605 308912529148223951370775 := by
  unfold tailWord_601605
  simp only [CollatzResearch.WordTrace]
  refine ⟨21942336985495305799086269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14628224656996870532724179 21942336985495305799086269)
  ·
    refine ⟨8228376369560739674657351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21942336985495305799086269 8228376369560739674657351)
    ·
      refine ⟨12342564554341109511986027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8228376369560739674657351 12342564554341109511986027)
      ·
        refine ⟨18513846831511664267979041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12342564554341109511986027 18513846831511664267979041)
        ·
          refine ⟨13885385123633748200984281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18513846831511664267979041 13885385123633748200984281)
          ·
            refine ⟨10414038842725311150738211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13885385123633748200984281 10414038842725311150738211)
            ·
              refine ⟨15621058264087966726107317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10414038842725311150738211 15621058264087966726107317)
              ·
                refine ⟨1464474212258246880572561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15621058264087966726107317 1464474212258246880572561)
                ·
                  refine ⟨1098355659193685160429421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1464474212258246880572561 1098355659193685160429421)
                  ·
                    refine ⟨411883372197631935161033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1098355659193685160429421 411883372197631935161033)
                    ·
                      refine ⟨308912529148223951370775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 411883372197631935161033 308912529148223951370775)
                      ·
                        rfl

theorem cell23_601605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 3, 2].length) (baseStart_601605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601605 prefixEnd_601605 := by exact prefixLift 601605
  have htrace : WordTrace (prefixWord ++ tailWord_601605) baseStart_601605 baseEnd_601605 := by
    simpa [prefixWord, tailWord_601605, baseEnd_601605] using wordTrace_append hprefix tailTrace_601605
  have hstable : (prefixWord ++ tailWord_601605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601605).length < 2 ^ (prefixWord ++ tailWord_601605).sum := by decide
  have hdescent : baseEnd_601605 < baseStart_601605 := by decide
  rcases family_descends (prefixWord ++ tailWord_601605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601648 : List Nat := [2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 4]
def baseStart_601648 : Nat := 118140960795 + 601648 * 2 ^ 59
def prefixEnd_601648 : Nat := 4983230072969 + 3 ^ 40 * 601648 * 2
def baseEnd_601648 : Nat := 308934608816367283133077

theorem tailTrace_601648 : CollatzResearch.WordTrace tailWord_601648 prefixEnd_601648 308934608816367283133077 := by
  unfold tailWord_601648
  simp only [CollatzResearch.WordTrace]
  refine ⟨10971952662169762071450799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14629270216226349428601065 10971952662169762071450799)
  ·
    refine ⟨16457928993254643107176199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10971952662169762071450799 16457928993254643107176199)
    ·
      refine ⟨24686893489881964660764299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16457928993254643107176199 24686893489881964660764299)
      ·
        refine ⟨37030340234822946991146449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24686893489881964660764299 37030340234822946991146449)
        ·
          refine ⟨27772755176117210243359837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37030340234822946991146449 27772755176117210243359837)
          ·
            refine ⟨10414783191043953841259939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27772755176117210243359837 10414783191043953841259939)
            ·
              refine ⟨15622174786565930761889909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10414783191043953841259939 15622174786565930761889909)
              ·
                refine ⟨1464578886240556008927179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15622174786565930761889909 1464578886240556008927179)
                ·
                  refine ⟨2196868329360834013390769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1464578886240556008927179 2196868329360834013390769)
                  ·
                    refine ⟨1647651247020625510043077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2196868329360834013390769 1647651247020625510043077)
                    ·
                      refine ⟨308934608816367283133077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1647651247020625510043077 308934608816367283133077)
                      ·
                        rfl

theorem cell23_601648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 4].length) (baseStart_601648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601648 prefixEnd_601648 := by exact prefixLift 601648
  have htrace : WordTrace (prefixWord ++ tailWord_601648) baseStart_601648 baseEnd_601648 := by
    simpa [prefixWord, tailWord_601648, baseEnd_601648] using wordTrace_append hprefix tailTrace_601648
  have hstable : (prefixWord ++ tailWord_601648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601648).length < 2 ^ (prefixWord ++ tailWord_601648).sum := by decide
  have hdescent : baseEnd_601648 < baseStart_601648 := by decide
  rcases family_descends (prefixWord ++ tailWord_601648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601655 : List Nat := [1, 1, 3, 1, 2, 5, 1, 1, 3, 2, 3]
def baseStart_601655 : Nat := 118140960795 + 601655 * 2 ^ 59
def prefixEnd_601655 : Nat := 4983230072969 + 3 ^ 40 * 601655 * 2
def baseEnd_601655 : Nat := 308938203180948755745545

theorem tailTrace_601655 : CollatzResearch.WordTrace tailWord_601655 prefixEnd_601655 308938203180948755745545 := by
  unfold tailWord_601655
  simp only [CollatzResearch.WordTrace]
  refine ⟨21944160635314164338406419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14629440423542776225604279 21944160635314164338406419)
  ·
    refine ⟨32916240952971246507609629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21944160635314164338406419 32916240952971246507609629)
    ·
      refine ⟨12343590357364217440353611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32916240952971246507609629 12343590357364217440353611)
      ·
        refine ⟨18515385536046326160530417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12343590357364217440353611 18515385536046326160530417)
        ·
          refine ⟨13886539152034744620397813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18515385536046326160530417 13886539152034744620397813)
          ·
            refine ⟨1301863045503257308162295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13886539152034744620397813 1301863045503257308162295)
            ·
              refine ⟨1952794568254885962243443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1301863045503257308162295 1952794568254885962243443)
              ·
                refine ⟨2929191852382328943365165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1952794568254885962243443 2929191852382328943365165)
                ·
                  refine ⟨1098446944643373353761937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2929191852382328943365165 1098446944643373353761937)
                  ·
                    refine ⟨823835208482530015321453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1098446944643373353761937 823835208482530015321453)
                    ·
                      refine ⟨308938203180948755745545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 823835208482530015321453 308938203180948755745545)
                      ·
                        rfl

theorem cell23_601655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 2, 3].length) (baseStart_601655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601655 prefixEnd_601655 := by exact prefixLift 601655
  have htrace : WordTrace (prefixWord ++ tailWord_601655) baseStart_601655 baseEnd_601655 := by
    simpa [prefixWord, tailWord_601655, baseEnd_601655] using wordTrace_append hprefix tailTrace_601655
  have hstable : (prefixWord ++ tailWord_601655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601655).length < 2 ^ (prefixWord ++ tailWord_601655).sum := by decide
  have hdescent : baseEnd_601655 < baseStart_601655 := by decide
  rcases family_descends (prefixWord ++ tailWord_601655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601665 : List Nat := [1, 2, 5, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_601665 : Nat := 118140960795 + 601665 * 2 ^ 59
def prefixEnd_601665 : Nat := 4983230072969 + 3 ^ 40 * 601665 * 2
def baseEnd_601665 : Nat := 308943337987493716620499

theorem tailTrace_601665 : CollatzResearch.WordTrace tailWord_601665 prefixEnd_601665 308943337987493716620499 := by
  unfold tailWord_601665
  simp only [CollatzResearch.WordTrace]
  refine ⟨21944525365277936046270449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14629683576851957364180299 21944525365277936046270449)
  ·
    refine ⟨16458394023958452034702837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21944525365277936046270449 16458394023958452034702837)
    ·
      refine ⟨1542974439746104878253391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16458394023958452034702837 1542974439746104878253391)
      ·
        refine ⟨2314461659619157317380087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1542974439746104878253391 2314461659619157317380087)
        ·
          refine ⟨3471692489428735976070131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2314461659619157317380087 3471692489428735976070131)
          ·
            refine ⟨5207538734143103964105197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3471692489428735976070131 5207538734143103964105197)
            ·
              refine ⟨1952827025303663986539449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5207538734143103964105197 1952827025303663986539449)
              ·
                refine ⟨1464620268977747989904587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1952827025303663986539449 1464620268977747989904587)
                ·
                  refine ⟨2196930403466621984856881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1464620268977747989904587 2196930403466621984856881)
                  ·
                    refine ⟨1647697802599966488642661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2196930403466621984856881 1647697802599966488642661)
                    ·
                      refine ⟨308943337987493716620499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1647697802599966488642661 308943337987493716620499)
                      ·
                        rfl

theorem cell23_601665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_601665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601665 prefixEnd_601665 := by exact prefixLift 601665
  have htrace : WordTrace (prefixWord ++ tailWord_601665) baseStart_601665 baseEnd_601665 := by
    simpa [prefixWord, tailWord_601665, baseEnd_601665] using wordTrace_append hprefix tailTrace_601665
  have hstable : (prefixWord ++ tailWord_601665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601665).length < 2 ^ (prefixWord ++ tailWord_601665).sum := by decide
  have hdescent : baseEnd_601665 < baseStart_601665 := by decide
  rcases family_descends (prefixWord ++ tailWord_601665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601669 : List Nat := [1, 3, 1, 1, 1, 4, 2, 5, 1, 2, 2]
def baseStart_601669 : Nat := 118140960795 + 601669 * 2 ^ 59
def prefixEnd_601669 : Nat := 4983230072969 + 3 ^ 40 * 601669 * 2
def baseEnd_601669 : Nat := 308945391910111700970481

theorem tailTrace_601669 : CollatzResearch.WordTrace tailWord_601669 prefixEnd_601669 308945391910111700970481 := by
  unfold tailWord_601669
  simp only [CollatzResearch.WordTrace]
  refine ⟨21944671257263444729416061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14629780838175629819610707 21944671257263444729416061)
  ·
    refine ⟨8229251721473791773531023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21944671257263444729416061 8229251721473791773531023)
    ·
      refine ⟨12343877582210687660296535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8229251721473791773531023 12343877582210687660296535)
      ·
        refine ⟨18515816373316031490444803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12343877582210687660296535 18515816373316031490444803)
        ·
          refine ⟨27773724559974047235667205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18515816373316031490444803 27773724559974047235667205)
          ·
            refine ⟨5207573354995133856687601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27773724559974047235667205 5207573354995133856687601)
            ·
              refine ⟨3905680016246350392515701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5207573354995133856687601 3905680016246350392515701)
              ·
                refine ⟨366157501523095349298347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3905680016246350392515701 366157501523095349298347)
                ·
                  refine ⟨549236252284643023947521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 366157501523095349298347 549236252284643023947521)
                  ·
                    refine ⟨411927189213482267960641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 549236252284643023947521 411927189213482267960641)
                    ·
                      refine ⟨308945391910111700970481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 411927189213482267960641 308945391910111700970481)
                      ·
                        rfl

theorem cell23_601669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 5, 1, 2, 2].length) (baseStart_601669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601669 prefixEnd_601669 := by exact prefixLift 601669
  have htrace : WordTrace (prefixWord ++ tailWord_601669) baseStart_601669 baseEnd_601669 := by
    simpa [prefixWord, tailWord_601669, baseEnd_601669] using wordTrace_append hprefix tailTrace_601669
  have hstable : (prefixWord ++ tailWord_601669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601669).length < 2 ^ (prefixWord ++ tailWord_601669).sum := by decide
  have hdescent : baseEnd_601669 < baseStart_601669 := by decide
  rcases family_descends (prefixWord ++ tailWord_601669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601708 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 4]
def baseStart_601708 : Nat := 118140960795 + 601708 * 2 ^ 59
def prefixEnd_601708 : Nat := 4983230072969 + 3 ^ 40 * 601708 * 2
def baseEnd_601708 : Nat := 308965417655637048382801

theorem tailTrace_601708 : CollatzResearch.WordTrace tailWord_601708 prefixEnd_601708 308965417655637048382801 := by
  unfold tailWord_601708
  simp only [CollatzResearch.WordTrace]
  refine ⟨10973046852061077195042889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14630729136081436260057185 10973046852061077195042889)
  ·
    refine ⟨8229785139045807896282167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10973046852061077195042889 8229785139045807896282167)
    ·
      refine ⟨12344677708568711844423251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8229785139045807896282167 12344677708568711844423251)
      ·
        refine ⟨18517016562853067766634877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12344677708568711844423251 18517016562853067766634877)
        ·
          refine ⟨6943881211069900412488079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18517016562853067766634877 6943881211069900412488079)
          ·
            refine ⟨10415821816604850618732119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6943881211069900412488079 10415821816604850618732119)
            ·
              refine ⟨15623732724907275928098179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10415821816604850618732119 15623732724907275928098179)
              ·
                refine ⟨23435599087360913892147269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15623732724907275928098179 23435599087360913892147269)
                ·
                  refine ⟨4394174828880171354777613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23435599087360913892147269 4394174828880171354777613)
                  ·
                    refine ⟨1647815560830064258041605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4394174828880171354777613 1647815560830064258041605)
                    ·
                      refine ⟨308965417655637048382801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1647815560830064258041605 308965417655637048382801)
                      ·
                        rfl

theorem cell23_601708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_601708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601708 prefixEnd_601708 := by exact prefixLift 601708
  have htrace : WordTrace (prefixWord ++ tailWord_601708) baseStart_601708 baseEnd_601708 := by
    simpa [prefixWord, tailWord_601708, baseEnd_601708] using wordTrace_append hprefix tailTrace_601708
  have hstable : (prefixWord ++ tailWord_601708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601708).length < 2 ^ (prefixWord ++ tailWord_601708).sum := by decide
  have hdescent : baseEnd_601708 < baseStart_601708 := by decide
  rcases family_descends (prefixWord ++ tailWord_601708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601712 : List Nat := [2, 1, 1, 1, 6, 1, 2, 1, 3, 3, 2]
def baseStart_601712 : Nat := 118140960795 + 601712 * 2 ^ 59
def prefixEnd_601712 : Nat := 4983230072969 + 3 ^ 40 * 601712 * 2
def baseEnd_601712 : Nat := 308967471578255032732783

theorem tailTrace_601712 : CollatzResearch.WordTrace tailWord_601712 prefixEnd_601712 308967471578255032732783 := by
  unfold tailWord_601712
  simp only [CollatzResearch.WordTrace]
  refine ⟨10973119798053831536615695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14630826397405108715487593 10973119798053831536615695)
  ·
    refine ⟨16459679697080747304923543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10973119798053831536615695 16459679697080747304923543)
    ·
      refine ⟨24689519545621120957385315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16459679697080747304923543 24689519545621120957385315)
      ·
        refine ⟨37034279318431681436077973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24689519545621120957385315 37034279318431681436077973)
        ·
          refine ⟨1735981843051485067316155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 37034279318431681436077973 1735981843051485067316155)
          ·
            refine ⟨2603972764577227600974233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1735981843051485067316155 2603972764577227600974233)
            ·
              refine ⟨1952979573432920700730675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2603972764577227600974233 1952979573432920700730675)
              ·
                refine ⟨2929469360149381051096013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1952979573432920700730675 2929469360149381051096013)
                ·
                  refine ⟨1098551010056017894161005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2929469360149381051096013 1098551010056017894161005)
                  ·
                    refine ⟨411956628771006710310377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1098551010056017894161005 411956628771006710310377)
                    ·
                      refine ⟨308967471578255032732783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 411956628771006710310377 308967471578255032732783)
                      ·
                        rfl

theorem cell23_601712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 3, 3, 2].length) (baseStart_601712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601712 prefixEnd_601712 := by exact prefixLift 601712
  have htrace : WordTrace (prefixWord ++ tailWord_601712) baseStart_601712 baseEnd_601712 := by
    simpa [prefixWord, tailWord_601712, baseEnd_601712] using wordTrace_append hprefix tailTrace_601712
  have hstable : (prefixWord ++ tailWord_601712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601712).length < 2 ^ (prefixWord ++ tailWord_601712).sum := by decide
  have hdescent : baseEnd_601712 < baseStart_601712 := by decide
  rcases family_descends (prefixWord ++ tailWord_601712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601728 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 5]
def baseStart_601728 : Nat := 118140960795 + 601728 * 2 ^ 59
def prefixEnd_601728 : Nat := 4983230072969 + 3 ^ 40 * 601728 * 2
def baseEnd_601728 : Nat := 308975687268726970132709

theorem tailTrace_601728 : CollatzResearch.WordTrace tailWord_601728 prefixEnd_601728 308975687268726970132709 := by
  unfold tailWord_601728
  simp only [CollatzResearch.WordTrace]
  refine ⟨10973411582024848902906919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14631215442699798537209225 10973411582024848902906919)
  ·
    refine ⟨16460117373037273354360379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10973411582024848902906919 16460117373037273354360379)
    ·
      refine ⟨24690176059555910031540569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16460117373037273354360379 24690176059555910031540569)
      ·
        refine ⟨18517632044666932523655427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24690176059555910031540569 18517632044666932523655427)
        ·
          refine ⟨27776448067000398785483141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18517632044666932523655427 27776448067000398785483141)
          ·
            refine ⟨5208084012562574772278089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27776448067000398785483141 5208084012562574772278089)
            ·
              refine ⟨3906063009421931079208567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5208084012562574772278089 3906063009421931079208567)
              ·
                refine ⟨5859094514132896618812851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3906063009421931079208567 5859094514132896618812851)
                ·
                  refine ⟨8788641771199344928219277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5859094514132896618812851 8788641771199344928219277)
                  ·
                    refine ⟨3295740664199754348082229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8788641771199344928219277 3295740664199754348082229)
                    ·
                      refine ⟨308975687268726970132709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3295740664199754348082229 308975687268726970132709)
                      ·
                        rfl

theorem cell23_601728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_601728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601728 prefixEnd_601728 := by exact prefixLift 601728
  have htrace : WordTrace (prefixWord ++ tailWord_601728) baseStart_601728 baseEnd_601728 := by
    simpa [prefixWord, tailWord_601728, baseEnd_601728] using wordTrace_append hprefix tailTrace_601728
  have hstable : (prefixWord ++ tailWord_601728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601728).length < 2 ^ (prefixWord ++ tailWord_601728).sum := by decide
  have hdescent : baseEnd_601728 < baseStart_601728 := by decide
  rcases family_descends (prefixWord ++ tailWord_601728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601729 : List Nat := [1, 2, 4, 2, 1, 3, 1, 3, 1, 3, 2]
def baseStart_601729 : Nat := 118140960795 + 601729 * 2 ^ 59
def prefixEnd_601729 : Nat := 4983230072969 + 3 ^ 40 * 601729 * 2
def baseEnd_601729 : Nat := 308976200749381466220205

theorem tailTrace_601729 : CollatzResearch.WordTrace tailWord_601729 prefixEnd_601729 308976200749381466220205 := by
  unfold tailWord_601729
  simp only [CollatzResearch.WordTrace]
  refine ⟨21946859637046074976600241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14631239758030716651066827 21946859637046074976600241)
  ·
    refine ⟨16460144727784556232450181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21946859637046074976600241 16460144727784556232450181)
    ·
      refine ⟨3086277136459604293584409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16460144727784556232450181 3086277136459604293584409)
      ·
        refine ⟨2314707852344703220188307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3086277136459604293584409 2314707852344703220188307)
        ·
          refine ⟨3472061778517054830282461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2314707852344703220188307 3472061778517054830282461)
          ·
            refine ⟨1302023166943895561355923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3472061778517054830282461 1302023166943895561355923)
            ·
              refine ⟨1953034750415843342033885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1302023166943895561355923 1953034750415843342033885)
              ·
                refine ⟨732388031405941253262707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1953034750415843342033885 732388031405941253262707)
                ·
                  refine ⟨1098582047108911879894061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 732388031405941253262707 1098582047108911879894061)
                  ·
                    refine ⟨411968267665841954960273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1098582047108911879894061 411968267665841954960273)
                    ·
                      refine ⟨308976200749381466220205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 411968267665841954960273 308976200749381466220205)
                      ·
                        rfl

theorem cell23_601729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_601729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601729 prefixEnd_601729 := by exact prefixLift 601729
  have htrace : WordTrace (prefixWord ++ tailWord_601729) baseStart_601729 baseEnd_601729 := by
    simpa [prefixWord, tailWord_601729, baseEnd_601729] using wordTrace_append hprefix tailTrace_601729
  have hstable : (prefixWord ++ tailWord_601729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601729).length < 2 ^ (prefixWord ++ tailWord_601729).sum := by decide
  have hdescent : baseEnd_601729 < baseStart_601729 := by decide
  rcases family_descends (prefixWord ++ tailWord_601729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601808 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 2, 8]
def baseStart_601808 : Nat := 118140960795 + 601808 * 2 ^ 59
def prefixEnd_601808 : Nat := 4983230072969 + 3 ^ 40 * 601808 * 2
def baseEnd_601808 : Nat := 103005588573695552377447

theorem tailTrace_601808 : CollatzResearch.WordTrace tailWord_601808 prefixEnd_601808 103005588573695552377447 := by
  unfold tailWord_601808
  simp only [CollatzResearch.WordTrace]
  refine ⟨10974870501879935734363039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14633160669173247645817385 10974870501879935734363039)
  ·
    refine ⟨16462305752819903601544559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10974870501879935734363039 16462305752819903601544559)
    ·
      refine ⟨24693458629229855402316839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16462305752819903601544559 24693458629229855402316839)
      ·
        refine ⟨37040187943844783103475259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24693458629229855402316839 37040187943844783103475259)
        ·
          refine ⟨55560281915767174655212889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37040187943844783103475259 55560281915767174655212889)
          ·
            refine ⟨41670211436825380991409667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55560281915767174655212889 41670211436825380991409667)
            ·
              refine ⟨62505317155238071487114501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41670211436825380991409667 62505317155238071487114501)
              ·
                refine ⟨11719746966607138403833969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62505317155238071487114501 11719746966607138403833969)
                ·
                  refine ⟨8789810224955353802875477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11719746966607138403833969 8789810224955353802875477)
                  ·
                    refine ⟨103005588573695552377447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 8789810224955353802875477 103005588573695552377447)
                    ·
                      rfl

theorem cell23_601808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 2, 8].length) (baseStart_601808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601808 prefixEnd_601808 := by exact prefixLift 601808
  have htrace : WordTrace (prefixWord ++ tailWord_601808) baseStart_601808 baseEnd_601808 := by
    simpa [prefixWord, tailWord_601808, baseEnd_601808] using wordTrace_append hprefix tailTrace_601808
  have hstable : (prefixWord ++ tailWord_601808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601808).length < 2 ^ (prefixWord ++ tailWord_601808).sum := by decide
  have hdescent : baseEnd_601808 < baseStart_601808 := by decide
  rcases family_descends (prefixWord ++ tailWord_601808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601815 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 4]
def baseStart_601815 : Nat := 118140960795 + 601815 * 2 ^ 59
def prefixEnd_601815 : Nat := 4983230072969 + 3 ^ 40 * 601815 * 2
def baseEnd_601815 : Nat := 309020360085668129744809

theorem tailTrace_601815 : CollatzResearch.WordTrace tailWord_601815 prefixEnd_601815 309020360085668129744809 := by
  unfold tailWord_601815
  simp only [CollatzResearch.WordTrace]
  refine ⟨21949996314734511664230899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14633330876489674442820599 21949996314734511664230899)
  ·
    refine ⟨32924994472101767496346349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21949996314734511664230899 32924994472101767496346349)
    ·
      refine ⟨12346872927038162811129881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32924994472101767496346349 12346872927038162811129881)
      ·
        refine ⟨9260154695278622108347411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12346872927038162811129881 9260154695278622108347411)
        ·
          refine ⟨13890232042917933162521117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9260154695278622108347411 13890232042917933162521117)
          ·
            refine ⟨5208837016094224935945419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13890232042917933162521117 5208837016094224935945419)
            ·
              refine ⟨7813255524141337403918129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5208837016094224935945419 7813255524141337403918129)
              ·
                refine ⟨5859941643106003052938597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7813255524141337403918129 5859941643106003052938597)
                ·
                  refine ⟨1098739058082375572425987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5859941643106003052938597 1098739058082375572425987)
                  ·
                    refine ⟨1648108587123563358638981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1098739058082375572425987 1648108587123563358638981)
                    ·
                      refine ⟨309020360085668129744809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1648108587123563358638981 309020360085668129744809)
                      ·
                        rfl

theorem cell23_601815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_601815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601815 prefixEnd_601815 := by exact prefixLift 601815
  have htrace : WordTrace (prefixWord ++ tailWord_601815) baseStart_601815 baseEnd_601815 := by
    simpa [prefixWord, tailWord_601815, baseEnd_601815] using wordTrace_append hprefix tailTrace_601815
  have hstable : (prefixWord ++ tailWord_601815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601815).length < 2 ^ (prefixWord ++ tailWord_601815).sum := by decide
  have hdescent : baseEnd_601815 < baseStart_601815 := by decide
  rcases family_descends (prefixWord ++ tailWord_601815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601832 : List Nat := [2, 1, 4, 1, 3, 1, 1, 3, 2, 1, 4]
def baseStart_601832 : Nat := 118140960795 + 601832 * 2 ^ 59
def prefixEnd_601832 : Nat := 4983230072969 + 3 ^ 40 * 601832 * 2
def baseEnd_601832 : Nat := 309029089256794563232231

theorem tailTrace_601832 : CollatzResearch.WordTrace tailWord_601832 prefixEnd_601832 309029089256794563232231 := by
  unfold tailWord_601832
  simp only [CollatzResearch.WordTrace]
  refine ⟨10975308177836461783799875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14633744237115282378399833 10975308177836461783799875)
  ·
    refine ⟨16462962266754692675699813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10975308177836461783799875 16462962266754692675699813)
    ·
      refine ⟨3086805425016504876693715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16462962266754692675699813 3086805425016504876693715)
      ·
        refine ⟨4630208137524757315040573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3086805425016504876693715 4630208137524757315040573)
        ·
          refine ⟨1736328051571783993140215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4630208137524757315040573 1736328051571783993140215)
          ·
            refine ⟨2604492077357675989710323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1736328051571783993140215 2604492077357675989710323)
            ·
              refine ⟨3906738116036513984565485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2604492077357675989710323 3906738116036513984565485)
              ·
                refine ⟨1465026793513692744212057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3906738116036513984565485 1465026793513692744212057)
                ·
                  refine ⟨1098770095135269558159043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1465026793513692744212057 1098770095135269558159043)
                  ·
                    refine ⟨1648155142702904337238565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1098770095135269558159043 1648155142702904337238565)
                    ·
                      refine ⟨309029089256794563232231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1648155142702904337238565 309029089256794563232231)
                      ·
                        rfl

theorem cell23_601832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_601832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601832 prefixEnd_601832 := by exact prefixLift 601832
  have htrace : WordTrace (prefixWord ++ tailWord_601832) baseStart_601832 baseEnd_601832 := by
    simpa [prefixWord, tailWord_601832, baseEnd_601832] using wordTrace_append hprefix tailTrace_601832
  have hstable : (prefixWord ++ tailWord_601832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601832).length < 2 ^ (prefixWord ++ tailWord_601832).sum := by decide
  have hdescent : baseEnd_601832 < baseStart_601832 := by decide
  rcases family_descends (prefixWord ++ tailWord_601832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601835 : List Nat := [1, 1, 1, 1, 2, 4, 2, 3, 1, 4, 3]
def baseStart_601835 : Nat := 118140960795 + 601835 * 2 ^ 59
def prefixEnd_601835 : Nat := 4983230072969 + 3 ^ 40 * 601835 * 2
def baseEnd_601835 : Nat := 309030629698758051494717

theorem tailTrace_601835 : CollatzResearch.WordTrace tailWord_601835 prefixEnd_601835 309030629698758051494717 := by
  unfold tailWord_601835
  simp only [CollatzResearch.WordTrace]
  refine ⟨21950725774662055079958959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14633817183108036719972639 21950725774662055079958959)
  ·
    refine ⟨32926088661993082619938439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21950725774662055079958959 32926088661993082619938439)
    ·
      refine ⟨49389132992989623929907659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32926088661993082619938439 49389132992989623929907659)
      ·
        refine ⟨74083699489484435894861489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49389132992989623929907659 74083699489484435894861489)
        ·
          refine ⟨55562774617113326921146117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74083699489484435894861489 55562774617113326921146117)
          ·
            refine ⟨10418020240708748797714897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55562774617113326921146117 10418020240708748797714897)
            ·
              refine ⟨7813515180531561598286173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10418020240708748797714897 7813515180531561598286173)
              ·
                refine ⟨2930068192699335599357315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7813515180531561598286173 2930068192699335599357315)
                ·
                  refine ⟨4395102289049003399035973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2930068192699335599357315 4395102289049003399035973)
                  ·
                    refine ⟨824081679196688137319245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4395102289049003399035973 824081679196688137319245)
                    ·
                      refine ⟨309030629698758051494717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 824081679196688137319245 309030629698758051494717)
                      ·
                        rfl

theorem cell23_601835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 4, 3].length) (baseStart_601835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601835 prefixEnd_601835 := by exact prefixLift 601835
  have htrace : WordTrace (prefixWord ++ tailWord_601835) baseStart_601835 baseEnd_601835 := by
    simpa [prefixWord, tailWord_601835, baseEnd_601835] using wordTrace_append hprefix tailTrace_601835
  have hstable : (prefixWord ++ tailWord_601835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601835).length < 2 ^ (prefixWord ++ tailWord_601835).sum := by decide
  have hdescent : baseEnd_601835 < baseStart_601835 := by decide
  rcases family_descends (prefixWord ++ tailWord_601835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601852 : List Nat := [2, 2, 2, 1, 3, 1, 1, 4, 2, 2, 3]
def baseStart_601852 : Nat := 118140960795 + 601852 * 2 ^ 59
def prefixEnd_601852 : Nat := 4983230072969 + 3 ^ 40 * 601852 * 2
def baseEnd_601852 : Nat := 309039358869884484982139

theorem tailTrace_601852 : CollatzResearch.WordTrace tailWord_601852 prefixEnd_601852 309039358869884484982139 := by
  unfold tailWord_601852
  simp only [CollatzResearch.WordTrace]
  refine ⟨10975672907800233491663905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14634230543733644655551873 10975672907800233491663905)
  ·
    refine ⟨8231754680850175118747929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10975672907800233491663905 8231754680850175118747929)
    ·
      refine ⟨6173816010637631339060947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8231754680850175118747929 6173816010637631339060947)
      ·
        refine ⟨9260724015956447008591421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6173816010637631339060947 9260724015956447008591421)
        ·
          refine ⟨3472771505983667628221783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9260724015956447008591421 3472771505983667628221783)
          ·
            refine ⟨5209157258975501442332675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3472771505983667628221783 5209157258975501442332675)
            ·
              refine ⟨7813735888463252163499013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5209157258975501442332675 7813735888463252163499013)
              ·
                refine ⟨1465075479086859780656065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7813735888463252163499013 1465075479086859780656065)
                ·
                  refine ⟨1098806609315144835492049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1465075479086859780656065 1098806609315144835492049)
                  ·
                    refine ⟨824104956986358626619037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1098806609315144835492049 824104956986358626619037)
                    ·
                      refine ⟨309039358869884484982139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 824104956986358626619037 309039358869884484982139)
                      ·
                        rfl

theorem cell23_601852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_601852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601852 prefixEnd_601852 := by exact prefixLift 601852
  have htrace : WordTrace (prefixWord ++ tailWord_601852) baseStart_601852 baseEnd_601852 := by
    simpa [prefixWord, tailWord_601852, baseEnd_601852] using wordTrace_append hprefix tailTrace_601852
  have hstable : (prefixWord ++ tailWord_601852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601852).length < 2 ^ (prefixWord ++ tailWord_601852).sum := by decide
  have hdescent : baseEnd_601852 < baseStart_601852 := by decide
  rcases family_descends (prefixWord ++ tailWord_601852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601855 : List Nat := [1, 1, 2, 2, 1, 3, 3, 4, 6]
def baseStart_601855 : Nat := 118140960795 + 601855 * 2 ^ 59
def prefixEnd_601855 : Nat := 4983230072969 + 3 ^ 40 * 601855 * 2
def baseEnd_601855 : Nat := 34337877701316441471625

theorem tailTrace_601855 : CollatzResearch.WordTrace tailWord_601855 prefixEnd_601855 34337877701316441471625 := by
  unfold tailWord_601855
  simp only [CollatzResearch.WordTrace]
  refine ⟨21951455234589598495687019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14634303489726398997124679 21951455234589598495687019)
  ·
    refine ⟨32927182851884397743530529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21951455234589598495687019 32927182851884397743530529)
    ·
      refine ⟨24695387138913298307647897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32927182851884397743530529 24695387138913298307647897)
      ·
        refine ⟨18521540354184973730735923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24695387138913298307647897 18521540354184973730735923)
        ·
          refine ⟨27782310531277460596103885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18521540354184973730735923 27782310531277460596103885)
          ·
            refine ⟨10418366449229047723538957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27782310531277460596103885 10418366449229047723538957)
            ·
              refine ⟨3906887418460892896327109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10418366449229047723538957 3906887418460892896327109)
              ·
                refine ⟨732541390961417418061333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3906887418460892896327109 732541390961417418061333)
                ·
                  refine ⟨34337877701316441471625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 732541390961417418061333 34337877701316441471625)
                  ·
                    rfl

theorem cell23_601855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 6].length) (baseStart_601855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601855 prefixEnd_601855 := by exact prefixLift 601855
  have htrace : WordTrace (prefixWord ++ tailWord_601855) baseStart_601855 baseEnd_601855 := by
    simpa [prefixWord, tailWord_601855, baseEnd_601855] using wordTrace_append hprefix tailTrace_601855
  have hstable : (prefixWord ++ tailWord_601855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601855).length < 2 ^ (prefixWord ++ tailWord_601855).sum := by decide
  have hdescent : baseEnd_601855 < baseStart_601855 := by decide
  rcases family_descends (prefixWord ++ tailWord_601855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601865 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 2, 5, 3]
def baseStart_601865 : Nat := 118140960795 + 601865 * 2 ^ 59
def prefixEnd_601865 : Nat := 4983230072969 + 3 ^ 40 * 601865 * 2
def baseEnd_601865 : Nat := 309046034118392934119579

theorem tailTrace_601865 : CollatzResearch.WordTrace tailWord_601865 prefixEnd_601865 309046034118392934119579 := by
  unfold tailWord_601865
  simp only [CollatzResearch.WordTrace]
  refine ⟨21951819964553370203551049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14634546643035580135700699 21951819964553370203551049)
  ·
    refine ⟨16463864973415027652663287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21951819964553370203551049 16463864973415027652663287)
    ·
      refine ⟨24695797460122541478994931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16463864973415027652663287 24695797460122541478994931)
      ·
        refine ⟨37043696190183812218492397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24695797460122541478994931 37043696190183812218492397)
        ·
          refine ⟨13891386071318929581934649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37043696190183812218492397 13891386071318929581934649)
          ·
            refine ⟨10418539553489197186450987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13891386071318929581934649 10418539553489197186450987)
            ·
              refine ⟨15627809330233795779676481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10418539553489197186450987 15627809330233795779676481)
              ·
                refine ⟨11720856997675346834757361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15627809330233795779676481 11720856997675346834757361)
                ·
                  refine ⟨8790642748256510126068021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11720856997675346834757361 8790642748256510126068021)
                  ·
                    refine ⟨824122757649047824318877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8790642748256510126068021 824122757649047824318877)
                    ·
                      refine ⟨309046034118392934119579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 824122757649047824318877 309046034118392934119579)
                      ·
                        rfl

theorem cell23_601865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 5, 3].length) (baseStart_601865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601865 prefixEnd_601865 := by exact prefixLift 601865
  have htrace : WordTrace (prefixWord ++ tailWord_601865) baseStart_601865 baseEnd_601865 := by
    simpa [prefixWord, tailWord_601865, baseEnd_601865] using wordTrace_append hprefix tailTrace_601865
  have hstable : (prefixWord ++ tailWord_601865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601865).length < 2 ^ (prefixWord ++ tailWord_601865).sum := by decide
  have hdescent : baseEnd_601865 < baseStart_601865 := by decide
  rcases family_descends (prefixWord ++ tailWord_601865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601916 : List Nat := [2, 2, 2, 2, 1, 1, 4, 4, 1, 1, 3]
def baseStart_601916 : Nat := 118140960795 + 601916 * 2 ^ 59
def prefixEnd_601916 : Nat := 4983230072969 + 3 ^ 40 * 601916 * 2
def baseEnd_601916 : Nat := 309072221631772234581845

theorem tailTrace_601916 : CollatzResearch.WordTrace tailWord_601916 prefixEnd_601916 309072221631772234581845 := by
  unfold tailWord_601916
  simp only [CollatzResearch.WordTrace]
  refine ⟨10976840043684302956828801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14635786724912403942438401 10976840043684302956828801)
  ·
    refine ⟨8232630032763227217621601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10976840043684302956828801 8232630032763227217621601)
    ·
      refine ⟨6174472524572420413216201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8232630032763227217621601 6174472524572420413216201)
      ·
        refine ⟨4630854393429315309912151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6174472524572420413216201 4630854393429315309912151)
        ·
          refine ⟨6946281590143972964868227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4630854393429315309912151 6946281590143972964868227)
          ·
            refine ⟨10419422385215959447302341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6946281590143972964868227 10419422385215959447302341)
            ·
              refine ⟨1953641697227992396369189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10419422385215959447302341 1953641697227992396369189)
              ·
                refine ⟨366307818230248574319223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1953641697227992396369189 366307818230248574319223)
                ·
                  refine ⟨549461727345372861478835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 366307818230248574319223 549461727345372861478835)
                  ·
                    refine ⟨824192591018059292218253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 549461727345372861478835 824192591018059292218253)
                    ·
                      refine ⟨309072221631772234581845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 824192591018059292218253 309072221631772234581845)
                      ·
                        rfl

theorem cell23_601916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_601916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601916 prefixEnd_601916 := by exact prefixLift 601916
  have htrace : WordTrace (prefixWord ++ tailWord_601916) baseStart_601916 baseEnd_601916 := by
    simpa [prefixWord, tailWord_601916, baseEnd_601916] using wordTrace_append hprefix tailTrace_601916
  have hstable : (prefixWord ++ tailWord_601916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601916).length < 2 ^ (prefixWord ++ tailWord_601916).sum := by decide
  have hdescent : baseEnd_601916 < baseStart_601916 := by decide
  rcases family_descends (prefixWord ++ tailWord_601916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601945 : List Nat := [1, 2, 1, 2, 2, 3, 3, 9]
def baseStart_601945 : Nat := 118140960795 + 601945 * 2 ^ 59
def prefixEnd_601945 : Nat := 4983230072969 + 3 ^ 40 * 601945 * 2
def baseEnd_601945 : Nat := 11447670835953800782193

theorem tailTrace_601945 : CollatzResearch.WordTrace tailWord_601945 prefixEnd_601945 11447670835953800782193 := by
  unfold tailWord_601945
  simp only [CollatzResearch.WordTrace]
  refine ⟨21954737804263543866463289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14636491869509029244308859 21954737804263543866463289)
  ·
    refine ⟨16466053353197657899847467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21954737804263543866463289 16466053353197657899847467)
    ·
      refine ⟨24699080029796486849771201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16466053353197657899847467 24699080029796486849771201)
      ·
        refine ⟨18524310022347365137328401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24699080029796486849771201 18524310022347365137328401)
        ·
          refine ⟨13893232516760523852996301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18524310022347365137328401 13893232516760523852996301)
          ·
            refine ⟨5209962193785196444873613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13893232516760523852996301 5209962193785196444873613)
            ·
              refine ⟨1953735822669448666827605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5209962193785196444873613 1953735822669448666827605)
              ·
                refine ⟨11447670835953800782193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1953735822669448666827605 11447670835953800782193)
                ·
                  rfl

theorem cell23_601945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 9].length) (baseStart_601945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601945 prefixEnd_601945 := by exact prefixLift 601945
  have htrace : WordTrace (prefixWord ++ tailWord_601945) baseStart_601945 baseEnd_601945 := by
    simpa [prefixWord, tailWord_601945, baseEnd_601945] using wordTrace_append hprefix tailTrace_601945
  have hstable : (prefixWord ++ tailWord_601945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601945).length < 2 ^ (prefixWord ++ tailWord_601945).sum := by decide
  have hdescent : baseEnd_601945 < baseStart_601945 := by decide
  rcases family_descends (prefixWord ++ tailWord_601945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601959 : List Nat := [1, 1, 5, 1, 2, 1, 1, 5, 1, 2, 3]
def baseStart_601959 : Nat := 118140960795 + 601959 * 2 ^ 59
def prefixEnd_601959 : Nat := 4983230072969 + 3 ^ 40 * 601959 * 2
def baseEnd_601959 : Nat := 309094301299915566344147

theorem tailTrace_601959 : CollatzResearch.WordTrace tailWord_601959 prefixEnd_601959 309094301299915566344147 := by
  unfold tailWord_601959
  simp only [CollatzResearch.WordTrace]
  refine ⟨21955248426212824257472931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14636832284141882838315287 21955248426212824257472931)
  ·
    refine ⟨32932872639319236386209397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21955248426212824257472931 32932872639319236386209397)
    ·
      refine ⟨3087456809936178411207131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32932872639319236386209397 3087456809936178411207131)
      ·
        refine ⟨4631185214904267616810697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3087456809936178411207131 4631185214904267616810697)
        ·
          refine ⟨3473388911178200712608023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4631185214904267616810697 3473388911178200712608023)
          ·
            refine ⟨5210083366767301068912035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3473388911178200712608023 5210083366767301068912035)
            ·
              refine ⟨7815125050150951603368053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5210083366767301068912035 7815125050150951603368053)
              ·
                refine ⟨732667973451651712815755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7815125050150951603368053 732667973451651712815755)
                ·
                  refine ⟨1099001960177477569223633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 732667973451651712815755 1099001960177477569223633)
                  ·
                    refine ⟨824251470133108176917725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1099001960177477569223633 824251470133108176917725)
                    ·
                      refine ⟨309094301299915566344147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 824251470133108176917725 309094301299915566344147)
                      ·
                        rfl

theorem cell23_601959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_601959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601959 prefixEnd_601959 := by exact prefixLift 601959
  have htrace : WordTrace (prefixWord ++ tailWord_601959) baseStart_601959 baseEnd_601959 := by
    simpa [prefixWord, tailWord_601959, baseEnd_601959] using wordTrace_append hprefix tailTrace_601959
  have hstable : (prefixWord ++ tailWord_601959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601959).length < 2 ^ (prefixWord ++ tailWord_601959).sum := by decide
  have hdescent : baseEnd_601959 < baseStart_601959 := by decide
  rcases family_descends (prefixWord ++ tailWord_601959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_601995 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 8]
def baseStart_601995 : Nat := 118140960795 + 601995 * 2 ^ 59
def prefixEnd_601995 : Nat := 4983230072969 + 3 ^ 40 * 601995 * 2
def baseEnd_601995 : Nat := 309112786603477425493981

theorem tailTrace_601995 : CollatzResearch.WordTrace tailWord_601995 prefixEnd_601995 309112786603477425493981 := by
  unfold tailWord_601995
  simp only [CollatzResearch.WordTrace]
  refine ⟨21956561454082402405783439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14637707636054934937188959 21956561454082402405783439)
  ·
    refine ⟨32934842181123603608675159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21956561454082402405783439 32934842181123603608675159)
    ·
      refine ⟨49402263271685405413012739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32934842181123603608675159 49402263271685405413012739)
      ·
        refine ⟨74103394907528108119519109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49402263271685405413012739 74103394907528108119519109)
        ·
          refine ⟨13894386545161520272409833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74103394907528108119519109 13894386545161520272409833)
          ·
            refine ⟨10420789908871140204307375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13894386545161520272409833 10420789908871140204307375)
            ·
              refine ⟨15631184863306710306461063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10420789908871140204307375 15631184863306710306461063)
              ·
                refine ⟨23446777294960065459691595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15631184863306710306461063 23446777294960065459691595)
                ·
                  refine ⟨35170165942440098189537393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23446777294960065459691595 35170165942440098189537393)
                  ·
                    refine ⟨26377624456830073642153045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35170165942440098189537393 26377624456830073642153045)
                    ·
                      refine ⟨309112786603477425493981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 26377624456830073642153045 309112786603477425493981)
                      ·
                        rfl

theorem cell23_601995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 8].length) (baseStart_601995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_601995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_601995 prefixEnd_601995 := by exact prefixLift 601995
  have htrace : WordTrace (prefixWord ++ tailWord_601995) baseStart_601995 baseEnd_601995 := by
    simpa [prefixWord, tailWord_601995, baseEnd_601995] using wordTrace_append hprefix tailTrace_601995
  have hstable : (prefixWord ++ tailWord_601995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_601995).length < 2 ^ (prefixWord ++ tailWord_601995).sum := by decide
  have hdescent : baseEnd_601995 < baseStart_601995 := by decide
  rcases family_descends (prefixWord ++ tailWord_601995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602023 : List Nat := [1, 1, 6, 1, 2, 2, 2, 2, 2, 1, 3]
def baseStart_602023 : Nat := 118140960795 + 602023 * 2 ^ 59
def prefixEnd_602023 : Nat := 4983230072969 + 3 ^ 40 * 602023 * 2
def baseEnd_602023 : Nat := 309127164061803315943853

theorem tailTrace_602023 : CollatzResearch.WordTrace tailWord_602023 prefixEnd_602023 309127164061803315943853 := by
  unfold tailWord_602023
  simp only [CollatzResearch.WordTrace]
  refine ⟨21957582697980963187802723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14638388465320642125201815 21957582697980963187802723)
  ·
    refine ⟨32936374046971444781704085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21957582697980963187802723 32936374046971444781704085)
    ·
      refine ⟨1543892533451786474142379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32936374046971444781704085 1543892533451786474142379)
      ·
        refine ⟨2315838800177679711213569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1543892533451786474142379 2315838800177679711213569)
        ·
          refine ⟨1736879100133259783410177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2315838800177679711213569 1736879100133259783410177)
          ·
            refine ⟨1302659325099944837557633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1736879100133259783410177 1302659325099944837557633)
            ·
              refine ⟨976994493824958628168225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1302659325099944837557633 976994493824958628168225)
              ·
                refine ⟨732745870368718971126169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 976994493824958628168225 732745870368718971126169)
                ·
                  refine ⟨549559402776539228344627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 732745870368718971126169 549559402776539228344627)
                  ·
                    refine ⟨824339104164808842516941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 549559402776539228344627 824339104164808842516941)
                    ·
                      refine ⟨309127164061803315943853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 824339104164808842516941 309127164061803315943853)
                      ·
                        rfl

theorem cell23_602023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_602023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602023 prefixEnd_602023 := by exact prefixLift 602023
  have htrace : WordTrace (prefixWord ++ tailWord_602023) baseStart_602023 baseEnd_602023 := by
    simpa [prefixWord, tailWord_602023, baseEnd_602023] using wordTrace_append hprefix tailTrace_602023
  have hstable : (prefixWord ++ tailWord_602023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602023).length < 2 ^ (prefixWord ++ tailWord_602023).sum := by decide
  have hdescent : baseEnd_602023 < baseStart_602023 := by decide
  rcases family_descends (prefixWord ++ tailWord_602023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602030 : List Nat := [4, 1, 5, 1, 2, 1, 1, 8]
def baseStart_602030 : Nat := 118140960795 + 602030 * 2 ^ 59
def prefixEnd_602030 : Nat := 4983230072969 + 3 ^ 40 * 602030 * 2
def baseEnd_602030 : Nat := 11449287349125362539123

theorem tailTrace_602030 : CollatzResearch.WordTrace tailWord_602030 prefixEnd_602030 11449287349125362539123 := by
  unfold tailWord_602030
  simp only [CollatzResearch.WordTrace]
  refine ⟨2744729751119450422913443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14638558672637068922205029 2744729751119450422913443)
  ·
    refine ⟨4117094626679175634370165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2744729751119450422913443 4117094626679175634370165)
    ·
      refine ⟨385977621251172715722203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4117094626679175634370165 385977621251172715722203)
      ·
        refine ⟨578966431876759073583305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385977621251172715722203 578966431876759073583305)
        ·
          refine ⟨434224823907569305187479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 578966431876759073583305 434224823907569305187479)
          ·
            refine ⟨651337235861353957781219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434224823907569305187479 651337235861353957781219)
            ·
              refine ⟨977005853792030936671829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 651337235861353957781219 977005853792030936671829)
              ·
                refine ⟨11449287349125362539123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 977005853792030936671829 11449287349125362539123)
                ·
                  rfl

theorem cell23_602030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 8].length) (baseStart_602030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602030 prefixEnd_602030 := by exact prefixLift 602030
  have htrace : WordTrace (prefixWord ++ tailWord_602030) baseStart_602030 baseEnd_602030 := by
    simpa [prefixWord, tailWord_602030, baseEnd_602030] using wordTrace_append hprefix tailTrace_602030
  have hstable : (prefixWord ++ tailWord_602030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602030).length < 2 ^ (prefixWord ++ tailWord_602030).sum := by decide
  have hdescent : baseEnd_602030 < baseStart_602030 := by decide
  rcases family_descends (prefixWord ++ tailWord_602030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602046 : List Nat := [4, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2]
def baseStart_602046 : Nat := 118140960795 + 602046 * 2 ^ 59
def prefixEnd_602046 : Nat := 4983230072969 + 3 ^ 40 * 602046 * 2
def baseEnd_602046 : Nat := 309138974116856725956247

theorem tailTrace_602046 : CollatzResearch.WordTrace tailWord_602046 prefixEnd_602046 309138974116856725956247 := by
  unfold tailWord_602046
  simp only [CollatzResearch.WordTrace]
  refine ⟨2744802697112204764486249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14638947717931758743926661 2744802697112204764486249)
  ·
    refine ⟨2058602022834153573364687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2744802697112204764486249 2058602022834153573364687)
    ·
      refine ⟨3087903034251230360047031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2058602022834153573364687 3087903034251230360047031)
      ·
        refine ⟨4631854551376845540070547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3087903034251230360047031 4631854551376845540070547)
        ·
          refine ⟨6947781827065268310105821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4631854551376845540070547 6947781827065268310105821)
          ·
            refine ⟨2605418185149475616289683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6947781827065268310105821 2605418185149475616289683)
            ·
              refine ⟨3908127277724213424434525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2605418185149475616289683 3908127277724213424434525)
              ·
                refine ⟨1465547729146580034162947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3908127277724213424434525 1465547729146580034162947)
                ·
                  refine ⟨2198321593719870051244421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1465547729146580034162947 2198321593719870051244421)
                  ·
                    refine ⟨412185298822475634608329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2198321593719870051244421 412185298822475634608329)
                    ·
                      refine ⟨309138974116856725956247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 412185298822475634608329 309138974116856725956247)
                      ·
                        rfl

theorem cell23_602046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_602046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602046 prefixEnd_602046 := by exact prefixLift 602046
  have htrace : WordTrace (prefixWord ++ tailWord_602046) baseStart_602046 baseEnd_602046 := by
    simpa [prefixWord, tailWord_602046, baseEnd_602046] using wordTrace_append hprefix tailTrace_602046
  have hstable : (prefixWord ++ tailWord_602046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602046).length < 2 ^ (prefixWord ++ tailWord_602046).sum := by decide
  have hdescent : baseEnd_602046 < baseStart_602046 := by decide
  rcases family_descends (prefixWord ++ tailWord_602046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602079 : List Nat := [1, 1, 2, 3, 4, 1, 1, 2, 2, 3, 3]
def baseStart_602079 : Nat := 118140960795 + 602079 * 2 ^ 59
def prefixEnd_602079 : Nat := 4983230072969 + 3 ^ 40 * 602079 * 2
def baseEnd_602079 : Nat := 309155918978455096843595

theorem tailTrace_602079 : CollatzResearch.WordTrace tailWord_602079 prefixEnd_602079 309155918978455096843595 := by
  unfold tailWord_602079
  simp only [CollatzResearch.WordTrace]
  refine ⟨21959625185778084751841291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14639750123852056501227527 21959625185778084751841291)
  ·
    refine ⟨32939437778667127127761937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21959625185778084751841291 32939437778667127127761937)
    ·
      refine ⟨24704578334000345345821453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32939437778667127127761937 24704578334000345345821453)
      ·
        refine ⟨9264216875250129504683045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24704578334000345345821453 9264216875250129504683045)
        ·
          refine ⟨1737040664109399282128071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9264216875250129504683045 1737040664109399282128071)
          ·
            refine ⟨2605560996164098923192107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1737040664109399282128071 2605560996164098923192107)
            ·
              refine ⟨3908341494246148384788161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2605560996164098923192107 3908341494246148384788161)
              ·
                refine ⟨2931256120684611288591121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3908341494246148384788161 2931256120684611288591121)
                ·
                  refine ⟨2198442090513458466443341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2931256120684611288591121 2198442090513458466443341)
                  ·
                    refine ⟨824415783942546924916253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2198442090513458466443341 824415783942546924916253)
                    ·
                      refine ⟨309155918978455096843595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 824415783942546924916253 309155918978455096843595)
                      ·
                        rfl

theorem cell23_602079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_602079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602079 prefixEnd_602079 := by exact prefixLift 602079
  have htrace : WordTrace (prefixWord ++ tailWord_602079) baseStart_602079 baseEnd_602079 := by
    simpa [prefixWord, tailWord_602079, baseEnd_602079] using wordTrace_append hprefix tailTrace_602079
  have hstable : (prefixWord ++ tailWord_602079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602079).length < 2 ^ (prefixWord ++ tailWord_602079).sum := by decide
  have hdescent : baseEnd_602079 < baseStart_602079 := by decide
  rcases family_descends (prefixWord ++ tailWord_602079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602092 : List Nat := [2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 5]
def baseStart_602092 : Nat := 118140960795 + 602092 * 2 ^ 59
def prefixEnd_602092 : Nat := 4983230072969 + 3 ^ 40 * 602092 * 2
def baseEnd_602092 : Nat := 309162594226963545981035

theorem tailTrace_602092 : CollatzResearch.WordTrace tailWord_602092 prefixEnd_602092 309162594226963545981035 := by
  unfold tailWord_602092
  simp only [CollatzResearch.WordTrace]
  refine ⟨10980049667365493986032265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14640066223153991981376353 10980049667365493986032265)
  ·
    refine ⟨8235037250524120489524199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10980049667365493986032265 8235037250524120489524199)
    ·
      refine ⟨12352555875786180734286299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8235037250524120489524199 12352555875786180734286299)
      ·
        refine ⟨18528833813679271101429449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12352555875786180734286299 18528833813679271101429449)
        ·
          refine ⟨13896625360259453326072087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18528833813679271101429449 13896625360259453326072087)
          ·
            refine ⟨20844938040389179989108131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13896625360259453326072087 20844938040389179989108131)
            ·
              refine ⟨31267407060583769983662197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20844938040389179989108131 31267407060583769983662197)
              ·
                refine ⟨2931319411929728435968331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31267407060583769983662197 2931319411929728435968331)
                ·
                  refine ⟨4396979117894592653952497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2931319411929728435968331 4396979117894592653952497)
                  ·
                    refine ⟨3297734338420944490464373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4396979117894592653952497 3297734338420944490464373)
                    ·
                      refine ⟨309162594226963545981035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3297734338420944490464373 309162594226963545981035)
                      ·
                        rfl

theorem cell23_602092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_602092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602092 prefixEnd_602092 := by exact prefixLift 602092
  have htrace : WordTrace (prefixWord ++ tailWord_602092) baseStart_602092 baseEnd_602092 := by
    simpa [prefixWord, tailWord_602092, baseEnd_602092] using wordTrace_append hprefix tailTrace_602092
  have hstable : (prefixWord ++ tailWord_602092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602092).length < 2 ^ (prefixWord ++ tailWord_602092).sum := by decide
  have hdescent : baseEnd_602092 < baseStart_602092 := by decide
  rcases family_descends (prefixWord ++ tailWord_602092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602119 : List Nat := [1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 4]
def baseStart_602119 : Nat := 118140960795 + 602119 * 2 ^ 59
def prefixEnd_602119 : Nat := 4983230072969 + 3 ^ 40 * 602119 * 2
def baseEnd_602119 : Nat := 309176458204634940343411

theorem tailTrace_602119 : CollatzResearch.WordTrace tailWord_602119 prefixEnd_602119 309176458204634940343411 := by
  unfold tailWord_602119
  simp only [CollatzResearch.WordTrace]
  refine ⟨21961084105633171583297411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14640722737088781055531607 21961084105633171583297411)
  ·
    refine ⟨32941626158449757374946117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21961084105633171583297411 32941626158449757374946117)
    ·
      refine ⟨6176554904709329507802397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32941626158449757374946117 6176554904709329507802397)
      ·
        refine ⟨2316208089265998565425899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6176554904709329507802397 2316208089265998565425899)
        ·
          refine ⟨3474312133898997848138849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2316208089265998565425899 3474312133898997848138849)
          ·
            refine ⟨2605734100424248386104137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3474312133898997848138849 2605734100424248386104137)
            ·
              refine ⟨1954300575318186289578103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2605734100424248386104137 1954300575318186289578103)
              ·
                refine ⟨2931450862977279434367155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1954300575318186289578103 2931450862977279434367155)
                ·
                  refine ⟨4397176294465919151550733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2931450862977279434367155 4397176294465919151550733)
                  ·
                    refine ⟨1648941110424719681831525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4397176294465919151550733 1648941110424719681831525)
                    ·
                      refine ⟨309176458204634940343411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1648941110424719681831525 309176458204634940343411)
                      ·
                        rfl

theorem cell23_602119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_602119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602119 prefixEnd_602119 := by exact prefixLift 602119
  have htrace : WordTrace (prefixWord ++ tailWord_602119) baseStart_602119 baseEnd_602119 := by
    simpa [prefixWord, tailWord_602119, baseEnd_602119] using wordTrace_append hprefix tailTrace_602119
  have hstable : (prefixWord ++ tailWord_602119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602119).length < 2 ^ (prefixWord ++ tailWord_602119).sum := by decide
  have hdescent : baseEnd_602119 < baseStart_602119 := by decide
  rcases family_descends (prefixWord ++ tailWord_602119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602196 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 3, 5, 2]
def baseStart_602196 : Nat := 118140960795 + 602196 * 2 ^ 59
def prefixEnd_602196 : Nat := 4983230072969 + 3 ^ 40 * 602196 * 2
def baseEnd_602196 : Nat := 309215996215031139080557

theorem tailTrace_602196 : CollatzResearch.WordTrace tailWord_602196 prefixEnd_602196 309215996215031139080557 := by
  unfold tailWord_602196
  simp only [CollatzResearch.WordTrace]
  refine ⟨10981946263177106866925221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14642595017569475822566961 10981946263177106866925221)
  ·
    refine ⟨2059114924345707537548479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10981946263177106866925221 2059114924345707537548479)
    ·
      refine ⟨3088672386518561306322719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2059114924345707537548479 3088672386518561306322719)
      ·
        refine ⟨4633008579777841959484079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3088672386518561306322719 4633008579777841959484079)
        ·
          refine ⟨6949512869666762939226119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4633008579777841959484079 6949512869666762939226119)
          ·
            refine ⟨10424269304500144408839179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6949512869666762939226119 10424269304500144408839179)
            ·
              refine ⟨15636403956750216613258769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10424269304500144408839179 15636403956750216613258769)
              ·
                refine ⟨11727302967562662459944077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15636403956750216613258769 11727302967562662459944077)
                ·
                  refine ⟨4397738612835998422479029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11727302967562662459944077 4397738612835998422479029)
                  ·
                    refine ⟨412287994953374852107409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4397738612835998422479029 412287994953374852107409)
                    ·
                      refine ⟨309215996215031139080557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 412287994953374852107409 309215996215031139080557)
                      ·
                        rfl

theorem cell23_602196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_602196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602196 prefixEnd_602196 := by exact prefixLift 602196
  have htrace : WordTrace (prefixWord ++ tailWord_602196) baseStart_602196 baseEnd_602196 := by
    simpa [prefixWord, tailWord_602196, baseEnd_602196] using wordTrace_append hprefix tailTrace_602196
  have hstable : (prefixWord ++ tailWord_602196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602196).length < 2 ^ (prefixWord ++ tailWord_602196).sum := by decide
  have hdescent : baseEnd_602196 < baseStart_602196 := by decide
  rcases family_descends (prefixWord ++ tailWord_602196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602226 : List Nat := [3, 2, 1, 2, 2, 2, 2, 1, 3, 1, 4]
def baseStart_602226 : Nat := 118140960795 + 602226 * 2 ^ 59
def prefixEnd_602226 : Nat := 4983230072969 + 3 ^ 40 * 602226 * 2
def baseEnd_602226 : Nat := 309231400634666021705419

theorem tailTrace_602226 : CollatzResearch.WordTrace tailWord_602226 prefixEnd_602226 309231400634666021705419 := by
  unfold tailWord_602226
  simp only [CollatzResearch.WordTrace]
  refine ⟨5491246679061382214360633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14643324477497019238295021 5491246679061382214360633)
  ·
    refine ⟨4118435009296036660770475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5491246679061382214360633 4118435009296036660770475)
    ·
      refine ⟨6177652513944054991155713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4118435009296036660770475 6177652513944054991155713)
      ·
        refine ⟨4633239385458041243366785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6177652513944054991155713 4633239385458041243366785)
        ·
          refine ⟨3474929539093530932525089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4633239385458041243366785 3474929539093530932525089)
          ·
            refine ⟨2606197154320148199393817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3474929539093530932525089 2606197154320148199393817)
            ·
              refine ⟨1954647865740111149545363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2606197154320148199393817 1954647865740111149545363)
              ·
                refine ⟨2931971798610166724318045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1954647865740111149545363 2931971798610166724318045)
                ·
                  refine ⟨1099489424478812521619267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2931971798610166724318045 1099489424478812521619267)
                  ·
                    refine ⟨1649234136718218782428901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1099489424478812521619267 1649234136718218782428901)
                    ·
                      refine ⟨309231400634666021705419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1649234136718218782428901 309231400634666021705419)
                      ·
                        rfl

theorem cell23_602226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_602226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602226 prefixEnd_602226 := by exact prefixLift 602226
  have htrace : WordTrace (prefixWord ++ tailWord_602226) baseStart_602226 baseEnd_602226 := by
    simpa [prefixWord, tailWord_602226, baseEnd_602226] using wordTrace_append hprefix tailTrace_602226
  have hstable : (prefixWord ++ tailWord_602226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602226).length < 2 ^ (prefixWord ++ tailWord_602226).sum := by decide
  have hdescent : baseEnd_602226 < baseStart_602226 := by decide
  rcases family_descends (prefixWord ++ tailWord_602226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602230 : List Nat := [5, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2]
def baseStart_602230 : Nat := 118140960795 + 602230 * 2 ^ 59
def prefixEnd_602230 : Nat := 4983230072969 + 3 ^ 40 * 602230 * 2
def baseEnd_602230 : Nat := 309233454557284006055401

theorem tailTrace_602230 : CollatzResearch.WordTrace tailWord_602230 prefixEnd_602230 309233454557284006055401 := by
  unfold tailWord_602230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1372820788014439846286759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14643421738820691693725429 1372820788014439846286759)
  ·
    refine ⟨2059231182021659769430139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1372820788014439846286759 2059231182021659769430139)
    ·
      refine ⟨3088846773032489654145209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2059231182021659769430139 3088846773032489654145209)
      ·
        refine ⟨2316635079774367240608907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3088846773032489654145209 2316635079774367240608907)
        ·
          refine ⟨3474952619661550860913361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2316635079774367240608907 3474952619661550860913361)
          ·
            refine ⟨2606214464746163145685021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3474952619661550860913361 2606214464746163145685021)
            ·
              refine ⟨977330424279811179631883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2606214464746163145685021 977330424279811179631883)
              ·
                refine ⟨1465995636419716769447825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 977330424279811179631883 1465995636419716769447825)
                ·
                  refine ⟨1099496727314787577085869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1465995636419716769447825 1099496727314787577085869)
                  ·
                    refine ⟨412311272743045341407201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1099496727314787577085869 412311272743045341407201)
                    ·
                      refine ⟨309233454557284006055401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 412311272743045341407201 309233454557284006055401)
                      ·
                        rfl

theorem cell23_602230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_602230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602230 prefixEnd_602230 := by exact prefixLift 602230
  have htrace : WordTrace (prefixWord ++ tailWord_602230) baseStart_602230 baseEnd_602230 := by
    simpa [prefixWord, tailWord_602230, baseEnd_602230] using wordTrace_append hprefix tailTrace_602230
  have hstable : (prefixWord ++ tailWord_602230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602230).length < 2 ^ (prefixWord ++ tailWord_602230).sum := by decide
  have hdescent : baseEnd_602230 < baseStart_602230 := by decide
  rcases family_descends (prefixWord ++ tailWord_602230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602243 : List Nat := [1, 1, 1, 3, 3, 3, 4, 1, 1, 1, 4]
def baseStart_602243 : Nat := 118140960795 + 602243 * 2 ^ 59
def prefixEnd_602243 : Nat := 4983230072969 + 3 ^ 40 * 602243 * 2
def baseEnd_602243 : Nat := 309240129805792455192841

theorem tailTrace_602243 : CollatzResearch.WordTrace tailWord_602243 prefixEnd_602243 309240129805792455192841 := by
  unfold tailWord_602243
  simp only [CollatzResearch.WordTrace]
  refine ⟨21965606757183940760811383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14643737838122627173874255 21965606757183940760811383)
  ·
    refine ⟨32948410135775911141217075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21965606757183940760811383 32948410135775911141217075)
    ·
      refine ⟨49422615203663866711825613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32948410135775911141217075 49422615203663866711825613)
      ·
        refine ⟨18533480701373950016934605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49422615203663866711825613 18533480701373950016934605)
        ·
          refine ⟨6950055263015231256350477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18533480701373950016934605 6950055263015231256350477)
          ·
            refine ⟨2606270723630711721131429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6950055263015231256350477 2606270723630711721131429)
            ·
              refine ⟨488675760680758447712143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2606270723630711721131429 488675760680758447712143)
              ·
                refine ⟨733013641021137671568215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 488675760680758447712143 733013641021137671568215)
                ·
                  refine ⟨1099520461531706507352323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 733013641021137671568215 1099520461531706507352323)
                  ·
                    refine ⟨1649280692297559761028485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1099520461531706507352323 1649280692297559761028485)
                    ·
                      refine ⟨309240129805792455192841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1649280692297559761028485 309240129805792455192841)
                      ·
                        rfl

theorem cell23_602243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 1, 1, 4].length) (baseStart_602243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602243 prefixEnd_602243 := by exact prefixLift 602243
  have htrace : WordTrace (prefixWord ++ tailWord_602243) baseStart_602243 baseEnd_602243 := by
    simpa [prefixWord, tailWord_602243, baseEnd_602243] using wordTrace_append hprefix tailTrace_602243
  have hstable : (prefixWord ++ tailWord_602243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602243).length < 2 ^ (prefixWord ++ tailWord_602243).sum := by decide
  have hdescent : baseEnd_602243 < baseStart_602243 := by decide
  rcases family_descends (prefixWord ++ tailWord_602243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602270 : List Nat := [4, 3, 1, 1, 3, 2, 1, 1, 1, 6]
def baseStart_602270 : Nat := 118140960795 + 602270 * 2 ^ 59
def prefixEnd_602270 : Nat := 4983230072969 + 3 ^ 40 * 602270 * 2
def baseEnd_602270 : Nat := 103084664594487949851739

theorem tailTrace_602270 : CollatzResearch.WordTrace tailWord_602270 prefixEnd_602270 103084664594487949851739 := by
  unfold tailWord_602270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2745823941010765546505533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14644394352057416248029509 2745823941010765546505533)
  ·
    refine ⟨1029683977879037079939575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2745823941010765546505533 1029683977879037079939575)
    ·
      refine ⟨1544525966818555619909363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1029683977879037079939575 1544525966818555619909363)
      ·
        refine ⟨2316788950227833429864045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1544525966818555619909363 2316788950227833429864045)
        ·
          refine ⟨868795856335437536199017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2316788950227833429864045 868795856335437536199017)
          ·
            refine ⟨651596892251578152149263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 868795856335437536199017 651596892251578152149263)
            ·
              refine ⟨977395338377367228223895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 651596892251578152149263 977395338377367228223895)
              ·
                refine ⟨1466093007566050842335843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 977395338377367228223895 1466093007566050842335843)
                ·
                  refine ⟨2199139511349076263503765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1466093007566050842335843 2199139511349076263503765)
                  ·
                    refine ⟨103084664594487949851739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2199139511349076263503765 103084664594487949851739)
                    ·
                      rfl

theorem cell23_602270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_602270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602270 prefixEnd_602270 := by exact prefixLift 602270
  have htrace : WordTrace (prefixWord ++ tailWord_602270) baseStart_602270 baseEnd_602270 := by
    simpa [prefixWord, tailWord_602270, baseEnd_602270] using wordTrace_append hprefix tailTrace_602270
  have hstable : (prefixWord ++ tailWord_602270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602270).length < 2 ^ (prefixWord ++ tailWord_602270).sum := by decide
  have hdescent : baseEnd_602270 < baseStart_602270 := by decide
  rcases family_descends (prefixWord ++ tailWord_602270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602273 : List Nat := [1, 2, 3, 3, 1, 4, 1, 1, 1, 2, 4]
def baseStart_602273 : Nat := 118140960795 + 602273 * 2 ^ 59
def prefixEnd_602273 : Nat := 4983230072969 + 3 ^ 40 * 602273 * 2
def baseEnd_602273 : Nat := 309255534225427337817703

theorem tailTrace_602273 : CollatzResearch.WordTrace tailWord_602273 prefixEnd_602273 309255534225427337817703 := by
  unfold tailWord_602273
  simp only [CollatzResearch.WordTrace]
  refine ⟨21966700947075255884403473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14644467298050170589602315 21966700947075255884403473)
  ·
    refine ⟨16475025710306441913302605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21966700947075255884403473 16475025710306441913302605)
    ·
      refine ⟨6178134641364915717488477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16475025710306441913302605 6178134641364915717488477)
      ·
        refine ⟨2316800490511843394058179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6178134641364915717488477 2316800490511843394058179)
        ·
          refine ⟨3475200735767765091087269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2316800490511843394058179 3475200735767765091087269)
          ·
            refine ⟨651600137956455954578863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3475200735767765091087269 651600137956455954578863)
            ·
              refine ⟨977400206934683931868295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 651600137956455954578863 977400206934683931868295)
              ·
                refine ⟨1466100310402025897802443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 977400206934683931868295 1466100310402025897802443)
                ·
                  refine ⟨2199150465603038846703665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1466100310402025897802443 2199150465603038846703665)
                  ·
                    refine ⟨1649362849202279135027749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2199150465603038846703665 1649362849202279135027749)
                    ·
                      refine ⟨309255534225427337817703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1649362849202279135027749 309255534225427337817703)
                      ·
                        rfl

theorem cell23_602273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_602273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602273 prefixEnd_602273 := by exact prefixLift 602273
  have htrace : WordTrace (prefixWord ++ tailWord_602273) baseStart_602273 baseEnd_602273 := by
    simpa [prefixWord, tailWord_602273, baseEnd_602273] using wordTrace_append hprefix tailTrace_602273
  have hstable : (prefixWord ++ tailWord_602273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602273).length < 2 ^ (prefixWord ++ tailWord_602273).sum := by decide
  have hdescent : baseEnd_602273 < baseStart_602273 := by decide
  rcases family_descends (prefixWord ++ tailWord_602273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602309 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 4, 6]
def baseStart_602309 : Nat := 118140960795 + 602309 * 2 ^ 59
def prefixEnd_602309 : Nat := 4983230072969 + 3 ^ 40 * 602309 * 2
def baseEnd_602309 : Nat := 103091339842996398989179

theorem tailTrace_602309 : CollatzResearch.WordTrace tailWord_602309 prefixEnd_602309 103091339842996398989179 := by
  unfold tailWord_602309
  simp only [CollatzResearch.WordTrace]
  refine ⟨21968013974944834032713981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14645342649963222688475987 21968013974944834032713981)
  ·
    refine ⟨8238005240604312762267743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21968013974944834032713981 8238005240604312762267743)
    ·
      refine ⟨12357007860906469143401615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8238005240604312762267743 12357007860906469143401615)
      ·
        refine ⟨18535511791359703715102423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12357007860906469143401615 18535511791359703715102423)
        ·
          refine ⟨27803267687039555572653635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18535511791359703715102423 27803267687039555572653635)
          ·
            refine ⟨41704901530559333358980453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27803267687039555572653635 41704901530559333358980453)
            ·
              refine ⟨7819669036979875004808835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41704901530559333358980453 7819669036979875004808835)
              ·
                refine ⟨11729503555469812507213253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7819669036979875004808835 11729503555469812507213253)
                ·
                  refine ⟨2199281916650589845102485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11729503555469812507213253 2199281916650589845102485)
                  ·
                    refine ⟨103091339842996398989179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2199281916650589845102485 103091339842996398989179)
                    ·
                      rfl

theorem cell23_602309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 6].length) (baseStart_602309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602309 prefixEnd_602309 := by exact prefixLift 602309
  have htrace : WordTrace (prefixWord ++ tailWord_602309) baseStart_602309 baseEnd_602309 := by
    simpa [prefixWord, tailWord_602309, baseEnd_602309] using wordTrace_append hprefix tailTrace_602309
  have hstable : (prefixWord ++ tailWord_602309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602309).length < 2 ^ (prefixWord ++ tailWord_602309).sum := by decide
  have hdescent : baseEnd_602309 < baseStart_602309 := by decide
  rcases family_descends (prefixWord ++ tailWord_602309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602319 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 5]
def baseStart_602319 : Nat := 118140960795 + 602319 * 2 ^ 59
def prefixEnd_602319 : Nat := 4983230072969 + 3 ^ 40 * 602319 * 2
def baseEnd_602319 : Nat := 309279154335534157842491

theorem tailTrace_602319 : CollatzResearch.WordTrace tailWord_602319 prefixEnd_602319 309279154335534157842491 := by
  unfold tailWord_602319
  simp only [CollatzResearch.WordTrace]
  refine ⟨21968378704908605740578011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14645585803272403827052007 21968378704908605740578011)
  ·
    refine ⟨32952568057362908610867017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21968378704908605740578011 32952568057362908610867017)
    ·
      refine ⟨24714426043022181458150263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32952568057362908610867017 24714426043022181458150263)
      ·
        refine ⟨37071639064533272187225395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24714426043022181458150263 37071639064533272187225395)
        ·
          refine ⟨55607458596799908280838093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37071639064533272187225395 55607458596799908280838093)
          ·
            refine ⟨20852796973799965605314285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55607458596799908280838093 20852796973799965605314285)
            ·
              refine ⟨7819798865174987101992857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20852796973799965605314285 7819798865174987101992857)
              ·
                refine ⟨5864849148881240326494643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7819798865174987101992857 5864849148881240326494643)
                ·
                  refine ⟨8797273723321860489741965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5864849148881240326494643 8797273723321860489741965)
                  ·
                    refine ⟨3298977646245697683653237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8797273723321860489741965 3298977646245697683653237)
                    ·
                      refine ⟨309279154335534157842491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3298977646245697683653237 309279154335534157842491)
                      ·
                        rfl

theorem cell23_602319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 5].length) (baseStart_602319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602319 prefixEnd_602319 := by exact prefixLift 602319
  have htrace : WordTrace (prefixWord ++ tailWord_602319) baseStart_602319 baseEnd_602319 := by
    simpa [prefixWord, tailWord_602319, baseEnd_602319] using wordTrace_append hprefix tailTrace_602319
  have hstable : (prefixWord ++ tailWord_602319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602319).length < 2 ^ (prefixWord ++ tailWord_602319).sum := by decide
  have hdescent : baseEnd_602319 < baseStart_602319 := by decide
  rcases family_descends (prefixWord ++ tailWord_602319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602359 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 6]
def baseStart_602359 : Nat := 118140960795 + 602359 * 2 ^ 59
def prefixEnd_602359 : Nat := 4983230072969 + 3 ^ 40 * 602359 * 2
def baseEnd_602359 : Nat := 309299693561714001342307

theorem tailTrace_602359 : CollatzResearch.WordTrace tailWord_602359 prefixEnd_602359 309299693561714001342307 := by
  unfold tailWord_602359
  simp only [CollatzResearch.WordTrace]
  refine ⟨21969837624763692572034131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14646558416509128381356087 21969837624763692572034131)
  ·
    refine ⟨32954756437145538858051197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21969837624763692572034131 32954756437145538858051197)
    ·
      refine ⟨12358033663929577071769199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32954756437145538858051197 12358033663929577071769199)
      ·
        refine ⟨18537050495894365607653799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12358033663929577071769199 18537050495894365607653799)
        ·
          refine ⟨27805575743841548411480699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18537050495894365607653799 27805575743841548411480699)
          ·
            refine ⟨41708363615762322617221049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27805575743841548411480699 41708363615762322617221049)
            ·
              refine ⟨31281272711821741962915787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41708363615762322617221049 31281272711821741962915787)
              ·
                refine ⟨46921909067732612944373681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31281272711821741962915787 46921909067732612944373681)
                ·
                  refine ⟨35191431800799459708280261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46921909067732612944373681 35191431800799459708280261)
                  ·
                    refine ⟨6598393462649898695302549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35191431800799459708280261 6598393462649898695302549)
                    ·
                      refine ⟨309299693561714001342307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6598393462649898695302549 309299693561714001342307)
                      ·
                        rfl

theorem cell23_602359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_602359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602359 prefixEnd_602359 := by exact prefixLift 602359
  have htrace : WordTrace (prefixWord ++ tailWord_602359) baseStart_602359 baseEnd_602359 := by
    simpa [prefixWord, tailWord_602359, baseEnd_602359] using wordTrace_append hprefix tailTrace_602359
  have hstable : (prefixWord ++ tailWord_602359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602359).length < 2 ^ (prefixWord ++ tailWord_602359).sum := by decide
  have hdescent : baseEnd_602359 < baseStart_602359 := by decide
  rcases family_descends (prefixWord ++ tailWord_602359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602496 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 4]
def baseStart_602496 : Nat := 118140960795 + 602496 * 2 ^ 59
def prefixEnd_602496 : Nat := 4983230072969 + 3 ^ 40 * 602496 * 2
def baseEnd_602496 : Nat := 309370040411379965329177

theorem tailTrace_602496 : CollatzResearch.WordTrace tailWord_602496 prefixEnd_602496 309370040411379965329177 := by
  unfold tailWord_602496
  simp only [CollatzResearch.WordTrace]
  refine ⟨10987417212633682484885671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14649889616844909979847561 10987417212633682484885671)
  ·
    refine ⟨16481125818950523727328507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10987417212633682484885671 16481125818950523727328507)
    ·
      refine ⟨24721688728425785590992761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16481125818950523727328507 24721688728425785590992761)
      ·
        refine ⟨18541266546319339193244571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24721688728425785590992761 18541266546319339193244571)
        ·
          refine ⟨27811899819479008789866857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18541266546319339193244571 27811899819479008789866857)
          ·
            refine ⟨20858924864609256592400143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27811899819479008789866857 20858924864609256592400143)
            ·
              refine ⟨31288387296913884888600215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20858924864609256592400143 31288387296913884888600215)
              ·
                refine ⟨46932580945370827332900323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31288387296913884888600215 46932580945370827332900323)
                ·
                  refine ⟨70398871418056240999350485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46932580945370827332900323 70398871418056240999350485)
                  ·
                    refine ⟨1649973548860693148422277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 70398871418056240999350485 1649973548860693148422277)
                    ·
                      refine ⟨309370040411379965329177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1649973548860693148422277 309370040411379965329177)
                      ·
                        rfl

theorem cell23_602496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_602496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602496 prefixEnd_602496 := by exact prefixLift 602496
  have htrace : WordTrace (prefixWord ++ tailWord_602496) baseStart_602496 baseEnd_602496 := by
    simpa [prefixWord, tailWord_602496, baseEnd_602496] using wordTrace_append hprefix tailTrace_602496
  have hstable : (prefixWord ++ tailWord_602496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602496).length < 2 ^ (prefixWord ++ tailWord_602496).sum := by decide
  have hdescent : baseEnd_602496 < baseStart_602496 := by decide
  rcases family_descends (prefixWord ++ tailWord_602496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602497 : List Nat := [1, 2, 4, 3, 1, 3, 2, 1, 6]
def baseStart_602497 : Nat := 118140960795 + 602497 * 2 ^ 59
def prefixEnd_602497 : Nat := 4983230072969 + 3 ^ 40 * 602497 * 2
def baseEnd_602497 : Nat := 34374505988003829046297

theorem tailTrace_602497 : CollatzResearch.WordTrace tailWord_602497 prefixEnd_602497 34374505988003829046297 := by
  unfold tailWord_602497
  simp only [CollatzResearch.WordTrace]
  refine ⟨21974870898263742140557745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14649913932175828093705163 21974870898263742140557745)
  ·
    refine ⟨16481153173697806605418309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21974870898263742140557745 16481153173697806605418309)
    ·
      refine ⟨3090216220068338738515933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16481153173697806605418309 3090216220068338738515933)
      ·
        refine ⟨1158831082525627026943475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3090216220068338738515933 1158831082525627026943475)
        ·
          refine ⟨1738246623788440540415213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1158831082525627026943475 1738246623788440540415213)
          ·
            refine ⟨651842483920665202655705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1738246623788440540415213 651842483920665202655705)
            ·
              refine ⟨488881862940498901991779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 651842483920665202655705 488881862940498901991779)
              ·
                refine ⟨733322794410748352987669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 488881862940498901991779 733322794410748352987669)
                ·
                  refine ⟨34374505988003829046297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 733322794410748352987669 34374505988003829046297)
                  ·
                    rfl

theorem cell23_602497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 6].length) (baseStart_602497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602497 prefixEnd_602497 := by exact prefixLift 602497
  have htrace : WordTrace (prefixWord ++ tailWord_602497) baseStart_602497 baseEnd_602497 := by
    simpa [prefixWord, tailWord_602497, baseEnd_602497] using wordTrace_append hprefix tailTrace_602497
  have hstable : (prefixWord ++ tailWord_602497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602497).length < 2 ^ (prefixWord ++ tailWord_602497).sum := by decide
  have hdescent : baseEnd_602497 < baseStart_602497 := by decide
  rcases family_descends (prefixWord ++ tailWord_602497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602500 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 4, 3, 2]
def baseStart_602500 : Nat := 118140960795 + 602500 * 2 ^ 59
def prefixEnd_602500 : Nat := 4983230072969 + 3 ^ 40 * 602500 * 2
def baseEnd_602500 : Nat := 309372094333997949679159

theorem tailTrace_602500 : CollatzResearch.WordTrace tailWord_602500 prefixEnd_602500 309372094333997949679159 := by
  unfold tailWord_602500
  simp only [CollatzResearch.WordTrace]
  refine ⟨10987490158626436826458477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14649986878168582435277969 10987490158626436826458477)
  ·
    refine ⟨4120308809484913809921929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10987490158626436826458477 4120308809484913809921929)
    ·
      refine ⟨3090231607113685357441447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4120308809484913809921929 3090231607113685357441447)
      ·
        refine ⟨4635347410670528036162171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3090231607113685357441447 4635347410670528036162171)
        ·
          refine ⟨6953021116005792054243257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4635347410670528036162171 6953021116005792054243257)
          ·
            refine ⟨5214765837004344040682443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6953021116005792054243257 5214765837004344040682443)
            ·
              refine ⟨7822148755506516061023665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5214765837004344040682443 7822148755506516061023665)
              ·
                refine ⟨5866611566629887045767749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7822148755506516061023665 5866611566629887045767749)
                ·
                  refine ⟨1099989668743103821081453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5866611566629887045767749 1099989668743103821081453)
                  ·
                    refine ⟨412496125778663932905545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1099989668743103821081453 412496125778663932905545)
                    ·
                      refine ⟨309372094333997949679159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 412496125778663932905545 309372094333997949679159)
                      ·
                        rfl

theorem cell23_602500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_602500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602500 prefixEnd_602500 := by exact prefixLift 602500
  have htrace : WordTrace (prefixWord ++ tailWord_602500) baseStart_602500 baseEnd_602500 := by
    simpa [prefixWord, tailWord_602500, baseEnd_602500] using wordTrace_append hprefix tailTrace_602500
  have hstable : (prefixWord ++ tailWord_602500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602500).length < 2 ^ (prefixWord ++ tailWord_602500).sum := by decide
  have hdescent : baseEnd_602500 < baseStart_602500 := by decide
  rcases family_descends (prefixWord ++ tailWord_602500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602510 : List Nat := [4, 1, 1, 4, 1, 2, 1, 1, 3, 5]
def baseStart_602510 : Nat := 118140960795 + 602510 * 2 ^ 59
def prefixEnd_602510 : Nat := 4983230072969 + 3 ^ 40 * 602510 * 2
def baseEnd_602510 : Nat := 103125743046847636851371

theorem tailTrace_602510 : CollatzResearch.WordTrace tailWord_602510 prefixEnd_602510 103125743046847636851371 := by
  unfold tailWord_602510
  simp only [CollatzResearch.WordTrace]
  refine ⟨2746918130902080670097623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14650230031477763573853989 2746918130902080670097623)
  ·
    refine ⟨4120377196353121005146435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2746918130902080670097623 4120377196353121005146435)
    ·
      refine ⟨6180565794529681507719653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4120377196353121005146435 6180565794529681507719653)
      ·
        refine ⟨1158856086474315282697435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6180565794529681507719653 1158856086474315282697435)
        ·
          refine ⟨1738284129711472924046153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1158856086474315282697435 1738284129711472924046153)
          ·
            refine ⟨1303713097283604693034615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1738284129711472924046153 1303713097283604693034615)
            ·
              refine ⟨1955569645925407039551923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1303713097283604693034615 1955569645925407039551923)
              ·
                refine ⟨2933354468888110559327885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1955569645925407039551923 2933354468888110559327885)
                ·
                  refine ⟨1100007925833041459747957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2933354468888110559327885 1100007925833041459747957)
                  ·
                    refine ⟨103125743046847636851371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1100007925833041459747957 103125743046847636851371)
                    ·
                      rfl

theorem cell23_602510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_602510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602510 prefixEnd_602510 := by exact prefixLift 602510
  have htrace : WordTrace (prefixWord ++ tailWord_602510) baseStart_602510 baseEnd_602510 := by
    simpa [prefixWord, tailWord_602510, baseEnd_602510] using wordTrace_append hprefix tailTrace_602510
  have hstable : (prefixWord ++ tailWord_602510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602510).length < 2 ^ (prefixWord ++ tailWord_602510).sum := by decide
  have hdescent : baseEnd_602510 < baseStart_602510 := by decide
  rcases family_descends (prefixWord ++ tailWord_602510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602541 : List Nat := [1, 5, 2, 2, 2, 1, 1, 4, 1, 1, 3]
def baseStart_602541 : Nat := 118140960795 + 602541 * 2 ^ 59
def prefixEnd_602541 : Nat := 4983230072969 + 3 ^ 40 * 602541 * 2
def baseEnd_602541 : Nat := 309393147040832289266471

theorem tailTrace_602541 : CollatzResearch.WordTrace tailWord_602541 prefixEnd_602541 309393147040832289266471 := by
  unfold tailWord_602541
  simp only [CollatzResearch.WordTrace]
  refine ⟨21976475710104337655159477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14650983806736225103439651 21976475710104337655159477)
  ·
    refine ⟨2060294597822281655171201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21976475710104337655159477 2060294597822281655171201)
    ·
      refine ⟨1545220948366711241378401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2060294597822281655171201 1545220948366711241378401)
      ·
        refine ⟨1158915711275033431033801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1545220948366711241378401 1158915711275033431033801)
        ·
          refine ⟨869186783456275073275351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1158915711275033431033801 869186783456275073275351)
          ·
            refine ⟨1303780175184412609913027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 869186783456275073275351 1303780175184412609913027)
            ·
              refine ⟨1955670262776618914869541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1303780175184412609913027 1955670262776618914869541)
              ·
                refine ⟨366688174270616046538039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1955670262776618914869541 366688174270616046538039)
                ·
                  refine ⟨550032261405924069807059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 366688174270616046538039 550032261405924069807059)
                  ·
                    refine ⟨825048392108886104710589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 550032261405924069807059 825048392108886104710589)
                    ·
                      refine ⟨309393147040832289266471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 825048392108886104710589 309393147040832289266471)
                      ·
                        rfl

theorem cell23_602541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_602541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602541 prefixEnd_602541 := by exact prefixLift 602541
  have htrace : WordTrace (prefixWord ++ tailWord_602541) baseStart_602541 baseEnd_602541 := by
    simpa [prefixWord, tailWord_602541, baseEnd_602541] using wordTrace_append hprefix tailTrace_602541
  have hstable : (prefixWord ++ tailWord_602541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602541).length < 2 ^ (prefixWord ++ tailWord_602541).sum := by decide
  have hdescent : baseEnd_602541 < baseStart_602541 := by decide
  rcases family_descends (prefixWord ++ tailWord_602541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602553 : List Nat := [1, 2, 1, 4, 3, 1, 3, 8]
def baseStart_602553 : Nat := 118140960795 + 602553 * 2 ^ 59
def prefixEnd_602553 : Nat := 4983230072969 + 3 ^ 40 * 602553 * 2
def baseEnd_602553 : Nat := 11459233659580971937645

theorem tailTrace_602553 : CollatzResearch.WordTrace tailWord_602553 prefixEnd_602553 11459233659580971937645 := by
  unfold tailWord_602553
  simp only [CollatzResearch.WordTrace]
  refine ⟨21976913386060863704596313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14651275590707242469730875 21976913386060863704596313)
  ·
    refine ⟨16482685039545647778447235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21976913386060863704596313 16482685039545647778447235)
    ·
      refine ⟨24724027559318471667670853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16482685039545647778447235 24724027559318471667670853)
      ·
        refine ⟨4635755167372213437688285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24724027559318471667670853 4635755167372213437688285)
        ·
          refine ⟨1738408187764580039133107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4635755167372213437688285 1738408187764580039133107)
          ·
            refine ⟨2607612281646870058699661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1738408187764580039133107 2607612281646870058699661)
            ·
              refine ⟨977854605617576272012373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2607612281646870058699661 977854605617576272012373)
              ·
                refine ⟨11459233659580971937645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 977854605617576272012373 11459233659580971937645)
                ·
                  rfl

theorem cell23_602553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 8].length) (baseStart_602553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602553 prefixEnd_602553 := by exact prefixLift 602553
  have htrace : WordTrace (prefixWord ++ tailWord_602553) baseStart_602553 baseEnd_602553 := by
    simpa [prefixWord, tailWord_602553, baseEnd_602553] using wordTrace_append hprefix tailTrace_602553
  have hstable : (prefixWord ++ tailWord_602553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602553).length < 2 ^ (prefixWord ++ tailWord_602553).sum := by decide
  have hdescent : baseEnd_602553 < baseStart_602553 := by decide
  rcases family_descends (prefixWord ++ tailWord_602553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602581 : List Nat := [1, 3, 2, 3, 1, 3, 2, 3, 1, 2, 2]
def baseStart_602581 : Nat := 118140960795 + 602581 * 2 ^ 59
def prefixEnd_602581 : Nat := 4983230072969 + 3 ^ 40 * 602581 * 2
def baseEnd_602581 : Nat := 309413686267012132766287

theorem tailTrace_602581 : CollatzResearch.WordTrace tailWord_602581 prefixEnd_602581 309413686267012132766287 := by
  unfold tailWord_602581
  simp only [CollatzResearch.WordTrace]
  refine ⟨21977934629959424486615597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14651956419972949657743731 21977934629959424486615597)
  ·
    refine ⟨8241725486234784182480849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21977934629959424486615597 8241725486234784182480849)
    ·
      refine ⟨6181294114676088136860637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8241725486234784182480849 6181294114676088136860637)
      ·
        refine ⟨2317985293003533051322739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6181294114676088136860637 2317985293003533051322739)
        ·
          refine ⟨3476977939505299576984109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2317985293003533051322739 3476977939505299576984109)
          ·
            refine ⟨1303866727314487341369041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3476977939505299576984109 1303866727314487341369041)
            ·
              refine ⟨977900045485865506026781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1303866727314487341369041 977900045485865506026781)
              ·
                refine ⟨366712517057199564760043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 977900045485865506026781 366712517057199564760043)
                ·
                  refine ⟨550068775585799347140065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 366712517057199564760043 550068775585799347140065)
                  ·
                    refine ⟨412551581689349510355049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 550068775585799347140065 412551581689349510355049)
                    ·
                      refine ⟨309413686267012132766287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 412551581689349510355049 309413686267012132766287)
                      ·
                        rfl

theorem cell23_602581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_602581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602581 prefixEnd_602581 := by exact prefixLift 602581
  have htrace : WordTrace (prefixWord ++ tailWord_602581) baseStart_602581 baseEnd_602581 := by
    simpa [prefixWord, tailWord_602581, baseEnd_602581] using wordTrace_append hprefix tailTrace_602581
  have hstable : (prefixWord ++ tailWord_602581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602581).length < 2 ^ (prefixWord ++ tailWord_602581).sum := by decide
  have hdescent : baseEnd_602581 < baseStart_602581 := by decide
  rcases family_descends (prefixWord ++ tailWord_602581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602623 : List Nat := [1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 5]
def baseStart_602623 : Nat := 118140960795 + 602623 * 2 ^ 59
def prefixEnd_602623 : Nat := 4983230072969 + 3 ^ 40 * 602623 * 2
def baseEnd_602623 : Nat := 309435252454500968441093

theorem tailTrace_602623 : CollatzResearch.WordTrace tailWord_602623 prefixEnd_602623 309435252454500968441093 := by
  unfold tailWord_602623
  simp only [CollatzResearch.WordTrace]
  refine ⟨21979466495807265659644523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14652977663871510439763015 21979466495807265659644523)
  ·
    refine ⟨32969199743710898489466785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21979466495807265659644523 32969199743710898489466785)
    ·
      refine ⟨24726899807783173867100089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32969199743710898489466785 24726899807783173867100089)
      ·
        refine ⟨18545174855837380400325067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24726899807783173867100089 18545174855837380400325067)
        ·
          refine ⟨27817762283756070600487601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18545174855837380400325067 27817762283756070600487601)
          ·
            refine ⟨20863321712817052950365701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27817762283756070600487601 20863321712817052950365701)
            ·
              refine ⟨3911872821153197428193569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20863321712817052950365701 3911872821153197428193569)
              ·
                refine ⟨2933904615864898071145177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3911872821153197428193569 2933904615864898071145177)
                ·
                  refine ⟨2200428461898673553358883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2933904615864898071145177 2200428461898673553358883)
                  ·
                    refine ⟨3300642692848010330038325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2200428461898673553358883 3300642692848010330038325)
                    ·
                      refine ⟨309435252454500968441093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3300642692848010330038325 309435252454500968441093)
                      ·
                        rfl

theorem cell23_602623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_602623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602623 prefixEnd_602623 := by exact prefixLift 602623
  have htrace : WordTrace (prefixWord ++ tailWord_602623) baseStart_602623 baseEnd_602623 := by
    simpa [prefixWord, tailWord_602623, baseEnd_602623] using wordTrace_append hprefix tailTrace_602623
  have hstable : (prefixWord ++ tailWord_602623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602623).length < 2 ^ (prefixWord ++ tailWord_602623).sum := by decide
  have hdescent : baseEnd_602623 < baseStart_602623 := by decide
  rcases family_descends (prefixWord ++ tailWord_602623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602633 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 4, 2, 4]
def baseStart_602633 : Nat := 118140960795 + 602633 * 2 ^ 59
def prefixEnd_602633 : Nat := 4983230072969 + 3 ^ 40 * 602633 * 2
def baseEnd_602633 : Nat := 309440387261045929316047

theorem tailTrace_602633 : CollatzResearch.WordTrace tailWord_602633 prefixEnd_602633 309440387261045929316047 := by
  unfold tailWord_602633
  simp only [CollatzResearch.WordTrace]
  refine ⟨21979831225771037367508553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14653220817180691578339035 21979831225771037367508553)
  ·
    refine ⟨16484873419328278025631415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21979831225771037367508553 16484873419328278025631415)
    ·
      refine ⟨24727310128992417038447123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16484873419328278025631415 24727310128992417038447123)
      ·
        refine ⟨37090965193488625557670685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24727310128992417038447123 37090965193488625557670685)
        ·
          refine ⟨13909111947558234584126507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37090965193488625557670685 13909111947558234584126507)
          ·
            refine ⟨20863667921337351876189761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13909111947558234584126507 20863667921337351876189761)
            ·
              refine ⟨15647750941003013907142321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20863667921337351876189761 15647750941003013907142321)
              ·
                refine ⟨11735813205752260430356741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15647750941003013907142321 11735813205752260430356741)
                ·
                  refine ⟨2200464976078548830691889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11735813205752260430356741 2200464976078548830691889)
                  ·
                    refine ⟨1650348732058911623018917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2200464976078548830691889 1650348732058911623018917)
                    ·
                      refine ⟨309440387261045929316047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1650348732058911623018917 309440387261045929316047)
                      ·
                        rfl

theorem cell23_602633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 2, 4].length) (baseStart_602633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602633 prefixEnd_602633 := by exact prefixLift 602633
  have htrace : WordTrace (prefixWord ++ tailWord_602633) baseStart_602633 baseEnd_602633 := by
    simpa [prefixWord, tailWord_602633, baseEnd_602633] using wordTrace_append hprefix tailTrace_602633
  have hstable : (prefixWord ++ tailWord_602633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602633).length < 2 ^ (prefixWord ++ tailWord_602633).sum := by decide
  have hdescent : baseEnd_602633 < baseStart_602633 := by decide
  rcases family_descends (prefixWord ++ tailWord_602633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602673 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 3, 7]
def baseStart_602673 : Nat := 118140960795 + 602673 * 2 ^ 59
def prefixEnd_602673 : Nat := 4983230072969 + 3 ^ 40 * 602673 * 2
def baseEnd_602673 : Nat := 103153642162408590938621

theorem tailTrace_602673 : CollatzResearch.WordTrace tailWord_602673 prefixEnd_602673 103153642162408590938621 := by
  unfold tailWord_602673
  simp only [CollatzResearch.WordTrace]
  refine ⟨21981290145626124198964673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14654193430417416132643115 21981290145626124198964673)
  ·
    refine ⟨16485967609219593149223505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21981290145626124198964673 16485967609219593149223505)
    ·
      refine ⟨12364475706914694861917629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16485967609219593149223505 12364475706914694861917629)
      ·
        refine ⟨4636678390093010573219111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12364475706914694861917629 4636678390093010573219111)
        ·
          refine ⟨6955017585139515859828667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4636678390093010573219111 6955017585139515859828667)
          ·
            refine ⟨10432526377709273789743001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6955017585139515859828667 10432526377709273789743001)
            ·
              refine ⟨7824394783281955342307251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10432526377709273789743001 7824394783281955342307251)
              ·
                refine ⟨11736592174922933013460877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7824394783281955342307251 11736592174922933013460877)
                ·
                  refine ⟨4401222065596099880047829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11736592174922933013460877 4401222065596099880047829)
                  ·
                    refine ⟨103153642162408590938621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4401222065596099880047829 103153642162408590938621)
                    ·
                      rfl

theorem cell23_602673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 7].length) (baseStart_602673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602673 prefixEnd_602673 := by exact prefixLift 602673
  have htrace : WordTrace (prefixWord ++ tailWord_602673) baseStart_602673 baseEnd_602673 := by
    simpa [prefixWord, tailWord_602673, baseEnd_602673] using wordTrace_append hprefix tailTrace_602673
  have hstable : (prefixWord ++ tailWord_602673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602673).length < 2 ^ (prefixWord ++ tailWord_602673).sum := by decide
  have hdescent : baseEnd_602673 < baseStart_602673 := by decide
  rcases family_descends (prefixWord ++ tailWord_602673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602741 : List Nat := [1, 3, 4, 2, 3, 1, 1, 1, 2, 5]
def baseStart_602741 : Nat := 118140960795 + 602741 * 2 ^ 59
def prefixEnd_602741 : Nat := 4983230072969 + 3 ^ 40 * 602741 * 2
def baseEnd_602741 : Nat := 103165281057243835588517

theorem tailTrace_602741 : CollatzResearch.WordTrace tailWord_602741 prefixEnd_602741 103165281057243835588517 := by
  unfold tailWord_602741
  simp only [CollatzResearch.WordTrace]
  refine ⟨21983770309379771812440077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14655846872919847874960051 21983770309379771812440077)
  ·
    refine ⟨8243913866017414429665029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21983770309379771812440077 8243913866017414429665029)
    ·
      refine ⟨1545733849878265205562193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8243913866017414429665029 1545733849878265205562193)
      ·
        refine ⟨1159300387408698904171645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1545733849878265205562193 1159300387408698904171645)
        ·
          refine ⟨434737645278262089064367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1159300387408698904171645 434737645278262089064367)
          ·
            refine ⟨652106467917393133596551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434737645278262089064367 652106467917393133596551)
            ·
              refine ⟨978159701876089700394827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 652106467917393133596551 978159701876089700394827)
              ·
                refine ⟨1467239552814134550592241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 978159701876089700394827 1467239552814134550592241)
                ·
                  refine ⟨1100429664610600912944181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1467239552814134550592241 1100429664610600912944181)
                  ·
                    refine ⟨103165281057243835588517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1100429664610600912944181 103165281057243835588517)
                    ·
                      rfl

theorem cell23_602741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_602741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602741 prefixEnd_602741 := by exact prefixLift 602741
  have htrace : WordTrace (prefixWord ++ tailWord_602741) baseStart_602741 baseEnd_602741 := by
    simpa [prefixWord, tailWord_602741, baseEnd_602741] using wordTrace_append hprefix tailTrace_602741
  have hstable : (prefixWord ++ tailWord_602741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602741).length < 2 ^ (prefixWord ++ tailWord_602741).sum := by decide
  have hdescent : baseEnd_602741 < baseStart_602741 := by decide
  rcases family_descends (prefixWord ++ tailWord_602741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602784 : List Nat := [2, 1, 1, 4, 4, 1, 3, 1, 6]
def baseStart_602784 : Nat := 118140960795 + 602784 * 2 ^ 59
def prefixEnd_602784 : Nat := 4983230072969 + 3 ^ 40 * 602784 * 2
def baseEnd_602784 : Nat := 34390880315541648725317

theorem tailTrace_602784 : CollatzResearch.WordTrace tailWord_602784 prefixEnd_602784 34390880315541648725317 := by
  unfold tailWord_602784
  simp only [CollatzResearch.WordTrace]
  refine ⟨10992669324111995078127703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14656892432149326770836937 10992669324111995078127703)
  ·
    refine ⟨16489003986167992617191555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10992669324111995078127703 16489003986167992617191555)
    ·
      refine ⟨24733505979251988925787333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16489003986167992617191555 24733505979251988925787333)
      ·
        refine ⟨4637532371109747923585125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24733505979251988925787333 4637532371109747923585125)
        ·
          refine ⟨869537319583077735672211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4637532371109747923585125 869537319583077735672211)
          ·
            refine ⟨1304305979374616603508317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 869537319583077735672211 1304305979374616603508317)
            ·
              refine ⟨489114742265481226315619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1304305979374616603508317 489114742265481226315619)
              ·
                refine ⟨733672113398221839473429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 489114742265481226315619 733672113398221839473429)
                ·
                  refine ⟨34390880315541648725317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 733672113398221839473429 34390880315541648725317)
                  ·
                    rfl

theorem cell23_602784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 6].length) (baseStart_602784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602784 prefixEnd_602784 := by exact prefixLift 602784
  have htrace : WordTrace (prefixWord ++ tailWord_602784) baseStart_602784 baseEnd_602784 := by
    simpa [prefixWord, tailWord_602784, baseEnd_602784] using wordTrace_append hprefix tailTrace_602784
  have hstable : (prefixWord ++ tailWord_602784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602784).length < 2 ^ (prefixWord ++ tailWord_602784).sum := by decide
  have hdescent : baseEnd_602784 < baseStart_602784 := by decide
  rcases family_descends (prefixWord ++ tailWord_602784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602787 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 6, 3, 2]
def baseStart_602787 : Nat := 118140960795 + 602787 * 2 ^ 59
def prefixEnd_602787 : Nat := 4983230072969 + 3 ^ 40 * 602787 * 2
def baseEnd_602787 : Nat := 309519463281838326790339

theorem tailTrace_602787 : CollatzResearch.WordTrace tailWord_602787 prefixEnd_602787 309519463281838326790339 := by
  unfold tailWord_602787
  simp only [CollatzResearch.WordTrace]
  refine ⟨21985448067213121668614615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14656965378142081112409743 21985448067213121668614615)
  ·
    refine ⟨32978172100819682502921923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21985448067213121668614615 32978172100819682502921923)
    ·
      refine ⟨49467258151229523754382885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32978172100819682502921923 49467258151229523754382885)
      ·
        refine ⟨9275110903355535703946791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49467258151229523754382885 9275110903355535703946791)
        ·
          refine ⟨13912666355033303555920187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9275110903355535703946791 13912666355033303555920187)
          ·
            refine ⟨20868999532549955333880281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13912666355033303555920187 20868999532549955333880281)
            ·
              refine ⟨15651749649412466500410211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20868999532549955333880281 15651749649412466500410211)
              ·
                refine ⟨23477624474118699750615317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15651749649412466500410211 23477624474118699750615317)
                ·
                  refine ⟨1100513647224314050810093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 23477624474118699750615317 1100513647224314050810093)
                  ·
                    refine ⟨412692617709117769053785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1100513647224314050810093 412692617709117769053785)
                    ·
                      refine ⟨309519463281838326790339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 412692617709117769053785 309519463281838326790339)
                      ·
                        rfl

theorem cell23_602787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 3, 2].length) (baseStart_602787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602787 prefixEnd_602787 := by exact prefixLift 602787
  have htrace : WordTrace (prefixWord ++ tailWord_602787) baseStart_602787 baseEnd_602787 := by
    simpa [prefixWord, tailWord_602787, baseEnd_602787] using wordTrace_append hprefix tailTrace_602787
  have hstable : (prefixWord ++ tailWord_602787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602787).length < 2 ^ (prefixWord ++ tailWord_602787).sum := by decide
  have hdescent : baseEnd_602787 < baseStart_602787 := by decide
  rcases family_descends (prefixWord ++ tailWord_602787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602810 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 3, 6]
def baseStart_602810 : Nat := 118140960795 + 602810 * 2 ^ 59
def prefixEnd_602810 : Nat := 4983230072969 + 3 ^ 40 * 602810 * 2
def baseEnd_602810 : Nat := 103177091112297245600911

theorem tailTrace_602810 : CollatzResearch.WordTrace tailWord_602810 prefixEnd_602810 103177091112297245600911 := by
  unfold tailWord_602810
  simp only [CollatzResearch.WordTrace]
  refine ⟨5496571736532449149175471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14657524630753197731134589 5496571736532449149175471)
  ·
    refine ⟨8244857604798673723763207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5496571736532449149175471 8244857604798673723763207)
    ·
      refine ⟨12367286407198010585644811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8244857604798673723763207 12367286407198010585644811)
      ·
        refine ⟨18550929610797015878467217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12367286407198010585644811 18550929610797015878467217)
        ·
          refine ⟨13913197208097761908850413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18550929610797015878467217 13913197208097761908850413)
          ·
            refine ⟨5217448953036660715818905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13913197208097761908850413 5217448953036660715818905)
            ·
              refine ⟨3913086714777495536864179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5217448953036660715818905 3913086714777495536864179)
              ·
                refine ⟨5869630072166243305296269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3913086714777495536864179 5869630072166243305296269)
                ·
                  refine ⟨2201111277062341239486101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5869630072166243305296269 2201111277062341239486101)
                  ·
                    refine ⟨103177091112297245600911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2201111277062341239486101 103177091112297245600911)
                    ·
                      rfl

theorem cell23_602810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 3, 6].length) (baseStart_602810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602810 prefixEnd_602810 := by exact prefixLift 602810
  have htrace : WordTrace (prefixWord ++ tailWord_602810) baseStart_602810 baseEnd_602810 := by
    simpa [prefixWord, tailWord_602810, baseEnd_602810] using wordTrace_append hprefix tailTrace_602810
  have hstable : (prefixWord ++ tailWord_602810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602810).length < 2 ^ (prefixWord ++ tailWord_602810).sum := by decide
  have hdescent : baseEnd_602810 < baseStart_602810 := by decide
  rcases family_descends (prefixWord ++ tailWord_602810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602822 : List Nat := [6, 1, 2, 1, 2, 1, 3, 2, 1, 4]
def baseStart_602822 : Nat := 118140960795 + 602822 * 2 ^ 59
def prefixEnd_602822 : Nat := 4983230072969 + 3 ^ 40 * 602822 * 2
def baseEnd_602822 : Nat := 103179145034915229950893

theorem tailTrace_602822 : CollatzResearch.WordTrace tailWord_602822 prefixEnd_602822 103179145034915229950893 := by
  unfold tailWord_602822
  simp only [CollatzResearch.WordTrace]
  refine ⟨687085144440197582691835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 14657816414724215097425813 687085144440197582691835)
  ·
    refine ⟨1030627716660296374037753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 687085144440197582691835 1030627716660296374037753)
    ·
      refine ⟨772970787495222280528315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1030627716660296374037753 772970787495222280528315)
      ·
        refine ⟨1159456181242833420792473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 772970787495222280528315 1159456181242833420792473)
        ·
          refine ⟨869592135932125065594355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1159456181242833420792473 869592135932125065594355)
          ·
            refine ⟨1304388203898187598391533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 869592135932125065594355 1304388203898187598391533)
            ·
              refine ⟨489145576461820349396825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1304388203898187598391533 489145576461820349396825)
              ·
                refine ⟨366859182346365262047619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 489145576461820349396825 366859182346365262047619)
                ·
                  refine ⟨550288773519547893071429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 366859182346365262047619 550288773519547893071429)
                  ·
                    refine ⟨103179145034915229950893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 550288773519547893071429 103179145034915229950893)
                    ·
                      rfl

theorem cell23_602822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_602822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602822 prefixEnd_602822 := by exact prefixLift 602822
  have htrace : WordTrace (prefixWord ++ tailWord_602822) baseStart_602822 baseEnd_602822 := by
    simpa [prefixWord, tailWord_602822, baseEnd_602822] using wordTrace_append hprefix tailTrace_602822
  have hstable : (prefixWord ++ tailWord_602822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602822).length < 2 ^ (prefixWord ++ tailWord_602822).sum := by decide
  have hdescent : baseEnd_602822 < baseStart_602822 := by decide
  rcases family_descends (prefixWord ++ tailWord_602822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602840 : List Nat := [2, 1, 2, 2, 3, 2, 1, 10]
def baseStart_602840 : Nat := 118140960795 + 602840 * 2 ^ 59
def prefixEnd_602840 : Nat := 4983230072969 + 3 ^ 40 * 602840 * 2
def baseEnd_602840 : Nat := 11464691768760245163985

theorem tailTrace_602840 : CollatzResearch.WordTrace tailWord_602840 prefixEnd_602840 11464691768760245163985 := by
  unfold tailWord_602840
  simp only [CollatzResearch.WordTrace]
  refine ⟨10993690568010555860146987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14658254090680741146862649 10993690568010555860146987)
  ·
    refine ⟨16490535852015833790220481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10993690568010555860146987 16490535852015833790220481)
    ·
      refine ⟨12367901889011875342665361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16490535852015833790220481 12367901889011875342665361)
      ·
        refine ⟨9275926416758906506999021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12367901889011875342665361 9275926416758906506999021)
        ·
          refine ⟨3478472406284589940124633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9275926416758906506999021 3478472406284589940124633)
          ·
            refine ⟨2608854304713442455093475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3478472406284589940124633 2608854304713442455093475)
            ·
              refine ⟨3913281457070163682640213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2608854304713442455093475 3913281457070163682640213)
              ·
                refine ⟨11464691768760245163985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3913281457070163682640213 11464691768760245163985)
                ·
                  rfl

theorem cell23_602840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 10].length) (baseStart_602840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602840 prefixEnd_602840 := by exact prefixLift 602840
  have htrace : WordTrace (prefixWord ++ tailWord_602840) baseStart_602840 baseEnd_602840 := by
    simpa [prefixWord, tailWord_602840, baseEnd_602840] using wordTrace_append hprefix tailTrace_602840
  have hstable : (prefixWord ++ tailWord_602840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602840).length < 2 ^ (prefixWord ++ tailWord_602840).sum := by decide
  have hdescent : baseEnd_602840 < baseStart_602840 := by decide
  rcases family_descends (prefixWord ++ tailWord_602840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602851 : List Nat := [1, 1, 1, 7, 1, 3, 1, 2, 1, 1, 4]
def baseStart_602851 : Nat := 118140960795 + 602851 * 2 ^ 59
def prefixEnd_602851 : Nat := 4983230072969 + 3 ^ 40 * 602851 * 2
def baseEnd_602851 : Nat := 309552326043726076390045

theorem tailTrace_602851 : CollatzResearch.WordTrace tailWord_602851 prefixEnd_602851 309552326043726076390045 := by
  unfold tailWord_602851
  simp only [CollatzResearch.WordTrace]
  refine ⟨21987782338981260598944407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14658521559320840399296271 21987782338981260598944407)
  ·
    refine ⟨32981673508471890898416611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21987782338981260598944407 32981673508471890898416611)
    ·
      refine ⟨49472510262707836347624917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32981673508471890898416611 49472510262707836347624917)
      ·
        refine ⟨1159511959282214914397459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 49472510262707836347624917 1159511959282214914397459)
        ·
          refine ⟨1739267938923322371596189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1159511959282214914397459 1739267938923322371596189)
          ·
            refine ⟨652225477096245889348571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1739267938923322371596189 652225477096245889348571)
            ·
              refine ⟨978338215644368834022857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 652225477096245889348571 978338215644368834022857)
              ·
                refine ⟨733753661733276625517143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 978338215644368834022857 733753661733276625517143)
                ·
                  refine ⟨1100630492599914938275715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 733753661733276625517143 1100630492599914938275715)
                  ·
                    refine ⟨1650945738899872407413573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1100630492599914938275715 1650945738899872407413573)
                    ·
                      refine ⟨309552326043726076390045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1650945738899872407413573 309552326043726076390045)
                      ·
                        rfl

theorem cell23_602851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_602851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602851 prefixEnd_602851 := by exact prefixLift 602851
  have htrace : WordTrace (prefixWord ++ tailWord_602851) baseStart_602851 baseEnd_602851 := by
    simpa [prefixWord, tailWord_602851, baseEnd_602851] using wordTrace_append hprefix tailTrace_602851
  have hstable : (prefixWord ++ tailWord_602851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602851).length < 2 ^ (prefixWord ++ tailWord_602851).sum := by decide
  have hdescent : baseEnd_602851 < baseStart_602851 := by decide
  rcases family_descends (prefixWord ++ tailWord_602851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602887 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 2, 7]
def baseStart_602887 : Nat := 118140960795 + 602887 * 2 ^ 59
def prefixEnd_602887 : Nat := 4983230072969 + 3 ^ 40 * 602887 * 2
def baseEnd_602887 : Nat := 103190270449095978513293

theorem tailTrace_602887 : CollatzResearch.WordTrace tailWord_602887 prefixEnd_602887 103190270449095978513293 := by
  unfold tailWord_602887
  simp only [CollatzResearch.WordTrace]
  refine ⟨21989095366850838747254915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14659396911233892498169943 21989095366850838747254915)
  ·
    refine ⟨32983643050276258120882373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21989095366850838747254915 32983643050276258120882373)
    ·
      refine ⟨6184433071926798397665445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32983643050276258120882373 6184433071926798397665445)
      ·
        refine ⟨1159581200986274699562271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6184433071926798397665445 1159581200986274699562271)
        ·
          refine ⟨1739371801479412049343407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1159581200986274699562271 1739371801479412049343407)
          ·
            refine ⟨2609057702219118074015111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1739371801479412049343407 2609057702219118074015111)
            ·
              refine ⟨3913586553328677111022667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2609057702219118074015111 3913586553328677111022667)
              ·
                refine ⟨5870379829993015666534001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3913586553328677111022667 5870379829993015666534001)
                ·
                  refine ⟨4402784872494761749900501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5870379829993015666534001 4402784872494761749900501)
                  ·
                    refine ⟨103190270449095978513293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4402784872494761749900501 103190270449095978513293)
                    ·
                      rfl

theorem cell23_602887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_602887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602887 prefixEnd_602887 := by exact prefixLift 602887
  have htrace : WordTrace (prefixWord ++ tailWord_602887) baseStart_602887 baseEnd_602887 := by
    simpa [prefixWord, tailWord_602887, baseEnd_602887] using wordTrace_append hprefix tailTrace_602887
  have hstable : (prefixWord ++ tailWord_602887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602887).length < 2 ^ (prefixWord ++ tailWord_602887).sum := by decide
  have hdescent : baseEnd_602887 < baseStart_602887 := by decide
  rcases family_descends (prefixWord ++ tailWord_602887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602922 : List Nat := [3, 1, 4, 3, 2, 1, 2, 1, 1, 2, 3]
def baseStart_602922 : Nat := 118140960795 + 602922 * 2 ^ 59
def prefixEnd_602922 : Nat := 4983230072969 + 3 ^ 40 * 602922 * 2
def baseEnd_602922 : Nat := 309588783170195298602219

theorem tailTrace_602922 : CollatzResearch.WordTrace tailWord_602922 prefixEnd_602922 309588783170195298602219 := by
  unfold tailWord_602922
  simp only [CollatzResearch.WordTrace]
  refine ⟨5497592980431009931194755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14660247947816026483186013 5497592980431009931194755)
  ·
    refine ⟨8246389470646514896792133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5497592980431009931194755 8246389470646514896792133)
    ·
      refine ⟨1546198025746221543148525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8246389470646514896792133 1546198025746221543148525)
      ·
        refine ⟨579824259654833078680697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1546198025746221543148525 579824259654833078680697)
        ·
          refine ⟨434868194741124809010523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 579824259654833078680697 434868194741124809010523)
          ·
            refine ⟨652302292111687213515785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434868194741124809010523 652302292111687213515785)
            ·
              refine ⟨489226719083765410136839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 652302292111687213515785 489226719083765410136839)
              ·
                refine ⟨733840078625648115205259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 489226719083765410136839 733840078625648115205259)
                ·
                  refine ⟨1100760117938472172807889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 733840078625648115205259 1100760117938472172807889)
                  ·
                    refine ⟨825570088453854129605917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1100760117938472172807889 825570088453854129605917)
                    ·
                      refine ⟨309588783170195298602219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 825570088453854129605917 309588783170195298602219)
                      ·
                        rfl

theorem cell23_602922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_602922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602922 prefixEnd_602922 := by exact prefixLift 602922
  have htrace : WordTrace (prefixWord ++ tailWord_602922) baseStart_602922 baseEnd_602922 := by
    simpa [prefixWord, tailWord_602922, baseEnd_602922] using wordTrace_append hprefix tailTrace_602922
  have hstable : (prefixWord ++ tailWord_602922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602922).length < 2 ^ (prefixWord ++ tailWord_602922).sum := by decide
  have hdescent : baseEnd_602922 < baseStart_602922 := by decide
  rcases family_descends (prefixWord ++ tailWord_602922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602924 : List Nat := [2, 2, 1, 1, 1, 4, 1, 4, 1, 4, 2]
def baseStart_602924 : Nat := 118140960795 + 602924 * 2 ^ 59
def prefixEnd_602924 : Nat := 4983230072969 + 3 ^ 40 * 602924 * 2
def baseEnd_602924 : Nat := 309589810131504290777209

theorem tailTrace_602924 : CollatzResearch.WordTrace tailWord_602924 prefixEnd_602924 309589810131504290777209 := by
  unfold tailWord_602924
  simp only [CollatzResearch.WordTrace]
  refine ⟨10995222433858397033175913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14660296578477862710901217 10995222433858397033175913)
  ·
    refine ⟨8246416825393797774881935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10995222433858397033175913 8246416825393797774881935)
    ·
      refine ⟨12369625238090696662322903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8246416825393797774881935 12369625238090696662322903)
      ·
        refine ⟨18554437857136044993484355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12369625238090696662322903 18554437857136044993484355)
        ·
          refine ⟨27831656785704067490226533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18554437857136044993484355 27831656785704067490226533)
          ·
            refine ⟨5218435647319512654417475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27831656785704067490226533 5218435647319512654417475)
            ·
              refine ⟨7827653470979268981626213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5218435647319512654417475 7827653470979268981626213)
              ·
                refine ⟨1467685025808612934054915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7827653470979268981626213 1467685025808612934054915)
                ·
                  refine ⟨2201527538712919401082373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1467685025808612934054915 2201527538712919401082373)
                  ·
                    refine ⟨412786413508672387702945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2201527538712919401082373 412786413508672387702945)
                    ·
                      refine ⟨309589810131504290777209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 412786413508672387702945 309589810131504290777209)
                      ·
                        rfl

theorem cell23_602924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 4, 2].length) (baseStart_602924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602924 prefixEnd_602924 := by exact prefixLift 602924
  have htrace : WordTrace (prefixWord ++ tailWord_602924) baseStart_602924 baseEnd_602924 := by
    simpa [prefixWord, tailWord_602924, baseEnd_602924] using wordTrace_append hprefix tailTrace_602924
  have hstable : (prefixWord ++ tailWord_602924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602924).length < 2 ^ (prefixWord ++ tailWord_602924).sum := by decide
  have hdescent : baseEnd_602924 < baseStart_602924 := by decide
  rcases family_descends (prefixWord ++ tailWord_602924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_602947 : List Nat := [1, 1, 1, 3, 1, 4, 4, 1, 7]
def baseStart_602947 : Nat := 118140960795 + 602947 * 2 ^ 59
def prefixEnd_602947 : Nat := 4983230072969 + 3 ^ 40 * 602947 * 2
def baseEnd_602947 : Nat := 34400180020728633421067

theorem tailTrace_602947 : CollatzResearch.WordTrace tailWord_602947 prefixEnd_602947 34400180020728633421067 := by
  unfold tailWord_602947
  simp only [CollatzResearch.WordTrace]
  refine ⟨21991283746633468994439095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14660855831088979329626063 21991283746633468994439095)
  ·
    refine ⟨32986925619950203491658643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21991283746633468994439095 32986925619950203491658643)
    ·
      refine ⟨49480388429925305237487965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32986925619950203491658643 49480388429925305237487965)
      ·
        refine ⟨18555145661221989464057987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49480388429925305237487965 18555145661221989464057987)
        ·
          refine ⟨27832718491832984196086981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18555145661221989464057987 27832718491832984196086981)
          ·
            refine ⟨5218634717218684536766309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27832718491832984196086981 5218634717218684536766309)
            ·
              refine ⟨978494009478503350643683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5218634717218684536766309 978494009478503350643683)
              ·
                refine ⟨1467741014217755025965525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 978494009478503350643683 1467741014217755025965525)
                ·
                  refine ⟨34400180020728633421067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1467741014217755025965525 34400180020728633421067)
                  ·
                    rfl

theorem cell23_602947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 7].length) (baseStart_602947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_602947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_602947 prefixEnd_602947 := by exact prefixLift 602947
  have htrace : WordTrace (prefixWord ++ tailWord_602947) baseStart_602947 baseEnd_602947 := by
    simpa [prefixWord, tailWord_602947, baseEnd_602947] using wordTrace_append hprefix tailTrace_602947
  have hstable : (prefixWord ++ tailWord_602947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_602947).length < 2 ^ (prefixWord ++ tailWord_602947).sum := by decide
  have hdescent : baseEnd_602947 < baseStart_602947 := by decide
  rcases family_descends (prefixWord ++ tailWord_602947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603077 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 1, 6, 5]
def baseStart_603077 : Nat := 118140960795 + 603077 * 2 ^ 59
def prefixEnd_603077 : Nat := 4983230072969 + 3 ^ 40 * 603077 * 2
def baseEnd_603077 : Nat := 309668372671642192164005

theorem tailTrace_603077 : CollatzResearch.WordTrace tailWord_603077 prefixEnd_603077 309668372671642192164005 := by
  unfold tailWord_603077
  simp only [CollatzResearch.WordTrace]
  refine ⟨21996025236162501196671485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14664016824108334131114323 21996025236162501196671485)
  ·
    refine ⟨8248509463560937948751807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21996025236162501196671485 8248509463560937948751807)
    ·
      refine ⟨12372764195341406923127711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8248509463560937948751807 12372764195341406923127711)
      ·
        refine ⟨18559146293012110384691567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12372764195341406923127711 18559146293012110384691567)
        ·
          refine ⟨27838719439518165577037351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18559146293012110384691567 27838719439518165577037351)
          ·
            refine ⟨41758079159277248365556027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27838719439518165577037351 41758079159277248365556027)
            ·
              refine ⟨62637118738915872548334041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41758079159277248365556027 62637118738915872548334041)
              ·
                refine ⟨46977839054186904411250531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62637118738915872548334041 46977839054186904411250531)
                ·
                  refine ⟨70466758581280356616875797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46977839054186904411250531 70466758581280356616875797)
                  ·
                    refine ⟨3303129308497516716416053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70466758581280356616875797 3303129308497516716416053)
                    ·
                      refine ⟨309668372671642192164005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3303129308497516716416053 309668372671642192164005)
                      ·
                        rfl

theorem cell23_603077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_603077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603077 prefixEnd_603077 := by exact prefixLift 603077
  have htrace : WordTrace (prefixWord ++ tailWord_603077) baseStart_603077 baseEnd_603077 := by
    simpa [prefixWord, tailWord_603077, baseEnd_603077] using wordTrace_append hprefix tailTrace_603077
  have hstable : (prefixWord ++ tailWord_603077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603077).length < 2 ^ (prefixWord ++ tailWord_603077).sum := by decide
  have hdescent : baseEnd_603077 < baseStart_603077 := by decide
  rcases family_descends (prefixWord ++ tailWord_603077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603084 : List Nat := [2, 2, 1, 4, 1, 1, 1, 3, 3, 5]
def baseStart_603084 : Nat := 118140960795 + 603084 * 2 ^ 59
def prefixEnd_603084 : Nat := 4983230072969 + 3 ^ 40 * 603084 * 2
def baseEnd_603084 : Nat := 103223989012074554925491

theorem tailTrace_603084 : CollatzResearch.WordTrace tailWord_603084 prefixEnd_603084 103223989012074554925491 := by
  unfold tailWord_603084
  simp only [CollatzResearch.WordTrace]
  refine ⟨10998140273568570696088153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14664187031424760928117537 10998140273568570696088153)
  ·
    refine ⟨8248605205176428022066115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10998140273568570696088153 8248605205176428022066115)
    ·
      refine ⟨12372907807764642033099173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8248605205176428022066115 12372907807764642033099173)
      ·
        refine ⟨2319920213955870381206095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12372907807764642033099173 2319920213955870381206095)
        ·
          refine ⟨3479880320933805571809143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2319920213955870381206095 3479880320933805571809143)
          ·
            refine ⟨5219820481400708357713715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3479880320933805571809143 5219820481400708357713715)
            ·
              refine ⟨7829730722101062536570573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5219820481400708357713715 7829730722101062536570573)
              ·
                refine ⟨2936149020787898451213965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7829730722101062536570573 2936149020787898451213965)
                ·
                  refine ⟨1101055882795461919205237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2936149020787898451213965 1101055882795461919205237)
                  ·
                    refine ⟨103223989012074554925491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1101055882795461919205237 103223989012074554925491)
                    ·
                      rfl

theorem cell23_603084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 3, 5].length) (baseStart_603084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603084 prefixEnd_603084 := by exact prefixLift 603084
  have htrace : WordTrace (prefixWord ++ tailWord_603084) baseStart_603084 baseEnd_603084 := by
    simpa [prefixWord, tailWord_603084, baseEnd_603084] using wordTrace_append hprefix tailTrace_603084
  have hstable : (prefixWord ++ tailWord_603084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603084).length < 2 ^ (prefixWord ++ tailWord_603084).sum := by decide
  have hdescent : baseEnd_603084 < baseStart_603084 := by decide
  rcases family_descends (prefixWord ++ tailWord_603084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603144 : List Nat := [2, 1, 3, 2, 1, 4, 1, 9]
def baseStart_603144 : Nat := 118140960795 + 603144 * 2 ^ 59
def prefixEnd_603144 : Nat := 4983230072969 + 3 ^ 40 * 603144 * 2
def baseEnd_603144 : Nat := 11470473180573830741711

theorem tailTrace_603144 : CollatzResearch.WordTrace tailWord_603144 prefixEnd_603144 11470473180573830741711 := by
  unfold tailWord_603144
  simp only [CollatzResearch.WordTrace]
  refine ⟨10999234463459885819680243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14665645951279847759573657 10999234463459885819680243)
  ·
    refine ⟨16498851695189828729520365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10999234463459885819680243 16498851695189828729520365)
    ·
      refine ⟨6187069385696185773570137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16498851695189828729520365 6187069385696185773570137)
      ·
        refine ⟨4640302039272139330177603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6187069385696185773570137 4640302039272139330177603)
        ·
          refine ⟨6960453058908208995266405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4640302039272139330177603 6960453058908208995266405)
          ·
            refine ⟨1305084948545289186612451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6960453058908208995266405 1305084948545289186612451)
            ·
              refine ⟨1957627422817933779918677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1305084948545289186612451 1957627422817933779918677)
              ·
                refine ⟨11470473180573830741711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1957627422817933779918677 11470473180573830741711)
                ·
                  rfl

theorem cell23_603144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 9].length) (baseStart_603144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603144 prefixEnd_603144 := by exact prefixLift 603144
  have htrace : WordTrace (prefixWord ++ tailWord_603144) baseStart_603144 baseEnd_603144 := by
    simpa [prefixWord, tailWord_603144, baseEnd_603144] using wordTrace_append hprefix tailTrace_603144
  have hstable : (prefixWord ++ tailWord_603144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603144).length < 2 ^ (prefixWord ++ tailWord_603144).sum := by decide
  have hdescent : baseEnd_603144 < baseStart_603144 := by decide
  rcases family_descends (prefixWord ++ tailWord_603144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603172 : List Nat := [2, 3, 1, 4, 1, 3, 1, 1, 3, 2, 2]
def baseStart_603172 : Nat := 118140960795 + 603172 * 2 ^ 59
def prefixEnd_603172 : Nat := 4983230072969 + 3 ^ 40 * 603172 * 2
def baseEnd_603172 : Nat := 309717153333819320476069

theorem tailTrace_603172 : CollatzResearch.WordTrace tailWord_603172 prefixEnd_603172 309717153333819320476069 := by
  unfold tailWord_603172
  simp only [CollatzResearch.WordTrace]
  refine ⟨10999745085409166210689885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14666326780545554947586513 10999745085409166210689885)
  ·
    refine ⟨4124904407028437329008707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10999745085409166210689885 4124904407028437329008707)
    ·
      refine ⟨6187356610542655993513061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4124904407028437329008707 6187356610542655993513061)
      ·
        refine ⟨1160129364476747998783699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6187356610542655993513061 1160129364476747998783699)
        ·
          refine ⟨1740194046715121998175549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1160129364476747998783699 1740194046715121998175549)
          ·
            refine ⟨652572767518170749315831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1740194046715121998175549 652572767518170749315831)
            ·
              refine ⟨978859151277256123973747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 652572767518170749315831 978859151277256123973747)
              ·
                refine ⟨1468288726915884185960621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 978859151277256123973747 1468288726915884185960621)
                ·
                  refine ⟨550608272593456569735233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1468288726915884185960621 550608272593456569735233)
                  ·
                    refine ⟨412956204445092427301425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 550608272593456569735233 412956204445092427301425)
                    ·
                      refine ⟨309717153333819320476069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 412956204445092427301425 309717153333819320476069)
                      ·
                        rfl

theorem cell23_603172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_603172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603172 prefixEnd_603172 := by exact prefixLift 603172
  have htrace : WordTrace (prefixWord ++ tailWord_603172) baseStart_603172 baseEnd_603172 := by
    simpa [prefixWord, tailWord_603172, baseEnd_603172] using wordTrace_append hprefix tailTrace_603172
  have hstable : (prefixWord ++ tailWord_603172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603172).length < 2 ^ (prefixWord ++ tailWord_603172).sum := by decide
  have hdescent : baseEnd_603172 < baseStart_603172 := by decide
  rcases family_descends (prefixWord ++ tailWord_603172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603228 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 3, 4, 2]
def baseStart_603228 : Nat := 118140960795 + 603228 * 2 ^ 59
def prefixEnd_603228 : Nat := 4983230072969 + 3 ^ 40 * 603228 * 2
def baseEnd_603228 : Nat := 309745908250471101375811

theorem tailTrace_603228 : CollatzResearch.WordTrace tailWord_603228 prefixEnd_603228 309745908250471101375811 := by
  unfold tailWord_603228
  simp only [CollatzResearch.WordTrace]
  refine ⟨11000766329307726992709169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14667688439076969323612225 11000766329307726992709169)
  ·
    refine ⟨8250574746980795244531877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11000766329307726992709169 8250574746980795244531877)
    ·
      refine ⟨1546982765058899108349727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8250574746980795244531877 1546982765058899108349727)
      ·
        refine ⟨2320474147588348662524591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1546982765058899108349727 2320474147588348662524591)
        ·
          refine ⟨3480711221382522993786887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2320474147588348662524591 3480711221382522993786887)
          ·
            refine ⟨5221066832073784490680331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3480711221382522993786887 5221066832073784490680331)
            ·
              refine ⟨7831600248110676736020497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5221066832073784490680331 7831600248110676736020497)
              ·
                refine ⟨5873700186083007552015373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7831600248110676736020497 5873700186083007552015373)
                ·
                  refine ⟨2202637569781127832005765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5873700186083007552015373 2202637569781127832005765)
                  ·
                    refine ⟨412994544333961468501081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2202637569781127832005765 412994544333961468501081)
                    ·
                      refine ⟨309745908250471101375811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 412994544333961468501081 309745908250471101375811)
                      ·
                        rfl

theorem cell23_603228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_603228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603228 prefixEnd_603228 := by exact prefixLift 603228
  have htrace : WordTrace (prefixWord ++ tailWord_603228) baseStart_603228 baseEnd_603228 := by
    simpa [prefixWord, tailWord_603228, baseEnd_603228] using wordTrace_append hprefix tailTrace_603228
  have hstable : (prefixWord ++ tailWord_603228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603228).length < 2 ^ (prefixWord ++ tailWord_603228).sum := by decide
  have hdescent : baseEnd_603228 < baseStart_603228 := by decide
  rcases family_descends (prefixWord ++ tailWord_603228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603241 : List Nat := [1, 2, 1, 1, 1, 7, 1, 1, 2, 2, 4]
def baseStart_603241 : Nat := 118140960795 + 603241 * 2 ^ 59
def prefixEnd_603241 : Nat := 4983230072969 + 3 ^ 40 * 603241 * 2
def baseEnd_603241 : Nat := 309752583498979550513251

theorem tailTrace_603241 : CollatzResearch.WordTrace tailWord_603241 prefixEnd_603241 309752583498979550513251 := by
  unfold tailWord_603241
  simp only [CollatzResearch.WordTrace]
  refine ⟨22002006807568357205641577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14668004538378904803761051 22002006807568357205641577)
  ·
    refine ⟨16501505105676267904231183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22002006807568357205641577 16501505105676267904231183)
    ·
      refine ⟨24752257658514401856346775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16501505105676267904231183 24752257658514401856346775)
      ·
        refine ⟨37128386487771602784520163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24752257658514401856346775 37128386487771602784520163)
        ·
          refine ⟨55692579731657404176780245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37128386487771602784520163 55692579731657404176780245)
          ·
            refine ⟨1305294837460720410393287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 55692579731657404176780245 1305294837460720410393287)
            ·
              refine ⟨1957942256191080615589931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1305294837460720410393287 1957942256191080615589931)
              ·
                refine ⟨2936913384286620923384897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1957942256191080615589931 2936913384286620923384897)
                ·
                  refine ⟨2202685038214965692538673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2936913384286620923384897 2202685038214965692538673)
                  ·
                    refine ⟨1652013778661224269404005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2202685038214965692538673 1652013778661224269404005)
                    ·
                      refine ⟨309752583498979550513251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1652013778661224269404005 309752583498979550513251)
                      ·
                        rfl

theorem cell23_603241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 2, 4].length) (baseStart_603241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603241 prefixEnd_603241 := by exact prefixLift 603241
  have htrace : WordTrace (prefixWord ++ tailWord_603241) baseStart_603241 baseEnd_603241 := by
    simpa [prefixWord, tailWord_603241, baseEnd_603241] using wordTrace_append hprefix tailTrace_603241
  have hstable : (prefixWord ++ tailWord_603241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603241).length < 2 ^ (prefixWord ++ tailWord_603241).sum := by decide
  have hdescent : baseEnd_603241 < baseStart_603241 := by decide
  rcases family_descends (prefixWord ++ tailWord_603241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603245 : List Nat := [1, 5, 1, 1, 2, 3, 2, 1, 1, 4, 2]
def baseStart_603245 : Nat := 118140960795 + 603245 * 2 ^ 59
def prefixEnd_603245 : Nat := 4983230072969 + 3 ^ 40 * 603245 * 2
def baseEnd_603245 : Nat := 309754637421597534863233

theorem tailTrace_603245 : CollatzResearch.WordTrace tailWord_603245 prefixEnd_603245 309754637421597534863233 := by
  unfold tailWord_603245
  simp only [CollatzResearch.WordTrace]
  refine ⟨22002152699553865888787189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14668101799702577259191459 22002152699553865888787189)
  ·
    refine ⟨2062701815583174927073799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22002152699553865888787189 2062701815583174927073799)
    ·
      refine ⟨3094052723374762390610699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2062701815583174927073799 3094052723374762390610699)
      ·
        refine ⟨4641079085062143585916049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3094052723374762390610699 4641079085062143585916049)
        ·
          refine ⟨3480809313796607689437037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4641079085062143585916049 3480809313796607689437037)
          ·
            refine ⟨1305303492673727883538889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3480809313796607689437037 1305303492673727883538889)
            ·
              refine ⟨978977619505295912654167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1305303492673727883538889 978977619505295912654167)
              ·
                refine ⟨1468466429257943868981251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 978977619505295912654167 1468466429257943868981251)
                ·
                  refine ⟨2202699643886915803471877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1468466429257943868981251 2202699643886915803471877)
                  ·
                    refine ⟨413006183228796713150977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2202699643886915803471877 413006183228796713150977)
                    ·
                      refine ⟨309754637421597534863233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 413006183228796713150977 309754637421597534863233)
                      ·
                        rfl

theorem cell23_603245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_603245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603245 prefixEnd_603245 := by exact prefixLift 603245
  have htrace : WordTrace (prefixWord ++ tailWord_603245) baseStart_603245 baseEnd_603245 := by
    simpa [prefixWord, tailWord_603245, baseEnd_603245] using wordTrace_append hprefix tailTrace_603245
  have hstable : (prefixWord ++ tailWord_603245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603245).length < 2 ^ (prefixWord ++ tailWord_603245).sum := by decide
  have hdescent : baseEnd_603245 < baseStart_603245 := by decide
  rcases family_descends (prefixWord ++ tailWord_603245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603261 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 1, 5, 3]
def baseStart_603261 : Nat := 118140960795 + 603261 * 2 ^ 59
def prefixEnd_603261 : Nat := 4983230072969 + 3 ^ 40 * 603261 * 2
def baseEnd_603261 : Nat := 309762853112069472263159

theorem tailTrace_603261 : CollatzResearch.WordTrace tailWord_603261 prefixEnd_603261 309762853112069472263159 := by
  unfold tailWord_603261
  simp only [CollatzResearch.WordTrace]
  refine ⟨22002736267495900621369637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14668490844997267080913091 22002736267495900621369637)
  ·
    refine ⟨4125513050155481366506807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22002736267495900621369637 4125513050155481366506807)
    ·
      refine ⟨6188269575233222049760211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4125513050155481366506807 6188269575233222049760211)
      ·
        refine ⟨9282404362849833074640317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6188269575233222049760211 9282404362849833074640317)
        ·
          refine ⟨3480901636068687402990119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9282404362849833074640317 3480901636068687402990119)
          ·
            refine ⟨5221352454103031104485179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3480901636068687402990119 5221352454103031104485179)
            ·
              refine ⟨7832028681154546656727769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5221352454103031104485179 7832028681154546656727769)
              ·
                refine ⟨5874021510865909992545827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7832028681154546656727769 5874021510865909992545827)
                ·
                  refine ⟨8811032266298864988818741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5874021510865909992545827 8811032266298864988818741)
                  ·
                    refine ⟨826034274965518592701757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8811032266298864988818741 826034274965518592701757)
                    ·
                      refine ⟨309762853112069472263159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 826034274965518592701757 309762853112069472263159)
                      ·
                        rfl

theorem cell23_603261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_603261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603261 prefixEnd_603261 := by exact prefixLift 603261
  have htrace : WordTrace (prefixWord ++ tailWord_603261) baseStart_603261 baseEnd_603261 := by
    simpa [prefixWord, tailWord_603261, baseEnd_603261] using wordTrace_append hprefix tailTrace_603261
  have hstable : (prefixWord ++ tailWord_603261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603261).length < 2 ^ (prefixWord ++ tailWord_603261).sum := by decide
  have hdescent : baseEnd_603261 < baseStart_603261 := by decide
  rcases family_descends (prefixWord ++ tailWord_603261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603268 : List Nat := [2, 3, 2, 1, 2, 2, 1, 5, 5]
def baseStart_603268 : Nat := 118140960795 + 603268 * 2 ^ 59
def prefixEnd_603268 : Nat := 4983230072969 + 3 ^ 40 * 603268 * 2
def baseEnd_603268 : Nat := 34418494164072327208403

theorem tailTrace_603268 : CollatzResearch.WordTrace tailWord_603268 prefixEnd_603268 34418494164072327208403 := by
  unfold tailWord_603268
  simp only [CollatzResearch.WordTrace]
  refine ⟨11001495789235270408437229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14668661052313693877916305 11001495789235270408437229)
  ·
    refine ⟨4125560920963226403163961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11001495789235270408437229 4125560920963226403163961)
    ·
      refine ⟨3094170690722419802372971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4125560920963226403163961 3094170690722419802372971)
      ·
        refine ⟨4641256036083629703559457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3094170690722419802372971 4641256036083629703559457)
        ·
          refine ⟨3480942027062722277669593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4641256036083629703559457 3480942027062722277669593)
          ·
            refine ⟨2610706520297041708252195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3480942027062722277669593 2610706520297041708252195)
            ·
              refine ⟨3916059780445562562378293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2610706520297041708252195 3916059780445562562378293)
              ·
                refine ⟨367130604416771490222965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3916059780445562562378293 367130604416771490222965)
                ·
                  refine ⟨34418494164072327208403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 367130604416771490222965 34418494164072327208403)
                  ·
                    rfl

theorem cell23_603268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 5, 5].length) (baseStart_603268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603268 prefixEnd_603268 := by exact prefixLift 603268
  have htrace : WordTrace (prefixWord ++ tailWord_603268) baseStart_603268 baseEnd_603268 := by
    simpa [prefixWord, tailWord_603268, baseEnd_603268] using wordTrace_append hprefix tailTrace_603268
  have hstable : (prefixWord ++ tailWord_603268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603268).length < 2 ^ (prefixWord ++ tailWord_603268).sum := by decide
  have hdescent : baseEnd_603268 < baseStart_603268 := by decide
  rcases family_descends (prefixWord ++ tailWord_603268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603278 : List Nat := [4, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3]
def baseStart_603278 : Nat := 118140960795 + 603278 * 2 ^ 59
def prefixEnd_603278 : Nat := 4983230072969 + 3 ^ 40 * 603278 * 2
def baseEnd_603278 : Nat := 309771582283195905750581

theorem tailTrace_603278 : CollatzResearch.WordTrace tailWord_603278 prefixEnd_603278 309771582283195905750581 := by
  unfold tailWord_603278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2750419538554289065592311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14668904205622875016492325 2750419538554289065592311)
  ·
    refine ⟨4125629307831433598388467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2750419538554289065592311 4125629307831433598388467)
    ·
      refine ⟨6188443961747150397582701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4125629307831433598388467 6188443961747150397582701)
      ·
        refine ⟨2320666485655181399093513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6188443961747150397582701 2320666485655181399093513)
        ·
          refine ⟨1740499864241386049320135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2320666485655181399093513 1740499864241386049320135)
          ·
            refine ⟨2610749796362079073980203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1740499864241386049320135 2610749796362079073980203)
            ·
              refine ⟨3916124694543118610970305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2610749796362079073980203 3916124694543118610970305)
              ·
                refine ⟨2937093520907338958227729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3916124694543118610970305 2937093520907338958227729)
                ·
                  refine ⟨2202820140680504218670797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2937093520907338958227729 2202820140680504218670797)
                  ·
                    refine ⟨826057552755189082001549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2202820140680504218670797 826057552755189082001549)
                    ·
                      refine ⟨309771582283195905750581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 826057552755189082001549 309771582283195905750581)
                      ·
                        rfl

theorem cell23_603278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_603278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603278 prefixEnd_603278 := by exact prefixLift 603278
  have htrace : WordTrace (prefixWord ++ tailWord_603278) baseStart_603278 baseEnd_603278 := by
    simpa [prefixWord, tailWord_603278, baseEnd_603278] using wordTrace_append hprefix tailTrace_603278
  have hstable : (prefixWord ++ tailWord_603278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603278).length < 2 ^ (prefixWord ++ tailWord_603278).sum := by decide
  have hdescent : baseEnd_603278 < baseStart_603278 := by decide
  rcases family_descends (prefixWord ++ tailWord_603278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603301 : List Nat := [1, 3, 1, 2, 1, 4, 1, 2, 1, 3, 4]
def baseStart_603301 : Nat := 118140960795 + 603301 * 2 ^ 59
def prefixEnd_603301 : Nat := 4983230072969 + 3 ^ 40 * 603301 * 2
def baseEnd_603301 : Nat := 309783392338249315762975

theorem tailTrace_603301 : CollatzResearch.WordTrace tailWord_603301 prefixEnd_603301 309783392338249315762975 := by
  unfold tailWord_603301
  simp only [CollatzResearch.WordTrace]
  refine ⟨22004195187350987452825757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14669463458233991635217171 22004195187350987452825757)
  ·
    refine ⟨8251573195256620294809659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22004195187350987452825757 8251573195256620294809659)
    ·
      refine ⟨12377359792884930442214489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8251573195256620294809659 12377359792884930442214489)
      ·
        refine ⟨9283019844663697831660867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12377359792884930442214489 9283019844663697831660867)
        ·
          refine ⟨13924529766995546747491301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9283019844663697831660867 13924529766995546747491301)
          ·
            refine ⟨2610849331311665015154619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13924529766995546747491301 2610849331311665015154619)
            ·
              refine ⟨3916273996967497522731929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2610849331311665015154619 3916273996967497522731929)
              ·
                refine ⟨2937205497725623142048947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3916273996967497522731929 2937205497725623142048947)
                ·
                  refine ⟨4405808246588434713073421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2937205497725623142048947 4405808246588434713073421)
                  ·
                    refine ⟨1652178092470663017402533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4405808246588434713073421 1652178092470663017402533)
                    ·
                      refine ⟨309783392338249315762975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1652178092470663017402533 309783392338249315762975)
                      ·
                        rfl

theorem cell23_603301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_603301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603301 prefixEnd_603301 := by exact prefixLift 603301
  have htrace : WordTrace (prefixWord ++ tailWord_603301) baseStart_603301 baseEnd_603301 := by
    simpa [prefixWord, tailWord_603301, baseEnd_603301] using wordTrace_append hprefix tailTrace_603301
  have hstable : (prefixWord ++ tailWord_603301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603301).length < 2 ^ (prefixWord ++ tailWord_603301).sum := by decide
  have hdescent : baseEnd_603301 < baseStart_603301 := by decide
  rcases family_descends (prefixWord ++ tailWord_603301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603338 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 4, 2, 3]
def baseStart_603338 : Nat := 118140960795 + 603338 * 2 ^ 59
def prefixEnd_603338 : Nat := 4983230072969 + 3 ^ 40 * 603338 * 2
def baseEnd_603338 : Nat := 309802391122465671000305

theorem tailTrace_603338 : CollatzResearch.WordTrace tailWord_603338 prefixEnd_603338 309802391122465671000305 := by
  unfold tailWord_603338
  simp only [CollatzResearch.WordTrace]
  refine ⟨5501386172054235692980667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14670363125477961847948445 5501386172054235692980667)
  ·
    refine ⟨8252079258081353539471001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5501386172054235692980667 8252079258081353539471001)
    ·
      refine ⟨6189059443561015154603251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8252079258081353539471001 6189059443561015154603251)
      ·
        refine ⟨9283589165341522731904877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6189059443561015154603251 9283589165341522731904877)
        ·
          refine ⟨3481345937003071024464329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9283589165341522731904877 3481345937003071024464329)
          ·
            refine ⟨2611009452752303268348247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3481345937003071024464329 2611009452752303268348247)
            ·
              refine ⟨3916514179128454902522371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2611009452752303268348247 3916514179128454902522371)
              ·
                refine ⟨5874771268692682353783557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3916514179128454902522371 5874771268692682353783557)
                ·
                  refine ⟨1101519612879877941334417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5874771268692682353783557 1101519612879877941334417)
                  ·
                    refine ⟨826139709659908456000813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1101519612879877941334417 826139709659908456000813)
                    ·
                      refine ⟨309802391122465671000305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 826139709659908456000813 309802391122465671000305)
                      ·
                        rfl

theorem cell23_603338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_603338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603338 prefixEnd_603338 := by exact prefixLift 603338
  have htrace : WordTrace (prefixWord ++ tailWord_603338) baseStart_603338 baseEnd_603338 := by
    simpa [prefixWord, tailWord_603338, baseEnd_603338] using wordTrace_append hprefix tailTrace_603338
  have hstable : (prefixWord ++ tailWord_603338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603338).length < 2 ^ (prefixWord ++ tailWord_603338).sum := by decide
  have hdescent : baseEnd_603338 < baseStart_603338 := by decide
  rcases family_descends (prefixWord ++ tailWord_603338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603395 : List Nat := [1, 1, 1, 3, 2, 4, 2, 2, 2, 3, 2]
def baseStart_603395 : Nat := 118140960795 + 603395 * 2 ^ 59
def prefixEnd_603395 : Nat := 4983230072969 + 3 ^ 40 * 603395 * 2
def baseEnd_603395 : Nat := 309831659519771947987543

theorem tailTrace_603395 : CollatzResearch.WordTrace tailWord_603395 prefixEnd_603395 309831659519771947987543 := by
  unfold tailWord_603395
  simp only [CollatzResearch.WordTrace]
  refine ⟨22007623649010441506747639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14671749099340294337831759 22007623649010441506747639)
  ·
    refine ⟨33011435473515662260121459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22007623649010441506747639 33011435473515662260121459)
    ·
      refine ⟨49517153210273493390182189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33011435473515662260121459 49517153210273493390182189)
      ·
        refine ⟨18568932453852560021318321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49517153210273493390182189 18568932453852560021318321)
        ·
          refine ⟨13926699340389420015988741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18568932453852560021318321 13926699340389420015988741)
          ·
            refine ⟨2611256126323016252997889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13926699340389420015988741 2611256126323016252997889)
            ·
              refine ⟨1958442094742262189748417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2611256126323016252997889 1958442094742262189748417)
              ·
                refine ⟨1468831571056696642311313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1958442094742262189748417 1468831571056696642311313)
                ·
                  refine ⟨1101623678292522481733485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1468831571056696642311313 1101623678292522481733485)
                  ·
                    refine ⟨413108879359695930650057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1101623678292522481733485 413108879359695930650057)
                    ·
                      refine ⟨309831659519771947987543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 413108879359695930650057 309831659519771947987543)
                      ·
                        rfl

theorem cell23_603395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 3, 2].length) (baseStart_603395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603395 prefixEnd_603395 := by exact prefixLift 603395
  have htrace : WordTrace (prefixWord ++ tailWord_603395) baseStart_603395 baseEnd_603395 := by
    simpa [prefixWord, tailWord_603395, baseEnd_603395] using wordTrace_append hprefix tailTrace_603395
  have hstable : (prefixWord ++ tailWord_603395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603395).length < 2 ^ (prefixWord ++ tailWord_603395).sum := by decide
  have hdescent : baseEnd_603395 < baseStart_603395 := by decide
  rcases family_descends (prefixWord ++ tailWord_603395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603401 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 3, 6]
def baseStart_603401 : Nat := 118140960795 + 603401 * 2 ^ 59
def prefixEnd_603401 : Nat := 4983230072969 + 3 ^ 40 * 603401 * 2
def baseEnd_603401 : Nat := 103278246801232974837505

theorem tailTrace_603401 : CollatzResearch.WordTrace tailWord_603401 prefixEnd_603401 103278246801232974837505 := by
  unfold tailWord_603401
  simp only [CollatzResearch.WordTrace]
  refine ⟨22007842486988704531466057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14671894991325803020977371 22007842486988704531466057)
  ·
    refine ⟨16505881865241528398599543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22007842486988704531466057 16505881865241528398599543)
    ·
      refine ⟨24758822797862292597899315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16505881865241528398599543 24758822797862292597899315)
      ·
        refine ⟨37138234196793438896848973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24758822797862292597899315 37138234196793438896848973)
        ·
          refine ⟨13926837823797539586318365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37138234196793438896848973 13926837823797539586318365)
          ·
            refine ⟨5222564183924077344869387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13926837823797539586318365 5222564183924077344869387)
            ·
              refine ⟨7833846275886116017304081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5222564183924077344869387 7833846275886116017304081)
              ·
                refine ⟨5875384706914587012978061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7833846275886116017304081 5875384706914587012978061)
                ·
                  refine ⟨2203269265092970129866773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5875384706914587012978061 2203269265092970129866773)
                  ·
                    refine ⟨103278246801232974837505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2203269265092970129866773 103278246801232974837505)
                    ·
                      rfl

theorem cell23_603401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 6].length) (baseStart_603401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603401 prefixEnd_603401 := by exact prefixLift 603401
  have htrace : WordTrace (prefixWord ++ tailWord_603401) baseStart_603401 baseEnd_603401 := by
    simpa [prefixWord, tailWord_603401, baseEnd_603401] using wordTrace_append hprefix tailTrace_603401
  have hstable : (prefixWord ++ tailWord_603401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603401).length < 2 ^ (prefixWord ++ tailWord_603401).sum := by decide
  have hdescent : baseEnd_603401 < baseStart_603401 := by decide
  rcases family_descends (prefixWord ++ tailWord_603401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603418 : List Nat := [3, 1, 1, 3, 3, 1, 1, 3, 1, 6]
def baseStart_603418 : Nat := 118140960795 + 603418 * 2 ^ 59
def prefixEnd_603418 : Nat := 4983230072969 + 3 ^ 40 * 603418 * 2
def baseEnd_603418 : Nat := 103281156524941785999979

theorem tailTrace_603418 : CollatzResearch.WordTrace tailWord_603418 prefixEnd_603418 103281156524941785999979 := by
  unfold tailWord_603418
  simp only [CollatzResearch.WordTrace]
  refine ⟨5502115631981779108708727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14672308351951410956556605 5502115631981779108708727)
  ·
    refine ⟨8253173447972668663063091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5502115631981779108708727 8253173447972668663063091)
    ·
      refine ⟨12379760171959002994594637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8253173447972668663063091 12379760171959002994594637)
      ·
        refine ⟨4642410064484626122972989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12379760171959002994594637 4642410064484626122972989)
        ·
          refine ⟨1740903774181734796114871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4642410064484626122972989 1740903774181734796114871)
          ·
            refine ⟨2611355661272602194172307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1740903774181734796114871 2611355661272602194172307)
            ·
              refine ⟨3917033491908903291258461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2611355661272602194172307 3917033491908903291258461)
              ·
                refine ⟨1468887559465838734221923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3917033491908903291258461 1468887559465838734221923)
                ·
                  refine ⟨2203331339198758101332885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1468887559465838734221923 2203331339198758101332885)
                  ·
                    refine ⟨103281156524941785999979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2203331339198758101332885 103281156524941785999979)
                    ·
                      rfl

theorem cell23_603418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 1, 6].length) (baseStart_603418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603418 prefixEnd_603418 := by exact prefixLift 603418
  have htrace : WordTrace (prefixWord ++ tailWord_603418) baseStart_603418 baseEnd_603418 := by
    simpa [prefixWord, tailWord_603418, baseEnd_603418] using wordTrace_append hprefix tailTrace_603418
  have hstable : (prefixWord ++ tailWord_603418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603418).length < 2 ^ (prefixWord ++ tailWord_603418).sum := by decide
  have hdescent : baseEnd_603418 < baseStart_603418 := by decide
  rcases family_descends (prefixWord ++ tailWord_603418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603442 : List Nat := [3, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4]
def baseStart_603442 : Nat := 118140960795 + 603442 * 2 ^ 59
def prefixEnd_603442 : Nat := 4983230072969 + 3 ^ 40 * 603442 * 2
def baseEnd_603442 : Nat := 309855793110533264099827

theorem tailTrace_603442 : CollatzResearch.WordTrace tailWord_603442 prefixEnd_603442 309855793110533264099827 := by
  unfold tailWord_603442
  simp only [CollatzResearch.WordTrace]
  refine ⟨5502334469960042133427145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14672891919893445689139053 5502334469960042133427145)
  ·
    refine ⟨4126750852470031600070359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5502334469960042133427145 4126750852470031600070359)
    ·
      refine ⟨6190126278705047400105539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4126750852470031600070359 6190126278705047400105539)
      ·
        refine ⟨9285189418057571100158309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6190126278705047400105539 9285189418057571100158309)
        ·
          refine ⟨1740973015885794581279683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9285189418057571100158309 1740973015885794581279683)
          ·
            refine ⟨2611459523828691871919525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1740973015885794581279683 2611459523828691871919525)
            ·
              refine ⟨489648660717879725984911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2611459523828691871919525 489648660717879725984911)
              ·
                refine ⟨734472991076819588977367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 489648660717879725984911 734472991076819588977367)
                ·
                  refine ⟨1101709486615229383466051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 734472991076819588977367 1101709486615229383466051)
                  ·
                    refine ⟨1652564229922844075199077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1101709486615229383466051 1652564229922844075199077)
                    ·
                      refine ⟨309855793110533264099827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1652564229922844075199077 309855793110533264099827)
                      ·
                        rfl

theorem cell23_603442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4].length) (baseStart_603442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603442 prefixEnd_603442 := by exact prefixLift 603442
  have htrace : WordTrace (prefixWord ++ tailWord_603442) baseStart_603442 baseEnd_603442 := by
    simpa [prefixWord, tailWord_603442, baseEnd_603442] using wordTrace_append hprefix tailTrace_603442
  have hstable : (prefixWord ++ tailWord_603442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603442).length < 2 ^ (prefixWord ++ tailWord_603442).sum := by decide
  have hdescent : baseEnd_603442 < baseStart_603442 := by decide
  rcases family_descends (prefixWord ++ tailWord_603442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603452 : List Nat := [2, 2, 2, 2, 1, 5, 1, 2, 2, 4]
def baseStart_603452 : Nat := 118140960795 + 603452 * 2 ^ 59
def prefixEnd_603452 : Nat := 4983230072969 + 3 ^ 40 * 603452 * 2
def baseEnd_603452 : Nat := 103286975972359408324927

theorem tailTrace_603452 : CollatzResearch.WordTrace tailWord_603452 prefixEnd_603452 103286975972359408324927 := by
  unfold tailWord_603452
  simp only [CollatzResearch.WordTrace]
  refine ⟨11004851304901970120786305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14673135073202626827715073 11004851304901970120786305)
  ·
    refine ⟨8253638478676477590589729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11004851304901970120786305 8253638478676477590589729)
    ·
      refine ⟨6190228859007358192942297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8253638478676477590589729 6190228859007358192942297)
      ·
        refine ⟨4642671644255518644706723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6190228859007358192942297 4642671644255518644706723)
        ·
          refine ⟨6964007466383277967060085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4642671644255518644706723 6964007466383277967060085)
          ·
            refine ⟨652875699973432309411883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6964007466383277967060085 652875699973432309411883)
            ·
              refine ⟨979313549960148464117825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 652875699973432309411883 979313549960148464117825)
              ·
                refine ⟨734485162470111348088369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 979313549960148464117825 734485162470111348088369)
                ·
                  refine ⟨550863871852583511066277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 734485162470111348088369 550863871852583511066277)
                  ·
                    refine ⟨103286975972359408324927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 550863871852583511066277 103286975972359408324927)
                    ·
                      rfl

theorem cell23_603452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_603452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603452 prefixEnd_603452 := by exact prefixLift 603452
  have htrace : WordTrace (prefixWord ++ tailWord_603452) baseStart_603452 baseEnd_603452 := by
    simpa [prefixWord, tailWord_603452, baseEnd_603452] using wordTrace_append hprefix tailTrace_603452
  have hstable : (prefixWord ++ tailWord_603452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603452).length < 2 ^ (prefixWord ++ tailWord_603452).sum := by decide
  have hdescent : baseEnd_603452 < baseStart_603452 := by decide
  rcases family_descends (prefixWord ++ tailWord_603452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603461 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 1, 9]
def baseStart_603461 : Nat := 118140960795 + 603461 * 2 ^ 59
def prefixEnd_603461 : Nat := 4983230072969 + 3 ^ 40 * 603461 * 2
def baseEnd_603461 : Nat := 103288516414322896587413

theorem tailTrace_603461 : CollatzResearch.WordTrace tailWord_603461 prefixEnd_603461 103288516414322896587413 := by
  unfold tailWord_603461
  simp only [CollatzResearch.WordTrace]
  refine ⟨22010030866771334778650237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14673353911180889852433491 22010030866771334778650237)
  ·
    refine ⟨8253761575039250541993839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22010030866771334778650237 8253761575039250541993839)
    ·
      refine ⟨12380642362558875812990759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8253761575039250541993839 12380642362558875812990759)
      ·
        refine ⟨18570963543838313719486139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12380642362558875812990759 18570963543838313719486139)
        ·
          refine ⟨27856445315757470579229209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18570963543838313719486139 27856445315757470579229209)
          ·
            refine ⟨20892333986818102934421907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27856445315757470579229209 20892333986818102934421907)
            ·
              refine ⟨31338500980227154401632861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20892333986818102934421907 31338500980227154401632861)
              ·
                refine ⟨11751937867585182900612323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31338500980227154401632861 11751937867585182900612323)
                ·
                  refine ⟨17627906801377774350918485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11751937867585182900612323 17627906801377774350918485)
                  ·
                    refine ⟨103288516414322896587413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 17627906801377774350918485 103288516414322896587413)
                    ·
                      rfl

theorem cell23_603461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 9].length) (baseStart_603461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603461 prefixEnd_603461 := by exact prefixLift 603461
  have htrace : WordTrace (prefixWord ++ tailWord_603461) baseStart_603461 baseEnd_603461 := by
    simpa [prefixWord, tailWord_603461, baseEnd_603461] using wordTrace_append hprefix tailTrace_603461
  have hstable : (prefixWord ++ tailWord_603461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603461).length < 2 ^ (prefixWord ++ tailWord_603461).sum := by decide
  have hdescent : baseEnd_603461 < baseStart_603461 := by decide
  rcases family_descends (prefixWord ++ tailWord_603461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603469 : List Nat := [1, 6, 1, 3, 1, 2, 1, 1, 1, 6]
def baseStart_603469 : Nat := 118140960795 + 603469 * 2 ^ 59
def prefixEnd_603469 : Nat := 4983230072969 + 3 ^ 40 * 603469 * 2
def baseEnd_603469 : Nat := 103289885696068219487401

theorem tailTrace_603469 : CollatzResearch.WordTrace tailWord_603469 prefixEnd_603469 103289885696068219487401 := by
  unfold tailWord_603469
  simp only [CollatzResearch.WordTrace]
  refine ⟨22010322650742352144941461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14673548433828234763294307 22010322650742352144941461)
  ·
    refine ⟨1031733874253547756794131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22010322650742352144941461 1031733874253547756794131)
    ·
      refine ⟨1547600811380321635191197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1031733874253547756794131 1547600811380321635191197)
      ·
        refine ⟨580350304267620613196699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1547600811380321635191197 580350304267620613196699)
        ·
          refine ⟨870525456401430919795049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 580350304267620613196699 870525456401430919795049)
          ·
            refine ⟨652894092301073189846287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 870525456401430919795049 652894092301073189846287)
            ·
              refine ⟨979341138451609784769431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 652894092301073189846287 979341138451609784769431)
              ·
                refine ⟨1469011707677414677154147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 979341138451609784769431 1469011707677414677154147)
                ·
                  refine ⟨2203517561516122015731221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1469011707677414677154147 2203517561516122015731221)
                  ·
                    refine ⟨103289885696068219487401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2203517561516122015731221 103289885696068219487401)
                    ·
                      rfl

theorem cell23_603469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_603469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603469 prefixEnd_603469 := by exact prefixLift 603469
  have htrace : WordTrace (prefixWord ++ tailWord_603469) baseStart_603469 baseEnd_603469 := by
    simpa [prefixWord, tailWord_603469, baseEnd_603469] using wordTrace_append hprefix tailTrace_603469
  have hstable : (prefixWord ++ tailWord_603469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603469).length < 2 ^ (prefixWord ++ tailWord_603469).sum := by decide
  have hdescent : baseEnd_603469 < baseStart_603469 := by decide
  rcases family_descends (prefixWord ++ tailWord_603469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603488 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 5]
def baseStart_603488 : Nat := 118140960795 + 603488 * 2 ^ 59
def prefixEnd_603488 : Nat := 4983230072969 + 3 ^ 40 * 603488 * 2
def baseEnd_603488 : Nat := 309879413220640084124615

theorem tailTrace_603488 : CollatzResearch.WordTrace tailWord_603488 prefixEnd_603488 309879413220640084124615 := by
  unfold tailWord_603488
  simp only [CollatzResearch.WordTrace]
  refine ⟨11005507818836759194941559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14674010425115678926588745 11005507818836759194941559)
  ·
    refine ⟨16508261728255138792412339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11005507818836759194941559 16508261728255138792412339)
    ·
      refine ⟨24762392592382708188618509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16508261728255138792412339 24762392592382708188618509)
      ·
        refine ⟨9285897222143515570731941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24762392592382708188618509 9285897222143515570731941)
        ·
          refine ⟨1741105729151909169512239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9285897222143515570731941 1741105729151909169512239)
          ·
            refine ⟨2611658593727863754268359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1741105729151909169512239 2611658593727863754268359)
            ·
              refine ⟨3917487890591795631402539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2611658593727863754268359 3917487890591795631402539)
              ·
                refine ⟨5876231835887693447103809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3917487890591795631402539 5876231835887693447103809)
                ·
                  refine ⟨4407173876915770085327857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5876231835887693447103809 4407173876915770085327857)
                  ·
                    refine ⟨3305380407686827563995893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4407173876915770085327857 3305380407686827563995893)
                    ·
                      refine ⟨309879413220640084124615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3305380407686827563995893 309879413220640084124615)
                      ·
                        rfl

theorem cell23_603488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_603488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603488 prefixEnd_603488 := by exact prefixLift 603488
  have htrace : WordTrace (prefixWord ++ tailWord_603488) baseStart_603488 baseEnd_603488 := by
    simpa [prefixWord, tailWord_603488, baseEnd_603488] using wordTrace_append hprefix tailTrace_603488
  have hstable : (prefixWord ++ tailWord_603488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603488).length < 2 ^ (prefixWord ++ tailWord_603488).sum := by decide
  have hdescent : baseEnd_603488 < baseStart_603488 := by decide
  rcases family_descends (prefixWord ++ tailWord_603488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603555 : List Nat := [1, 1, 1, 4, 1, 3, 2, 5, 5]
def baseStart_603555 : Nat := 118140960795 + 603555 * 2 ^ 59
def prefixEnd_603555 : Nat := 4983230072969 + 3 ^ 40 * 603555 * 2
def baseEnd_603555 : Nat := 34434868491610146887423

theorem tailTrace_603555 : CollatzResearch.WordTrace tailWord_603555 prefixEnd_603555 34434868491610146887423 := by
  unfold tailWord_603555
  simp only [CollatzResearch.WordTrace]
  refine ⟨22013459328430788832572119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14675639552287192555048079 22013459328430788832572119)
  ·
    refine ⟨33020188992646183248858179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22013459328430788832572119 33020188992646183248858179)
    ·
      refine ⟨49530283488969274873287269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33020188992646183248858179 49530283488969274873287269)
      ·
        refine ⟨9286928154181739038741363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49530283488969274873287269 9286928154181739038741363)
        ·
          refine ⟨13930392231272608558112045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9286928154181739038741363 13930392231272608558112045)
          ·
            refine ⟨5223897086727228209292017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13930392231272608558112045 5223897086727228209292017)
            ·
              refine ⟨3917922815045421156969013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5223897086727228209292017 3917922815045421156969013)
              ·
                refine ⟨367305263910508233465845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3917922815045421156969013 367305263910508233465845)
                ·
                  refine ⟨34434868491610146887423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 367305263910508233465845 34434868491610146887423)
                  ·
                    rfl

theorem cell23_603555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 5, 5].length) (baseStart_603555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603555 prefixEnd_603555 := by exact prefixLift 603555
  have htrace : WordTrace (prefixWord ++ tailWord_603555) baseStart_603555 baseEnd_603555 := by
    simpa [prefixWord, tailWord_603555, baseEnd_603555] using wordTrace_append hprefix tailTrace_603555
  have hstable : (prefixWord ++ tailWord_603555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603555).length < 2 ^ (prefixWord ++ tailWord_603555).sum := by decide
  have hdescent : baseEnd_603555 < baseStart_603555 := by decide
  rcases family_descends (prefixWord ++ tailWord_603555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603568 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 4, 5]
def baseStart_603568 : Nat := 118140960795 + 603568 * 2 ^ 59
def prefixEnd_603568 : Nat := 4983230072969 + 3 ^ 40 * 603568 * 2
def baseEnd_603568 : Nat := 103306830557666590374749

theorem tailTrace_603568 : CollatzResearch.WordTrace tailWord_603568 prefixEnd_603568 103306830557666590374749 := by
  unfold tailWord_603568
  simp only [CollatzResearch.WordTrace]
  refine ⟨11006966738691846026397679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14675955651589128035196905 11006966738691846026397679)
  ·
    refine ⟨16510450108037769039596519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11006966738691846026397679 16510450108037769039596519)
    ·
      refine ⟨24765675162056653559394779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16510450108037769039596519 24765675162056653559394779)
      ·
        refine ⟨37148512743084980339092169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24765675162056653559394779 37148512743084980339092169)
        ·
          refine ⟨27861384557313735254319127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37148512743084980339092169 27861384557313735254319127)
          ·
            refine ⟨41792076835970602881478691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27861384557313735254319127 41792076835970602881478691)
            ·
              refine ⟨62688115253955904322218037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41792076835970602881478691 62688115253955904322218037)
              ·
                refine ⟨5877010805058366030207941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62688115253955904322218037 5877010805058366030207941)
                ·
                  refine ⟨1101939525948443630663989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5877010805058366030207941 1101939525948443630663989)
                  ·
                    refine ⟨103306830557666590374749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1101939525948443630663989 103306830557666590374749)
                    ·
                      rfl

theorem cell23_603568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 4, 5].length) (baseStart_603568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603568 prefixEnd_603568 := by exact prefixLift 603568
  have htrace : WordTrace (prefixWord ++ tailWord_603568) baseStart_603568 baseEnd_603568 := by
    simpa [prefixWord, tailWord_603568, baseEnd_603568] using wordTrace_append hprefix tailTrace_603568
  have hstable : (prefixWord ++ tailWord_603568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603568).length < 2 ^ (prefixWord ++ tailWord_603568).sum := by decide
  have hdescent : baseEnd_603568 < baseStart_603568 := by decide
  rcases family_descends (prefixWord ++ tailWord_603568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603575 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 1, 7, 2]
def baseStart_603575 : Nat := 118140960795 + 603575 * 2 ^ 59
def prefixEnd_603575 : Nat := 4983230072969 + 3 ^ 40 * 603575 * 2
def baseEnd_603575 : Nat := 309924086037581243736715

theorem tailTrace_603575 : CollatzResearch.WordTrace tailWord_603575 prefixEnd_603575 309924086037581243736715 := by
  unfold tailWord_603575
  simp only [CollatzResearch.WordTrace]
  refine ⟨22014188788358332248300179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14676125858905554832200119 22014188788358332248300179)
  ·
    refine ⟨33021283182537498372450269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22014188788358332248300179 33021283182537498372450269)
    ·
      refine ⟨12382981193451561889668851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33021283182537498372450269 12382981193451561889668851)
      ·
        refine ⟨18574471790177342834503277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12382981193451561889668851 18574471790177342834503277)
        ·
          refine ⟨6965426921316503562938729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18574471790177342834503277 6965426921316503562938729)
          ·
            refine ⟨5224070190987377672204047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6965426921316503562938729 5224070190987377672204047)
            ·
              refine ⟨7836105286481066508306071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5224070190987377672204047 7836105286481066508306071)
              ·
                refine ⟨11754157929721599762459107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7836105286481066508306071 11754157929721599762459107)
                ·
                  refine ⟨17631236894582399643688661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11754157929721599762459107 17631236894582399643688661)
                  ·
                    refine ⟨413232114716774991648953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17631236894582399643688661 413232114716774991648953)
                    ·
                      refine ⟨309924086037581243736715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 413232114716774991648953 309924086037581243736715)
                      ·
                        rfl

theorem cell23_603575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 7, 2].length) (baseStart_603575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603575 prefixEnd_603575 := by exact prefixLift 603575
  have htrace : WordTrace (prefixWord ++ tailWord_603575) baseStart_603575 baseEnd_603575 := by
    simpa [prefixWord, tailWord_603575, baseEnd_603575] using wordTrace_append hprefix tailTrace_603575
  have hstable : (prefixWord ++ tailWord_603575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603575).length < 2 ^ (prefixWord ++ tailWord_603575).sum := by decide
  have hdescent : baseEnd_603575 < baseStart_603575 := by decide
  rcases family_descends (prefixWord ++ tailWord_603575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603605 : List Nat := [1, 3, 2, 3, 1, 1, 3, 1, 1, 3, 4]
def baseStart_603605 : Nat := 118140960795 + 603605 * 2 ^ 59
def prefixEnd_603605 : Nat := 4983230072969 + 3 ^ 40 * 603605 * 2
def baseEnd_603605 : Nat := 309939490457216126361577

theorem tailTrace_603605 : CollatzResearch.WordTrace tailWord_603605 prefixEnd_603605 309939490457216126361577 := by
  unfold tailWord_603605
  simp only [CollatzResearch.WordTrace]
  refine ⟨22015282978249647371892269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14676855318833098247928179 22015282978249647371892269)
  ·
    refine ⟨8255731116843617764459601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22015282978249647371892269 8255731116843617764459601)
    ·
      refine ⟨6191798337632713323344701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8255731116843617764459601 6191798337632713323344701)
      ·
        refine ⟨2321924376612267496254263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6191798337632713323344701 2321924376612267496254263)
        ·
          refine ⟨3482886564918401244381395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2321924376612267496254263 3482886564918401244381395)
          ·
            refine ⟨5224329847377601866572093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3482886564918401244381395 5224329847377601866572093)
            ·
              refine ⟨1959123692766600699964535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5224329847377601866572093 1959123692766600699964535)
              ·
                refine ⟨2938685539149901049946803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1959123692766600699964535 2938685539149901049946803)
                ·
                  refine ⟨4408028308724851574920205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2938685539149901049946803 4408028308724851574920205)
                  ·
                    refine ⟨1653010615771819340595077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4408028308724851574920205 1653010615771819340595077)
                    ·
                      refine ⟨309939490457216126361577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1653010615771819340595077 309939490457216126361577)
                      ·
                        rfl

theorem cell23_603605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_603605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603605 prefixEnd_603605 := by exact prefixLift 603605
  have htrace : WordTrace (prefixWord ++ tailWord_603605) baseStart_603605 baseEnd_603605 := by
    simpa [prefixWord, tailWord_603605, baseEnd_603605] using wordTrace_append hprefix tailTrace_603605
  have hstable : (prefixWord ++ tailWord_603605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603605).length < 2 ^ (prefixWord ++ tailWord_603605).sum := by decide
  have hdescent : baseEnd_603605 < baseStart_603605 := by decide
  rcases family_descends (prefixWord ++ tailWord_603605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603615 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 5, 4]
def baseStart_603615 : Nat := 118140960795 + 603615 * 2 ^ 59
def prefixEnd_603615 : Nat := 4983230072969 + 3 ^ 40 * 603615 * 2
def baseEnd_603615 : Nat := 103314875087920362412177

theorem tailTrace_603615 : CollatzResearch.WordTrace tailWord_603615 prefixEnd_603615 103314875087920362412177 := by
  unfold tailWord_603615
  simp only [CollatzResearch.WordTrace]
  refine ⟨22015647708213419079756299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14677098472142279386504199 22015647708213419079756299)
  ·
    refine ⟨33023471562320128619634449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22015647708213419079756299 33023471562320128619634449)
    ·
      refine ⟨24767603671740096464725837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33023471562320128619634449 24767603671740096464725837)
      ·
        refine ⟨9287851376902536174272189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24767603671740096464725837 9287851376902536174272189)
        ·
          refine ⟨3482944266338451065352071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9287851376902536174272189 3482944266338451065352071)
          ·
            refine ⟨5224416399507676598028107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3482944266338451065352071 5224416399507676598028107)
            ·
              refine ⟨7836624599261514897042161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5224416399507676598028107 7836624599261514897042161)
              ·
                refine ⟨5877468449446136172781621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7836624599261514897042161 5877468449446136172781621)
                ·
                  refine ⟨551012667135575266198277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5877468449446136172781621 551012667135575266198277)
                  ·
                    refine ⟨103314875087920362412177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 551012667135575266198277 103314875087920362412177)
                    ·
                      rfl

theorem cell23_603615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 5, 4].length) (baseStart_603615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603615 prefixEnd_603615 := by exact prefixLift 603615
  have htrace : WordTrace (prefixWord ++ tailWord_603615) baseStart_603615 baseEnd_603615 := by
    simpa [prefixWord, tailWord_603615, baseEnd_603615] using wordTrace_append hprefix tailTrace_603615
  have hstable : (prefixWord ++ tailWord_603615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603615).length < 2 ^ (prefixWord ++ tailWord_603615).sum := by decide
  have hdescent : baseEnd_603615 < baseStart_603615 := by decide
  rcases family_descends (prefixWord ++ tailWord_603615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603632 : List Nat := [2, 1, 1, 1, 3, 5, 2, 1, 3, 4]
def baseStart_603632 : Nat := 118140960795 + 603632 * 2 ^ 59
def prefixEnd_603632 : Nat := 4983230072969 + 3 ^ 40 * 603632 * 2
def baseEnd_603632 : Nat := 103317784811629173574651

theorem tailTrace_603632 : CollatzResearch.WordTrace tailWord_603632 prefixEnd_603632 103317784811629173574651 := by
  unfold tailWord_603632
  simp only [CollatzResearch.WordTrace]
  refine ⟨11008133874575915491562575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14677511832767887322083433 11008133874575915491562575)
  ·
    refine ⟨16512200811863873237343863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11008133874575915491562575 16512200811863873237343863)
    ·
      refine ⟨24768301217795809856015795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16512200811863873237343863 24768301217795809856015795)
      ·
        refine ⟨37152451826693714784023693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24768301217795809856015795 37152451826693714784023693)
        ·
          refine ⟨13932169435010143044008885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37152451826693714784023693 13932169435010143044008885)
          ·
            refine ⟨1306140884532200910375833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13932169435010143044008885 1306140884532200910375833)
            ·
              refine ⟨979605663399150682781875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1306140884532200910375833 979605663399150682781875)
              ·
                refine ⟨1469408495098726024172813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 979605663399150682781875 1469408495098726024172813)
                ·
                  refine ⟨551028185662022259064805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1469408495098726024172813 551028185662022259064805)
                  ·
                    refine ⟨103317784811629173574651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 551028185662022259064805 103317784811629173574651)
                    ·
                      rfl

theorem cell23_603632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 3, 4].length) (baseStart_603632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603632 prefixEnd_603632 := by exact prefixLift 603632
  have htrace : WordTrace (prefixWord ++ tailWord_603632) baseStart_603632 baseEnd_603632 := by
    simpa [prefixWord, tailWord_603632, baseEnd_603632] using wordTrace_append hprefix tailTrace_603632
  have hstable : (prefixWord ++ tailWord_603632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603632).length < 2 ^ (prefixWord ++ tailWord_603632).sum := by decide
  have hdescent : baseEnd_603632 < baseStart_603632 := by decide
  rcases family_descends (prefixWord ++ tailWord_603632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603729 : List Nat := [1, 2, 2, 1, 3, 2, 5, 1, 1, 1, 4]
def baseStart_603729 : Nat := 118140960795 + 603729 * 2 ^ 59
def prefixEnd_603729 : Nat := 4983230072969 + 3 ^ 40 * 603729 * 2
def baseEnd_603729 : Nat := 310003162058373641211007

theorem tailTrace_603729 : CollatzResearch.WordTrace tailWord_603729 prefixEnd_603729 310003162058373641211007 := by
  unfold tailWord_603729
  simp only [CollatzResearch.WordTrace]
  refine ⟨22019805629800416549406241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14679870419866944366270827 22019805629800416549406241)
  ·
    refine ⟨16514854222350312412054681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22019805629800416549406241 16514854222350312412054681)
    ·
      refine ⟨12386140666762734309041011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16514854222350312412054681 12386140666762734309041011)
      ·
        refine ⟨18579211000144101463561517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12386140666762734309041011 18579211000144101463561517)
        ·
          refine ⟨6967204125054038048835569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18579211000144101463561517 6967204125054038048835569)
          ·
            refine ⟨5225403093790528536626677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6967204125054038048835569 5225403093790528536626677)
            ·
              refine ⟨489881540042862050308751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5225403093790528536626677 489881540042862050308751)
              ·
                refine ⟨734822310064293075463127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 489881540042862050308751 734822310064293075463127)
                ·
                  refine ⟨1102233465096439613194691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 734822310064293075463127 1102233465096439613194691)
                  ·
                    refine ⟨1653350197644659419792037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1102233465096439613194691 1653350197644659419792037)
                    ·
                      refine ⟨310003162058373641211007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1653350197644659419792037 310003162058373641211007)
                      ·
                        rfl

theorem cell23_603729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 1, 1, 4].length) (baseStart_603729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603729 prefixEnd_603729 := by exact prefixLift 603729
  have htrace : WordTrace (prefixWord ++ tailWord_603729) baseStart_603729 baseEnd_603729 := by
    simpa [prefixWord, tailWord_603729, baseEnd_603729] using wordTrace_append hprefix tailTrace_603729
  have hstable : (prefixWord ++ tailWord_603729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603729).length < 2 ^ (prefixWord ++ tailWord_603729).sum := by decide
  have hdescent : baseEnd_603729 < baseStart_603729 := by decide
  rcases family_descends (prefixWord ++ tailWord_603729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603734 : List Nat := [5, 2, 2, 2, 2, 1, 2, 2, 1, 4]
def baseStart_603734 : Nat := 118140960795 + 603734 * 2 ^ 59
def prefixEnd_603734 : Nat := 4983230072969 + 3 ^ 40 * 603734 * 2
def baseEnd_603734 : Nat := 103335243153882040549495

theorem tailTrace_603734 : CollatzResearch.WordTrace tailWord_603734 prefixEnd_603734 103335243153882040549495 := by
  unfold tailWord_603734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1376249249673893900208641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14679991996521534935558837 1376249249673893900208641)
  ·
    refine ⟨1032186937255420425156481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1376249249673893900208641 1032186937255420425156481)
    ·
      refine ⟨774140202941565318867361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1032186937255420425156481 774140202941565318867361)
      ·
        refine ⟨580605152206173989150521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 774140202941565318867361 580605152206173989150521)
        ·
          refine ⟨435453864154630491862891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 580605152206173989150521 435453864154630491862891)
          ·
            refine ⟨653180796231945737794337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435453864154630491862891 653180796231945737794337)
            ·
              refine ⟨489885597173959303345753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 653180796231945737794337 489885597173959303345753)
              ·
                refine ⟨367414197880469477509315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 489885597173959303345753 367414197880469477509315)
                ·
                  refine ⟨551121296820704216263973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 367414197880469477509315 551121296820704216263973)
                  ·
                    refine ⟨103335243153882040549495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 551121296820704216263973 103335243153882040549495)
                    ·
                      rfl

theorem cell23_603734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_603734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603734 prefixEnd_603734 := by exact prefixLift 603734
  have htrace : WordTrace (prefixWord ++ tailWord_603734) baseStart_603734 baseEnd_603734 := by
    simpa [prefixWord, tailWord_603734, baseEnd_603734] using wordTrace_append hprefix tailTrace_603734
  have hstable : (prefixWord ++ tailWord_603734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603734).length < 2 ^ (prefixWord ++ tailWord_603734).sum := by decide
  have hdescent : baseEnd_603734 < baseStart_603734 := by decide
  rcases family_descends (prefixWord ++ tailWord_603734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_603740 : List Nat := [2, 2, 4, 1, 2, 3, 2, 2, 1, 1, 3]
def baseStart_603740 : Nat := 118140960795 + 603740 * 2 ^ 59
def prefixEnd_603740 : Nat := 4983230072969 + 3 ^ 40 * 603740 * 2
def baseEnd_603740 : Nat := 310008810345573098173457

theorem tailTrace_603740 : CollatzResearch.WordTrace tailWord_603740 prefixEnd_603740 310008810345573098173457 := by
  unfold tailWord_603740
  simp only [CollatzResearch.WordTrace]
  refine ⟨11010103416380282714028337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14680137888507043618704449 11010103416380282714028337)
  ·
    refine ⟨8257577562285212035521253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11010103416380282714028337 8257577562285212035521253)
    ·
      refine ⟨1548295792928477256660235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8257577562285212035521253 1548295792928477256660235)
      ·
        refine ⟨2322443689392715884990353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1548295792928477256660235 2322443689392715884990353)
        ·
          refine ⟨1741832767044536913742765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2322443689392715884990353 1741832767044536913742765)
          ·
            refine ⟨653187287641701342653537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1741832767044536913742765 653187287641701342653537)
            ·
              refine ⟨489890465731276006990153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 653187287641701342653537 489890465731276006990153)
              ·
                refine ⟨367417849298457005242615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 489890465731276006990153 367417849298457005242615)
                ·
                  refine ⟨551126773947685507863923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 367417849298457005242615 551126773947685507863923)
                  ·
                    refine ⟨826690160921528261795885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 551126773947685507863923 826690160921528261795885)
                    ·
                      refine ⟨310008810345573098173457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 826690160921528261795885 310008810345573098173457)
                      ·
                        rfl

theorem cell23_603740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_603740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_603740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_603740 prefixEnd_603740 := by exact prefixLift 603740
  have htrace : WordTrace (prefixWord ++ tailWord_603740) baseStart_603740 baseEnd_603740 := by
    simpa [prefixWord, tailWord_603740, baseEnd_603740] using wordTrace_append hprefix tailTrace_603740
  have hstable : (prefixWord ++ tailWord_603740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_603740).length < 2 ^ (prefixWord ++ tailWord_603740).sum := by decide
  have hdescent : baseEnd_603740 < baseStart_603740 := by decide
  rcases family_descends (prefixWord ++ tailWord_603740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
