import V185TrunkScan23Chunk0440

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2607406 : List Nat := [4, 1, 3, 3, 2, 1, 2, 1, 2, 1, 3]
def baseStart_2607406 : Nat := 118140960795 + 2607406 * 2 ^ 59
def prefixEnd_2607406 : Nat := 4983230072969 + 3 ^ 40 * 2607406 * 2
def baseEnd_2607406 : Nat := 1338852539417130745733765

theorem tailTrace_2607406 : CollatzResearch.WordTrace tailWord_2607406 prefixEnd_2607406 1338852539417130745733765 := by
  unfold tailWord_2607406
  simp only [CollatzResearch.WordTrace]
  refine ⟨11887488698977605792126259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63399939727880564224673381 11887488698977605792126259)
  ·
    refine ⟨17831233048466408688189389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11887488698977605792126259 17831233048466408688189389)
    ·
      refine ⟨6686712393174903258071021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17831233048466408688189389 6686712393174903258071021)
      ·
        refine ⟨2507517147440588721776633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6686712393174903258071021 2507517147440588721776633)
        ·
          refine ⟨1880637860580441541332475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2507517147440588721776633 1880637860580441541332475)
          ·
            refine ⟨2820956790870662311998713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1880637860580441541332475 2820956790870662311998713)
            ·
              refine ⟨2115717593152996733999035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2820956790870662311998713 2115717593152996733999035)
              ·
                refine ⟨3173576389729495100998553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2115717593152996733999035 3173576389729495100998553)
                ·
                  refine ⟨2380182292297121325748915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3173576389729495100998553 2380182292297121325748915)
                  ·
                    refine ⟨3570273438445681988623373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2380182292297121325748915 3570273438445681988623373)
                    ·
                      refine ⟨1338852539417130745733765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3570273438445681988623373 1338852539417130745733765)
                      ·
                        rfl

theorem cell23_2607406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_2607406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607406 prefixEnd_2607406 := by exact prefixLift 2607406
  have htrace : WordTrace (prefixWord ++ tailWord_2607406) baseStart_2607406 baseEnd_2607406 := by
    simpa [prefixWord, tailWord_2607406, baseEnd_2607406] using wordTrace_append hprefix tailTrace_2607406
  have hstable : (prefixWord ++ tailWord_2607406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607406).length < 2 ^ (prefixWord ++ tailWord_2607406).sum := by decide
  have hdescent : baseEnd_2607406 < baseStart_2607406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607412 : List Nat := [2, 5, 1, 1, 1, 3, 1, 3, 2, 2, 2]
def baseStart_2607412 : Nat := 118140960795 + 2607412 * 2 ^ 59
def prefixEnd_2607412 : Nat := 4983230072969 + 3 ^ 40 * 2607412 * 2
def baseEnd_2607412 : Nat := 1338855620301057722258737

theorem tailTrace_2607412 : CollatzResearch.WordTrace tailWord_2607412 prefixEnd_2607412 1338855620301057722258737 := by
  unfold tailWord_2607412
  simp only [CollatzResearch.WordTrace]
  refine ⟨47550064214899554680864245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63400085619866072907818993 47550064214899554680864245)
  ·
    refine ⟨4457818520146833251331023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47550064214899554680864245 4457818520146833251331023)
    ·
      refine ⟨6686727780220249876996535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4457818520146833251331023 6686727780220249876996535)
      ·
        refine ⟨10030091670330374815494803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6686727780220249876996535 10030091670330374815494803)
        ·
          refine ⟨15045137505495562223242205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10030091670330374815494803 15045137505495562223242205)
          ·
            refine ⟨5641926564560835833715827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15045137505495562223242205 5641926564560835833715827)
            ·
              refine ⟨8462889846841253750573741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5641926564560835833715827 8462889846841253750573741)
              ·
                refine ⟨3173583692565470156465153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8462889846841253750573741 3173583692565470156465153)
                ·
                  refine ⟨2380187769424102617348865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3173583692565470156465153 2380187769424102617348865)
                  ·
                    refine ⟨1785140827068076963011649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2380187769424102617348865 1785140827068076963011649)
                    ·
                      refine ⟨1338855620301057722258737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1785140827068076963011649 1338855620301057722258737)
                      ·
                        rfl

theorem cell23_2607412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_2607412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607412 prefixEnd_2607412 := by exact prefixLift 2607412
  have htrace : WordTrace (prefixWord ++ tailWord_2607412) baseStart_2607412 baseEnd_2607412 := by
    simpa [prefixWord, tailWord_2607412, baseEnd_2607412] using wordTrace_append hprefix tailTrace_2607412
  have hstable : (prefixWord ++ tailWord_2607412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607412).length < 2 ^ (prefixWord ++ tailWord_2607412).sum := by decide
  have hdescent : baseEnd_2607412 < baseStart_2607412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607431 : List Nat := [1, 1, 4, 1, 2, 2, 4, 1, 2, 5]
def baseStart_2607431 : Nat := 118140960795 + 2607431 * 2 ^ 59
def prefixEnd_2607431 : Nat := 4983230072969 + 3 ^ 40 * 2607431 * 2
def baseEnd_2607431 : Nat := 446288458811164382640383

theorem tailTrace_2607431 : CollatzResearch.WordTrace tailWord_2607431 prefixEnd_2607431 446288458811164382640383 := by
  unfold tailWord_2607431
  simp only [CollatzResearch.WordTrace]
  refine ⟨95100821416730275606670147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63400547611153517071113431 95100821416730275606670147)
  ·
    refine ⟨142651232125095413410005221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95100821416730275606670147 142651232125095413410005221)
    ·
      refine ⟨26747106023455390014375979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142651232125095413410005221 26747106023455390014375979)
      ·
        refine ⟨40120659035183085021563969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26747106023455390014375979 40120659035183085021563969)
        ·
          refine ⟨30090494276387313766172977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40120659035183085021563969 30090494276387313766172977)
          ·
            refine ⟨22567870707290485324629733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30090494276387313766172977 22567870707290485324629733)
            ·
              refine ⟨4231475757616965998368075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22567870707290485324629733 4231475757616965998368075)
              ·
                refine ⟨6347213636425448997552113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4231475757616965998368075 6347213636425448997552113)
                ·
                  refine ⟨4760410227319086748164085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6347213636425448997552113 4760410227319086748164085)
                  ·
                    refine ⟨446288458811164382640383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4760410227319086748164085 446288458811164382640383)
                    ·
                      rfl

theorem cell23_2607431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_2607431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607431 prefixEnd_2607431 := by exact prefixLift 2607431
  have htrace : WordTrace (prefixWord ++ tailWord_2607431) baseStart_2607431 baseEnd_2607431 := by
    simpa [prefixWord, tailWord_2607431, baseEnd_2607431] using wordTrace_append hprefix tailTrace_2607431
  have hstable : (prefixWord ++ tailWord_2607431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607431).length < 2 ^ (prefixWord ++ tailWord_2607431).sum := by decide
  have hdescent : baseEnd_2607431 < baseStart_2607431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607495 : List Nat := [1, 1, 4, 2, 2, 1, 4, 3, 1, 4]
def baseStart_2607495 : Nat := 118140960795 + 2607495 * 2 ^ 59
def prefixEnd_2607495 : Nat := 4983230072969 + 3 ^ 40 * 2607495 * 2
def baseEnd_2607495 : Nat := 446299413065126965840285

theorem tailTrace_2607495 : CollatzResearch.WordTrace tailWord_2607495 prefixEnd_2607495 446299413065126965840285 := by
  unfold tailWord_2607495
  simp only [CollatzResearch.WordTrace]
  refine ⟨95103155688498414536999939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63402103792332276357999959 95103155688498414536999939)
  ·
    refine ⟨142654733532747621805499909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95103155688498414536999939 142654733532747621805499909)
    ·
      refine ⟨26747762537390179088531233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142654733532747621805499909 26747762537390179088531233)
      ·
        refine ⟨20060821903042634316398425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26747762537390179088531233 20060821903042634316398425)
        ·
          refine ⟨15045616427281975737298819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20060821903042634316398425 15045616427281975737298819)
          ·
            refine ⟨22568424640922963605948229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15045616427281975737298819 22568424640922963605948229)
            ·
              refine ⟨4231579620173055676115293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22568424640922963605948229 4231579620173055676115293)
              ·
                refine ⟨1586842357564895878543235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4231579620173055676115293 1586842357564895878543235)
                ·
                  refine ⟨2380263536347343817814853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1586842357564895878543235 2380263536347343817814853)
                  ·
                    refine ⟨446299413065126965840285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2380263536347343817814853 446299413065126965840285)
                    ·
                      rfl

theorem cell23_2607495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 3, 1, 4].length) (baseStart_2607495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607495 prefixEnd_2607495 := by exact prefixLift 2607495
  have htrace : WordTrace (prefixWord ++ tailWord_2607495) baseStart_2607495 baseEnd_2607495 := by
    simpa [prefixWord, tailWord_2607495, baseEnd_2607495] using wordTrace_append hprefix tailTrace_2607495
  have hstable : (prefixWord ++ tailWord_2607495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607495).length < 2 ^ (prefixWord ++ tailWord_2607495).sum := by decide
  have hdescent : baseEnd_2607495 < baseStart_2607495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607508 : List Nat := [2, 4, 2, 1, 3, 1, 1, 1, 8]
def baseStart_2607508 : Nat := 118140960795 + 2607508 * 2 ^ 59
def prefixEnd_2607508 : Nat := 4983230072969 + 3 ^ 40 * 2607508 * 2
def baseEnd_2607508 : Nat := 148767212715987705184255

theorem tailTrace_2607508 : CollatzResearch.WordTrace tailWord_2607508 prefixEnd_2607508 148767212715987705184255 := by
  unfold tailWord_2607508
  simp only [CollatzResearch.WordTrace]
  refine ⟨47551814918725658878611589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63402419891634211838148785 47551814918725658878611589)
  ·
    refine ⟨8915965297261061039739673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47551814918725658878611589 8915965297261061039739673)
    ·
      refine ⟨6686973972945795779804755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8915965297261061039739673 6686973972945795779804755)
      ·
        refine ⟨10030460959418693669707133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6686973972945795779804755 10030460959418693669707133)
        ·
          refine ⟨3761422859782010126140175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10030460959418693669707133 3761422859782010126140175)
          ·
            refine ⟨5642134289673015189210263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3761422859782010126140175 5642134289673015189210263)
            ·
              refine ⟨8463201434509522783815395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5642134289673015189210263 8463201434509522783815395)
              ·
                refine ⟨12694802151764284175723093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8463201434509522783815395 12694802151764284175723093)
                ·
                  refine ⟨148767212715987705184255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12694802151764284175723093 148767212715987705184255)
                  ·
                    rfl

theorem cell23_2607508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_2607508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607508 prefixEnd_2607508 := by exact prefixLift 2607508
  have htrace : WordTrace (prefixWord ++ tailWord_2607508) baseStart_2607508 baseEnd_2607508 := by
    simpa [prefixWord, tailWord_2607508, baseEnd_2607508] using wordTrace_append hprefix tailTrace_2607508
  have hstable : (prefixWord ++ tailWord_2607508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607508).length < 2 ^ (prefixWord ++ tailWord_2607508).sum := by decide
  have hdescent : baseEnd_2607508 < baseStart_2607508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607538 : List Nat := [3, 2, 1, 1, 1, 1, 6, 2, 1, 5]
def baseStart_2607538 : Nat := 118140960795 + 2607538 * 2 ^ 59
def prefixEnd_2607538 : Nat := 4983230072969 + 3 ^ 40 * 2607538 * 2
def baseEnd_2607538 : Nat := 446306772954508076427719

theorem tailTrace_2607538 : CollatzResearch.WordTrace tailWord_2607538 prefixEnd_2607538 446306772954508076427719 := by
  unfold tailWord_2607538
  simp only [CollatzResearch.WordTrace]
  refine ⟨23776181006835658220203817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63403149351561755253876845 23776181006835658220203817)
  ·
    refine ⟨17832135755126743665152863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23776181006835658220203817 17832135755126743665152863)
    ·
      refine ⟨26748203632690115497729295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17832135755126743665152863 26748203632690115497729295)
      ·
        refine ⟨40122305449035173246593943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26748203632690115497729295 40122305449035173246593943)
        ·
          refine ⟨60183458173552759869890915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40122305449035173246593943 60183458173552759869890915)
          ·
            refine ⟨90275187260329139804836373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60183458173552759869890915 90275187260329139804836373)
            ·
              refine ⟨4231649402827928428351705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90275187260329139804836373 4231649402827928428351705)
              ·
                refine ⟨3173737052120946321263779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4231649402827928428351705 3173737052120946321263779)
                ·
                  refine ⟨4760605578181419481895669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3173737052120946321263779 4760605578181419481895669)
                  ·
                    refine ⟨446306772954508076427719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4760605578181419481895669 446306772954508076427719)
                    ·
                      rfl

theorem cell23_2607538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_2607538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607538 prefixEnd_2607538 := by exact prefixLift 2607538
  have htrace : WordTrace (prefixWord ++ tailWord_2607538) baseStart_2607538 baseEnd_2607538 := by
    simpa [prefixWord, tailWord_2607538, baseEnd_2607538] using wordTrace_append hprefix tailTrace_2607538
  have hstable : (prefixWord ++ tailWord_2607538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607538).length < 2 ^ (prefixWord ++ tailWord_2607538).sum := by decide
  have hdescent : baseEnd_2607538 < baseStart_2607538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607561 : List Nat := [1, 2, 1, 1, 2, 1, 5, 3, 1, 1, 5]
def baseStart_2607561 : Nat := 118140960795 + 2607561 * 2 ^ 59
def prefixEnd_2607561 : Nat := 4983230072969 + 3 ^ 40 * 2607561 * 2
def baseEnd_2607561 : Nat := 1338932128918577639295551

theorem tailTrace_2607561 : CollatzResearch.WordTrace tailWord_2607561 prefixEnd_2607561 1338932128918577639295551 := by
  unfold tailWord_2607561
  simp only [CollatzResearch.WordTrace]
  refine ⟨95105562906259307808902537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63403708604172871872601691 95105562906259307808902537)
  ·
    refine ⟨71329172179694480856676903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95105562906259307808902537 71329172179694480856676903)
    ·
      refine ⟨106993758269541721285015355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71329172179694480856676903 106993758269541721285015355)
      ·
        refine ⟨160490637404312581927523033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106993758269541721285015355 160490637404312581927523033)
        ·
          refine ⟨120367978053234436445642275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160490637404312581927523033 120367978053234436445642275)
          ·
            refine ⟨180551967079851654668463413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120367978053234436445642275 180551967079851654668463413)
            ·
              refine ⟨16926746913736092625168445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 180551967079851654668463413 16926746913736092625168445)
              ·
                refine ⟨6347530092651034734438167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16926746913736092625168445 6347530092651034734438167)
                ·
                  refine ⟨9521295138976552101657251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6347530092651034734438167 9521295138976552101657251)
                  ·
                    refine ⟨14281942708464828152485877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9521295138976552101657251 14281942708464828152485877)
                    ·
                      refine ⟨1338932128918577639295551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14281942708464828152485877 1338932128918577639295551)
                      ·
                        rfl

theorem cell23_2607561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 1, 5].length) (baseStart_2607561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607561 prefixEnd_2607561 := by exact prefixLift 2607561
  have htrace : WordTrace (prefixWord ++ tailWord_2607561) baseStart_2607561 baseEnd_2607561 := by
    simpa [prefixWord, tailWord_2607561, baseEnd_2607561] using wordTrace_append hprefix tailTrace_2607561
  have hstable : (prefixWord ++ tailWord_2607561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607561).length < 2 ^ (prefixWord ++ tailWord_2607561).sum := by decide
  have hdescent : baseEnd_2607561 < baseStart_2607561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607578 : List Nat := [3, 1, 1, 2, 3, 1, 2, 2, 3, 2, 3]
def baseStart_2607578 : Nat := 118140960795 + 2607578 * 2 ^ 59
def prefixEnd_2607578 : Nat := 4983230072969 + 3 ^ 40 * 2607578 * 2
def baseEnd_2607578 : Nat := 1338940858089704072782973

theorem tailTrace_2607578 : CollatzResearch.WordTrace tailWord_2607578 prefixEnd_2607578 1338940858089704072782973 := by
  unfold tailWord_2607578
  simp only [CollatzResearch.WordTrace]
  refine ⟨23776545736799429928067847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63404121964798479808180925 23776545736799429928067847)
  ·
    refine ⟨35664818605199144892101771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23776545736799429928067847 35664818605199144892101771)
    ·
      refine ⟨53497227907798717338152657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35664818605199144892101771 53497227907798717338152657)
      ·
        refine ⟨40122920930849038003614493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53497227907798717338152657 40122920930849038003614493)
        ·
          refine ⟨15046095349068389251355435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40122920930849038003614493 15046095349068389251355435)
          ·
            refine ⟨22569143023602583877033153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15046095349068389251355435 22569143023602583877033153)
            ·
              refine ⟨16926857267701937907774865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22569143023602583877033153 16926857267701937907774865)
              ·
                refine ⟨12695142950776453430831149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16926857267701937907774865 12695142950776453430831149)
                ·
                  refine ⟨4760678606541170036561681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12695142950776453430831149 4760678606541170036561681)
                  ·
                    refine ⟨3570508954905877527421261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4760678606541170036561681 3570508954905877527421261)
                    ·
                      refine ⟨1338940858089704072782973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3570508954905877527421261 1338940858089704072782973)
                      ·
                        rfl

theorem cell23_2607578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_2607578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607578 prefixEnd_2607578 := by exact prefixLift 2607578
  have htrace : WordTrace (prefixWord ++ tailWord_2607578) baseStart_2607578 baseEnd_2607578 := by
    simpa [prefixWord, tailWord_2607578, baseEnd_2607578] using wordTrace_append hprefix tailTrace_2607578
  have hstable : (prefixWord ++ tailWord_2607578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607578).length < 2 ^ (prefixWord ++ tailWord_2607578).sum := by decide
  have hdescent : baseEnd_2607578 < baseStart_2607578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607608 : List Nat := [2, 1, 2, 1, 1, 4, 3, 2, 1, 3, 3]
def baseStart_2607608 : Nat := 118140960795 + 2607608 * 2 ^ 59
def prefixEnd_2607608 : Nat := 4983230072969 + 3 ^ 40 * 2607608 * 2
def baseEnd_2607608 : Nat := 1338956262509338955407835

theorem tailTrace_2607608 : CollatzResearch.WordTrace tailWord_2607608 prefixEnd_2607608 1338956262509338955407835 := by
  unfold tailWord_2607608
  simp only [CollatzResearch.WordTrace]
  refine ⟨47553638568544517417931739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63404851424726023223908985 47553638568544517417931739)
  ·
    refine ⟨71330457852816776126897609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47553638568544517417931739 71330457852816776126897609)
    ·
      refine ⟨53497843389612582095173207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71330457852816776126897609 53497843389612582095173207)
      ·
        refine ⟨80246765084418873142759811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53497843389612582095173207 80246765084418873142759811)
        ·
          refine ⟨120370147626628309714139717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80246765084418873142759811 120370147626628309714139717)
          ·
            refine ⟨22569402679992808071401197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120370147626628309714139717 22569402679992808071401197)
            ·
              refine ⟨8463526004997303026775449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22569402679992808071401197 8463526004997303026775449)
              ·
                refine ⟨6347644503747977270081587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8463526004997303026775449 6347644503747977270081587)
                ·
                  refine ⟨9521466755621965905122381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6347644503747977270081587 9521466755621965905122381)
                  ·
                    refine ⟨3570550033358237214420893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9521466755621965905122381 3570550033358237214420893)
                    ·
                      refine ⟨1338956262509338955407835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3570550033358237214420893 1338956262509338955407835)
                      ·
                        rfl

theorem cell23_2607608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 1, 3, 3].length) (baseStart_2607608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607608 prefixEnd_2607608 := by exact prefixLift 2607608
  have htrace : WordTrace (prefixWord ++ tailWord_2607608) baseStart_2607608 baseEnd_2607608 := by
    simpa [prefixWord, tailWord_2607608, baseEnd_2607608] using wordTrace_append hprefix tailTrace_2607608
  have hstable : (prefixWord ++ tailWord_2607608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607608).length < 2 ^ (prefixWord ++ tailWord_2607608).sum := by decide
  have hdescent : baseEnd_2607608 < baseStart_2607608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607621 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 2, 2, 5]
def baseStart_2607621 : Nat := 118140960795 + 2607621 * 2 ^ 59
def prefixEnd_2607621 : Nat := 4983230072969 + 3 ^ 40 * 2607621 * 2
def baseEnd_2607621 : Nat := 1338962937757847404545275

theorem tailTrace_2607621 : CollatzResearch.WordTrace tailWord_2607621 prefixEnd_2607621 1338962937757847404545275 := by
  unfold tailWord_2607621
  simp only [CollatzResearch.WordTrace]
  refine ⟨95107751286041938056086717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63405167524027958704057811 95107751286041938056086717)
  ·
    refine ⟨35665406732265726771032519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95107751286041938056086717 35665406732265726771032519)
    ·
      refine ⟨53498110098398590156548779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35665406732265726771032519 53498110098398590156548779)
      ·
        refine ⟨80247165147597885234823169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53498110098398590156548779 80247165147597885234823169)
        ·
          refine ⟨60185373860698413926117377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80247165147597885234823169 60185373860698413926117377)
          ·
            refine ⟨45139030395523810444588033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60185373860698413926117377 45139030395523810444588033)
            ·
              refine ⟨33854272796642857833441025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45139030395523810444588033 33854272796642857833441025)
              ·
                refine ⟨25390704597482143375080769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33854272796642857833441025 25390704597482143375080769)
                ·
                  refine ⟨19043028448111607531310577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25390704597482143375080769 19043028448111607531310577)
                  ·
                    refine ⟨14282271336083705648482933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19043028448111607531310577 14282271336083705648482933)
                    ·
                      refine ⟨1338962937757847404545275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14282271336083705648482933 1338962937757847404545275)
                      ·
                        rfl

theorem cell23_2607621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_2607621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607621 prefixEnd_2607621 := by exact prefixLift 2607621
  have htrace : WordTrace (prefixWord ++ tailWord_2607621) baseStart_2607621 baseEnd_2607621 := by
    simpa [prefixWord, tailWord_2607621, baseEnd_2607621] using wordTrace_append hprefix tailTrace_2607621
  have hstable : (prefixWord ++ tailWord_2607621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607621).length < 2 ^ (prefixWord ++ tailWord_2607621).sum := by decide
  have hdescent : baseEnd_2607621 < baseStart_2607621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607631 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 4]
def baseStart_2607631 : Nat := 118140960795 + 2607631 * 2 ^ 59
def prefixEnd_2607631 : Nat := 4983230072969 + 3 ^ 40 * 2607631 * 2
def baseEnd_2607631 : Nat := 1338968072564392365420229

theorem tailTrace_2607631 : CollatzResearch.WordTrace tailWord_2607631 prefixEnd_2607631 1338968072564392365420229 := by
  unfold tailWord_2607631
  simp only [CollatzResearch.WordTrace]
  refine ⟨95108116016005709763950747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63405410677337139842633831 95108116016005709763950747)
  ·
    refine ⟨142662174024008564645926121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95108116016005709763950747 142662174024008564645926121)
    ·
      refine ⟨106996630518006423484444591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142662174024008564645926121 106996630518006423484444591)
      ·
        refine ⟨160494945777009635226666887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106996630518006423484444591 160494945777009635226666887)
        ·
          refine ⟨240742418665514452840000331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160494945777009635226666887 240742418665514452840000331)
          ·
            refine ⟨361113627998271679260000497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240742418665514452840000331 361113627998271679260000497)
            ·
              refine ⟨270835220998703759445000373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 361113627998271679260000497 270835220998703759445000373)
              ·
                refine ⟨25390801968628477447968785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 270835220998703759445000373 25390801968628477447968785)
                ·
                  refine ⟨19043101476471358085976589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25390801968628477447968785 19043101476471358085976589)
                  ·
                    refine ⟨7141163053676759282241221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19043101476471358085976589 7141163053676759282241221)
                    ·
                      refine ⟨1338968072564392365420229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7141163053676759282241221 1338968072564392365420229)
                      ·
                        rfl

theorem cell23_2607631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 4].length) (baseStart_2607631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607631 prefixEnd_2607631 := by exact prefixLift 2607631
  have htrace : WordTrace (prefixWord ++ tailWord_2607631) baseStart_2607631 baseEnd_2607631 := by
    simpa [prefixWord, tailWord_2607631, baseEnd_2607631] using wordTrace_append hprefix tailTrace_2607631
  have hstable : (prefixWord ++ tailWord_2607631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607631).length < 2 ^ (prefixWord ++ tailWord_2607631).sum := by decide
  have hdescent : baseEnd_2607631 < baseStart_2607631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607641 : List Nat := [1, 2, 1, 2, 1, 1, 2, 5, 2, 6]
def baseStart_2607641 : Nat := 118140960795 + 2607641 * 2 ^ 59
def prefixEnd_2607641 : Nat := 4983230072969 + 3 ^ 40 * 2607641 * 2
def baseEnd_2607641 : Nat := 446324402456979108765061

theorem tailTrace_2607641 : CollatzResearch.WordTrace tailWord_2607641 prefixEnd_2607641 446324402456979108765061 := by
  unfold tailWord_2607641
  simp only [CollatzResearch.WordTrace]
  refine ⟨95108480745969481471814777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63405653830646320981209851 95108480745969481471814777)
  ·
    refine ⟨71331360559477111103861083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95108480745969481471814777 71331360559477111103861083)
    ·
      refine ⟨106997040839215666655791625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71331360559477111103861083 106997040839215666655791625)
      ·
        refine ⟨80247780629411749991843719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106997040839215666655791625 80247780629411749991843719)
        ·
          refine ⟨120371670944117624987765579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80247780629411749991843719 120371670944117624987765579)
          ·
            refine ⟨180557506416176437481648369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120371670944117624987765579 180557506416176437481648369)
            ·
              refine ⟨135418129812132328111236277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180557506416176437481648369 135418129812132328111236277)
              ·
                refine ⟨12695449669887405760428401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 135418129812132328111236277 12695449669887405760428401)
                ·
                  refine ⟨9521587252415554320321301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12695449669887405760428401 9521587252415554320321301)
                  ·
                    refine ⟨446324402456979108765061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9521587252415554320321301 446324402456979108765061)
                    ·
                      rfl

theorem cell23_2607641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 6].length) (baseStart_2607641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607641 prefixEnd_2607641 := by exact prefixLift 2607641
  have htrace : WordTrace (prefixWord ++ tailWord_2607641) baseStart_2607641 baseEnd_2607641 := by
    simpa [prefixWord, tailWord_2607641, baseEnd_2607641] using wordTrace_append hprefix tailTrace_2607641
  have hstable : (prefixWord ++ tailWord_2607641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607641).length < 2 ^ (prefixWord ++ tailWord_2607641).sum := by decide
  have hdescent : baseEnd_2607641 < baseStart_2607641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607665 : List Nat := [1, 2, 2, 3, 1, 1, 4, 2, 1, 4, 2]
def baseStart_2607665 : Nat := 118140960795 + 2607665 * 2 ^ 59
def prefixEnd_2607665 : Nat := 4983230072969 + 3 ^ 40 * 2607665 * 2
def baseEnd_2607665 : Nat := 1338985530906645232395073

theorem tailTrace_2607665 : CollatzResearch.WordTrace tailWord_2607665 prefixEnd_2607665 1338985530906645232395073 := by
  unfold tailWord_2607665
  simp only [CollatzResearch.WordTrace]
  refine ⟨95109356097882533570688449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63406237398588355713792299 95109356097882533570688449)
  ·
    refine ⟨71332017073411900178016337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95109356097882533570688449 71332017073411900178016337)
    ·
      refine ⟨53499012805058925133512253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71332017073411900178016337 53499012805058925133512253)
      ·
        refine ⟨20062129801897096925067095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53499012805058925133512253 20062129801897096925067095)
        ·
          refine ⟨30093194702845645387600643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20062129801897096925067095 30093194702845645387600643)
          ·
            refine ⟨45139792054268468081400965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30093194702845645387600643 45139792054268468081400965)
            ·
              refine ⟨8463711010175337765262681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45139792054268468081400965 8463711010175337765262681)
              ·
                refine ⟨6347783257631503323947011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8463711010175337765262681 6347783257631503323947011)
                ·
                  refine ⟨9521674886447254985920517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6347783257631503323947011 9521674886447254985920517)
                  ·
                    refine ⟨1785314041208860309860097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9521674886447254985920517 1785314041208860309860097)
                    ·
                      refine ⟨1338985530906645232395073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1785314041208860309860097 1338985530906645232395073)
                      ·
                        rfl

theorem cell23_2607665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_2607665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607665 prefixEnd_2607665 := by exact prefixLift 2607665
  have htrace : WordTrace (prefixWord ++ tailWord_2607665) baseStart_2607665 baseEnd_2607665 := by
    simpa [prefixWord, tailWord_2607665, baseEnd_2607665] using wordTrace_append hprefix tailTrace_2607665
  have hstable : (prefixWord ++ tailWord_2607665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607665).length < 2 ^ (prefixWord ++ tailWord_2607665).sum := by decide
  have hdescent : baseEnd_2607665 < baseStart_2607665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607671 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 9]
def baseStart_2607671 : Nat := 118140960795 + 2607671 * 2 ^ 59
def prefixEnd_2607671 : Nat := 4983230072969 + 3 ^ 40 * 2607671 * 2
def baseEnd_2607671 : Nat := 148776512421174689880005

theorem tailTrace_2607671 : CollatzResearch.WordTrace tailWord_2607671 prefixEnd_2607671 148776512421174689880005 := by
  unfold tailWord_2607671
  simp only [CollatzResearch.WordTrace]
  refine ⟨95109574935860796595406867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63406383290573864396937911 95109574935860796595406867)
  ·
    refine ⟨142664362403791194893110301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95109574935860796595406867 142664362403791194893110301)
    ·
      refine ⟨53499135901421698084916363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142664362403791194893110301 53499135901421698084916363)
      ·
        refine ⟨80248703852132547127374545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53499135901421698084916363 80248703852132547127374545)
        ·
          refine ⟨60186527889099410345530909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80248703852132547127374545 60186527889099410345530909)
          ·
            refine ⟨22569947958412278879574091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60186527889099410345530909 22569947958412278879574091)
            ·
              refine ⟨33854921937618418319361137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22569947958412278879574091 33854921937618418319361137)
              ·
                refine ⟨25391191453213813739520853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33854921937618418319361137 25391191453213813739520853)
                ·
                  refine ⟨148776512421174689880005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25391191453213813739520853 148776512421174689880005)
                  ·
                    rfl

theorem cell23_2607671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 9].length) (baseStart_2607671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607671 prefixEnd_2607671 := by exact prefixLift 2607671
  have htrace : WordTrace (prefixWord ++ tailWord_2607671) baseStart_2607671 baseEnd_2607671 := by
    simpa [prefixWord, tailWord_2607671, baseEnd_2607671] using wordTrace_append hprefix tailTrace_2607671
  have hstable : (prefixWord ++ tailWord_2607671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607671).length < 2 ^ (prefixWord ++ tailWord_2607671).sum := by decide
  have hdescent : baseEnd_2607671 < baseStart_2607671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607772 : List Nat := [2, 2, 3, 2, 2, 2, 2, 1, 2, 1, 4]
def baseStart_2607772 : Nat := 118140960795 + 2607772 * 2 ^ 59
def prefixEnd_2607772 : Nat := 4983230072969 + 3 ^ 40 * 2607772 * 2
def baseEnd_2607772 : Nat := 1339040473336676313757081

theorem tailTrace_2607772 : CollatzResearch.WordTrace tailWord_2607772 prefixEnd_2607772 1339040473336676313757081 := by
  unfold tailWord_2607772
  simp only [CollatzResearch.WordTrace]
  refine ⟨47556629354247445422416785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63408839138996593896555713 47556629354247445422416785)
  ·
    refine ⟨35667472015685584066812589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47556629354247445422416785 35667472015685584066812589)
    ·
      refine ⟨13375302005882094025054721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35667472015685584066812589 13375302005882094025054721)
      ·
        refine ⟨10031476504411570518791041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13375302005882094025054721 10031476504411570518791041)
        ·
          refine ⟨7523607378308677889093281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10031476504411570518791041 7523607378308677889093281)
          ·
            refine ⟨5642705533731508416819961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7523607378308677889093281 5642705533731508416819961)
            ·
              refine ⟨4232029150298631312614971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5642705533731508416819961 4232029150298631312614971)
              ·
                refine ⟨6348043725447946968922457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4232029150298631312614971 6348043725447946968922457)
                ·
                  refine ⟨4761032794085960226691843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6348043725447946968922457 4761032794085960226691843)
                  ·
                    refine ⟨7141549191128940340037765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4761032794085960226691843 7141549191128940340037765)
                    ·
                      refine ⟨1339040473336676313757081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7141549191128940340037765 1339040473336676313757081)
                      ·
                        rfl

theorem cell23_2607772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_2607772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607772 prefixEnd_2607772 := by exact prefixLift 2607772
  have htrace : WordTrace (prefixWord ++ tailWord_2607772) baseStart_2607772 baseEnd_2607772 := by
    simpa [prefixWord, tailWord_2607772, baseEnd_2607772] using wordTrace_append hprefix tailTrace_2607772
  have hstable : (prefixWord ++ tailWord_2607772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607772).length < 2 ^ (prefixWord ++ tailWord_2607772).sum := by decide
  have hdescent : baseEnd_2607772 < baseStart_2607772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607795 : List Nat := [1, 1, 1, 2, 3, 5, 2, 2, 6]
def baseStart_2607795 : Nat := 118140960795 + 2607795 * 2 ^ 59
def prefixEnd_2607795 : Nat := 4983230072969 + 3 ^ 40 * 2607795 * 2
def baseEnd_2607795 : Nat := 148783587043525524863275

theorem tailTrace_2607795 : CollatzResearch.WordTrace tailWord_2607795 prefixEnd_2607795 148783587043525524863275 := by
  unfold tailWord_2607795
  simp only [CollatzResearch.WordTrace]
  refine ⟨95114097587411565772920839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63409398391607710515280559 95114097587411565772920839)
  ·
    refine ⟨142671146381117348659381259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95114097587411565772920839 142671146381117348659381259)
    ·
      refine ⟨214006719571676022989071889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142671146381117348659381259 214006719571676022989071889)
      ·
        refine ⟨160505039678757017241803917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214006719571676022989071889 160505039678757017241803917)
        ·
          refine ⟨60189389879533881465676469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160505039678757017241803917 60189389879533881465676469)
          ·
            refine ⟨5642755301206301387407169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60189389879533881465676469 5642755301206301387407169)
            ·
              refine ⟨4232066475904726040555377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5642755301206301387407169 4232066475904726040555377)
              ·
                refine ⟨3174049856928544530416533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4232066475904726040555377 3174049856928544530416533)
                ·
                  refine ⟨148783587043525524863275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3174049856928544530416533 148783587043525524863275)
                  ·
                    rfl

theorem cell23_2607795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 6].length) (baseStart_2607795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607795 prefixEnd_2607795 := by exact prefixLift 2607795
  have htrace : WordTrace (prefixWord ++ tailWord_2607795) baseStart_2607795 baseEnd_2607795 := by
    simpa [prefixWord, tailWord_2607795, baseEnd_2607795] using wordTrace_append hprefix tailTrace_2607795
  have hstable : (prefixWord ++ tailWord_2607795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607795).length < 2 ^ (prefixWord ++ tailWord_2607795).sum := by decide
  have hdescent : baseEnd_2607795 < baseStart_2607795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607799 : List Nat := [1, 1, 3, 1, 6, 1, 1, 4, 1, 4]
def baseStart_2607799 : Nat := 118140960795 + 2607799 * 2 ^ 59
def prefixEnd_2607799 : Nat := 4983230072969 + 3 ^ 40 * 2607799 * 2
def baseEnd_2607799 : Nat := 446351445771449236039819

theorem tailTrace_2607799 : CollatzResearch.WordTrace tailWord_2607799 prefixEnd_2607799 446351445771449236039819 := by
  unfold tailWord_2607799
  simp only [CollatzResearch.WordTrace]
  refine ⟨95114243479397074456066451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63409495652931382970710967 95114243479397074456066451)
  ·
    refine ⟨142671365219095611684099677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95114243479397074456066451 142671365219095611684099677)
    ·
      refine ⟨53501761957160854381537379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142671365219095611684099677 53501761957160854381537379)
      ·
        refine ⟨80252642935741281572306069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53501761957160854381537379 80252642935741281572306069)
        ·
          refine ⟨3761842637612872573701847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 80252642935741281572306069 3761842637612872573701847)
          ·
            refine ⟨5642763956419308860552771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3761842637612872573701847 5642763956419308860552771)
            ·
              refine ⟨8464145934628963290829157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5642763956419308860552771 8464145934628963290829157)
              ·
                refine ⟨1587027362742930617030467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8464145934628963290829157 1587027362742930617030467)
                ·
                  refine ⟨2380541044114395925545701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1587027362742930617030467 2380541044114395925545701)
                  ·
                    refine ⟨446351445771449236039819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2380541044114395925545701 446351445771449236039819)
                    ·
                      rfl

theorem cell23_2607799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 4, 1, 4].length) (baseStart_2607799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607799 prefixEnd_2607799 := by exact prefixLift 2607799
  have htrace : WordTrace (prefixWord ++ tailWord_2607799) baseStart_2607799 baseEnd_2607799 := by
    simpa [prefixWord, tailWord_2607799, baseEnd_2607799] using wordTrace_append hprefix tailTrace_2607799
  have hstable : (prefixWord ++ tailWord_2607799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607799).length < 2 ^ (prefixWord ++ tailWord_2607799).sum := by decide
  have hdescent : baseEnd_2607799 < baseStart_2607799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607822 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3]
def baseStart_2607822 : Nat := 118140960795 + 2607822 * 2 ^ 59
def prefixEnd_2607822 : Nat := 4983230072969 + 3 ^ 40 * 2607822 * 2
def baseEnd_2607822 : Nat := 1339066147369401118131851

theorem tailTrace_2607822 : CollatzResearch.WordTrace tailWord_2607822 prefixEnd_2607822 1339066147369401118131851 := by
  unfold tailWord_2607822
  simp only [CollatzResearch.WordTrace]
  refine ⟨11889385294789218673019215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63410054905542499589435813 11889385294789218673019215)
  ·
    refine ⟨17834077942183828009528823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11889385294789218673019215 17834077942183828009528823)
    ·
      refine ⟨26751116913275742014293235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17834077942183828009528823 26751116913275742014293235)
      ·
        refine ⟨40126675369913613021439853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26751116913275742014293235 40126675369913613021439853)
        ·
          refine ⟨15047503263717604883039945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40126675369913613021439853 15047503263717604883039945)
          ·
            refine ⟨11285627447788203662279959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15047503263717604883039945 11285627447788203662279959)
            ·
              refine ⟨16928441171682305493419939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11285627447788203662279959 16928441171682305493419939)
              ·
                refine ⟨25392661757523458240129909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16928441171682305493419939 25392661757523458240129909)
                ·
                  refine ⟨2380562039767824210012179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25392661757523458240129909 2380562039767824210012179)
                  ·
                    refine ⟨3570843059651736315018269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2380562039767824210012179 3570843059651736315018269)
                    ·
                      refine ⟨1339066147369401118131851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3570843059651736315018269 1339066147369401118131851)
                      ·
                        rfl

theorem cell23_2607822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3].length) (baseStart_2607822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607822 prefixEnd_2607822 := by exact prefixLift 2607822
  have htrace : WordTrace (prefixWord ++ tailWord_2607822) baseStart_2607822 baseEnd_2607822 := by
    simpa [prefixWord, tailWord_2607822, baseEnd_2607822] using wordTrace_append hprefix tailTrace_2607822
  have hstable : (prefixWord ++ tailWord_2607822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607822).length < 2 ^ (prefixWord ++ tailWord_2607822).sum := by decide
  have hdescent : baseEnd_2607822 < baseStart_2607822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607825 : List Nat := [1, 2, 2, 1, 2, 3, 2, 4, 1, 5]
def baseStart_2607825 : Nat := 118140960795 + 2607825 * 2 ^ 59
def prefixEnd_2607825 : Nat := 4983230072969 + 3 ^ 40 * 2607825 * 2
def baseEnd_2607825 : Nat := 446355895937121535464779

theorem tailTrace_2607825 : CollatzResearch.WordTrace tailWord_2607825 prefixEnd_2607825 446355895937121535464779 := by
  unfold tailWord_2607825
  simp only [CollatzResearch.WordTrace]
  refine ⟨95115191777302880896512929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63410127851535253931008619 95115191777302880896512929)
  ·
    refine ⟨71336393832977160672384697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95115191777302880896512929 71336393832977160672384697)
    ·
      refine ⟨53502295374732870504288523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71336393832977160672384697 53502295374732870504288523)
      ·
        refine ⟨80253443062099305756432785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53502295374732870504288523 80253443062099305756432785)
        ·
          refine ⟨60190082296574479317324589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80253443062099305756432785 60190082296574479317324589)
          ·
            refine ⟨22571280861215429743996721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60190082296574479317324589 22571280861215429743996721)
            ·
              refine ⟨16928460645911572307997541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22571280861215429743996721 16928460645911572307997541)
              ·
                refine ⟨3174086371108419807749539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16928460645911572307997541 3174086371108419807749539)
                ·
                  refine ⟨4761129556662629711624309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3174086371108419807749539 4761129556662629711624309)
                  ·
                    refine ⟨446355895937121535464779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4761129556662629711624309 446355895937121535464779)
                    ·
                      rfl

theorem cell23_2607825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 5].length) (baseStart_2607825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607825 prefixEnd_2607825 := by exact prefixLift 2607825
  have htrace : WordTrace (prefixWord ++ tailWord_2607825) baseStart_2607825 baseEnd_2607825 := by
    simpa [prefixWord, tailWord_2607825, baseEnd_2607825] using wordTrace_append hprefix tailTrace_2607825
  have hstable : (prefixWord ++ tailWord_2607825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607825).length < 2 ^ (prefixWord ++ tailWord_2607825).sum := by decide
  have hdescent : baseEnd_2607825 < baseStart_2607825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607826 : List Nat := [3, 2, 2, 2, 4, 1, 1, 1, 2, 2, 3]
def baseStart_2607826 : Nat := 118140960795 + 2607826 * 2 ^ 59
def prefixEnd_2607826 : Nat := 4983230072969 + 3 ^ 40 * 2607826 * 2
def baseEnd_2607826 : Nat := 1339068201292019102481833

theorem tailTrace_2607826 : CollatzResearch.WordTrace tailWord_2607826 prefixEnd_2607826 1339068201292019102481833 := by
  unfold tailWord_2607826
  simp only [CollatzResearch.WordTrace]
  refine ⟨23778807062574814516824833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63410152166866172044866221 23778807062574814516824833)
  ·
    refine ⟨17834105296931110887618625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23778807062574814516824833 17834105296931110887618625)
    ·
      refine ⟨13375578972698333165713969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17834105296931110887618625 13375578972698333165713969)
      ·
        refine ⟨10031684229523749874285477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13375578972698333165713969 10031684229523749874285477)
        ·
          refine ⟨1880940793035703101428527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10031684229523749874285477 1880940793035703101428527)
          ·
            refine ⟨2821411189553554652142791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1880940793035703101428527 2821411189553554652142791)
            ·
              refine ⟨4232116784330331978214187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2821411189553554652142791 4232116784330331978214187)
              ·
                refine ⟨6348175176495497967321281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4232116784330331978214187 6348175176495497967321281)
                ·
                  refine ⟨4761131382371623475490961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6348175176495497967321281 4761131382371623475490961)
                  ·
                    refine ⟨3570848536778717606618221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4761131382371623475490961 3570848536778717606618221)
                    ·
                      refine ⟨1339068201292019102481833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3570848536778717606618221 1339068201292019102481833)
                      ·
                        rfl

theorem cell23_2607826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_2607826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607826 prefixEnd_2607826 := by exact prefixLift 2607826
  have htrace : WordTrace (prefixWord ++ tailWord_2607826) baseStart_2607826 baseEnd_2607826 := by
    simpa [prefixWord, tailWord_2607826, baseEnd_2607826] using wordTrace_append hprefix tailTrace_2607826
  have hstable : (prefixWord ++ tailWord_2607826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607826).length < 2 ^ (prefixWord ++ tailWord_2607826).sum := by decide
  have hdescent : baseEnd_2607826 < baseStart_2607826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607832 : List Nat := [2, 1, 2, 2, 3, 3, 1, 1, 1, 5, 2]
def baseStart_2607832 : Nat := 118140960795 + 2607832 * 2 ^ 59
def prefixEnd_2607832 : Nat := 4983230072969 + 3 ^ 40 * 2607832 * 2
def baseEnd_2607832 : Nat := 1339071282175946079006805

theorem tailTrace_2607832 : CollatzResearch.WordTrace tailWord_2607832 prefixEnd_2607832 1339071282175946079006805 := by
  unfold tailWord_2607832
  simp only [CollatzResearch.WordTrace]
  refine ⟨47557723544138760546008875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63410298058851680728011833 47557723544138760546008875)
  ·
    refine ⟨71336585316208140819013313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47557723544138760546008875 71336585316208140819013313)
    ·
      refine ⟨53502438987156105614259985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71336585316208140819013313 53502438987156105614259985)
      ·
        refine ⟨40126829240367079210694989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53502438987156105614259985 40126829240367079210694989)
        ·
          refine ⟨15047560965137654704010621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40126829240367079210694989 15047560965137654704010621)
          ·
            refine ⟨5642835361926620514003983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15047560965137654704010621 5642835361926620514003983)
            ·
              refine ⟨8464253042889930771005975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5642835361926620514003983 8464253042889930771005975)
              ·
                refine ⟨12696379564334896156508963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8464253042889930771005975 12696379564334896156508963)
                ·
                  refine ⟨19044569346502344234763445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12696379564334896156508963 19044569346502344234763445)
                  ·
                    refine ⟨1785428376234594772009073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19044569346502344234763445 1785428376234594772009073)
                    ·
                      refine ⟨1339071282175946079006805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1785428376234594772009073 1339071282175946079006805)
                      ·
                        rfl

theorem cell23_2607832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 1, 5, 2].length) (baseStart_2607832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607832 prefixEnd_2607832 := by exact prefixLift 2607832
  have htrace : WordTrace (prefixWord ++ tailWord_2607832) baseStart_2607832 baseEnd_2607832 := by
    simpa [prefixWord, tailWord_2607832, baseEnd_2607832] using wordTrace_append hprefix tailTrace_2607832
  have hstable : (prefixWord ++ tailWord_2607832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607832).length < 2 ^ (prefixWord ++ tailWord_2607832).sum := by decide
  have hdescent : baseEnd_2607832 < baseStart_2607832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607839 : List Nat := [1, 1, 2, 3, 2, 3, 1, 5, 1, 1, 3]
def baseStart_2607839 : Nat := 118140960795 + 2607839 * 2 ^ 59
def prefixEnd_2607839 : Nat := 4983230072969 + 3 ^ 40 * 2607839 * 2
def baseEnd_2607839 : Nat := 1339074876540527551619273

theorem tailTrace_2607839 : CollatzResearch.WordTrace tailWord_2607839 prefixEnd_2607839 1339074876540527551619273 := by
  unfold tailWord_2607839
  simp only [CollatzResearch.WordTrace]
  refine ⟨95115702399252161287522571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63410468266168107525015047 95115702399252161287522571)
  ·
    refine ⟨142673553598878241931283857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95115702399252161287522571 142673553598878241931283857)
    ·
      refine ⟨107005165199158681448462893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142673553598878241931283857 107005165199158681448462893)
      ·
        refine ⟨40126936949684505543173585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107005165199158681448462893 40126936949684505543173585)
        ·
          refine ⟨30095202712263379157380189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40126936949684505543173585 30095202712263379157380189)
          ·
            refine ⟨11285701017098767184017571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30095202712263379157380189 11285701017098767184017571)
            ·
              refine ⟨16928551525648150776026357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11285701017098767184017571 16928551525648150776026357)
              ·
                refine ⟨1587051705529514135252471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16928551525648150776026357 1587051705529514135252471)
                ·
                  refine ⟨2380577558294271202878707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1587051705529514135252471 2380577558294271202878707)
                  ·
                    refine ⟨3570866337441406804318061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2380577558294271202878707 3570866337441406804318061)
                    ·
                      refine ⟨1339074876540527551619273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3570866337441406804318061 1339074876540527551619273)
                      ·
                        rfl

theorem cell23_2607839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 5, 1, 1, 3].length) (baseStart_2607839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607839 prefixEnd_2607839 := by exact prefixLift 2607839
  have htrace : WordTrace (prefixWord ++ tailWord_2607839) baseStart_2607839 baseEnd_2607839 := by
    simpa [prefixWord, tailWord_2607839, baseEnd_2607839] using wordTrace_append hprefix tailTrace_2607839
  have hstable : (prefixWord ++ tailWord_2607839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607839).length < 2 ^ (prefixWord ++ tailWord_2607839).sum := by decide
  have hdescent : baseEnd_2607839 < baseStart_2607839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607865 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 5, 2, 3]
def baseStart_2607865 : Nat := 118140960795 + 2607865 * 2 ^ 59
def prefixEnd_2607865 : Nat := 4983230072969 + 3 ^ 40 * 2607865 * 2
def baseEnd_2607865 : Nat := 1339088227037544449894153

theorem tailTrace_2607865 : CollatzResearch.WordTrace tailWord_2607865 prefixEnd_2607865 1339088227037544449894153 := by
  unfold tailWord_2607865
  simp only [CollatzResearch.WordTrace]
  refine ⟨95116650697157967727969049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63411100464771978485312699 95116650697157967727969049)
  ·
    refine ⟨71337488022868475795976787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95116650697157967727969049 71337488022868475795976787)
    ·
      refine ⟨107006232034302713693965181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71337488022868475795976787 107006232034302713693965181)
      ·
        refine ⟨40127337012863517635236943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107006232034302713693965181 40127337012863517635236943)
        ·
          refine ⟨60191005519295276452855415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40127337012863517635236943 60191005519295276452855415)
          ·
            refine ⟨90286508278942914679283123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60191005519295276452855415 90286508278942914679283123)
            ·
              refine ⟨135429762418414372018924685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90286508278942914679283123 135429762418414372018924685)
              ·
                refine ⟨50786160906905389507096757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135429762418414372018924685 50786160906905389507096757)
                ·
                  refine ⟨4761202585022380266290321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50786160906905389507096757 4761202585022380266290321)
                  ·
                    refine ⟨3570901938766785199717741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4761202585022380266290321 3570901938766785199717741)
                    ·
                      refine ⟨1339088227037544449894153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3570901938766785199717741 1339088227037544449894153)
                      ·
                        rfl

theorem cell23_2607865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_2607865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607865 prefixEnd_2607865 := by exact prefixLift 2607865
  have htrace : WordTrace (prefixWord ++ tailWord_2607865) baseStart_2607865 baseEnd_2607865 := by
    simpa [prefixWord, tailWord_2607865, baseEnd_2607865] using wordTrace_append hprefix tailTrace_2607865
  have hstable : (prefixWord ++ tailWord_2607865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607865).length < 2 ^ (prefixWord ++ tailWord_2607865).sum := by decide
  have hdescent : baseEnd_2607865 < baseStart_2607865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607879 : List Nat := [1, 1, 4, 4, 1, 2, 2, 2, 1, 1, 4]
def baseStart_2607879 : Nat := 118140960795 + 2607879 * 2 ^ 59
def prefixEnd_2607879 : Nat := 4983230072969 + 3 ^ 40 * 2607879 * 2
def baseEnd_2607879 : Nat := 1339095415766707395119089

theorem tailTrace_2607879 : CollatzResearch.WordTrace tailWord_2607879 prefixEnd_2607879 1339095415766707395119089 := by
  unfold tailWord_2607879
  simp only [CollatzResearch.WordTrace]
  refine ⟨95117161319107248118978691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63411440879404832079319127 95117161319107248118978691)
  ·
    refine ⟨142675741978660872178468037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95117161319107248118978691 142675741978660872178468037)
    ·
      refine ⟨26751701620998913533462757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142675741978660872178468037 26751701620998913533462757)
      ·
        refine ⟨5015944053937296287524267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26751701620998913533462757 5015944053937296287524267)
        ·
          refine ⟨7523916080905944431286401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5015944053937296287524267 7523916080905944431286401)
          ·
            refine ⟨5642937060679458323464801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7523916080905944431286401 5642937060679458323464801)
            ·
              refine ⟨4232202795509593742598601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5642937060679458323464801 4232202795509593742598601)
              ·
                refine ⟨3174152096632195306948951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4232202795509593742598601 3174152096632195306948951)
                ·
                  refine ⟨4761228144948292960423427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3174152096632195306948951 4761228144948292960423427)
                  ·
                    refine ⟨7141842217422439440635141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4761228144948292960423427 7141842217422439440635141)
                    ·
                      refine ⟨1339095415766707395119089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7141842217422439440635141 1339095415766707395119089)
                      ·
                        rfl

theorem cell23_2607879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_2607879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607879 prefixEnd_2607879 := by exact prefixLift 2607879
  have htrace : WordTrace (prefixWord ++ tailWord_2607879) baseStart_2607879 baseEnd_2607879 := by
    simpa [prefixWord, tailWord_2607879, baseEnd_2607879] using wordTrace_append hprefix tailTrace_2607879
  have hstable : (prefixWord ++ tailWord_2607879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607879).length < 2 ^ (prefixWord ++ tailWord_2607879).sum := by decide
  have hdescent : baseEnd_2607879 < baseStart_2607879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607890 : List Nat := [3, 2, 4, 1, 2, 2, 1, 3, 1, 1, 3]
def baseStart_2607890 : Nat := 118140960795 + 2607890 * 2 ^ 59
def prefixEnd_2607890 : Nat := 4983230072969 + 3 ^ 40 * 2607890 * 2
def baseEnd_2607890 : Nat := 1339101064053906852081539

theorem tailTrace_2607890 : CollatzResearch.WordTrace tailWord_2607890 prefixEnd_2607890 1339101064053906852081539 := by
  unfold tailWord_2607890
  simp only [CollatzResearch.WordTrace]
  refine ⟨23779390630516849249407281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63411708348044931331752749 23779390630516849249407281)
  ·
    refine ⟨17834542972887636937055461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23779390630516849249407281 17834542972887636937055461)
    ·
      refine ⟨3343976807416431925697899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17834542972887636937055461 3343976807416431925697899)
      ·
        refine ⟨5015965211124647888546849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3343976807416431925697899 5015965211124647888546849)
        ·
          refine ⟨3761973908343485916410137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5015965211124647888546849 3761973908343485916410137)
          ·
            refine ⟨2821480431257614437307603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3761973908343485916410137 2821480431257614437307603)
            ·
              refine ⟨4232220646886421655961405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2821480431257614437307603 4232220646886421655961405)
              ·
                refine ⟨1587082742582408120985527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4232220646886421655961405 1587082742582408120985527)
                ·
                  refine ⟨2380624113873612181478291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1587082742582408120985527 2380624113873612181478291)
                  ·
                    refine ⟨3570936170810418272217437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2380624113873612181478291 3570936170810418272217437)
                    ·
                      refine ⟨1339101064053906852081539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3570936170810418272217437 1339101064053906852081539)
                      ·
                        rfl

theorem cell23_2607890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_2607890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607890 prefixEnd_2607890 := by exact prefixLift 2607890
  have htrace : WordTrace (prefixWord ++ tailWord_2607890) baseStart_2607890 baseEnd_2607890 := by
    simpa [prefixWord, tailWord_2607890, baseEnd_2607890] using wordTrace_append hprefix tailTrace_2607890
  have hstable : (prefixWord ++ tailWord_2607890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607890).length < 2 ^ (prefixWord ++ tailWord_2607890).sum := by decide
  have hdescent : baseEnd_2607890 < baseStart_2607890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607933 : List Nat := [1, 4, 1, 4, 3, 1, 1, 2, 1, 2, 3]
def baseStart_2607933 : Nat := 118140960795 + 2607933 * 2 ^ 59
def prefixEnd_2607933 : Nat := 4983230072969 + 3 ^ 40 * 2607933 * 2
def baseEnd_2607933 : Nat := 1339123143722050183843841

theorem tailTrace_2607933 : CollatzResearch.WordTrace tailWord_2607933 prefixEnd_2607933 1339123143722050183843841 := by
  unfold tailWord_2607933
  simp only [CollatzResearch.WordTrace]
  refine ⟨95119130860911615341444453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63412753907274410227629635 95119130860911615341444453)
  ·
    refine ⟨17834837036420927876520835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95119130860911615341444453 17834837036420927876520835)
    ·
      refine ⟨26752255554631391814781253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17834837036420927876520835 26752255554631391814781253)
      ·
        refine ⟨5016047916493385965271485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26752255554631391814781253 5016047916493385965271485)
        ·
          refine ⟨1881017968685019736976807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5016047916493385965271485 1881017968685019736976807)
          ·
            refine ⟨2821526953027529605465211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1881017968685019736976807 2821526953027529605465211)
            ·
              refine ⟨4232290429541294408197817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2821526953027529605465211 4232290429541294408197817)
              ·
                refine ⟨3174217822155970806148363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4232290429541294408197817 3174217822155970806148363)
                ·
                  refine ⟨4761326733233956209222545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3174217822155970806148363 4761326733233956209222545)
                  ·
                    refine ⟨3570995049925467156916909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4761326733233956209222545 3570995049925467156916909)
                    ·
                      refine ⟨1339123143722050183843841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3570995049925467156916909 1339123143722050183843841)
                      ·
                        rfl

theorem cell23_2607933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_2607933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607933 prefixEnd_2607933 := by exact prefixLift 2607933
  have htrace : WordTrace (prefixWord ++ tailWord_2607933) baseStart_2607933 baseEnd_2607933 := by
    simpa [prefixWord, tailWord_2607933, baseEnd_2607933] using wordTrace_append hprefix tailTrace_2607933
  have hstable : (prefixWord ++ tailWord_2607933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607933).length < 2 ^ (prefixWord ++ tailWord_2607933).sum := by decide
  have hdescent : baseEnd_2607933 < baseStart_2607933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607952 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 3, 4, 2]
def baseStart_2607952 : Nat := 118140960795 + 2607952 * 2 ^ 59
def prefixEnd_2607952 : Nat := 4983230072969 + 3 ^ 40 * 2607952 * 2
def baseEnd_2607952 : Nat := 1339132899854485609506253

theorem tailTrace_2607952 : CollatzResearch.WordTrace tailWord_2607952 prefixEnd_2607952 1339132899854485609506253 := by
  unfold tailWord_2607952
  simp only [CollatzResearch.WordTrace]
  refine ⟨47559911923921390793193055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63413215898561854390924073 47559911923921390793193055)
  ·
    refine ⟨71339867885882086189789583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47559911923921390793193055 71339867885882086189789583)
    ·
      refine ⟨107009801828823129284684375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71339867885882086189789583 107009801828823129284684375)
      ·
        refine ⟨160514702743234693927026563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107009801828823129284684375 160514702743234693927026563)
        ·
          refine ⟨240772054114852040890539845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160514702743234693927026563 240772054114852040890539845)
          ·
            refine ⟨45144760146534757666976221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 240772054114852040890539845 45144760146534757666976221)
            ·
              refine ⟨16929285054950534125116083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45144760146534757666976221 16929285054950534125116083)
              ·
                refine ⟨25393927582425801187674125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16929285054950534125116083 25393927582425801187674125)
                ·
                  refine ⟨9522722843409675445377797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25393927582425801187674125 9522722843409675445377797)
                  ·
                    refine ⟨1785510533139314146008337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9522722843409675445377797 1785510533139314146008337)
                    ·
                      refine ⟨1339132899854485609506253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1785510533139314146008337 1339132899854485609506253)
                      ·
                        rfl

theorem cell23_2607952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 3, 4, 2].length) (baseStart_2607952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607952 prefixEnd_2607952 := by exact prefixLift 2607952
  have htrace : WordTrace (prefixWord ++ tailWord_2607952) baseStart_2607952 baseEnd_2607952 := by
    simpa [prefixWord, tailWord_2607952, baseEnd_2607952] using wordTrace_append hprefix tailTrace_2607952
  have hstable : (prefixWord ++ tailWord_2607952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607952).length < 2 ^ (prefixWord ++ tailWord_2607952).sum := by decide
  have hdescent : baseEnd_2607952 < baseStart_2607952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607955 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 4, 4, 3]
def baseStart_2607955 : Nat := 118140960795 + 2607955 * 2 ^ 59
def prefixEnd_2607955 : Nat := 4983230072969 + 3 ^ 40 * 2607955 * 2
def baseEnd_2607955 : Nat := 1339134440296449097768739

theorem tailTrace_2607955 : CollatzResearch.WordTrace tailWord_2607955 prefixEnd_2607955 1339134440296449097768739 := by
  unfold tailWord_2607955
  simp only [CollatzResearch.WordTrace]
  refine ⟨95119933266831913098745319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63413288844554608732496879 95119933266831913098745319)
  ·
    refine ⟨142679899900247869648117979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95119933266831913098745319 142679899900247869648117979)
    ·
      refine ⟨214019849850371804472176969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142679899900247869648117979 214019849850371804472176969)
      ·
        refine ⟨160514887387778853354132727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214019849850371804472176969 160514887387778853354132727)
        ·
          refine ⟨240772331081668280031199091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160514887387778853354132727 240772331081668280031199091)
          ·
            refine ⟨361158496622502420046798637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240772331081668280031199091 361158496622502420046798637)
            ·
              refine ⟨135434436233438407517549489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 361158496622502420046798637 135434436233438407517549489)
              ·
                refine ⟨101575827175078805638162117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135434436233438407517549489 101575827175078805638162117)
                ·
                  refine ⟨19045467595327276057155397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101575827175078805638162117 19045467595327276057155397)
                  ·
                    refine ⟨3571025174123864260716637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19045467595327276057155397 3571025174123864260716637)
                    ·
                      refine ⟨1339134440296449097768739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3571025174123864260716637 1339134440296449097768739)
                      ·
                        rfl

theorem cell23_2607955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 4, 3].length) (baseStart_2607955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607955 prefixEnd_2607955 := by exact prefixLift 2607955
  have htrace : WordTrace (prefixWord ++ tailWord_2607955) baseStart_2607955 baseEnd_2607955 := by
    simpa [prefixWord, tailWord_2607955, baseEnd_2607955] using wordTrace_append hprefix tailTrace_2607955
  have hstable : (prefixWord ++ tailWord_2607955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607955).length < 2 ^ (prefixWord ++ tailWord_2607955).sum := by decide
  have hdescent : baseEnd_2607955 < baseStart_2607955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607972 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 2, 4, 3]
def baseStart_2607972 : Nat := 118140960795 + 2607972 * 2 ^ 59
def prefixEnd_2607972 : Nat := 4983230072969 + 3 ^ 40 * 2607972 * 2
def baseEnd_2607972 : Nat := 1339143169467575531256161

theorem tailTrace_2607972 : CollatzResearch.WordTrace tailWord_2607972 prefixEnd_2607972 1339143169467575531256161 := by
  unfold tailWord_2607972
  simp only [CollatzResearch.WordTrace]
  refine ⟨47560276653885162501057085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63413702205180216668076113 47560276653885162501057085)
  ·
    refine ⟨17835103745206935937896407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47560276653885162501057085 17835103745206935937896407)
    ·
      refine ⟨26752655617810403906844611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17835103745206935937896407 26752655617810403906844611)
      ·
        refine ⟨40128983426715605860266917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26752655617810403906844611 40128983426715605860266917)
        ·
          refine ⟨7524184392509176098800047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40128983426715605860266917 7524184392509176098800047)
          ·
            refine ⟨11286276588763764148200071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7524184392509176098800047 11286276588763764148200071)
            ·
              refine ⟨16929414883145646222300107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11286276588763764148200071 16929414883145646222300107)
              ·
                refine ⟨25394122324718469333450161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16929414883145646222300107 25394122324718469333450161)
                ·
                  refine ⟨19045591743538852000087621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25394122324718469333450161 19045591743538852000087621)
                  ·
                    refine ⟨3571048451913534750016429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19045591743538852000087621 3571048451913534750016429)
                    ·
                      refine ⟨1339143169467575531256161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3571048451913534750016429 1339143169467575531256161)
                      ·
                        rfl

theorem cell23_2607972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_2607972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607972 prefixEnd_2607972 := by exact prefixLift 2607972
  have htrace : WordTrace (prefixWord ++ tailWord_2607972) baseStart_2607972 baseEnd_2607972 := by
    simpa [prefixWord, tailWord_2607972, baseEnd_2607972] using wordTrace_append hprefix tailTrace_2607972
  have hstable : (prefixWord ++ tailWord_2607972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607972).length < 2 ^ (prefixWord ++ tailWord_2607972).sum := by decide
  have hdescent : baseEnd_2607972 < baseStart_2607972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607986 : List Nat := [3, 2, 1, 2, 1, 1, 4, 3, 2, 2, 2]
def baseStart_2607986 : Nat := 118140960795 + 2607986 * 2 ^ 59
def prefixEnd_2607986 : Nat := 4983230072969 + 3 ^ 40 * 2607986 * 2
def baseEnd_2607986 : Nat := 1339150358196738476481097

theorem tailTrace_2607986 : CollatzResearch.WordTrace tailWord_2607986 prefixEnd_2607986 1339150358196738476481097 := by
  unfold tailWord_2607986
  simp only [CollatzResearch.WordTrace]
  refine ⟨23780265982429901348280953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63414042619813070262082541 23780265982429901348280953)
  ·
    refine ⟨17835199486822426011210715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23780265982429901348280953 17835199486822426011210715)
    ·
      refine ⟨26752799230233639016816073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17835199486822426011210715 26752799230233639016816073)
      ·
        refine ⟨20064599422675229262612055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26752799230233639016816073 20064599422675229262612055)
        ·
          refine ⟨30096899134012843893918083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20064599422675229262612055 30096899134012843893918083)
          ·
            refine ⟨45145348701019265840877125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30096899134012843893918083 45145348701019265840877125)
            ·
              refine ⟨8464752881441112345164461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45145348701019265840877125 8464752881441112345164461)
              ·
                refine ⟨3174282330540417129436673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8464752881441112345164461 3174282330540417129436673)
                ·
                  refine ⟨2380711747905312847077505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3174282330540417129436673 2380711747905312847077505)
                  ·
                    refine ⟨1785533810928984635308129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2380711747905312847077505 1785533810928984635308129)
                    ·
                      refine ⟨1339150358196738476481097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1785533810928984635308129 1339150358196738476481097)
                      ·
                        rfl

theorem cell23_2607986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_2607986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2607986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2607986 prefixEnd_2607986 := by exact prefixLift 2607986
  have htrace : WordTrace (prefixWord ++ tailWord_2607986) baseStart_2607986 baseEnd_2607986 := by
    simpa [prefixWord, tailWord_2607986, baseEnd_2607986] using wordTrace_append hprefix tailTrace_2607986
  have hstable : (prefixWord ++ tailWord_2607986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607986).length < 2 ^ (prefixWord ++ tailWord_2607986).sum := by decide
  have hdescent : baseEnd_2607986 < baseStart_2607986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608009 : List Nat := [1, 2, 1, 1, 5, 3, 2, 3, 5]
def baseStart_2608009 : Nat := 118140960795 + 2608009 * 2 ^ 59
def prefixEnd_2608009 : Nat := 4983230072969 + 3 ^ 40 * 2608009 * 2
def baseEnd_2608009 : Nat := 148795796472421320721499

theorem tailTrace_2608009 : CollatzResearch.WordTrace tailWord_2608009 prefixEnd_2608009 148795796472421320721499 := by
  unfold tailWord_2608009
  simp only [CollatzResearch.WordTrace]
  refine ⟨95121902808636280321211081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63414601872424186880807387 95121902808636280321211081)
  ·
    refine ⟨71341427106477210240908311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95121902808636280321211081 71341427106477210240908311)
    ·
      refine ⟨107012140659715815361362467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71341427106477210240908311 107012140659715815361362467)
      ·
        refine ⟨160518210989573723042043701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107012140659715815361362467 160518210989573723042043701)
        ·
          refine ⟨15048582280272536535191597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 160518210989573723042043701 15048582280272536535191597)
          ·
            refine ⟨5643218355102201200696849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15048582280272536535191597 5643218355102201200696849)
            ·
              refine ⟨4232413766326650900522637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5643218355102201200696849 4232413766326650900522637)
              ·
                refine ⟨1587155162372494087695989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4232413766326650900522637 1587155162372494087695989)
                ·
                  refine ⟨148795796472421320721499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1587155162372494087695989 148795796472421320721499)
                  ·
                    rfl

theorem cell23_2608009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 3, 5].length) (baseStart_2608009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608009 prefixEnd_2608009 := by exact prefixLift 2608009
  have htrace : WordTrace (prefixWord ++ tailWord_2608009) baseStart_2608009 baseEnd_2608009 := by
    simpa [prefixWord, tailWord_2608009, baseEnd_2608009] using wordTrace_append hprefix tailTrace_2608009
  have hstable : (prefixWord ++ tailWord_2608009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608009).length < 2 ^ (prefixWord ++ tailWord_2608009).sum := by decide
  have hdescent : baseEnd_2608009 < baseStart_2608009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608077 : List Nat := [1, 6, 3, 1, 1, 1, 3, 2, 5]
def baseStart_2608077 : Nat := 118140960795 + 2608077 * 2 ^ 59
def prefixEnd_2608077 : Nat := 4983230072969 + 3 ^ 40 * 2608077 * 2
def baseEnd_2608077 : Nat := 148799676104033068938131

theorem tailTrace_2608077 : CollatzResearch.WordTrace tailWord_2608077 prefixEnd_2608077 148799676104033068938131 := by
  unfold tailWord_2608077
  simp only [CollatzResearch.WordTrace]
  refine ⟨95124382972389927934686485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63416255314926618623124323 95124382972389927934686485)
  ·
    refine ⟨4458955451830777871938429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 95124382972389927934686485 4458955451830777871938429)
    ·
      refine ⟨1672108294436541701976911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4458955451830777871938429 1672108294436541701976911)
      ·
        refine ⟨2508162441654812552965367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1672108294436541701976911 2508162441654812552965367)
        ·
          refine ⟨3762243662482218829448051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2508162441654812552965367 3762243662482218829448051)
          ·
            refine ⟨5643365493723328244172077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3762243662482218829448051 5643365493723328244172077)
            ·
              refine ⟨2116262060146248091564529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5643365493723328244172077 2116262060146248091564529)
              ·
                refine ⟨1587196545109686068673397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2116262060146248091564529 1587196545109686068673397)
                ·
                  refine ⟨148799676104033068938131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1587196545109686068673397 148799676104033068938131)
                  ·
                    rfl

theorem cell23_2608077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_2608077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608077 prefixEnd_2608077 := by exact prefixLift 2608077
  have htrace : WordTrace (prefixWord ++ tailWord_2608077) baseStart_2608077 baseEnd_2608077 := by
    simpa [prefixWord, tailWord_2608077, baseEnd_2608077] using wordTrace_append hprefix tailTrace_2608077
  have hstable : (prefixWord ++ tailWord_2608077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608077).length < 2 ^ (prefixWord ++ tailWord_2608077).sum := by decide
  have hdescent : baseEnd_2608077 < baseStart_2608077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608079 : List Nat := [1, 1, 2, 1, 1, 7, 1, 2, 2, 2, 3]
def baseStart_2608079 : Nat := 118140960795 + 2608079 * 2 ^ 59
def prefixEnd_2608079 : Nat := 4983230072969 + 3 ^ 40 * 2608079 * 2
def baseEnd_2608079 : Nat := 1339198111897606612618169

theorem tailTrace_2608079 : CollatzResearch.WordTrace tailWord_2608079 prefixEnd_2608079 1339198111897606612618169 := by
  unfold tailWord_2608079
  simp only [CollatzResearch.WordTrace]
  refine ⟨95124455918382682276259291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63416303945588454850839527 95124455918382682276259291)
  ·
    refine ⟨142686683877574023414388937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95124455918382682276259291 142686683877574023414388937)
    ·
      refine ⟨107015012908180517560791703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142686683877574023414388937 107015012908180517560791703)
      ·
        refine ⟨160522519362270776341187555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107015012908180517560791703 160522519362270776341187555)
        ·
          refine ⟨240783779043406164511781333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160522519362270776341187555 240783779043406164511781333)
          ·
            refine ⟨5643369821329831980744875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 240783779043406164511781333 5643369821329831980744875)
            ·
              refine ⟨8465054731994747971117313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5643369821329831980744875 8465054731994747971117313)
              ·
                refine ⟨6348791048996060978337985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8465054731994747971117313 6348791048996060978337985)
                ·
                  refine ⟨4761593286747045733753489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6348791048996060978337985 4761593286747045733753489)
                  ·
                    refine ⟨3571194965060284300315117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4761593286747045733753489 3571194965060284300315117)
                    ·
                      refine ⟨1339198111897606612618169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3571194965060284300315117 1339198111897606612618169)
                      ·
                        rfl

theorem cell23_2608079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 2, 3].length) (baseStart_2608079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608079 prefixEnd_2608079 := by exact prefixLift 2608079
  have htrace : WordTrace (prefixWord ++ tailWord_2608079) baseStart_2608079 baseEnd_2608079 := by
    simpa [prefixWord, tailWord_2608079, baseEnd_2608079] using wordTrace_append hprefix tailTrace_2608079
  have hstable : (prefixWord ++ tailWord_2608079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608079).length < 2 ^ (prefixWord ++ tailWord_2608079).sum := by decide
  have hdescent : baseEnd_2608079 < baseStart_2608079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608136 : List Nat := [2, 1, 3, 2, 1, 3, 2, 2, 2, 3, 2]
def baseStart_2608136 : Nat := 118140960795 + 2608136 * 2 ^ 59
def prefixEnd_2608136 : Nat := 4983230072969 + 3 ^ 40 * 2608136 * 2
def baseEnd_2608136 : Nat := 1339227380294912889605407

theorem tailTrace_2608136 : CollatzResearch.WordTrace tailWord_2608136 prefixEnd_2608136 1339227380294912889605407 := by
  unfold tailWord_2608136
  simp only [CollatzResearch.WordTrace]
  refine ⟨47563267439588090505542131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63417689919450787340722841 47563267439588090505542131)
  ·
    refine ⟨71344901159382135758313197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47563267439588090505542131 71344901159382135758313197)
    ·
      refine ⟨26754337934768300909367449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71344901159382135758313197 26754337934768300909367449)
      ·
        refine ⟨20065753451076225682025587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26754337934768300909367449 20065753451076225682025587)
        ·
          refine ⟨30098630176614338523038381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20065753451076225682025587 30098630176614338523038381)
          ·
            refine ⟨11286986316230376946139393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30098630176614338523038381 11286986316230376946139393)
            ·
              refine ⟨8465239737172782709604545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11286986316230376946139393 8465239737172782709604545)
              ·
                refine ⟨6348929802879587032203409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8465239737172782709604545 6348929802879587032203409)
                ·
                  refine ⟨4761697352159690274152557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6348929802879587032203409 4761697352159690274152557)
                  ·
                    refine ⟨1785636507059883852807209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4761697352159690274152557 1785636507059883852807209)
                    ·
                      refine ⟨1339227380294912889605407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1785636507059883852807209 1339227380294912889605407)
                      ·
                        rfl

theorem cell23_2608136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_2608136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608136 prefixEnd_2608136 := by exact prefixLift 2608136
  have htrace : WordTrace (prefixWord ++ tailWord_2608136) baseStart_2608136 baseEnd_2608136 := by
    simpa [prefixWord, tailWord_2608136, baseEnd_2608136] using wordTrace_append hprefix tailTrace_2608136
  have hstable : (prefixWord ++ tailWord_2608136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608136).length < 2 ^ (prefixWord ++ tailWord_2608136).sum := by decide
  have hdescent : baseEnd_2608136 < baseStart_2608136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608149 : List Nat := [1, 3, 2, 1, 4, 1, 1, 2, 3, 1, 4]
def baseStart_2608149 : Nat := 118140960795 + 2608149 * 2 ^ 59
def prefixEnd_2608149 : Nat := 4983230072969 + 3 ^ 40 * 2608149 * 2
def baseEnd_2608149 : Nat := 1339234055543421338742847

theorem tailTrace_2608149 : CollatzResearch.WordTrace tailWord_2608149 prefixEnd_2608149 1339234055543421338742847 := by
  unfold tailWord_2608149
  simp only [CollatzResearch.WordTrace]
  refine ⟨95127009028129084231307501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63418006018752722820871667 95127009028129084231307501)
  ·
    refine ⟨35672628385548406586740313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95127009028129084231307501 35672628385548406586740313)
    ·
      refine ⟨26754471289161304940055235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35672628385548406586740313 26754471289161304940055235)
      ·
        refine ⟨40131706933741957410082853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26754471289161304940055235 40131706933741957410082853)
        ·
          refine ⟨7524695050076617014390535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40131706933741957410082853 7524695050076617014390535)
          ·
            refine ⟨11287042575114925521585803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7524695050076617014390535 11287042575114925521585803)
            ·
              refine ⟨16930563862672388282378705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11287042575114925521585803 16930563862672388282378705)
              ·
                refine ⟨12697922897004291211784029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16930563862672388282378705 12697922897004291211784029)
                ·
                  refine ⟨4761721086376609204419011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12697922897004291211784029 4761721086376609204419011)
                  ·
                    refine ⟨7142581629564913806628517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4761721086376609204419011 7142581629564913806628517)
                    ·
                      refine ⟨1339234055543421338742847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7142581629564913806628517 1339234055543421338742847)
                      ·
                        rfl

theorem cell23_2608149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_2608149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608149 prefixEnd_2608149 := by exact prefixLift 2608149
  have htrace : WordTrace (prefixWord ++ tailWord_2608149) baseStart_2608149 baseEnd_2608149 := by
    simpa [prefixWord, tailWord_2608149, baseEnd_2608149] using wordTrace_append hprefix tailTrace_2608149
  have hstable : (prefixWord ++ tailWord_2608149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608149).length < 2 ^ (prefixWord ++ tailWord_2608149).sum := by decide
  have hdescent : baseEnd_2608149 < baseStart_2608149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608159 : List Nat := [1, 1, 2, 4, 1, 4, 2, 1, 1, 6]
def baseStart_2608159 : Nat := 118140960795 + 2608159 * 2 ^ 59
def prefixEnd_2608159 : Nat := 4983230072969 + 3 ^ 40 * 2608159 * 2
def baseEnd_2608159 : Nat := 446413063449988766539267

theorem tailTrace_2608159 : CollatzResearch.WordTrace tailWord_2608159 prefixEnd_2608159 446413063449988766539267 := by
  unfold tailWord_2608159
  simp only [CollatzResearch.WordTrace]
  refine ⟨95127373758092855939171531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63418249172061903959447687 95127373758092855939171531)
  ·
    refine ⟨142691060637139283908757297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95127373758092855939171531 142691060637139283908757297)
    ·
      refine ⟨107018295477854462931567973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142691060637139283908757297 107018295477854462931567973)
      ·
        refine ⟨20065930402097711799668995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107018295477854462931567973 20065930402097711799668995)
        ·
          refine ⟨30098895603146567699503493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20065930402097711799668995 30098895603146567699503493)
          ·
            refine ⟨5643542925589981443656905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30098895603146567699503493 5643542925589981443656905)
            ·
              refine ⟨4232657194192486082742679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5643542925589981443656905 4232657194192486082742679)
              ·
                refine ⟨6348985791288729124114019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4232657194192486082742679 6348985791288729124114019)
                ·
                  refine ⟨9523478686933093686171029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6348985791288729124114019 9523478686933093686171029)
                  ·
                    refine ⟨446413063449988766539267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9523478686933093686171029 446413063449988766539267)
                    ·
                      rfl

theorem cell23_2608159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 6].length) (baseStart_2608159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608159 prefixEnd_2608159 := by exact prefixLift 2608159
  have htrace : WordTrace (prefixWord ++ tailWord_2608159) baseStart_2608159 baseEnd_2608159 := by
    simpa [prefixWord, tailWord_2608159, baseEnd_2608159] using wordTrace_append hprefix tailTrace_2608159
  have hstable : (prefixWord ++ tailWord_2608159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608159).length < 2 ^ (prefixWord ++ tailWord_2608159).sum := by decide
  have hdescent : baseEnd_2608159 < baseStart_2608159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608170 : List Nat := [3, 1, 4, 1, 3, 2, 1, 1, 2, 3, 2]
def baseStart_2608170 : Nat := 118140960795 + 2608170 * 2 ^ 59
def prefixEnd_2608170 : Nat := 4983230072969 + 3 ^ 40 * 2608170 * 2
def baseEnd_2608170 : Nat := 1339244838637165756580251

theorem tailTrace_2608170 : CollatzResearch.WordTrace tailWord_2608170 prefixEnd_2608170 1339244838637165756580251 := by
  unfold tailWord_2608170
  simp only [CollatzResearch.WordTrace]
  refine ⟨23781943740263251204455491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63418516640702003211881309 23781943740263251204455491)
  ·
    refine ⟨35672915610394876806683237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23781943740263251204455491 35672915610394876806683237)
    ·
      refine ⟨6688671676949039401253107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35672915610394876806683237 6688671676949039401253107)
      ·
        refine ⟨10033007515423559101879661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6688671676949039401253107 10033007515423559101879661)
        ·
          refine ⟨3762377818283834663204873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10033007515423559101879661 3762377818283834663204873)
          ·
            refine ⟨2821783363712875997403655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3762377818283834663204873 2821783363712875997403655)
            ·
              refine ⟨4232675045569313996105483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2821783363712875997403655 4232675045569313996105483)
              ·
                refine ⟨6349012568353970994158225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4232675045569313996105483 6349012568353970994158225)
                ·
                  refine ⟨4761759426265478245618669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6349012568353970994158225 4761759426265478245618669)
                  ·
                    refine ⟨1785659784849554342107001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4761759426265478245618669 1785659784849554342107001)
                    ·
                      refine ⟨1339244838637165756580251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1785659784849554342107001 1339244838637165756580251)
                      ·
                        rfl

theorem cell23_2608170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_2608170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608170 prefixEnd_2608170 := by exact prefixLift 2608170
  have htrace : WordTrace (prefixWord ++ tailWord_2608170) baseStart_2608170 baseEnd_2608170 := by
    simpa [prefixWord, tailWord_2608170, baseEnd_2608170] using wordTrace_append hprefix tailTrace_2608170
  have hstable : (prefixWord ++ tailWord_2608170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608170).length < 2 ^ (prefixWord ++ tailWord_2608170).sum := by decide
  have hdescent : baseEnd_2608170 < baseStart_2608170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608180 : List Nat := [2, 5, 1, 2, 1, 3, 2, 1, 1, 5]
def baseStart_2608180 : Nat := 118140960795 + 2608180 * 2 ^ 59
def prefixEnd_2608180 : Nat := 4983230072969 + 3 ^ 40 * 2608180 * 2
def baseEnd_2608180 : Nat := 446416657814570239151735

theorem tailTrace_2608180 : CollatzResearch.WordTrace tailWord_2608180 prefixEnd_2608180 446416657814570239151735 := by
  unfold tailWord_2608180
  simp only [CollatzResearch.WordTrace]
  refine ⟨47564069845508388262842997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63418759794011184350457329 47564069845508388262842997)
  ·
    refine ⟨4459131548016411399641531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47564069845508388262842997 4459131548016411399641531)
    ·
      refine ⟨6688697322024617099462297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4459131548016411399641531 6688697322024617099462297)
      ·
        refine ⟨5016522991518462824596723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6688697322024617099462297 5016522991518462824596723)
        ·
          refine ⟨7524784487277694236895085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5016522991518462824596723 7524784487277694236895085)
          ·
            refine ⟨2821794182729135338835657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7524784487277694236895085 2821794182729135338835657)
            ·
              refine ⟨2116345637046851504126743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2821794182729135338835657 2116345637046851504126743)
              ·
                refine ⟨3174518455570277256190115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2116345637046851504126743 3174518455570277256190115)
                ·
                  refine ⟨4761777683355415884285173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3174518455570277256190115 4761777683355415884285173)
                  ·
                    refine ⟨446416657814570239151735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4761777683355415884285173 446416657814570239151735)
                    ·
                      rfl

theorem cell23_2608180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_2608180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608180 prefixEnd_2608180 := by exact prefixLift 2608180
  have htrace : WordTrace (prefixWord ++ tailWord_2608180) baseStart_2608180 baseEnd_2608180 := by
    simpa [prefixWord, tailWord_2608180, baseEnd_2608180] using wordTrace_append hprefix tailTrace_2608180
  have hstable : (prefixWord ++ tailWord_2608180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608180).length < 2 ^ (prefixWord ++ tailWord_2608180).sum := by decide
  have hdescent : baseEnd_2608180 < baseStart_2608180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608202 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 1, 9]
def baseStart_2608202 : Nat := 118140960795 + 2608202 * 2 ^ 59
def prefixEnd_2608202 : Nat := 4983230072969 + 3 ^ 40 * 2608202 * 2
def baseEnd_2608202 : Nat := 446420423339369877126701

theorem tailTrace_2608202 : CollatzResearch.WordTrace tailWord_2608202 prefixEnd_2608202 446420423339369877126701 := by
  unfold tailWord_2608202
  simp only [CollatzResearch.WordTrace]
  refine ⟨23782235524234268570746715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63419294731291382855324573 23782235524234268570746715)
  ·
    refine ⟨35673353286351402856120073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23782235524234268570746715 35673353286351402856120073)
    ·
      refine ⟨26755014964763552142090055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35673353286351402856120073 26755014964763552142090055)
      ·
        refine ⟨40132522447145328213135083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26755014964763552142090055 40132522447145328213135083)
        ·
          refine ⟨60198783670717992319702625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40132522447145328213135083 60198783670717992319702625)
          ·
            refine ⟨45149087753038494239776969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60198783670717992319702625 45149087753038494239776969)
            ·
              refine ⟨33861815814778870679832727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45149087753038494239776969 33861815814778870679832727)
              ·
                refine ⟨50792723722168306019749091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33861815814778870679832727 50792723722168306019749091)
                ·
                  refine ⟨76189085583252459029623637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50792723722168306019749091 76189085583252459029623637)
                  ·
                    refine ⟨446420423339369877126701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 76189085583252459029623637 446420423339369877126701)
                    ·
                      rfl

theorem cell23_2608202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_2608202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608202 prefixEnd_2608202 := by exact prefixLift 2608202
  have htrace : WordTrace (prefixWord ++ tailWord_2608202) baseStart_2608202 baseEnd_2608202 := by
    simpa [prefixWord, tailWord_2608202, baseEnd_2608202] using wordTrace_append hprefix tailTrace_2608202
  have hstable : (prefixWord ++ tailWord_2608202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608202).length < 2 ^ (prefixWord ++ tailWord_2608202).sum := by decide
  have hdescent : baseEnd_2608202 < baseStart_2608202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608259 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 2, 4, 3]
def baseStart_2608259 : Nat := 118140960795 + 2608259 * 2 ^ 59
def prefixEnd_2608259 : Nat := 4983230072969 + 3 ^ 40 * 2608259 * 2
def baseEnd_2608259 : Nat := 1339290538415415908367341

theorem tailTrace_2608259 : CollatzResearch.WordTrace tailWord_2608259 prefixEnd_2608259 1339290538415415908367341 := by
  unfold tailWord_2608259
  simp only [CollatzResearch.WordTrace]
  refine ⟨95131021057730573017811831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63420680705153715345207887 95131021057730573017811831)
  ·
    refine ⟨142696531586595859526717747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95131021057730573017811831 142696531586595859526717747)
    ·
      refine ⟨214044797379893789290076621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142696531586595859526717747 214044797379893789290076621)
      ·
        refine ⟨80266799017460170983778733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214044797379893789290076621 80266799017460170983778733)
        ·
          refine ⟨30100049631547564118917025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80266799017460170983778733 30100049631547564118917025)
          ·
            refine ⟨22575037223660673089187769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30100049631547564118917025 22575037223660673089187769)
            ·
              refine ⟨16931277917745504816890827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22575037223660673089187769 16931277917745504816890827)
              ·
                refine ⟨25396916876618257225336241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16931277917745504816890827 25396916876618257225336241)
                ·
                  refine ⟨19047687657463692919002181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25396916876618257225336241 19047687657463692919002181)
                  ·
                    refine ⟨3571441435774442422312909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19047687657463692919002181 3571441435774442422312909)
                    ·
                      refine ⟨1339290538415415908367341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3571441435774442422312909 1339290538415415908367341)
                      ·
                        rfl

theorem cell23_2608259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 4, 3].length) (baseStart_2608259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608259 prefixEnd_2608259 := by exact prefixLift 2608259
  have htrace : WordTrace (prefixWord ++ tailWord_2608259) baseStart_2608259 baseEnd_2608259 := by
    simpa [prefixWord, tailWord_2608259, baseEnd_2608259] using wordTrace_append hprefix tailTrace_2608259
  have hstable : (prefixWord ++ tailWord_2608259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608259).length < 2 ^ (prefixWord ++ tailWord_2608259).sum := by decide
  have hdescent : baseEnd_2608259 < baseStart_2608259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608290 : List Nat := [3, 3, 1, 3, 2, 1, 1, 2, 1, 4, 2]
def baseStart_2608290 : Nat := 118140960795 + 2608290 * 2 ^ 59
def prefixEnd_2608290 : Nat := 4983230072969 + 3 ^ 40 * 2608290 * 2
def baseEnd_2608290 : Nat := 1339306456315705287079699

theorem tailTrace_2608290 : CollatzResearch.WordTrace tailWord_2608290 prefixEnd_2608290 1339306456315705287079699 := by
  unfold tailWord_2608290
  simp only [CollatzResearch.WordTrace]
  refine ⟨23783037930154566328047581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63421434480412176874793549 23783037930154566328047581)
  ·
    refine ⟨8918639223807962373017843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23783037930154566328047581 8918639223807962373017843)
    ·
      refine ⟨13377958835711943559526765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8918639223807962373017843 13377958835711943559526765)
      ·
        refine ⟨5016734563391978834822537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13377958835711943559526765 5016734563391978834822537)
        ·
          refine ⟨3762550922543984126116903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5016734563391978834822537 3762550922543984126116903)
          ·
            refine ⟨5643826383815976189175355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3762550922543984126116903 5643826383815976189175355)
            ·
              refine ⟨8465739575723964283763033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5643826383815976189175355 8465739575723964283763033)
              ·
                refine ⟨6349304681792973212822275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8465739575723964283763033 6349304681792973212822275)
                ·
                  refine ⟨9523957022689459819233413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6349304681792973212822275 9523957022689459819233413)
                  ·
                    refine ⟨1785741941754273716106265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9523957022689459819233413 1785741941754273716106265)
                    ·
                      refine ⟨1339306456315705287079699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1785741941754273716106265 1339306456315705287079699)
                      ·
                        rfl

theorem cell23_2608290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_2608290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608290 prefixEnd_2608290 := by exact prefixLift 2608290
  have htrace : WordTrace (prefixWord ++ tailWord_2608290) baseStart_2608290 baseEnd_2608290 := by
    simpa [prefixWord, tailWord_2608290, baseEnd_2608290] using wordTrace_append hprefix tailTrace_2608290
  have hstable : (prefixWord ++ tailWord_2608290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608290).length < 2 ^ (prefixWord ++ tailWord_2608290).sum := by decide
  have hdescent : baseEnd_2608290 < baseStart_2608290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608313 : List Nat := [1, 2, 1, 4, 1, 3, 4, 2, 5]
def baseStart_2608313 : Nat := 118140960795 + 2608313 * 2 ^ 59
def prefixEnd_2608313 : Nat := 4983230072969 + 3 ^ 40 * 2608313 * 2
def baseEnd_2608313 : Nat := 148813140707862077454677

theorem tailTrace_2608313 : CollatzResearch.WordTrace tailWord_2608313 prefixEnd_2608313 148813140707862077454677 := by
  unfold tailWord_2608313
  simp only [CollatzResearch.WordTrace]
  refine ⟨95132990599534940240277593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63421993733023293493518395 95132990599534940240277593)
  ·
    refine ⟨71349742949651205180208195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95132990599534940240277593 71349742949651205180208195)
    ·
      refine ⟨107024614424476807770312293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71349742949651205180208195 107024614424476807770312293)
      ·
        refine ⟨20067115204589401456933555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107024614424476807770312293 20067115204589401456933555)
        ·
          refine ⟨30100672806884102185400333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20067115204589401456933555 30100672806884102185400333)
          ·
            refine ⟨11287752302581538319525125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30100672806884102185400333 11287752302581538319525125)
            ·
              refine ⟨2116453556734038434910961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11287752302581538319525125 2116453556734038434910961)
              ·
                refine ⟨1587340167550528826183221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2116453556734038434910961 1587340167550528826183221)
                ·
                  refine ⟨148813140707862077454677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1587340167550528826183221 148813140707862077454677)
                  ·
                    rfl

theorem cell23_2608313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 2, 5].length) (baseStart_2608313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608313 prefixEnd_2608313 := by exact prefixLift 2608313
  have htrace : WordTrace (prefixWord ++ tailWord_2608313) baseStart_2608313 baseEnd_2608313 := by
    simpa [prefixWord, tailWord_2608313, baseEnd_2608313] using wordTrace_append hprefix tailTrace_2608313
  have hstable : (prefixWord ++ tailWord_2608313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608313).length < 2 ^ (prefixWord ++ tailWord_2608313).sum := by decide
  have hdescent : baseEnd_2608313 < baseStart_2608313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608319 : List Nat := [1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 5]
def baseStart_2608319 : Nat := 118140960795 + 2608319 * 2 ^ 59
def prefixEnd_2608319 : Nat := 4983230072969 + 3 ^ 40 * 2608319 * 2
def baseEnd_2608319 : Nat := 1339321347254685673617065

theorem tailTrace_2608319 : CollatzResearch.WordTrace tailWord_2608319 prefixEnd_2608319 1339321347254685673617065 := by
  unfold tailWord_2608319
  simp only [CollatzResearch.WordTrace]
  refine ⟨95133209437513203264996011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63422139625008802176664007 95133209437513203264996011)
  ·
    refine ⟨142699814156269804897494017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95133209437513203264996011 142699814156269804897494017)
    ·
      refine ⟨107024860617202353673120513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142699814156269804897494017 107024860617202353673120513)
      ·
        refine ⟨80268645462901765254840385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107024860617202353673120513 80268645462901765254840385)
        ·
          refine ⟨60201484097176323941130289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80268645462901765254840385 60201484097176323941130289)
          ·
            refine ⟨45151113072882242955847717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60201484097176323941130289 45151113072882242955847717)
            ·
              refine ⟨8465833701165420554221447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45151113072882242955847717 8465833701165420554221447)
              ·
                refine ⟨12698750551748130831332171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8465833701165420554221447 12698750551748130831332171)
                ·
                  refine ⟨19048125827622196246998257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12698750551748130831332171 19048125827622196246998257)
                  ·
                    refine ⟨14286094370716647185248693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19048125827622196246998257 14286094370716647185248693)
                    ·
                      refine ⟨1339321347254685673617065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14286094370716647185248693 1339321347254685673617065)
                      ·
                        rfl

theorem cell23_2608319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_2608319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608319 prefixEnd_2608319 := by exact prefixLift 2608319
  have htrace : WordTrace (prefixWord ++ tailWord_2608319) baseStart_2608319 baseEnd_2608319 := by
    simpa [prefixWord, tailWord_2608319, baseEnd_2608319] using wordTrace_append hprefix tailTrace_2608319
  have hstable : (prefixWord ++ tailWord_2608319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608319).length < 2 ^ (prefixWord ++ tailWord_2608319).sum := by decide
  have hdescent : baseEnd_2608319 < baseStart_2608319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608346 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 2]
def baseStart_2608346 : Nat := 118140960795 + 2608346 * 2 ^ 59
def prefixEnd_2608346 : Nat := 4983230072969 + 3 ^ 40 * 2608346 * 2
def baseEnd_2608346 : Nat := 1339335211232357067979441

theorem tailTrace_2608346 : CollatzResearch.WordTrace tailWord_2608346 prefixEnd_2608346 1339335211232357067979441 := by
  unfold tailWord_2608346
  simp only [CollatzResearch.WordTrace]
  refine ⟨23783548552103846719057223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63422796138943591250819261 23783548552103846719057223)
  ·
    refine ⟨35675322828155770078585835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23783548552103846719057223 35675322828155770078585835)
    ·
      refine ⟨53512984242233655117878753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35675322828155770078585835 53512984242233655117878753)
      ·
        refine ⟨40134738181675241338409065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53512984242233655117878753 40134738181675241338409065)
        ·
          refine ⟨30101053636256431003806799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40134738181675241338409065 30101053636256431003806799)
          ·
            refine ⟨45151580454384646505710199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30101053636256431003806799 45151580454384646505710199)
            ·
              refine ⟨67727370681576969758565299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45151580454384646505710199 67727370681576969758565299)
              ·
                refine ⟨101591056022365454637847949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67727370681576969758565299 101591056022365454637847949)
                ·
                  refine ⟨38096646008387045489192981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101591056022365454637847949 38096646008387045489192981)
                  ·
                    refine ⟨1785780281643142757305921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38096646008387045489192981 1785780281643142757305921)
                    ·
                      refine ⟨1339335211232357067979441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1785780281643142757305921 1339335211232357067979441)
                      ·
                        rfl

theorem cell23_2608346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 2].length) (baseStart_2608346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608346 prefixEnd_2608346 := by exact prefixLift 2608346
  have htrace : WordTrace (prefixWord ++ tailWord_2608346) baseStart_2608346 baseEnd_2608346 := by
    simpa [prefixWord, tailWord_2608346, baseEnd_2608346] using wordTrace_append hprefix tailTrace_2608346
  have hstable : (prefixWord ++ tailWord_2608346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608346).length < 2 ^ (prefixWord ++ tailWord_2608346).sum := by decide
  have hdescent : baseEnd_2608346 < baseStart_2608346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608389 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 1, 2, 6]
def baseStart_2608389 : Nat := 118140960795 + 2608389 * 2 ^ 59
def prefixEnd_2608389 : Nat := 4983230072969 + 3 ^ 40 * 2608389 * 2
def baseEnd_2608389 : Nat := 1339357290900500399741743

theorem tailTrace_2608389 : CollatzResearch.WordTrace tailWord_2608389 prefixEnd_2608389 1339357290900500399741743 := by
  unfold tailWord_2608389
  simp only [CollatzResearch.WordTrace]
  refine ⟨95135762547259605220044221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63423841698173070146696147 95135762547259605220044221)
  ·
    refine ⟨35675910955222351957516583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95135762547259605220044221 35675910955222351957516583)
    ·
      refine ⟨53513866432833527936274875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35675910955222351957516583 53513866432833527936274875)
      ·
        refine ⟨80270799649250291904412313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53513866432833527936274875 80270799649250291904412313)
        ·
          refine ⟨60203099736937718928309235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80270799649250291904412313 60203099736937718928309235)
          ·
            refine ⟨90304649605406578392463853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60203099736937718928309235 90304649605406578392463853)
            ·
              refine ⟨33864243602027466897173945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90304649605406578392463853 33864243602027466897173945)
              ·
                refine ⟨25398182701520600172880459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33864243602027466897173945 25398182701520600172880459)
                ·
                  refine ⟨38097274052280900259320689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25398182701520600172880459 38097274052280900259320689)
                  ·
                    refine ⟨28572955539210675194490517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38097274052280900259320689 28572955539210675194490517)
                    ·
                      refine ⟨1339357290900500399741743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28572955539210675194490517 1339357290900500399741743)
                      ·
                        rfl

theorem cell23_2608389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_2608389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608389 prefixEnd_2608389 := by exact prefixLift 2608389
  have htrace : WordTrace (prefixWord ++ tailWord_2608389) baseStart_2608389 baseEnd_2608389 := by
    simpa [prefixWord, tailWord_2608389, baseEnd_2608389] using wordTrace_append hprefix tailTrace_2608389
  have hstable : (prefixWord ++ tailWord_2608389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608389).length < 2 ^ (prefixWord ++ tailWord_2608389).sum := by decide
  have hdescent : baseEnd_2608389 < baseStart_2608389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608473 : List Nat := [1, 2, 1, 2, 2, 2, 2, 5, 1, 2, 3]
def baseStart_2608473 : Nat := 118140960795 + 2608473 * 2 ^ 59
def prefixEnd_2608473 : Nat := 4983230072969 + 3 ^ 40 * 2608473 * 2
def baseEnd_2608473 : Nat := 1339400423275478071091357

theorem tailTrace_2608473 : CollatzResearch.WordTrace tailWord_2608473 prefixEnd_2608473 1339400423275478071091357 := by
  unfold tailWord_2608473
  simp only [CollatzResearch.WordTrace]
  refine ⟨95138826278955287566102073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63425884185970191710734715 95138826278955287566102073)
  ·
    refine ⟨71354119709216465674576555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95138826278955287566102073 71354119709216465674576555)
    ·
      refine ⟨107031179563824698511864833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71354119709216465674576555 107031179563824698511864833)
      ·
        refine ⟨80273384672868523883898625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107031179563824698511864833 80273384672868523883898625)
        ·
          refine ⟨60205038504651392912923969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80273384672868523883898625 60205038504651392912923969)
          ·
            refine ⟨45153778878488544684692977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60205038504651392912923969 45153778878488544684692977)
            ·
              refine ⟨33865334158866408513519733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45153778878488544684692977 33865334158866408513519733)
              ·
                refine ⟨3174875077393725798142475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33865334158866408513519733 3174875077393725798142475)
                ·
                  refine ⟨4762312616090588697213713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3174875077393725798142475 4762312616090588697213713)
                  ·
                    refine ⟨3571734462067941522910285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4762312616090588697213713 3571734462067941522910285)
                    ·
                      refine ⟨1339400423275478071091357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3571734462067941522910285 1339400423275478071091357)
                      ·
                        rfl

theorem cell23_2608473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 2, 3].length) (baseStart_2608473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608473 prefixEnd_2608473 := by exact prefixLift 2608473
  have htrace : WordTrace (prefixWord ++ tailWord_2608473) baseStart_2608473 baseEnd_2608473 := by
    simpa [prefixWord, tailWord_2608473, baseEnd_2608473] using wordTrace_append hprefix tailTrace_2608473
  have hstable : (prefixWord ++ tailWord_2608473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608473).length < 2 ^ (prefixWord ++ tailWord_2608473).sum := by decide
  have hdescent : baseEnd_2608473 < baseStart_2608473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608480 : List Nat := [2, 1, 1, 3, 4, 2, 2, 2, 2, 4]
def baseStart_2608480 : Nat := 118140960795 + 2608480 * 2 ^ 59
def prefixEnd_2608480 : Nat := 4983230072969 + 3 ^ 40 * 2608480 * 2
def baseEnd_2608480 : Nat := 446468005880019847901275

theorem tailTrace_2608480 : CollatzResearch.WordTrace tailWord_2608480 prefixEnd_2608480 446468005880019847901275 := by
  unfold tailWord_2608480
  simp only [CollatzResearch.WordTrace]
  refine ⟨47569540794964963880803447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63426054393286618507737929 47569540794964963880803447)
  ·
    refine ⟨71354311192447445821205171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47569540794964963880803447 71354311192447445821205171)
    ·
      refine ⟨107031466788671168731807757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71354311192447445821205171 107031466788671168731807757)
      ·
        refine ⟨40136800045751688274427909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107031466788671168731807757 40136800045751688274427909)
        ·
          refine ⟨7525650008578441551455233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40136800045751688274427909 7525650008578441551455233)
          ·
            refine ⟨5644237506433831163591425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7525650008578441551455233 5644237506433831163591425)
            ·
              refine ⟨4233178129825373372693569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5644237506433831163591425 4233178129825373372693569)
              ·
                refine ⟨3174883597369030029520177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4233178129825373372693569 3174883597369030029520177)
                ·
                  refine ⟨2381162698026772522140133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3174883597369030029520177 2381162698026772522140133)
                  ·
                    refine ⟨446468005880019847901275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2381162698026772522140133 446468005880019847901275)
                    ·
                      rfl

theorem cell23_2608480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 2, 4].length) (baseStart_2608480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608480 prefixEnd_2608480 := by exact prefixLift 2608480
  have htrace : WordTrace (prefixWord ++ tailWord_2608480) baseStart_2608480 baseEnd_2608480 := by
    simpa [prefixWord, tailWord_2608480, baseEnd_2608480] using wordTrace_append hprefix tailTrace_2608480
  have hstable : (prefixWord ++ tailWord_2608480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608480).length < 2 ^ (prefixWord ++ tailWord_2608480).sum := by decide
  have hdescent : baseEnd_2608480 < baseStart_2608480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608493 : List Nat := [1, 5, 1, 1, 1, 5, 1, 8]
def baseStart_2608493 : Nat := 118140960795 + 2608493 * 2 ^ 59
def prefixEnd_2608493 : Nat := 4983230072969 + 3 ^ 40 * 2608493 * 2
def baseEnd_2608493 : Nat := 49607803440317333068195

theorem tailTrace_2608493 : CollatzResearch.WordTrace tailWord_2608493 prefixEnd_2608493 49607803440317333068195 := by
  unfold tailWord_2608493
  simp only [CollatzResearch.WordTrace]
  refine ⟨95139555738882830981830133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63426370492588553987886755 95139555738882830981830133)
  ·
    refine ⟨8919333350520265404546575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95139555738882830981830133 8919333350520265404546575)
    ·
      refine ⟨13379000025780398106819863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8919333350520265404546575 13379000025780398106819863)
      ·
        refine ⟨20068500038670597160229795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13379000025780398106819863 20068500038670597160229795)
        ·
          refine ⟨30102750058005895740344693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20068500038670597160229795 30102750058005895740344693)
          ·
            refine ⟨2822132817938052725657315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30102750058005895740344693 2822132817938052725657315)
            ·
              refine ⟨4233199226907079088485973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2822132817938052725657315 4233199226907079088485973)
              ·
                refine ⟨49607803440317333068195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4233199226907079088485973 49607803440317333068195)
                ·
                  rfl

theorem cell23_2608493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 8].length) (baseStart_2608493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608493 prefixEnd_2608493 := by exact prefixLift 2608493
  have htrace : WordTrace (prefixWord ++ tailWord_2608493) baseStart_2608493 baseEnd_2608493 := by
    simpa [prefixWord, tailWord_2608493, baseEnd_2608493] using wordTrace_append hprefix tailTrace_2608493
  have hstable : (prefixWord ++ tailWord_2608493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608493).length < 2 ^ (prefixWord ++ tailWord_2608493).sum := by decide
  have hdescent : baseEnd_2608493 < baseStart_2608493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608503 : List Nat := [1, 1, 3, 1, 1, 2, 6, 1, 1, 3, 3]
def baseStart_2608503 : Nat := 118140960795 + 2608503 * 2 ^ 59
def prefixEnd_2608503 : Nat := 4983230072969 + 3 ^ 40 * 2608503 * 2
def baseEnd_2608503 : Nat := 1339415827695112953716219

theorem tailTrace_2608503 : CollatzResearch.WordTrace tailWord_2608503 prefixEnd_2608503 1339415827695112953716219 := by
  unfold tailWord_2608503
  simp only [CollatzResearch.WordTrace]
  refine ⟨95139920468846602689694163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63426613645897735126462775 95139920468846602689694163)
  ·
    refine ⟨142709880703269904034541245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95139920468846602689694163 142709880703269904034541245)
    ·
      refine ⟨53516205263726214012952967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142709880703269904034541245 53516205263726214012952967)
      ·
        refine ⟨80274307895589321019429451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53516205263726214012952967 80274307895589321019429451)
        ·
          refine ⟨120411461843383981529144177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80274307895589321019429451 120411461843383981529144177)
          ·
            refine ⟨90308596382537986146858133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120411461843383981529144177 90308596382537986146858133)
            ·
              refine ⟨4233215455431468100633975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90308596382537986146858133 4233215455431468100633975)
              ·
                refine ⟨6349823183147202150950963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4233215455431468100633975 6349823183147202150950963)
                ·
                  refine ⟨9524734774720803226426445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6349823183147202150950963 9524734774720803226426445)
                  ·
                    refine ⟨3571775540520301209909917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9524734774720803226426445 3571775540520301209909917)
                    ·
                      refine ⟨1339415827695112953716219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3571775540520301209909917 1339415827695112953716219)
                      ·
                        rfl

theorem cell23_2608503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 3, 3].length) (baseStart_2608503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608503 prefixEnd_2608503 := by exact prefixLift 2608503
  have htrace : WordTrace (prefixWord ++ tailWord_2608503) baseStart_2608503 baseEnd_2608503 := by
    simpa [prefixWord, tailWord_2608503, baseEnd_2608503] using wordTrace_append hprefix tailTrace_2608503
  have hstable : (prefixWord ++ tailWord_2608503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608503).length < 2 ^ (prefixWord ++ tailWord_2608503).sum := by decide
  have hdescent : baseEnd_2608503 < baseStart_2608503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608537 : List Nat := [1, 2, 1, 2, 1, 7, 1, 2, 2, 1, 3]
def baseStart_2608537 : Nat := 118140960795 + 2608537 * 2 ^ 59
def prefixEnd_2608537 : Nat := 4983230072969 + 3 ^ 40 * 2608537 * 2
def baseEnd_2608537 : Nat := 1339433286037365820691063

theorem tailTrace_2608537 : CollatzResearch.WordTrace tailWord_2608537 prefixEnd_2608537 1339433286037365820691063 := by
  unfold tailWord_2608537
  simp only [CollatzResearch.WordTrace]
  refine ⟨95141160550723426496431865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63427440367148950997621243 95141160550723426496431865)
  ·
    refine ⟨71355870413042569872323899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95141160550723426496431865 71355870413042569872323899)
    ·
      refine ⟨107033805619563854808485849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71355870413042569872323899 107033805619563854808485849)
      ·
        refine ⟨80275354214672891106364387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107033805619563854808485849 80275354214672891106364387)
        ·
          refine ⟨120413031322009336659546581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80275354214672891106364387 120413031322009336659546581)
          ·
            refine ⟨2822180421609593827958123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 120413031322009336659546581 2822180421609593827958123)
            ·
              refine ⟨4233270632414390741937185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2822180421609593827958123 4233270632414390741937185)
              ·
                refine ⟨3174952974310793056452889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4233270632414390741937185 3174952974310793056452889)
                ·
                  refine ⟨2381214730733094792339667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3174952974310793056452889 2381214730733094792339667)
                  ·
                    refine ⟨3571822096099642188509501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2381214730733094792339667 3571822096099642188509501)
                    ·
                      refine ⟨1339433286037365820691063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3571822096099642188509501 1339433286037365820691063)
                      ·
                        rfl

theorem cell23_2608537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 2, 1, 3].length) (baseStart_2608537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608537 prefixEnd_2608537 := by exact prefixLift 2608537
  have htrace : WordTrace (prefixWord ++ tailWord_2608537) baseStart_2608537 baseEnd_2608537 := by
    simpa [prefixWord, tailWord_2608537, baseEnd_2608537] using wordTrace_append hprefix tailTrace_2608537
  have hstable : (prefixWord ++ tailWord_2608537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608537).length < 2 ^ (prefixWord ++ tailWord_2608537).sum := by decide
  have hdescent : baseEnd_2608537 < baseStart_2608537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608580 : List Nat := [2, 3, 3, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_2608580 : Nat := 118140960795 + 2608580 * 2 ^ 59
def prefixEnd_2608580 : Nat := 4983230072969 + 3 ^ 40 * 2608580 * 2
def baseEnd_2608580 : Nat := 1339455365705509152453365

theorem tailTrace_2608580 : CollatzResearch.WordTrace tailWord_2608580 prefixEnd_2608580 1339455365705509152453365 := by
  unfold tailWord_2608580
  simp only [CollatzResearch.WordTrace]
  refine ⟨47571364444783822420123597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63428485926378429893498129 47571364444783822420123597)
  ·
    refine ⟨17839261666793933407546349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47571364444783822420123597 17839261666793933407546349)
    ·
      refine ⟨6689723125047725027829881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17839261666793933407546349 6689723125047725027829881)
      ·
        refine ⟨5017292343785793770872411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6689723125047725027829881 5017292343785793770872411)
        ·
          refine ⟨7525938515678690656308617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5017292343785793770872411 7525938515678690656308617)
          ·
            refine ⟨5644453886759017992231463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7525938515678690656308617 5644453886759017992231463)
            ·
              refine ⟨8466680830138526988347195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5644453886759017992231463 8466680830138526988347195)
              ·
                refine ⟨12700021245207790482520793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8466680830138526988347195 12700021245207790482520793)
                ·
                  refine ⟨9525015933905842861890595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12700021245207790482520793 9525015933905842861890595)
                  ·
                    refine ⟨14287523900858764292835893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9525015933905842861890595 14287523900858764292835893)
                    ·
                      refine ⟨1339455365705509152453365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14287523900858764292835893 1339455365705509152453365)
                      ·
                        rfl

theorem cell23_2608580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_2608580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608580 prefixEnd_2608580 := by exact prefixLift 2608580
  have htrace : WordTrace (prefixWord ++ tailWord_2608580) baseStart_2608580 baseEnd_2608580 := by
    simpa [prefixWord, tailWord_2608580, baseEnd_2608580] using wordTrace_append hprefix tailTrace_2608580
  have hstable : (prefixWord ++ tailWord_2608580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608580).length < 2 ^ (prefixWord ++ tailWord_2608580).sum := by decide
  have hdescent : baseEnd_2608580 < baseStart_2608580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608603 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 5, 7, 2]
def baseStart_2608603 : Nat := 118140960795 + 2608603 * 2 ^ 59
def prefixEnd_2608603 : Nat := 4983230072969 + 3 ^ 40 * 2608603 * 2
def baseEnd_2608603 : Nat := 1339467175760562562465759

theorem tailTrace_2608603 : CollatzResearch.WordTrace tailWord_2608603 prefixEnd_2608603 1339467175760562562465759 := by
  unfold tailWord_2608603
  simp only [CollatzResearch.WordTrace]
  refine ⟨95143567768484319768334463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63429045178989546512222975 95143567768484319768334463)
  ·
    refine ⟨142715351652726479652501695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95143567768484319768334463 142715351652726479652501695)
    ·
      refine ⟨214073027479089719478752543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142715351652726479652501695 214073027479089719478752543)
      ·
        refine ⟨321109541218634579218128815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214073027479089719478752543 321109541218634579218128815)
        ·
          refine ⟨481664311827951868827193223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321109541218634579218128815 481664311827951868827193223)
          ·
            refine ⟨722496467741927803240789835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 481664311827951868827193223 722496467741927803240789835)
            ·
              refine ⟨1083744701612891704861184753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 722496467741927803240789835 1083744701612891704861184753)
              ·
                refine ⟨812808526209668778645888565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1083744701612891704861184753 812808526209668778645888565)
                ·
                  refine ⟨76200799332156447998052053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 812808526209668778645888565 76200799332156447998052053)
                  ·
                    refine ⟨1785956234347416749954345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 76200799332156447998052053 1785956234347416749954345)
                    ·
                      refine ⟨1339467175760562562465759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1785956234347416749954345 1339467175760562562465759)
                      ·
                        rfl

theorem cell23_2608603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 7, 2].length) (baseStart_2608603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608603 prefixEnd_2608603 := by exact prefixLift 2608603
  have htrace : WordTrace (prefixWord ++ tailWord_2608603) baseStart_2608603 baseEnd_2608603 := by
    simpa [prefixWord, tailWord_2608603, baseEnd_2608603] using wordTrace_append hprefix tailTrace_2608603
  have hstable : (prefixWord ++ tailWord_2608603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608603).length < 2 ^ (prefixWord ++ tailWord_2608603).sum := by decide
  have hdescent : baseEnd_2608603 < baseStart_2608603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608611 : List Nat := [1, 1, 1, 6, 2, 3, 2, 1, 2, 2, 2]
def baseStart_2608611 : Nat := 118140960795 + 2608611 * 2 ^ 59
def prefixEnd_2608611 : Nat := 4983230072969 + 3 ^ 40 * 2608611 * 2
def baseEnd_2608611 : Nat := 1339471283605798531165723

theorem tailTrace_2608611 : CollatzResearch.WordTrace tailWord_2608611 prefixEnd_2608611 1339471283605798531165723 := by
  unfold tailWord_2608611
  simp only [CollatzResearch.WordTrace]
  refine ⟨95143859552455337134625687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63429239701636891423083791 95143859552455337134625687)
  ·
    refine ⟨142715789328683005701938531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95143859552455337134625687 142715789328683005701938531)
    ·
      refine ⟨214073683993024508552907797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142715789328683005701938531 214073683993024508552907797)
      ·
        refine ⟨10034703937173023838417553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 214073683993024508552907797 10034703937173023838417553)
        ·
          refine ⟨7526027952879767878813165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10034703937173023838417553 7526027952879767878813165)
          ·
            refine ⟨2822260482329912954554937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7526027952879767878813165 2822260482329912954554937)
            ·
              refine ⟨2116695361747434715916203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2822260482329912954554937 2116695361747434715916203)
              ·
                refine ⟨3175043042621152073874305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2116695361747434715916203 3175043042621152073874305)
                ·
                  refine ⟨2381282281965864055405729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3175043042621152073874305 2381282281965864055405729)
                  ·
                    refine ⟨1785961711474398041554297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2381282281965864055405729 1785961711474398041554297)
                    ·
                      refine ⟨1339471283605798531165723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1785961711474398041554297 1339471283605798531165723)
                      ·
                        rfl

theorem cell23_2608611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_2608611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608611 prefixEnd_2608611 := by exact prefixLift 2608611
  have htrace : WordTrace (prefixWord ++ tailWord_2608611) baseStart_2608611 baseEnd_2608611 := by
    simpa [prefixWord, tailWord_2608611, baseEnd_2608611] using wordTrace_append hprefix tailTrace_2608611
  have hstable : (prefixWord ++ tailWord_2608611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608611).length < 2 ^ (prefixWord ++ tailWord_2608611).sum := by decide
  have hdescent : baseEnd_2608611 < baseStart_2608611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608630 : List Nat := [5, 1, 1, 1, 2, 2, 1, 3, 2, 5]
def baseStart_2608630 : Nat := 118140960795 + 2608630 * 2 ^ 59
def prefixEnd_2608630 : Nat := 4983230072969 + 3 ^ 40 * 2608630 * 2
def baseEnd_2608630 : Nat := 446493679912744652276045

theorem tailTrace_2608630 : CollatzResearch.WordTrace tailWord_2608630 prefixEnd_2608630 446493679912744652276045 := by
  unfold tailWord_2608630
  simp only [CollatzResearch.WordTrace]
  refine ⟨5946534533711656461222959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63429701692924335586378229 5946534533711656461222959)
  ·
    refine ⟨8919801800567484691834439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5946534533711656461222959 8919801800567484691834439)
    ·
      refine ⟨13379702700851227037751659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8919801800567484691834439 13379702700851227037751659)
      ·
        refine ⟨20069554051276840556627489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13379702700851227037751659 20069554051276840556627489)
        ·
          refine ⟨15052165538457630417470617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20069554051276840556627489 15052165538457630417470617)
          ·
            refine ⟨11289124153843222813102963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15052165538457630417470617 11289124153843222813102963)
            ·
              refine ⟨16933686230764834219654445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11289124153843222813102963 16933686230764834219654445)
              ·
                refine ⟨6350132336536812832370417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16933686230764834219654445 6350132336536812832370417)
                ·
                  refine ⟨4762599252402609624277813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6350132336536812832370417 4762599252402609624277813)
                  ·
                    refine ⟨446493679912744652276045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4762599252402609624277813 446493679912744652276045)
                    ·
                      rfl

theorem cell23_2608630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_2608630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608630 prefixEnd_2608630 := by exact prefixLift 2608630
  have htrace : WordTrace (prefixWord ++ tailWord_2608630) baseStart_2608630 baseEnd_2608630 := by
    simpa [prefixWord, tailWord_2608630, baseEnd_2608630] using wordTrace_append hprefix tailTrace_2608630
  have hstable : (prefixWord ++ tailWord_2608630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608630).length < 2 ^ (prefixWord ++ tailWord_2608630).sum := by decide
  have hdescent : baseEnd_2608630 < baseStart_2608630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608643 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 7, 4]
def baseStart_2608643 : Nat := 118140960795 + 2608643 * 2 ^ 59
def prefixEnd_2608643 : Nat := 4983230072969 + 3 ^ 40 * 2608643 * 2
def baseEnd_2608643 : Nat := 446495904995580801988525

theorem tailTrace_2608643 : CollatzResearch.WordTrace tailWord_2608643 prefixEnd_2608643 446495904995580801988525 := by
  unfold tailWord_2608643
  simp only [CollatzResearch.WordTrace]
  refine ⟨95145026688339406599790583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63430017792226271066527055 95145026688339406599790583)
  ·
    refine ⟨142717540032509109899685875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95145026688339406599790583 142717540032509109899685875)
    ·
      refine ⟨214076310048763664849528813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142717540032509109899685875 214076310048763664849528813)
      ·
        refine ⟨80278616268286374318573305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214076310048763664849528813 80278616268286374318573305)
        ·
          refine ⟨60208962201214780738929979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80278616268286374318573305 60208962201214780738929979)
          ·
            refine ⟨90313443301822171108394969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60208962201214780738929979 90313443301822171108394969)
            ·
              refine ⟨67735082476366628331296227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90313443301822171108394969 67735082476366628331296227)
              ·
                refine ⟨101602623714549942496944341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67735082476366628331296227 101602623714549942496944341)
                ·
                  refine ⟨2381311493309764277272133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 101602623714549942496944341 2381311493309764277272133)
                  ·
                    refine ⟨446495904995580801988525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2381311493309764277272133 446495904995580801988525)
                    ·
                      rfl

theorem cell23_2608643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 7, 4].length) (baseStart_2608643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608643 prefixEnd_2608643 := by exact prefixLift 2608643
  have htrace : WordTrace (prefixWord ++ tailWord_2608643) baseStart_2608643 baseEnd_2608643 := by
    simpa [prefixWord, tailWord_2608643, baseEnd_2608643] using wordTrace_append hprefix tailTrace_2608643
  have hstable : (prefixWord ++ tailWord_2608643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608643).length < 2 ^ (prefixWord ++ tailWord_2608643).sum := by decide
  have hdescent : baseEnd_2608643 < baseStart_2608643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608650 : List Nat := [3, 1, 2, 2, 2, 2, 2, 2, 2, 1, 4]
def baseStart_2608650 : Nat := 118140960795 + 2608650 * 2 ^ 59
def prefixEnd_2608650 : Nat := 4983230072969 + 3 ^ 40 * 2608650 * 2
def baseEnd_2608650 : Nat := 1339491309351323878578043

theorem tailTrace_2608650 : CollatzResearch.WordTrace tailWord_2608650 prefixEnd_2608650 1339491309351323878578043 := by
  unfold tailWord_2608650
  simp only [CollatzResearch.WordTrace]
  refine ⟨23786320499828511698823851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63430187999542697863530269 23786320499828511698823851)
  ·
    refine ⟨35679480749742767548235777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23786320499828511698823851 35679480749742767548235777)
    ·
      refine ⟨26759610562307075661176833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35679480749742767548235777 26759610562307075661176833)
      ·
        refine ⟨20069707921730306745882625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26759610562307075661176833 20069707921730306745882625)
        ·
          refine ⟨15052280941297730059411969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20069707921730306745882625 15052280941297730059411969)
          ·
            refine ⟨11289210705973297544558977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15052280941297730059411969 11289210705973297544558977)
            ·
              refine ⟨8466908029479973158419233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11289210705973297544558977 8466908029479973158419233)
              ·
                refine ⟨6350181022109979868814425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8466908029479973158419233 6350181022109979868814425)
                ·
                  refine ⟨4762635766582484901610819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6350181022109979868814425 4762635766582484901610819)
                  ·
                    refine ⟨7143953649873727352416229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4762635766582484901610819 7143953649873727352416229)
                    ·
                      refine ⟨1339491309351323878578043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7143953649873727352416229 1339491309351323878578043)
                      ·
                        rfl

theorem cell23_2608650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_2608650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608650 prefixEnd_2608650 := by exact prefixLift 2608650
  have htrace : WordTrace (prefixWord ++ tailWord_2608650) baseStart_2608650 baseEnd_2608650 := by
    simpa [prefixWord, tailWord_2608650, baseEnd_2608650] using wordTrace_append hprefix tailTrace_2608650
  have hstable : (prefixWord ++ tailWord_2608650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608650).length < 2 ^ (prefixWord ++ tailWord_2608650).sum := by decide
  have hdescent : baseEnd_2608650 < baseStart_2608650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608793 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 4, 7]
def baseStart_2608793 : Nat := 118140960795 + 2608793 * 2 ^ 59
def prefixEnd_2608793 : Nat := 4983230072969 + 3 ^ 40 * 2608793 * 2
def baseEnd_2608793 : Nat := 446521579028305606363295

theorem tailTrace_2608793 : CollatzResearch.WordTrace tailWord_2608793 prefixEnd_2608793 446521579028305606363295 := by
  unfold tailWord_2608793
  simp only [CollatzResearch.WordTrace]
  refine ⟨95150497637795982217751033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63433665091863988145167355 95150497637795982217751033)
  ·
    refine ⟨71362873228346986663313275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95150497637795982217751033 71362873228346986663313275)
    ·
      refine ⟨107044309842520479994969913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71362873228346986663313275 107044309842520479994969913)
      ·
        refine ⟨80283232381890359996227435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107044309842520479994969913 80283232381890359996227435)
        ·
          refine ⟨120424848572835539994341153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80283232381890359996227435 120424848572835539994341153)
          ·
            refine ⟨90318636429626654995755865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120424848572835539994341153 90318636429626654995755865)
            ·
              refine ⟨67738977322219991246816899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90318636429626654995755865 67738977322219991246816899)
              ·
                refine ⟨101608465983329986870225349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67738977322219991246816899 101608465983329986870225349)
                ·
                  refine ⟨19051587371874372538167253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101608465983329986870225349 19051587371874372538167253)
                  ·
                    refine ⟨446521579028305606363295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19051587371874372538167253 446521579028305606363295)
                    ·
                      rfl

theorem cell23_2608793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 7].length) (baseStart_2608793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608793 prefixEnd_2608793 := by exact prefixLift 2608793
  have htrace : WordTrace (prefixWord ++ tailWord_2608793) baseStart_2608793 baseEnd_2608793 := by
    simpa [prefixWord, tailWord_2608793, baseEnd_2608793] using wordTrace_append hprefix tailTrace_2608793
  have hstable : (prefixWord ++ tailWord_2608793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608793).length < 2 ^ (prefixWord ++ tailWord_2608793).sum := by decide
  have hdescent : baseEnd_2608793 < baseStart_2608793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608840 : List Nat := [2, 1, 3, 1, 2, 2, 3, 1, 2, 6]
def baseStart_2608840 : Nat := 118140960795 + 2608840 * 2 ^ 59
def prefixEnd_2608840 : Nat := 4983230072969 + 3 ^ 40 * 2608840 * 2
def baseEnd_2608840 : Nat := 446529623558559378400723

theorem tailTrace_2608840 : CollatzResearch.WordTrace tailWord_2608840 prefixEnd_2608840 446529623558559378400723 := by
  unfold tailWord_2608840
  simp only [CollatzResearch.WordTrace]
  refine ⟨47576105934312854622355987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63434807912417139496474649 47576105934312854622355987)
  ·
    refine ⟨71364158901469281933533981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47576105934312854622355987 71364158901469281933533981)
    ·
      refine ⟨26761559588050980725075243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71364158901469281933533981 26761559588050980725075243)
      ·
        refine ⟨40142339382076471087612865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26761559588050980725075243 40142339382076471087612865)
        ·
          refine ⟨30106754536557353315709649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40142339382076471087612865 30106754536557353315709649)
          ·
            refine ⟨22580065902418014986782237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30106754536557353315709649 22580065902418014986782237)
            ·
              refine ⟨8467524713406755620043339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22580065902418014986782237 8467524713406755620043339)
              ·
                refine ⟨12701287070110133430065009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8467524713406755620043339 12701287070110133430065009)
                ·
                  refine ⟨9525965302582600072548757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12701287070110133430065009 9525965302582600072548757)
                  ·
                    refine ⟨446529623558559378400723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9525965302582600072548757 446529623558559378400723)
                    ·
                      rfl

theorem cell23_2608840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_2608840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608840 prefixEnd_2608840 := by exact prefixLift 2608840
  have htrace : WordTrace (prefixWord ++ tailWord_2608840) baseStart_2608840 baseEnd_2608840 := by
    simpa [prefixWord, tailWord_2608840, baseEnd_2608840] using wordTrace_append hprefix tailTrace_2608840
  have hstable : (prefixWord ++ tailWord_2608840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608840).length < 2 ^ (prefixWord ++ tailWord_2608840).sum := by decide
  have hdescent : baseEnd_2608840 < baseStart_2608840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608877 : List Nat := [1, 5, 1, 2, 1, 2, 1, 2, 2, 2, 4]
def baseStart_2608877 : Nat := 118140960795 + 2608877 * 2 ^ 59
def prefixEnd_2608877 : Nat := 4983230072969 + 3 ^ 40 * 2608877 * 2
def baseEnd_2608877 : Nat := 1339607869459894490439499

theorem tailTrace_2608877 : CollatzResearch.WordTrace tailWord_2608877 prefixEnd_2608877 1339607869459894490439499 := by
  unfold tailWord_2608877
  simp only [CollatzResearch.WordTrace]
  refine ⟨95153561369491664563808885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63435707579661109709205923 95153561369491664563808885)
  ·
    refine ⟨8920646378389843552857083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95153561369491664563808885 8920646378389843552857083)
    ·
      refine ⟨13380969567584765329285625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8920646378389843552857083 13380969567584765329285625)
      ·
        refine ⟨10035727175688573996964219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13380969567584765329285625 10035727175688573996964219)
        ·
          refine ⟨15053590763532860995446329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10035727175688573996964219 15053590763532860995446329)
          ·
            refine ⟨11290193072649645746584747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15053590763532860995446329 11290193072649645746584747)
            ·
              refine ⟨16935289608974468619877121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11290193072649645746584747 16935289608974468619877121)
              ·
                refine ⟨12701467206730851464907841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16935289608974468619877121 12701467206730851464907841)
                ·
                  refine ⟨9526100405048138598680881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12701467206730851464907841 9526100405048138598680881)
                  ·
                    refine ⟨7144575303786103949010661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9526100405048138598680881 7144575303786103949010661)
                    ·
                      refine ⟨1339607869459894490439499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7144575303786103949010661 1339607869459894490439499)
                      ·
                        rfl

theorem cell23_2608877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_2608877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608877 prefixEnd_2608877 := by exact prefixLift 2608877
  have htrace : WordTrace (prefixWord ++ tailWord_2608877) baseStart_2608877 baseEnd_2608877 := by
    simpa [prefixWord, tailWord_2608877, baseEnd_2608877] using wordTrace_append hprefix tailTrace_2608877
  have hstable : (prefixWord ++ tailWord_2608877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608877).length < 2 ^ (prefixWord ++ tailWord_2608877).sum := by decide
  have hdescent : baseEnd_2608877 < baseStart_2608877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608881 : List Nat := [1, 2, 2, 2, 2, 3, 3, 2, 2, 2, 2]
def baseStart_2608881 : Nat := 118140960795 + 2608881 * 2 ^ 59
def prefixEnd_2608881 : Nat := 4983230072969 + 3 ^ 40 * 2608881 * 2
def baseEnd_2608881 : Nat := 1339609923382512474789481

theorem tailTrace_2608881 : CollatzResearch.WordTrace tailWord_2608881 prefixEnd_2608881 1339609923382512474789481 := by
  unfold tailWord_2608881
  simp only [CollatzResearch.WordTrace]
  refine ⟨95153707261477173246954497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63435804840984782164636331 95153707261477173246954497)
  ·
    refine ⟨71365280446107879935215873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95153707261477173246954497 71365280446107879935215873)
    ·
      refine ⟨53523960334580909951411905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71365280446107879935215873 53523960334580909951411905)
      ·
        refine ⟨40142970250935682463558929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53523960334580909951411905 40142970250935682463558929)
        ·
          refine ⟨30107227688201761847669197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40142970250935682463558929 30107227688201761847669197)
          ·
            refine ⟨11290210383075660692875949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30107227688201761847669197 11290210383075660692875949)
            ·
              refine ⟨4233828893653372759828481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11290210383075660692875949 4233828893653372759828481)
              ·
                refine ⟨3175371670240029569871361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4233828893653372759828481 3175371670240029569871361)
                ·
                  refine ⟨2381528752680022177403521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3175371670240029569871361 2381528752680022177403521)
                  ·
                    refine ⟨1786146564510016633052641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2381528752680022177403521 1786146564510016633052641)
                    ·
                      refine ⟨1339609923382512474789481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1786146564510016633052641 1339609923382512474789481)
                      ·
                        rfl

theorem cell23_2608881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 2, 2, 2].length) (baseStart_2608881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608881 prefixEnd_2608881 := by exact prefixLift 2608881
  have htrace : WordTrace (prefixWord ++ tailWord_2608881) baseStart_2608881 baseEnd_2608881 := by
    simpa [prefixWord, tailWord_2608881, baseEnd_2608881] using wordTrace_append hprefix tailTrace_2608881
  have hstable : (prefixWord ++ tailWord_2608881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608881).length < 2 ^ (prefixWord ++ tailWord_2608881).sum := by decide
  have hdescent : baseEnd_2608881 < baseStart_2608881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608887 : List Nat := [1, 1, 3, 1, 1, 1, 6, 4, 5]
def baseStart_2608887 : Nat := 118140960795 + 2608887 * 2 ^ 59
def prefixEnd_2608887 : Nat := 4983230072969 + 3 ^ 40 * 2608887 * 2
def baseEnd_2608887 : Nat := 148845889362937716812717

theorem tailTrace_2608887 : CollatzResearch.WordTrace tailWord_2608887 prefixEnd_2608887 148845889362937716812717 := by
  unfold tailWord_2608887
  simp only [CollatzResearch.WordTrace]
  refine ⟨95153926099455436271672915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63435950732970290847781943 95153926099455436271672915)
  ·
    refine ⟨142730889149183154407509373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95153926099455436271672915 142730889149183154407509373)
    ·
      refine ⟨53524083430943682902816015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142730889149183154407509373 53524083430943682902816015)
      ·
        refine ⟨80286125146415524354224023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53524083430943682902816015 80286125146415524354224023)
        ·
          refine ⟨120429187719623286531336035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80286125146415524354224023 120429187719623286531336035)
          ·
            refine ⟨180643781579434929797004053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120429187719623286531336035 180643781579434929797004053)
            ·
              refine ⟨8467677261536012334234565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 180643781579434929797004053 8467677261536012334234565)
              ·
                refine ⟨1587689486538002312668981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8467677261536012334234565 1587689486538002312668981)
                ·
                  refine ⟨148845889362937716812717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1587689486538002312668981 148845889362937716812717)
                  ·
                    rfl

theorem cell23_2608887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 4, 5].length) (baseStart_2608887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608887 prefixEnd_2608887 := by exact prefixLift 2608887
  have htrace : WordTrace (prefixWord ++ tailWord_2608887) baseStart_2608887 baseEnd_2608887 := by
    simpa [prefixWord, tailWord_2608887, baseEnd_2608887] using wordTrace_append hprefix tailTrace_2608887
  have hstable : (prefixWord ++ tailWord_2608887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608887).length < 2 ^ (prefixWord ++ tailWord_2608887).sum := by decide
  have hdescent : baseEnd_2608887 < baseStart_2608887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608897 : List Nat := [1, 2, 4, 1, 1, 1, 4, 1, 2, 3, 3]
def baseStart_2608897 : Nat := 118140960795 + 2608897 * 2 ^ 59
def prefixEnd_2608897 : Nat := 4983230072969 + 3 ^ 40 * 2608897 * 2
def baseEnd_2608897 : Nat := 1339618139072984412189407

theorem tailTrace_2608897 : CollatzResearch.WordTrace tailWord_2608897 prefixEnd_2608897 1339618139072984412189407 := by
  unfold tailWord_2608897
  simp only [CollatzResearch.WordTrace]
  refine ⟨95154290829419207979536945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63436193886279471986357963 95154290829419207979536945)
  ·
    refine ⟨71365718122064405984652709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95154290829419207979536945 71365718122064405984652709)
    ·
      refine ⟨13381072147887076122122383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71365718122064405984652709 13381072147887076122122383)
      ·
        refine ⟨20071608221830614183183575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13381072147887076122122383 20071608221830614183183575)
        ·
          refine ⟨30107412332745921274775363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20071608221830614183183575 30107412332745921274775363)
          ·
            refine ⟨45161118499118881912163045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30107412332745921274775363 45161118499118881912163045)
            ·
              refine ⟨8467709718584790358530571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45161118499118881912163045 8467709718584790358530571)
              ·
                refine ⟨12701564577877185537795857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8467709718584790358530571 12701564577877185537795857)
                ·
                  refine ⟨9526173433407889153346893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12701564577877185537795857 9526173433407889153346893)
                  ·
                    refine ⟨3572315037527958432505085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9526173433407889153346893 3572315037527958432505085)
                    ·
                      refine ⟨1339618139072984412189407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3572315037527958432505085 1339618139072984412189407)
                      ·
                        rfl

theorem cell23_2608897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_2608897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608897 prefixEnd_2608897 := by exact prefixLift 2608897
  have htrace : WordTrace (prefixWord ++ tailWord_2608897) baseStart_2608897 baseEnd_2608897 := by
    simpa [prefixWord, tailWord_2608897, baseEnd_2608897] using wordTrace_append hprefix tailTrace_2608897
  have hstable : (prefixWord ++ tailWord_2608897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608897).length < 2 ^ (prefixWord ++ tailWord_2608897).sum := by decide
  have hdescent : baseEnd_2608897 < baseStart_2608897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608907 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 2, 5, 2]
def baseStart_2608907 : Nat := 118140960795 + 2608907 * 2 ^ 59
def prefixEnd_2608907 : Nat := 4983230072969 + 3 ^ 40 * 2608907 * 2
def baseEnd_2608907 : Nat := 1339623273879529373064361

theorem tailTrace_2608907 : CollatzResearch.WordTrace tailWord_2608907 prefixEnd_2608907 1339623273879529373064361 := by
  unfold tailWord_2608907
  simp only [CollatzResearch.WordTrace]
  refine ⟨95154655559382979687400975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63436437039588653124933983 95154655559382979687400975)
  ·
    refine ⟨142731983339074469531101463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95154655559382979687400975 142731983339074469531101463)
    ·
      refine ⟨214097975008611704296652195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142731983339074469531101463 214097975008611704296652195)
      ·
        refine ⟨321146962512917556444978293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214097975008611704296652195 321146962512917556444978293)
        ·
          refine ⟨30107527735586020916716715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 321146962512917556444978293 30107527735586020916716715)
          ·
            refine ⟨45161291603379031375075073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30107527735586020916716715 45161291603379031375075073)
            ·
              refine ⟨33870968702534273531306305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45161291603379031375075073 33870968702534273531306305)
              ·
                refine ⟨25403226526900705148479729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33870968702534273531306305 25403226526900705148479729)
                ·
                  refine ⟨19052419895175528861359797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25403226526900705148479729 19052419895175528861359797)
                  ·
                    refine ⟨1786164365172705830752481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19052419895175528861359797 1786164365172705830752481)
                    ·
                      refine ⟨1339623273879529373064361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1786164365172705830752481 1339623273879529373064361)
                      ·
                        rfl

theorem cell23_2608907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 5, 2].length) (baseStart_2608907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608907 prefixEnd_2608907 := by exact prefixLift 2608907
  have htrace : WordTrace (prefixWord ++ tailWord_2608907) baseStart_2608907 baseEnd_2608907 := by
    simpa [prefixWord, tailWord_2608907, baseEnd_2608907] using wordTrace_append hprefix tailTrace_2608907
  have hstable : (prefixWord ++ tailWord_2608907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608907).length < 2 ^ (prefixWord ++ tailWord_2608907).sum := by decide
  have hdescent : baseEnd_2608907 < baseStart_2608907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608994 : List Nat := [3, 3, 2, 1, 2, 1, 1, 4, 6]
def baseStart_2608994 : Nat := 118140960795 + 2608994 * 2 ^ 59
def prefixEnd_2608994 : Nat := 4983230072969 + 3 ^ 40 * 2608994 * 2
def baseEnd_2608994 : Nat := 148851994077385614741829

theorem tailTrace_2608994 : CollatzResearch.WordTrace tailWord_2608994 prefixEnd_2608994 148851994077385614741829 := by
  unfold tailWord_2608994
  simp only [CollatzResearch.WordTrace]
  refine ⟨23789457177516948386454509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63438552473378529030545357 23789457177516948386454509)
  ·
    refine ⟨8921046441568855644920441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23789457177516948386454509 8921046441568855644920441)
    ·
      refine ⟨6690784831176641733690331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8921046441568855644920441 6690784831176641733690331)
      ·
        refine ⟨10036177246764962600535497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6690784831176641733690331 10036177246764962600535497)
        ·
          refine ⟨7527132935073721950401623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10036177246764962600535497 7527132935073721950401623)
          ·
            refine ⟨11290699402610582925602435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7527132935073721950401623 11290699402610582925602435)
            ·
              refine ⟨16936049103915874388403653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11290699402610582925602435 16936049103915874388403653)
              ·
                refine ⟨3175509206984226447825685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16936049103915874388403653 3175509206984226447825685)
                ·
                  refine ⟨148851994077385614741829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3175509206984226447825685 148851994077385614741829)
                  ·
                    rfl

theorem cell23_2608994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_2608994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2608994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2608994 prefixEnd_2608994 := by exact prefixLift 2608994
  have htrace : WordTrace (prefixWord ++ tailWord_2608994) baseStart_2608994 baseEnd_2608994 := by
    simpa [prefixWord, tailWord_2608994, baseEnd_2608994] using wordTrace_append hprefix tailTrace_2608994
  have hstable : (prefixWord ++ tailWord_2608994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608994).length < 2 ^ (prefixWord ++ tailWord_2608994).sum := by decide
  have hdescent : baseEnd_2608994 < baseStart_2608994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609025 : List Nat := [1, 2, 4, 4, 2, 1, 1, 1, 2, 2, 3]
def baseStart_2609025 : Nat := 118140960795 + 2609025 * 2 ^ 59
def prefixEnd_2609025 : Nat := 4983230072969 + 3 ^ 40 * 2609025 * 2
def baseEnd_2609025 : Nat := 1339683864596759911388819

theorem tailTrace_2609025 : CollatzResearch.WordTrace tailWord_2609025 prefixEnd_2609025 1339683864596759911388819 := by
  unfold tailWord_2609025
  simp only [CollatzResearch.WordTrace]
  refine ⟨95158959372955485840196529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63439306248636990560131019 95158959372955485840196529)
  ·
    refine ⟨71369219529716614380147397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95158959372955485840196529 71369219529716614380147397)
    ·
      refine ⟨13381728661821865196277637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71369219529716614380147397 13381728661821865196277637)
      ·
        refine ⟨2509074124091599724302057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13381728661821865196277637 2509074124091599724302057)
        ·
          refine ⟨1881805593068699793226543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2509074124091599724302057 1881805593068699793226543)
          ·
            refine ⟨2822708389603049689839815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1881805593068699793226543 2822708389603049689839815)
            ·
              refine ⟨4234062584404574534759723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2822708389603049689839815 4234062584404574534759723)
              ·
                refine ⟨6351093876606861802139585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4234062584404574534759723 6351093876606861802139585)
                ·
                  refine ⟨4763320407455146351604689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6351093876606861802139585 4763320407455146351604689)
                  ·
                    refine ⟨3572490305591359763703517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4763320407455146351604689 3572490305591359763703517)
                    ·
                      refine ⟨1339683864596759911388819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3572490305591359763703517 1339683864596759911388819)
                      ·
                        rfl

theorem cell23_2609025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_2609025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609025 prefixEnd_2609025 := by exact prefixLift 2609025
  have htrace : WordTrace (prefixWord ++ tailWord_2609025) baseStart_2609025 baseEnd_2609025 := by
    simpa [prefixWord, tailWord_2609025, baseEnd_2609025] using wordTrace_append hprefix tailTrace_2609025
  have hstable : (prefixWord ++ tailWord_2609025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609025).length < 2 ^ (prefixWord ++ tailWord_2609025).sum := by decide
  have hdescent : baseEnd_2609025 < baseStart_2609025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609031 : List Nat := [1, 1, 4, 2, 4, 1, 1, 1, 1, 5, 2]
def baseStart_2609031 : Nat := 118140960795 + 2609031 * 2 ^ 59
def prefixEnd_2609031 : Nat := 4983230072969 + 3 ^ 40 * 2609031 * 2
def baseEnd_2609031 : Nat := 1339686945480686887913791

theorem tailTrace_2609031 : CollatzResearch.WordTrace tailWord_2609031 prefixEnd_2609031 1339686945480686887913791 := by
  unfold tailWord_2609031
  simp only [CollatzResearch.WordTrace]
  refine ⟨95159178210933748864914947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63439452140622499243276631 95159178210933748864914947)
  ·
    refine ⟨142738767316400623297372421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95159178210933748864914947 142738767316400623297372421)
    ·
      refine ⟨26763518871825116868257329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142738767316400623297372421 26763518871825116868257329)
      ·
        refine ⟨20072639153868837651192997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26763518871825116868257329 20072639153868837651192997)
        ·
          refine ⟨3763619841350407059598687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20072639153868837651192997 3763619841350407059598687)
          ·
            refine ⟨5645429762025610589398031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3763619841350407059598687 5645429762025610589398031)
            ·
              refine ⟨8468144643038415884097047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5645429762025610589398031 8468144643038415884097047)
              ·
                refine ⟨12702216964557623826145571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8468144643038415884097047 12702216964557623826145571)
                ·
                  refine ⟨19053325446836435739218357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12702216964557623826145571 19053325446836435739218357)
                  ·
                    refine ⟨1786249260640915850551721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19053325446836435739218357 1786249260640915850551721)
                    ·
                      refine ⟨1339686945480686887913791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1786249260640915850551721 1339686945480686887913791)
                      ·
                        rfl

theorem cell23_2609031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_2609031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609031 prefixEnd_2609031 := by exact prefixLift 2609031
  have htrace : WordTrace (prefixWord ++ tailWord_2609031) baseStart_2609031 baseEnd_2609031 := by
    simpa [prefixWord, tailWord_2609031, baseEnd_2609031] using wordTrace_append hprefix tailTrace_2609031
  have hstable : (prefixWord ++ tailWord_2609031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609031).length < 2 ^ (prefixWord ++ tailWord_2609031).sum := by decide
  have hdescent : baseEnd_2609031 < baseStart_2609031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609071 : List Nat := [1, 1, 2, 1, 2, 2, 7, 1, 2, 4]
def baseStart_2609071 : Nat := 118140960795 + 2609071 * 2 ^ 59
def prefixEnd_2609071 : Nat := 4983230072969 + 3 ^ 40 * 2609071 * 2
def baseEnd_2609071 : Nat := 446569161568955577137869

theorem tailTrace_2609071 : CollatzResearch.WordTrace tailWord_2609071 prefixEnd_2609071 446569161568955577137869 := by
  unfold tailWord_2609071
  simp only [CollatzResearch.WordTrace]
  refine ⟨95160637130788835696371067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63440424753859223797580711 95160637130788835696371067)
  ·
    refine ⟨142740955696183253544556601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95160637130788835696371067 142740955696183253544556601)
    ·
      refine ⟨107055716772137440158417451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142740955696183253544556601 107055716772137440158417451)
      ·
        refine ⟨160583575158206160237626177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107055716772137440158417451 160583575158206160237626177)
        ·
          refine ⟨120437681368654620178219633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160583575158206160237626177 120437681368654620178219633)
          ·
            refine ⟨90328261026490965133664725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120437681368654620178219633 90328261026490965133664725)
            ·
              refine ⟨2117068617808381995320267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 90328261026490965133664725 2117068617808381995320267)
              ·
                refine ⟨3175602926712572992980401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2117068617808381995320267 3175602926712572992980401)
                ·
                  refine ⟨2381702195034429744735301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3175602926712572992980401 2381702195034429744735301)
                  ·
                    refine ⟨446569161568955577137869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2381702195034429744735301 446569161568955577137869)
                    ·
                      rfl

theorem cell23_2609071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 2, 4].length) (baseStart_2609071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609071 prefixEnd_2609071 := by exact prefixLift 2609071
  have htrace : WordTrace (prefixWord ++ tailWord_2609071) baseStart_2609071 baseEnd_2609071 := by
    simpa [prefixWord, tailWord_2609071, baseEnd_2609071] using wordTrace_append hprefix tailTrace_2609071
  have hstable : (prefixWord ++ tailWord_2609071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609071).length < 2 ^ (prefixWord ++ tailWord_2609071).sum := by decide
  have hdescent : baseEnd_2609071 < baseStart_2609071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609081 : List Nat := [1, 2, 1, 4, 2, 1, 4, 2, 1, 2, 3]
def baseStart_2609081 : Nat := 118140960795 + 2609081 * 2 ^ 59
def prefixEnd_2609081 : Nat := 4983230072969 + 3 ^ 40 * 2609081 * 2
def baseEnd_2609081 : Nat := 1339712619513411692288561

theorem tailTrace_2609081 : CollatzResearch.WordTrace tailWord_2609081 prefixEnd_2609081 1339712619513411692288561 := by
  unfold tailWord_2609081
  simp only [CollatzResearch.WordTrace]
  refine ⟨95161001860752607404235097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63440667907168404936156731 95161001860752607404235097)
  ·
    refine ⟨71370751395564455553176323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95161001860752607404235097 71370751395564455553176323)
    ·
      refine ⟨107056127093346683329764485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71370751395564455553176323 107056127093346683329764485)
      ·
        refine ⟨20073023830002503124330841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107056127093346683329764485 20073023830002503124330841)
        ·
          refine ⟨15054767872501877343248131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20073023830002503124330841 15054767872501877343248131)
          ·
            refine ⟨22582151808752816014872197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15054767872501877343248131 22582151808752816014872197)
            ·
              refine ⟨4234153464141153002788537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22582151808752816014872197 4234153464141153002788537)
              ·
                refine ⟨3175615098105864752091403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4234153464141153002788537 3175615098105864752091403)
                ·
                  refine ⟨4763422647158797128137105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3175615098105864752091403 4763422647158797128137105)
                  ·
                    refine ⟨3572566985369097846102829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4763422647158797128137105 3572566985369097846102829)
                    ·
                      refine ⟨1339712619513411692288561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3572566985369097846102829 1339712619513411692288561)
                      ·
                        rfl

theorem cell23_2609081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_2609081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609081 prefixEnd_2609081 := by exact prefixLift 2609081
  have htrace : WordTrace (prefixWord ++ tailWord_2609081) baseStart_2609081 baseEnd_2609081 := by
    simpa [prefixWord, tailWord_2609081, baseEnd_2609081] using wordTrace_append hprefix tailTrace_2609081
  have hstable : (prefixWord ++ tailWord_2609081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609081).length < 2 ^ (prefixWord ++ tailWord_2609081).sum := by decide
  have hdescent : baseEnd_2609081 < baseStart_2609081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609111 : List Nat := [1, 1, 3, 2, 1, 1, 4, 4, 2, 1, 3]
def baseStart_2609111 : Nat := 118140960795 + 2609111 * 2 ^ 59
def prefixEnd_2609111 : Nat := 4983230072969 + 3 ^ 40 * 2609111 * 2
def baseEnd_2609111 : Nat := 1339728023933046574913423

theorem tailTrace_2609111 : CollatzResearch.WordTrace tailWord_2609111 prefixEnd_2609111 1339728023933046574913423 := by
  unfold tailWord_2609111
  simp only [CollatzResearch.WordTrace]
  refine ⟨95162096050643922527827187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63441397367095948351884791 95162096050643922527827187)
  ·
    refine ⟨142743144075965883791740781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95162096050643922527827187 142743144075965883791740781)
    ·
      refine ⟨53528679028487206421902793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142743144075965883791740781 53528679028487206421902793)
      ·
        refine ⟨40146509271365404816427095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53528679028487206421902793 40146509271365404816427095)
        ·
          refine ⟨60219763907048107224640643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40146509271365404816427095 60219763907048107224640643)
          ·
            refine ⟨90329645860572160836960965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60219763907048107224640643 90329645860572160836960965)
            ·
              refine ⟨16936808598857280156930181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90329645860572160836960965 16936808598857280156930181)
              ·
                refine ⟨3175651612285740029424409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16936808598857280156930181 3175651612285740029424409)
                ·
                  refine ⟨2381738709214305022068307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3175651612285740029424409 2381738709214305022068307)
                  ·
                    refine ⟨3572608063821457533102461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2381738709214305022068307 3572608063821457533102461)
                    ·
                      refine ⟨1339728023933046574913423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3572608063821457533102461 1339728023933046574913423)
                      ·
                        rfl

theorem cell23_2609111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 2, 1, 3].length) (baseStart_2609111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609111 prefixEnd_2609111 := by exact prefixLift 2609111
  have htrace : WordTrace (prefixWord ++ tailWord_2609111) baseStart_2609111 baseEnd_2609111 := by
    simpa [prefixWord, tailWord_2609111, baseEnd_2609111] using wordTrace_append hprefix tailTrace_2609111
  have hstable : (prefixWord ++ tailWord_2609111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609111).length < 2 ^ (prefixWord ++ tailWord_2609111).sum := by decide
  have hdescent : baseEnd_2609111 < baseStart_2609111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609122 : List Nat := [3, 3, 3, 1, 2, 2, 2, 1, 2, 4]
def baseStart_2609122 : Nat := 118140960795 + 2609122 * 2 ^ 59
def prefixEnd_2609122 : Nat := 4983230072969 + 3 ^ 40 * 2609122 * 2
def baseEnd_2609122 : Nat := 446577890740082010625291

theorem tailTrace_2609122 : CollatzResearch.WordTrace tailWord_2609122 prefixEnd_2609122 446577890740082010625291 := by
  unfold tailWord_2609122
  simp only [CollatzResearch.WordTrace]
  refine ⟨23790624313401017851619405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63441664835736047604318413 23790624313401017851619405)
  ·
    refine ⟨8921484117525381694357277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23790624313401017851619405 8921484117525381694357277)
    ·
      refine ⟨3345556544072018135383979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8921484117525381694357277 3345556544072018135383979)
      ·
        refine ⟨5018334816108027203075969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3345556544072018135383979 5018334816108027203075969)
        ·
          refine ⟨3763751112081020402306977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5018334816108027203075969 3763751112081020402306977)
          ·
            refine ⟨2822813334060765301730233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3763751112081020402306977 2822813334060765301730233)
            ·
              refine ⟨2117110000545573976297675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2822813334060765301730233 2117110000545573976297675)
              ·
                refine ⟨3175665000818360964446513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2117110000545573976297675 3175665000818360964446513)
                ·
                  refine ⟨2381748750613770723334885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3175665000818360964446513 2381748750613770723334885)
                  ·
                    refine ⟨446577890740082010625291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2381748750613770723334885 446577890740082010625291)
                    ·
                      rfl

theorem cell23_2609122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_2609122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609122 prefixEnd_2609122 := by exact prefixLift 2609122
  have htrace : WordTrace (prefixWord ++ tailWord_2609122) baseStart_2609122 baseEnd_2609122 := by
    simpa [prefixWord, tailWord_2609122, baseEnd_2609122] using wordTrace_append hprefix tailTrace_2609122
  have hstable : (prefixWord ++ tailWord_2609122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609122).length < 2 ^ (prefixWord ++ tailWord_2609122).sum := by decide
  have hdescent : baseEnd_2609122 < baseStart_2609122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609151 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 6, 2, 2]
def baseStart_2609151 : Nat := 118140960795 + 2609151 * 2 ^ 59
def prefixEnd_2609151 : Nat := 4983230072969 + 3 ^ 40 * 2609151 * 2
def baseEnd_2609151 : Nat := 1339748563159226418413239

theorem tailTrace_2609151 : CollatzResearch.WordTrace tailWord_2609151 prefixEnd_2609151 1339748563159226418413239 := by
  unfold tailWord_2609151
  simp only [CollatzResearch.WordTrace]
  refine ⟨95163554970499009359283307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63442369980332672906188871 95163554970499009359283307)
  ·
    refine ⟨142745332455748514038924961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95163554970499009359283307 142745332455748514038924961)
    ·
      refine ⟨107058999341811385529193721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142745332455748514038924961 107058999341811385529193721)
      ·
        refine ⟨80294249506358539146895291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107058999341811385529193721 80294249506358539146895291)
        ·
          refine ⟨120441374259537808720342937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80294249506358539146895291 120441374259537808720342937)
          ·
            refine ⟨90331030694653356540257203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120441374259537808720342937 90331030694653356540257203)
            ·
              refine ⟨135496546041980034810385805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90331030694653356540257203 135496546041980034810385805)
              ·
                refine ⟨50811204765742513053894677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135496546041980034810385805 50811204765742513053894677)
                ·
                  refine ⟨2381775223394180299401313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50811204765742513053894677 2381775223394180299401313)
                  ·
                    refine ⟨1786331417545635224550985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2381775223394180299401313 1786331417545635224550985)
                    ·
                      refine ⟨1339748563159226418413239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1786331417545635224550985 1339748563159226418413239)
                      ·
                        rfl

theorem cell23_2609151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 6, 2, 2].length) (baseStart_2609151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609151 prefixEnd_2609151 := by exact prefixLift 2609151
  have htrace : WordTrace (prefixWord ++ tailWord_2609151) baseStart_2609151 baseEnd_2609151 := by
    simpa [prefixWord, tailWord_2609151, baseEnd_2609151] using wordTrace_append hprefix tailTrace_2609151
  have hstable : (prefixWord ++ tailWord_2609151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609151).length < 2 ^ (prefixWord ++ tailWord_2609151).sum := by decide
  have hdescent : baseEnd_2609151 < baseStart_2609151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609164 : List Nat := [2, 2, 1, 2, 3, 1, 2, 2, 2, 2, 4]
def baseStart_2609164 : Nat := 118140960795 + 2609164 * 2 ^ 59
def prefixEnd_2609164 : Nat := 4983230072969 + 3 ^ 40 * 2609164 * 2
def baseEnd_2609164 : Nat := 1339755238407734867550679

theorem tailTrace_2609164 : CollatzResearch.WordTrace tailWord_2609164 prefixEnd_2609164 1339755238407734867550679 := by
  unfold tailWord_2609164
  simp only [CollatzResearch.WordTrace]
  refine ⟨47582014559725956289753273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63442686079634608386337697 47582014559725956289753273)
  ·
    refine ⟨35686510919794467217314955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47582014559725956289753273 35686510919794467217314955)
    ·
      refine ⟨53529766379691700825972433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35686510919794467217314955 53529766379691700825972433)
      ·
        refine ⟨40147324784768775619479325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53529766379691700825972433 40147324784768775619479325)
        ·
          refine ⟨15055246794288290857304747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40147324784768775619479325 15055246794288290857304747)
          ·
            refine ⟨22582870191432436285957121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15055246794288290857304747 22582870191432436285957121)
            ·
              refine ⟨16937152643574327214467841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22582870191432436285957121 16937152643574327214467841)
              ·
                refine ⟨12702864482680745410850881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16937152643574327214467841 12702864482680745410850881)
                ·
                  refine ⟨9527148362010559058138161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12702864482680745410850881 9527148362010559058138161)
                  ·
                    refine ⟨7145361271507919293603621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9527148362010559058138161 7145361271507919293603621)
                    ·
                      refine ⟨1339755238407734867550679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7145361271507919293603621 1339755238407734867550679)
                      ·
                        rfl

theorem cell23_2609164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_2609164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609164 prefixEnd_2609164 := by exact prefixLift 2609164
  have htrace : WordTrace (prefixWord ++ tailWord_2609164) baseStart_2609164 baseEnd_2609164 := by
    simpa [prefixWord, tailWord_2609164, baseEnd_2609164] using wordTrace_append hprefix tailTrace_2609164
  have hstable : (prefixWord ++ tailWord_2609164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609164).length < 2 ^ (prefixWord ++ tailWord_2609164).sum := by decide
  have hdescent : baseEnd_2609164 < baseStart_2609164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609177 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 2, 1, 8]
def baseStart_2609177 : Nat := 118140960795 + 2609177 * 2 ^ 59
def prefixEnd_2609177 : Nat := 4983230072969 + 3 ^ 40 * 2609177 * 2
def baseEnd_2609177 : Nat := 1339761913656243316688119

theorem tailTrace_2609177 : CollatzResearch.WordTrace tailWord_2609177 prefixEnd_2609177 1339761913656243316688119 := by
  unfold tailWord_2609177
  simp only [CollatzResearch.WordTrace]
  refine ⟨95164503268404815799729785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63443002178936543866486523 95164503268404815799729785)
  ·
    refine ⟨71373377451303611849797339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95164503268404815799729785 71373377451303611849797339)
    ·
      refine ⟨107060066176955417774696009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71373377451303611849797339 107060066176955417774696009)
      ·
        refine ⟨80295049632716563331022007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107060066176955417774696009 80295049632716563331022007)
        ·
          refine ⟨120442574449074844996533011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80295049632716563331022007 120442574449074844996533011)
          ·
            refine ⟨180663861673612267494799517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120442574449074844996533011 180663861673612267494799517)
            ·
              refine ⟨67748948127604600310549819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 180663861673612267494799517 67748948127604600310549819)
              ·
                refine ⟨101623422191406900465824729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67748948127604600310549819 101623422191406900465824729)
                ·
                  refine ⟨76217566643555175349368547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101623422191406900465824729 76217566643555175349368547)
                  ·
                    refine ⟨114326349965332763024052821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76217566643555175349368547 114326349965332763024052821)
                    ·
                      refine ⟨1339761913656243316688119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 114326349965332763024052821 1339761913656243316688119)
                      ·
                        rfl

theorem cell23_2609177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_2609177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609177 prefixEnd_2609177 := by exact prefixLift 2609177
  have htrace : WordTrace (prefixWord ++ tailWord_2609177) baseStart_2609177 baseEnd_2609177 := by
    simpa [prefixWord, tailWord_2609177, baseEnd_2609177] using wordTrace_append hprefix tailTrace_2609177
  have hstable : (prefixWord ++ tailWord_2609177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609177).length < 2 ^ (prefixWord ++ tailWord_2609177).sum := by decide
  have hdescent : baseEnd_2609177 < baseStart_2609177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609181 : List Nat := [1, 4, 2, 2, 2, 2, 1, 1, 2, 2, 4]
def baseStart_2609181 : Nat := 118140960795 + 2609181 * 2 ^ 59
def prefixEnd_2609181 : Nat := 4983230072969 + 3 ^ 40 * 2609181 * 2
def baseEnd_2609181 : Nat := 1339763967578861301038101

theorem tailTrace_2609181 : CollatzResearch.WordTrace tailWord_2609181 prefixEnd_2609181 1339763967578861301038101 := by
  unfold tailWord_2609181
  simp only [CollatzResearch.WordTrace]
  refine ⟨95164649160390324482875397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63443099440260216321916931 95164649160390324482875397)
  ·
    refine ⟨17843371717573185840539137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95164649160390324482875397 17843371717573185840539137)
    ·
      refine ⟨13382528788179889380404353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17843371717573185840539137 13382528788179889380404353)
      ·
        refine ⟨10036896591134917035303265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13382528788179889380404353 10036896591134917035303265)
        ·
          refine ⟨7527672443351187776477449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10036896591134917035303265 7527672443351187776477449)
          ·
            refine ⟨5645754332513390832358087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7527672443351187776477449 5645754332513390832358087)
            ·
              refine ⟨8468631498770086248537131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5645754332513390832358087 8468631498770086248537131)
              ·
                refine ⟨12702947248155129372805697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8468631498770086248537131 12702947248155129372805697)
                ·
                  refine ⟨9527210436116347029604273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12702947248155129372805697 9527210436116347029604273)
                  ·
                    refine ⟨7145407827087260272203205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9527210436116347029604273 7145407827087260272203205)
                    ·
                      refine ⟨1339763967578861301038101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7145407827087260272203205 1339763967578861301038101)
                      ·
                        rfl

theorem cell23_2609181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_2609181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609181 prefixEnd_2609181 := by exact prefixLift 2609181
  have htrace : WordTrace (prefixWord ++ tailWord_2609181) baseStart_2609181 baseEnd_2609181 := by
    simpa [prefixWord, tailWord_2609181, baseEnd_2609181] using wordTrace_append hprefix tailTrace_2609181
  have hstable : (prefixWord ++ tailWord_2609181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609181).length < 2 ^ (prefixWord ++ tailWord_2609181).sum := by decide
  have hdescent : baseEnd_2609181 < baseStart_2609181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609208 : List Nat := [2, 1, 2, 1, 6, 1, 2, 3, 5]
def baseStart_2609208 : Nat := 118140960795 + 2609208 * 2 ^ 59
def prefixEnd_2609208 : Nat := 4983230072969 + 3 ^ 40 * 2609208 * 2
def baseEnd_2609208 : Nat := 148864203506281410600053

theorem tailTrace_2609208 : CollatzResearch.WordTrace tailWord_2609208 prefixEnd_2609208 148864203506281410600053 := by
  unfold tailWord_2609208
  simp only [CollatzResearch.WordTrace]
  refine ⟨47582816965646254047054139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63443755954195005396072185 47582816965646254047054139)
  ·
    refine ⟨71374225448469381070581209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47582816965646254047054139 71374225448469381070581209)
    ·
      refine ⟨53530669086352035802935907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71374225448469381070581209 53530669086352035802935907)
      ·
        refine ⟨80296003629528053704403861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53530669086352035802935907 80296003629528053704403861)
        ·
          refine ⟨3763875170134127517393931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 80296003629528053704403861 3763875170134127517393931)
          ·
            refine ⟨5645812755201191276090897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3763875170134127517393931 5645812755201191276090897)
            ·
              refine ⟨4234359566400893457068173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5645812755201191276090897 4234359566400893457068173)
              ·
                refine ⟨1587884837400335046400565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4234359566400893457068173 1587884837400335046400565)
                ·
                  refine ⟨148864203506281410600053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1587884837400335046400565 148864203506281410600053)
                  ·
                    rfl

theorem cell23_2609208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 3, 5].length) (baseStart_2609208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609208 prefixEnd_2609208 := by exact prefixLift 2609208
  have htrace : WordTrace (prefixWord ++ tailWord_2609208) baseStart_2609208 baseEnd_2609208 := by
    simpa [prefixWord, tailWord_2609208, baseEnd_2609208] using wordTrace_append hprefix tailTrace_2609208
  have hstable : (prefixWord ++ tailWord_2609208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609208).length < 2 ^ (prefixWord ++ tailWord_2609208).sum := by decide
  have hdescent : baseEnd_2609208 < baseStart_2609208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609238 : List Nat := [5, 2, 2, 1, 1, 1, 1, 2, 1, 7]
def baseStart_2609238 : Nat := 118140960795 + 2609238 * 2 ^ 59
def prefixEnd_2609238 : Nat := 4983230072969 + 3 ^ 40 * 2609238 * 2
def baseEnd_2609238 : Nat := 446597745325389192675113

theorem tailTrace_2609238 : CollatzResearch.WordTrace tailWord_2609238 prefixEnd_2609238 446597745325389192675113 := by
  unfold tailWord_2609238
  simp only [CollatzResearch.WordTrace]
  refine ⟨5947920507573988951106273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63444485414122548811800245 5947920507573988951106273)
  ·
    refine ⟨4460940380680491713329705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5947920507573988951106273 4460940380680491713329705)
    ·
      refine ⟨3345705285510368784997279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4460940380680491713329705 3345705285510368784997279)
      ·
        refine ⟨5018557928265553177495919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3345705285510368784997279 5018557928265553177495919)
        ·
          refine ⟨7527836892398329766243879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5018557928265553177495919 7527836892398329766243879)
          ·
            refine ⟨11291755338597494649365819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7527836892398329766243879 11291755338597494649365819)
            ·
              refine ⟨16937633007896241974048729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11291755338597494649365819 16937633007896241974048729)
              ·
                refine ⟨12703224755922181480536547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16937633007896241974048729 12703224755922181480536547)
                ·
                  refine ⟨19054837133883272220804821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12703224755922181480536547 19054837133883272220804821)
                  ·
                    refine ⟨446597745325389192675113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19054837133883272220804821 446597745325389192675113)
                    ·
                      rfl

theorem cell23_2609238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_2609238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609238 prefixEnd_2609238 := by exact prefixLift 2609238
  have htrace : WordTrace (prefixWord ++ tailWord_2609238) baseStart_2609238 baseEnd_2609238 := by
    simpa [prefixWord, tailWord_2609238, baseEnd_2609238] using wordTrace_append hprefix tailTrace_2609238
  have hstable : (prefixWord ++ tailWord_2609238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609238).length < 2 ^ (prefixWord ++ tailWord_2609238).sum := by decide
  have hdescent : baseEnd_2609238 < baseStart_2609238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609241 : List Nat := [1, 2, 1, 2, 2, 1, 3, 3, 2, 4, 2]
def baseStart_2609241 : Nat := 118140960795 + 2609241 * 2 ^ 59
def prefixEnd_2609241 : Nat := 4983230072969 + 3 ^ 40 * 2609241 * 2
def baseEnd_2609241 : Nat := 1339794776418131066287825

theorem tailTrace_2609241 : CollatzResearch.WordTrace tailWord_2609241 prefixEnd_2609241 1339794776418131066287825 := by
  unfold tailWord_2609241
  simp only [CollatzResearch.WordTrace]
  refine ⟨95166837540172954730059577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63444558360115303153373051 95166837540172954730059577)
  ·
    refine ⟨71375128155129716047544683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95166837540172954730059577 71375128155129716047544683)
    ·
      refine ⟨107062692232694574071317025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71375128155129716047544683 107062692232694574071317025)
      ·
        refine ⟨80297019174520930553487769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107062692232694574071317025 80297019174520930553487769)
        ·
          refine ⟨60222764380890697915115827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80297019174520930553487769 60222764380890697915115827)
          ·
            refine ⟨90334146571336046872673741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60222764380890697915115827 90334146571336046872673741)
            ·
              refine ⟨33875304964251017577252653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90334146571336046872673741 33875304964251017577252653)
              ·
                refine ⟨12703239361594131591469745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33875304964251017577252653 12703239361594131591469745)
                ·
                  refine ⟨9527429521195598693602309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12703239361594131591469745 9527429521195598693602309)
                  ·
                    refine ⟨1786393035224174755050433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9527429521195598693602309 1786393035224174755050433)
                    ·
                      refine ⟨1339794776418131066287825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1786393035224174755050433 1339794776418131066287825)
                      ·
                        rfl

theorem cell23_2609241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 4, 2].length) (baseStart_2609241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609241 prefixEnd_2609241 := by exact prefixLift 2609241
  have htrace : WordTrace (prefixWord ++ tailWord_2609241) baseStart_2609241 baseEnd_2609241 := by
    simpa [prefixWord, tailWord_2609241, baseEnd_2609241] using wordTrace_append hprefix tailTrace_2609241
  have hstable : (prefixWord ++ tailWord_2609241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609241).length < 2 ^ (prefixWord ++ tailWord_2609241).sum := by decide
  have hdescent : baseEnd_2609241 < baseStart_2609241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609251 : List Nat := [1, 1, 1, 5, 1, 1, 4, 2, 3, 4]
def baseStart_2609251 : Nat := 118140960795 + 2609251 * 2 ^ 59
def prefixEnd_2609251 : Nat := 4983230072969 + 3 ^ 40 * 2609251 * 2
def baseEnd_2609251 : Nat := 446599970408225342387593

theorem tailTrace_2609251 : CollatzResearch.WordTrace tailWord_2609251 prefixEnd_2609251 446599970408225342387593 := by
  unfold tailWord_2609251
  simp only [CollatzResearch.WordTrace]
  refine ⟨95167202270136726437923607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63444801513424484291949071 95167202270136726437923607)
  ·
    refine ⟨142750803405205089656885411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95167202270136726437923607 142750803405205089656885411)
    ·
      refine ⟨214126205107807634485328117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142750803405205089656885411 214126205107807634485328117)
      ·
        refine ⟨20074331728856965732999511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 214126205107807634485328117 20074331728856965732999511)
        ·
          refine ⟨30111497593285448599499267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20074331728856965732999511 30111497593285448599499267)
          ·
            refine ⟨45167246389928172899248901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30111497593285448599499267 45167246389928172899248901)
            ·
              refine ⟨8468858698111532418609169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45167246389928172899248901 8468858698111532418609169)
              ·
                refine ⟨6351644023583649313956877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8468858698111532418609169 6351644023583649313956877)
                ·
                  refine ⟨2381866508843868492733829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6351644023583649313956877 2381866508843868492733829)
                  ·
                    refine ⟨446599970408225342387593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2381866508843868492733829 446599970408225342387593)
                    ·
                      rfl

theorem cell23_2609251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 3, 4].length) (baseStart_2609251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609251 prefixEnd_2609251 := by exact prefixLift 2609251
  have htrace : WordTrace (prefixWord ++ tailWord_2609251) baseStart_2609251 baseEnd_2609251 := by
    simpa [prefixWord, tailWord_2609251, baseEnd_2609251] using wordTrace_append hprefix tailTrace_2609251
  have hstable : (prefixWord ++ tailWord_2609251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609251).length < 2 ^ (prefixWord ++ tailWord_2609251).sum := by decide
  have hdescent : baseEnd_2609251 < baseStart_2609251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609261 : List Nat := [1, 5, 1, 1, 2, 1, 1, 3, 1, 4, 3]
def baseStart_2609261 : Nat := 118140960795 + 2609261 * 2 ^ 59
def prefixEnd_2609261 : Nat := 4983230072969 + 3 ^ 40 * 2609261 * 2
def baseEnd_2609261 : Nat := 1339805046031220988037733

theorem tailTrace_2609261 : CollatzResearch.WordTrace tailWord_2609261 prefixEnd_2609261 1339805046031220988037733 := by
  unfold tailWord_2609261
  simp only [CollatzResearch.WordTrace]
  refine ⟨95167567000100498145787637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63445044666733665430525091 95167567000100498145787637)
  ·
    refine ⟨8921959406259421701167591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95167567000100498145787637 8921959406259421701167591)
    ·
      refine ⟨13382939109389132551751387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8921959406259421701167591 13382939109389132551751387)
      ·
        refine ⟨20074408664083698827627081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13382939109389132551751387 20074408664083698827627081)
        ·
          refine ⟨15055806498062774120720311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20074408664083698827627081 15055806498062774120720311)
          ·
            refine ⟨22583709747094161181080467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15055806498062774120720311 22583709747094161181080467)
            ·
              refine ⟨33875564620641241771620701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22583709747094161181080467 33875564620641241771620701)
              ·
                refine ⟨12703336732740465664357763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33875564620641241771620701 12703336732740465664357763)
                ·
                  refine ⟨19055005099110698496536645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12703336732740465664357763 19055005099110698496536645)
                  ·
                    refine ⟨3572813456083255968100621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19055005099110698496536645 3572813456083255968100621)
                    ·
                      refine ⟨1339805046031220988037733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3572813456083255968100621 1339805046031220988037733)
                      ·
                        rfl

theorem cell23_2609261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_2609261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609261 prefixEnd_2609261 := by exact prefixLift 2609261
  have htrace : WordTrace (prefixWord ++ tailWord_2609261) baseStart_2609261 baseEnd_2609261 := by
    simpa [prefixWord, tailWord_2609261, baseEnd_2609261] using wordTrace_append hprefix tailTrace_2609261
  have hstable : (prefixWord ++ tailWord_2609261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609261).length < 2 ^ (prefixWord ++ tailWord_2609261).sum := by decide
  have hdescent : baseEnd_2609261 < baseStart_2609261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609264 : List Nat := [2, 1, 1, 1, 5, 2, 1, 2, 8]
def baseStart_2609264 : Nat := 118140960795 + 2609264 * 2 ^ 59
def prefixEnd_2609264 : Nat := 4983230072969 + 3 ^ 40 * 2609264 * 2
def baseEnd_2609264 : Nat := 148867398497020497366691

theorem tailTrace_2609264 : CollatzResearch.WordTrace tailWord_2609264 prefixEnd_2609264 148867398497020497366691 := by
  unfold tailWord_2609264
  simp only [CollatzResearch.WordTrace]
  refine ⟨47583838209544814829073423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63445117612726419772097897 47583838209544814829073423)
  ·
    refine ⟨71375757314317222243610135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47583838209544814829073423 71375757314317222243610135)
    ·
      refine ⟨107063635971475833365415203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71375757314317222243610135 107063635971475833365415203)
      ·
        refine ⟨160595453957213750048122805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107063635971475833365415203 160595453957213750048122805)
        ·
          refine ⟨15055823808488789067011513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 160595453957213750048122805 15055823808488789067011513)
          ·
            refine ⟨11291867856366591800258635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15055823808488789067011513 11291867856366591800258635)
            ·
              refine ⟨16937801784549887700387953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11291867856366591800258635 16937801784549887700387953)
              ·
                refine ⟨12703351338412415775290965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16937801784549887700387953 12703351338412415775290965)
                ·
                  refine ⟨148867398497020497366691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12703351338412415775290965 148867398497020497366691)
                  ·
                    rfl

theorem cell23_2609264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 8].length) (baseStart_2609264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609264 prefixEnd_2609264 := by exact prefixLift 2609264
  have htrace : WordTrace (prefixWord ++ tailWord_2609264) baseStart_2609264 baseEnd_2609264 := by
    simpa [prefixWord, tailWord_2609264, baseEnd_2609264] using wordTrace_append hprefix tailTrace_2609264
  have hstable : (prefixWord ++ tailWord_2609264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609264).length < 2 ^ (prefixWord ++ tailWord_2609264).sum := by decide
  have hdescent : baseEnd_2609264 < baseStart_2609264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609308 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 5, 1, 3]
def baseStart_2609308 : Nat := 118140960795 + 2609308 * 2 ^ 59
def prefixEnd_2609308 : Nat := 4983230072969 + 3 ^ 40 * 2609308 * 2
def baseEnd_2609308 : Nat := 1339829179621982304150017

theorem tailTrace_2609308 : CollatzResearch.WordTrace tailWord_2609308 prefixEnd_2609308 1339829179621982304150017 := by
  unfold tailWord_2609308
  simp only [CollatzResearch.WordTrace]
  refine ⟨47584640615465112586374289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63446187487286816781832385 47584640615465112586374289)
  ·
    refine ⟨35688480461598834439780717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47584640615465112586374289 35688480461598834439780717)
    ·
      refine ⟨13383180173099562914917769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35688480461598834439780717 13383180173099562914917769)
      ·
        refine ⟨10037385129824672186188327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13383180173099562914917769 10037385129824672186188327)
        ·
          refine ⟨15056077694737008279282491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10037385129824672186188327 15056077694737008279282491)
          ·
            refine ⟨22584116542105512418923737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15056077694737008279282491 22584116542105512418923737)
            ·
              refine ⟨16938087406579134314192803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22584116542105512418923737 16938087406579134314192803)
              ·
                refine ⟨25407131109868701471289205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16938087406579134314192803 25407131109868701471289205)
                ·
                  refine ⟨2381918541550190762933363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25407131109868701471289205 2381918541550190762933363)
                  ·
                    refine ⟨3572877812325286144400045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2381918541550190762933363 3572877812325286144400045)
                    ·
                      refine ⟨1339829179621982304150017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3572877812325286144400045 1339829179621982304150017)
                      ·
                        rfl

theorem cell23_2609308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_2609308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609308 prefixEnd_2609308 := by exact prefixLift 2609308
  have htrace : WordTrace (prefixWord ++ tailWord_2609308) baseStart_2609308 baseEnd_2609308 := by
    simpa [prefixWord, tailWord_2609308, baseEnd_2609308] using wordTrace_append hprefix tailTrace_2609308
  have hstable : (prefixWord ++ tailWord_2609308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609308).length < 2 ^ (prefixWord ++ tailWord_2609308).sum := by decide
  have hdescent : baseEnd_2609308 < baseStart_2609308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609348 : List Nat := [2, 3, 3, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_2609348 : Nat := 118140960795 + 2609348 * 2 ^ 59
def prefixEnd_2609348 : Nat := 4983230072969 + 3 ^ 40 * 2609348 * 2
def baseEnd_2609348 : Nat := 1339849718848162147649833

theorem tailTrace_2609348 : CollatzResearch.WordTrace tailWord_2609348 prefixEnd_2609348 1339849718848162147649833 := by
  unfold tailWord_2609348
  simp only [CollatzResearch.WordTrace]
  refine ⟨47585370075392656002102349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63447160100523541336136465 47585370075392656002102349)
  ·
    refine ⟨17844513778272246000788381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47585370075392656002102349 17844513778272246000788381)
    ·
      refine ⟨6691692666852092250295643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17844513778272246000788381 6691692666852092250295643)
      ·
        refine ⟨10037539000278138375443465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6691692666852092250295643 10037539000278138375443465)
        ·
          refine ⟨7528154250208603781582599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10037539000278138375443465 7528154250208603781582599)
          ·
            refine ⟨11292231375312905672373899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7528154250208603781582599 11292231375312905672373899)
            ·
              refine ⟨16938347062969358508560849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11292231375312905672373899 16938347062969358508560849)
              ·
                refine ⟨12703760297227018881420637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16938347062969358508560849 12703760297227018881420637)
                ·
                  refine ⟨4763910111460132080532739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12703760297227018881420637 4763910111460132080532739)
                  ·
                    refine ⟨7145865167190198120799109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4763910111460132080532739 7145865167190198120799109)
                    ·
                      refine ⟨1339849718848162147649833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7145865167190198120799109 1339849718848162147649833)
                      ·
                        rfl

theorem cell23_2609348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_2609348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609348 prefixEnd_2609348 := by exact prefixLift 2609348
  have htrace : WordTrace (prefixWord ++ tailWord_2609348) baseStart_2609348 baseEnd_2609348 := by
    simpa [prefixWord, tailWord_2609348, baseEnd_2609348] using wordTrace_append hprefix tailTrace_2609348
  have hstable : (prefixWord ++ tailWord_2609348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609348).length < 2 ^ (prefixWord ++ tailWord_2609348).sum := by decide
  have hdescent : baseEnd_2609348 < baseStart_2609348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609358 : List Nat := [4, 1, 1, 1, 4, 2, 2, 1, 1, 6]
def baseStart_2609358 : Nat := 118140960795 + 2609358 * 2 ^ 59
def prefixEnd_2609358 : Nat := 4983230072969 + 3 ^ 40 * 2609358 * 2
def baseEnd_2609358 : Nat := 446618284551569036174929

theorem tailTrace_2609358 : CollatzResearch.WordTrace tailWord_2609358 prefixEnd_2609358 446618284551569036174929 := by
  unfold tailWord_2609358
  simp only [CollatzResearch.WordTrace]
  refine ⟨11896388110093635464008591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63447403253832722474712485 11896388110093635464008591)
  ·
    refine ⟨17844582165140453196012887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11896388110093635464008591 17844582165140453196012887)
    ·
      refine ⟨26766873247710679794019331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17844582165140453196012887 26766873247710679794019331)
      ·
        refine ⟨40150309871566019691028997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26766873247710679794019331 40150309871566019691028997)
        ·
          refine ⟨7528183100918628692067937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40150309871566019691028997 7528183100918628692067937)
          ·
            refine ⟨5646137325688971519050953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7528183100918628692067937 5646137325688971519050953)
            ·
              refine ⟨4234602994266728639288215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5646137325688971519050953 4234602994266728639288215)
              ·
                refine ⟨6351904491400092958932323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4234602994266728639288215 6351904491400092958932323)
                ·
                  refine ⟨9527856737100139438398485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6351904491400092958932323 9527856737100139438398485)
                  ·
                    refine ⟨446618284551569036174929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9527856737100139438398485 446618284551569036174929)
                    ·
                      rfl

theorem cell23_2609358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_2609358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609358 prefixEnd_2609358 := by exact prefixLift 2609358
  have htrace : WordTrace (prefixWord ++ tailWord_2609358) baseStart_2609358 baseEnd_2609358 := by
    simpa [prefixWord, tailWord_2609358, baseEnd_2609358] using wordTrace_append hprefix tailTrace_2609358
  have hstable : (prefixWord ++ tailWord_2609358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609358).length < 2 ^ (prefixWord ++ tailWord_2609358).sum := by decide
  have hdescent : baseEnd_2609358 < baseStart_2609358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609361 : List Nat := [1, 2, 2, 1, 2, 2, 3, 3, 1, 2, 4]
def baseStart_2609361 : Nat := 118140960795 + 2609361 * 2 ^ 59
def prefixEnd_2609361 : Nat := 4983230072969 + 3 ^ 40 * 2609361 * 2
def baseEnd_2609361 : Nat := 1339856394096670596787273

theorem tailTrace_2609361 : CollatzResearch.WordTrace tailWord_2609361 prefixEnd_2609361 1339856394096670596787273 := by
  unfold tailWord_2609361
  simp only [CollatzResearch.WordTrace]
  refine ⟨95171214299738215224427937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63447476199825476816285291 95171214299738215224427937)
  ·
    refine ⟨71378410724803661418320953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95171214299738215224427937 71378410724803661418320953)
    ·
      refine ⟨53533808043602746063740715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71378410724803661418320953 53533808043602746063740715)
      ·
        refine ⟨80300712065404119095611073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53533808043602746063740715 80300712065404119095611073)
        ·
          refine ⟨60225534049053089321708305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80300712065404119095611073 60225534049053089321708305)
          ·
            refine ⟨45169150536789816991281229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60225534049053089321708305 45169150536789816991281229)
            ·
              refine ⟨16938431451296181371730461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45169150536789816991281229 16938431451296181371730461)
              ·
                refine ⟨6351911794236068014398923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16938431451296181371730461 6351911794236068014398923)
                ·
                  refine ⟨9527867691354102021598385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6351911794236068014398923 9527867691354102021598385)
                  ·
                    refine ⟨7145900768515576516198789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9527867691354102021598385 7145900768515576516198789)
                    ·
                      refine ⟨1339856394096670596787273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7145900768515576516198789 1339856394096670596787273)
                      ·
                        rfl

theorem cell23_2609361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 2, 4].length) (baseStart_2609361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609361 prefixEnd_2609361 := by exact prefixLift 2609361
  have htrace : WordTrace (prefixWord ++ tailWord_2609361) baseStart_2609361 baseEnd_2609361 := by
    simpa [prefixWord, tailWord_2609361, baseEnd_2609361] using wordTrace_append hprefix tailTrace_2609361
  have hstable : (prefixWord ++ tailWord_2609361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609361).length < 2 ^ (prefixWord ++ tailWord_2609361).sum := by decide
  have hdescent : baseEnd_2609361 < baseStart_2609361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609368 : List Nat := [2, 1, 2, 2, 4, 1, 2, 1, 3, 2, 3]
def baseStart_2609368 : Nat := 118140960795 + 2609368 * 2 ^ 59
def prefixEnd_2609368 : Nat := 4983230072969 + 3 ^ 40 * 2609368 * 2
def baseEnd_2609368 : Nat := 1339859988461252069399741

theorem tailTrace_2609368 : CollatzResearch.WordTrace tailWord_2609368 prefixEnd_2609368 1339859988461252069399741 := by
  unfold tailWord_2609368
  simp only [CollatzResearch.WordTrace]
  refine ⟨47585734805356427709966379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63447646407141903613288505 47585734805356427709966379)
  ·
    refine ⟨71378602208034641564949569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47585734805356427709966379 71378602208034641564949569)
    ·
      refine ⟨53533951656025981173712177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71378602208034641564949569 53533951656025981173712177)
      ·
        refine ⟨40150463742019485880284133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53533951656025981173712177 40150463742019485880284133)
        ·
          refine ⟨7528211951628653602553275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40150463742019485880284133 7528211951628653602553275)
          ·
            refine ⟨11292317927442980403829913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7528211951628653602553275 11292317927442980403829913)
            ·
              refine ⟨8469238445582235302872435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11292317927442980403829913 8469238445582235302872435)
              ·
                refine ⟨12703857668373352954308653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8469238445582235302872435 12703857668373352954308653)
                ·
                  refine ⟨4763946625640007357865745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12703857668373352954308653 4763946625640007357865745)
                  ·
                    refine ⟨3572959969230005518399309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4763946625640007357865745 3572959969230005518399309)
                    ·
                      refine ⟨1339859988461252069399741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3572959969230005518399309 1339859988461252069399741)
                      ·
                        rfl

theorem cell23_2609368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_2609368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609368 prefixEnd_2609368 := by exact prefixLift 2609368
  have htrace : WordTrace (prefixWord ++ tailWord_2609368) baseStart_2609368 baseEnd_2609368 := by
    simpa [prefixWord, tailWord_2609368, baseEnd_2609368] using wordTrace_append hprefix tailTrace_2609368
  have hstable : (prefixWord ++ tailWord_2609368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609368).length < 2 ^ (prefixWord ++ tailWord_2609368).sum := by decide
  have hdescent : baseEnd_2609368 < baseStart_2609368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609379 : List Nat := [1, 1, 1, 8, 2, 1, 2, 1, 1, 5]
def baseStart_2609379 : Nat := 118140960795 + 2609379 * 2 ^ 59
def prefixEnd_2609379 : Nat := 4983230072969 + 3 ^ 40 * 2609379 * 2
def baseEnd_2609379 : Nat := 446621878916150508787397

theorem tailTrace_2609379 : CollatzResearch.WordTrace tailWord_2609379 prefixEnd_2609379 446621878916150508787397 := by
  unfold tailWord_2609379
  simp only [CollatzResearch.WordTrace]
  refine ⟨95171870813673004298583191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63447913875782002865722127 95171870813673004298583191)
  ·
    refine ⟨142757806220509506447874787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95171870813673004298583191 142757806220509506447874787)
    ·
      refine ⟨214136709330764259671812181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142757806220509506447874787 214136709330764259671812181)
      ·
        refine ⟨2509414562469893668029049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 214136709330764259671812181 2509414562469893668029049)
        ·
          refine ⟨1882060921852420251021787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2509414562469893668029049 1882060921852420251021787)
          ·
            refine ⟨2823091382778630376532681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1882060921852420251021787 2823091382778630376532681)
            ·
              refine ⟨2117318537083972782399511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2823091382778630376532681 2117318537083972782399511)
              ·
                refine ⟨3175977805625959173599267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2117318537083972782399511 3175977805625959173599267)
                ·
                  refine ⟨4763966708438938760398901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3175977805625959173599267 4763966708438938760398901)
                  ·
                    refine ⟨446621878916150508787397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4763966708438938760398901 446621878916150508787397)
                    ·
                      rfl

theorem cell23_2609379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 1, 5].length) (baseStart_2609379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609379 prefixEnd_2609379 := by exact prefixLift 2609379
  have htrace : WordTrace (prefixWord ++ tailWord_2609379) baseStart_2609379 baseEnd_2609379 := by
    simpa [prefixWord, tailWord_2609379, baseEnd_2609379] using wordTrace_append hprefix tailTrace_2609379
  have hstable : (prefixWord ++ tailWord_2609379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609379).length < 2 ^ (prefixWord ++ tailWord_2609379).sum := by decide
  have hdescent : baseEnd_2609379 < baseStart_2609379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609398 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3]
def baseStart_2609398 : Nat := 118140960795 + 2609398 * 2 ^ 59
def prefixEnd_2609398 : Nat := 4983230072969 + 3 ^ 40 * 2609398 * 2
def baseEnd_2609398 : Nat := 1339875392880886952024603

theorem tailTrace_2609398 : CollatzResearch.WordTrace tailWord_2609398 prefixEnd_2609398 1339875392880886952024603 := by
  unfold tailWord_2609398
  simp only [CollatzResearch.WordTrace]
  refine ⟨5948285237537760658970303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63448375867069447029016565 5948285237537760658970303)
  ·
    refine ⟨8922427856306640988455455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5948285237537760658970303 8922427856306640988455455)
    ·
      refine ⟨13383641784459961482683183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8922427856306640988455455 13383641784459961482683183)
      ·
        refine ⟨20075462676689942224024775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13383641784459961482683183 20075462676689942224024775)
        ·
          refine ⟨30113194015034913336037163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20075462676689942224024775 30113194015034913336037163)
          ·
            refine ⟨45169791022552370004055745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30113194015034913336037163 45169791022552370004055745)
            ·
              refine ⟨33877343266914277503041809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45169791022552370004055745 33877343266914277503041809)
              ·
                refine ⟨25408007450185708127281357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33877343266914277503041809 25408007450185708127281357)
                ·
                  refine ⟨9528002793819640547730509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25408007450185708127281357 9528002793819640547730509)
                  ·
                    refine ⟨3573001047682365205398941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9528002793819640547730509 3573001047682365205398941)
                    ·
                      refine ⟨1339875392880886952024603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3573001047682365205398941 1339875392880886952024603)
                      ·
                        rfl

theorem cell23_2609398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_2609398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609398 prefixEnd_2609398 := by exact prefixLift 2609398
  have htrace : WordTrace (prefixWord ++ tailWord_2609398) baseStart_2609398 baseEnd_2609398 := by
    simpa [prefixWord, tailWord_2609398, baseEnd_2609398] using wordTrace_append hprefix tailTrace_2609398
  have hstable : (prefixWord ++ tailWord_2609398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609398).length < 2 ^ (prefixWord ++ tailWord_2609398).sum := by decide
  have hdescent : baseEnd_2609398 < baseStart_2609398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609408 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 5, 3, 2]
def baseStart_2609408 : Nat := 118140960795 + 2609408 * 2 ^ 59
def prefixEnd_2609408 : Nat := 4983230072969 + 3 ^ 40 * 2609408 * 2
def baseEnd_2609408 : Nat := 1339880527687431912899557

theorem tailTrace_2609408 : CollatzResearch.WordTrace tailWord_2609408 prefixEnd_2609408 1339880527687431912899557 := by
  unfold tailWord_2609408
  simp only [CollatzResearch.WordTrace]
  refine ⟨47586464265283971125694439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63448619020378628167592585 47586464265283971125694439)
  ·
    refine ⟨71379696397925956688541659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47586464265283971125694439 71379696397925956688541659)
    ·
      refine ⟨107069544596888935032812489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71379696397925956688541659 107069544596888935032812489)
      ·
        refine ⟨80302158447666701274609367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107069544596888935032812489 80302158447666701274609367)
        ·
          refine ⟨120453237671500051911914051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80302158447666701274609367 120453237671500051911914051)
          ·
            refine ⟨180679856507250077867871077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120453237671500051911914051 180679856507250077867871077)
            ·
              refine ⟨33877473095109389600225827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 180679856507250077867871077 33877473095109389600225827)
              ·
                refine ⟨50816209642664084400338741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33877473095109389600225827 50816209642664084400338741)
                ·
                  refine ⟨4764019653999757912531757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50816209642664084400338741 4764019653999757912531757)
                  ·
                    refine ⟨1786507370249909217199409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4764019653999757912531757 1786507370249909217199409)
                    ·
                      refine ⟨1339880527687431912899557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1786507370249909217199409 1339880527687431912899557)
                      ·
                        rfl

theorem cell23_2609408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 5, 3, 2].length) (baseStart_2609408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609408 prefixEnd_2609408 := by exact prefixLift 2609408
  have htrace : WordTrace (prefixWord ++ tailWord_2609408) baseStart_2609408 baseEnd_2609408 := by
    simpa [prefixWord, tailWord_2609408, baseEnd_2609408] using wordTrace_append hprefix tailTrace_2609408
  have hstable : (prefixWord ++ tailWord_2609408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609408).length < 2 ^ (prefixWord ++ tailWord_2609408).sum := by decide
  have hdescent : baseEnd_2609408 < baseStart_2609408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609412 : List Nat := [2, 3, 2, 2, 4, 1, 1, 1, 1, 2, 4]
def baseStart_2609412 : Nat := 118140960795 + 2609412 * 2 ^ 59
def prefixEnd_2609412 : Nat := 4983230072969 + 3 ^ 40 * 2609412 * 2
def baseEnd_2609412 : Nat := 1339882581610049897249539

theorem tailTrace_2609412 : CollatzResearch.WordTrace tailWord_2609412 prefixEnd_2609412 1339882581610049897249539 := by
  unfold tailWord_2609412
  simp only [CollatzResearch.WordTrace]
  refine ⟨47586537211276725467267245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63448716281702300623022993 47586537211276725467267245)
  ·
    refine ⟨17844951454228772050225217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47586537211276725467267245 17844951454228772050225217)
    ·
      refine ⟨13383713590671579037668913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17844951454228772050225217 13383713590671579037668913)
      ·
        refine ⟨10037785193003684278251685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13383713590671579037668913 10037785193003684278251685)
        ·
          refine ⟨1882084723688190802172191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10037785193003684278251685 1882084723688190802172191)
          ·
            refine ⟨2823127085532286203258287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1882084723688190802172191 2823127085532286203258287)
            ·
              refine ⟨4234690628298429304887431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2823127085532286203258287 4234690628298429304887431)
              ·
                refine ⟨6352035942447643957331147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4234690628298429304887431 6352035942447643957331147)
                ·
                  refine ⟨9528053913671465935996721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6352035942447643957331147 9528053913671465935996721)
                  ·
                    refine ⟨7146040435253599451997541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9528053913671465935996721 7146040435253599451997541)
                    ·
                      refine ⟨1339882581610049897249539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7146040435253599451997541 1339882581610049897249539)
                      ·
                        rfl

theorem cell23_2609412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_2609412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609412 prefixEnd_2609412 := by exact prefixLift 2609412
  have htrace : WordTrace (prefixWord ++ tailWord_2609412) baseStart_2609412 baseEnd_2609412 := by
    simpa [prefixWord, tailWord_2609412, baseEnd_2609412] using wordTrace_append hprefix tailTrace_2609412
  have hstable : (prefixWord ++ tailWord_2609412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609412).length < 2 ^ (prefixWord ++ tailWord_2609412).sum := by decide
  have hdescent : baseEnd_2609412 < baseStart_2609412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609425 : List Nat := [1, 2, 2, 1, 1, 5, 1, 4, 1, 3, 2]
def baseStart_2609425 : Nat := 118140960795 + 2609425 * 2 ^ 59
def prefixEnd_2609425 : Nat := 4983230072969 + 3 ^ 40 * 2609425 * 2
def baseEnd_2609425 : Nat := 1339889256858558346386979

theorem tailTrace_2609425 : CollatzResearch.WordTrace tailWord_2609425 prefixEnd_2609425 1339889256858558346386979 := by
  unfold tailWord_2609425
  simp only [CollatzResearch.WordTrace]
  refine ⟨95173548571506354154757729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63449032381004236103171819 95173548571506354154757729)
  ·
    refine ⟨71380161428629765616068297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95173548571506354154757729 71380161428629765616068297)
    ·
      refine ⟨53535121071472324212051223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71380161428629765616068297 53535121071472324212051223)
      ·
        refine ⟨80302681607208486318076835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53535121071472324212051223 80302681607208486318076835)
        ·
          refine ⟨120454022410812729477115253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80302681607208486318076835 120454022410812729477115253)
          ·
            refine ⟨11292564601013693388479555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 120454022410812729477115253 11292564601013693388479555)
            ·
              refine ⟨16938846901520540082719333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11292564601013693388479555 16938846901520540082719333)
              ·
                refine ⟨3176033794035101265509875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16938846901520540082719333 3176033794035101265509875)
                ·
                  refine ⟨4764050691052651898264813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3176033794035101265509875 4764050691052651898264813)
                  ·
                    refine ⟨1786519009144744461849305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4764050691052651898264813 1786519009144744461849305)
                    ·
                      refine ⟨1339889256858558346386979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1786519009144744461849305 1339889256858558346386979)
                      ·
                        rfl

theorem cell23_2609425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 3, 2].length) (baseStart_2609425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609425 prefixEnd_2609425 := by exact prefixLift 2609425
  have htrace : WordTrace (prefixWord ++ tailWord_2609425) baseStart_2609425 baseEnd_2609425 := by
    simpa [prefixWord, tailWord_2609425, baseEnd_2609425] using wordTrace_append hprefix tailTrace_2609425
  have hstable : (prefixWord ++ tailWord_2609425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609425).length < 2 ^ (prefixWord ++ tailWord_2609425).sum := by decide
  have hdescent : baseEnd_2609425 < baseStart_2609425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609441 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 1, 3, 5]
def baseStart_2609441 : Nat := 118140960795 + 2609441 * 2 ^ 59
def prefixEnd_2609441 : Nat := 4983230072969 + 3 ^ 40 * 2609441 * 2
def baseEnd_2609441 : Nat := 1339897472549030283786905

theorem tailTrace_2609441 : CollatzResearch.WordTrace tailWord_2609441 prefixEnd_2609441 1339897472549030283786905 := by
  unfold tailWord_2609441
  simp only [CollatzResearch.WordTrace]
  refine ⟨95174132139448388887340177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63449421426298925924893451 95174132139448388887340177)
  ·
    refine ⟨71380599104586291665505133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95174132139448388887340177 71380599104586291665505133)
    ·
      refine ⟨26767724664219859374564425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71380599104586291665505133 26767724664219859374564425)
      ·
        refine ⟨20075793498164894530923319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26767724664219859374564425 20075793498164894530923319)
        ·
          refine ⟨30113690247247341796384979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20075793498164894530923319 30113690247247341796384979)
          ·
            refine ⟨45170535370871012694577469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30113690247247341796384979 45170535370871012694577469)
            ·
              refine ⟨16938950764076629760466551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45170535370871012694577469 16938950764076629760466551)
              ·
                refine ⟨25408426146114944640699827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16938950764076629760466551 25408426146114944640699827)
                ·
                  refine ⟨38112639219172416961049741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25408426146114944640699827 38112639219172416961049741)
                  ·
                    refine ⟨14292239707189656360393653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38112639219172416961049741 14292239707189656360393653)
                    ·
                      refine ⟨1339897472549030283786905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14292239707189656360393653 1339897472549030283786905)
                      ·
                        rfl

theorem cell23_2609441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_2609441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609441 prefixEnd_2609441 := by exact prefixLift 2609441
  have htrace : WordTrace (prefixWord ++ tailWord_2609441) baseStart_2609441 baseEnd_2609441 := by
    simpa [prefixWord, tailWord_2609441, baseEnd_2609441] using wordTrace_append hprefix tailTrace_2609441
  have hstable : (prefixWord ++ tailWord_2609441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609441).length < 2 ^ (prefixWord ++ tailWord_2609441).sum := by decide
  have hdescent : baseEnd_2609441 < baseStart_2609441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609442 : List Nat := [3, 3, 1, 1, 3, 1, 2, 3, 1, 3, 2]
def baseStart_2609442 : Nat := 118140960795 + 2609442 * 2 ^ 59
def prefixEnd_2609442 : Nat := 4983230072969 + 3 ^ 40 * 2609442 * 2
def baseEnd_2609442 : Nat := 1339897986029684779874401

theorem tailTrace_2609442 : CollatzResearch.WordTrace tailWord_2609442 prefixEnd_2609442 1339897986029684779874401 := by
  unfold tailWord_2609442
  simp only [CollatzResearch.WordTrace]
  refine ⟨23793542153111191514531645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63449445741629844038751053 23793542153111191514531645)
  ·
    refine ⟨8922578307416696817949367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23793542153111191514531645 8922578307416696817949367)
    ·
      refine ⟨13383867461125045226924051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8922578307416696817949367 13383867461125045226924051)
      ·
        refine ⟨20075801191687567840386077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13383867461125045226924051 20075801191687567840386077)
        ·
          refine ⟨7528425446882837940144779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20075801191687567840386077 7528425446882837940144779)
          ·
            refine ⟨11292638170324256910217169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7528425446882837940144779 11292638170324256910217169)
            ·
              refine ⟨8469478627743192682662877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11292638170324256910217169 8469478627743192682662877)
              ·
                refine ⟨3176054485403697255998579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8469478627743192682662877 3176054485403697255998579)
                ·
                  refine ⟨4764081728105545883997869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3176054485403697255998579 4764081728105545883997869)
                  ·
                    refine ⟨1786530648039579706499201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4764081728105545883997869 1786530648039579706499201)
                    ·
                      refine ⟨1339897986029684779874401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1786530648039579706499201 1339897986029684779874401)
                      ·
                        rfl

theorem cell23_2609442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_2609442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609442 prefixEnd_2609442 := by exact prefixLift 2609442
  have htrace : WordTrace (prefixWord ++ tailWord_2609442) baseStart_2609442 baseEnd_2609442 := by
    simpa [prefixWord, tailWord_2609442, baseEnd_2609442] using wordTrace_append hprefix tailTrace_2609442
  have hstable : (prefixWord ++ tailWord_2609442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609442).length < 2 ^ (prefixWord ++ tailWord_2609442).sum := by decide
  have hdescent : baseEnd_2609442 < baseStart_2609442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609455 : List Nat := [1, 1, 2, 1, 2, 1, 6, 1, 4, 2, 2]
def baseStart_2609455 : Nat := 118140960795 + 2609455 * 2 ^ 59
def prefixEnd_2609455 : Nat := 4983230072969 + 3 ^ 40 * 2609455 * 2
def baseEnd_2609455 : Nat := 1339904661278193229011841

theorem tailTrace_2609455 : CollatzResearch.WordTrace tailWord_2609455 prefixEnd_2609455 1339904661278193229011841 := by
  unfold tailWord_2609455
  simp only [CollatzResearch.WordTrace]
  refine ⟨95174642761397669278349819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63449761840931779518899879 95174642761397669278349819)
  ·
    refine ⟨142761964142096503917524729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95174642761397669278349819 142761964142096503917524729)
    ·
      refine ⟨107071473106572377938143547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142761964142096503917524729 107071473106572377938143547)
      ·
        refine ⟨160607209659858566907215321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107071473106572377938143547 160607209659858566907215321)
        ·
          refine ⟨120455407244893925180411491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160607209659858566907215321 120455407244893925180411491)
          ·
            refine ⟨180683110867340887770617237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120455407244893925180411491 180683110867340887770617237)
            ·
              refine ⟨8469520821906604114247683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 180683110867340887770617237 8469520821906604114247683)
              ·
                refine ⟨12704281232859906171371525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8469520821906604114247683 12704281232859906171371525)
                ·
                  refine ⟨2382052731161232407132161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12704281232859906171371525 2382052731161232407132161)
                  ·
                    refine ⟨1786539548370924305349121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2382052731161232407132161 1786539548370924305349121)
                    ·
                      refine ⟨1339904661278193229011841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1786539548370924305349121 1339904661278193229011841)
                      ·
                        rfl

theorem cell23_2609455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 4, 2, 2].length) (baseStart_2609455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609455 prefixEnd_2609455 := by exact prefixLift 2609455
  have htrace : WordTrace (prefixWord ++ tailWord_2609455) baseStart_2609455 baseEnd_2609455 := by
    simpa [prefixWord, tailWord_2609455, baseEnd_2609455] using wordTrace_append hprefix tailTrace_2609455
  have hstable : (prefixWord ++ tailWord_2609455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609455).length < 2 ^ (prefixWord ++ tailWord_2609455).sum := by decide
  have hdescent : baseEnd_2609455 < baseStart_2609455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609476 : List Nat := [2, 3, 4, 1, 2, 2, 1, 2, 1, 3, 2]
def baseStart_2609476 : Nat := 118140960795 + 2609476 * 2 ^ 59
def prefixEnd_2609476 : Nat := 4983230072969 + 3 ^ 40 * 2609476 * 2
def baseEnd_2609476 : Nat := 1339915444371937646849245

theorem tailTrace_2609476 : CollatzResearch.WordTrace tailWord_2609476 prefixEnd_2609476 1339915444371937646849245 := by
  unfold tailWord_2609476
  simp only [CollatzResearch.WordTrace]
  refine ⟨47587704347160794932432141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63450272462881059909909521 47587704347160794932432141)
  ·
    refine ⟨17845389130185298099662053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47587704347160794932432141 17845389130185298099662053)
    ·
      refine ⟨3346010461909743393686635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17845389130185298099662053 3346010461909743393686635)
      ·
        refine ⟨5019015692864615090529953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3346010461909743393686635 5019015692864615090529953)
        ·
          refine ⟨3764261769648461317897465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5019015692864615090529953 3764261769648461317897465)
          ·
            refine ⟨2823196327236345988423099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3764261769648461317897465 2823196327236345988423099)
            ·
              refine ⟨4234794490854518982634649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2823196327236345988423099 4234794490854518982634649)
              ·
                refine ⟨3176095868140889236975987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4234794490854518982634649 3176095868140889236975987)
                ·
                  refine ⟨4764143802211333855463981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3176095868140889236975987 4764143802211333855463981)
                  ·
                    refine ⟨1786553925829250195798993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4764143802211333855463981 1786553925829250195798993)
                    ·
                      refine ⟨1339915444371937646849245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1786553925829250195798993 1339915444371937646849245)
                      ·
                        rfl

theorem cell23_2609476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_2609476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609476 prefixEnd_2609476 := by exact prefixLift 2609476
  have htrace : WordTrace (prefixWord ++ tailWord_2609476) baseStart_2609476 baseEnd_2609476 := by
    simpa [prefixWord, tailWord_2609476, baseEnd_2609476] using wordTrace_append hprefix tailTrace_2609476
  have hstable : (prefixWord ++ tailWord_2609476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609476).length < 2 ^ (prefixWord ++ tailWord_2609476).sum := by decide
  have hdescent : baseEnd_2609476 < baseStart_2609476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609508 : List Nat := [2, 3, 1, 1, 3, 1, 1, 4, 2, 5]
def baseStart_2609508 : Nat := 118140960795 + 2609508 * 2 ^ 59
def prefixEnd_2609508 : Nat := 4983230072969 + 3 ^ 40 * 2609508 * 2
def baseEnd_2609508 : Nat := 446643958584293840549699

theorem tailTrace_2609508 : CollatzResearch.WordTrace tailWord_2609508 prefixEnd_2609508 446643958584293840549699 := by
  unfold tailWord_2609508
  simp only [CollatzResearch.WordTrace]
  refine ⟨47588287915102829665014589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63451050553470439553352785 47588287915102829665014589)
  ·
    refine ⟨17845607968163561124380471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47588287915102829665014589 17845607968163561124380471)
    ·
      refine ⟨26768411952245341686570707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17845607968163561124380471 26768411952245341686570707)
      ·
        refine ⟨40152617928368012529856061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26768411952245341686570707 40152617928368012529856061)
        ·
          refine ⟨15057231723138004698696023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40152617928368012529856061 15057231723138004698696023)
          ·
            refine ⟨22585847584707007048044035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15057231723138004698696023 22585847584707007048044035)
            ·
              refine ⟨33878771377060510572066053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22585847584707007048044035 33878771377060510572066053)
              ·
                refine ⟨6352269633198845732262385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33878771377060510572066053 6352269633198845732262385)
                ·
                  refine ⟨4764202224899134299196789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6352269633198845732262385 4764202224899134299196789)
                  ·
                    refine ⟨446643958584293840549699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4764202224899134299196789 446643958584293840549699)
                    ·
                      rfl

theorem cell23_2609508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_2609508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609508 prefixEnd_2609508 := by exact prefixLift 2609508
  have htrace : WordTrace (prefixWord ++ tailWord_2609508) baseStart_2609508 baseEnd_2609508 := by
    simpa [prefixWord, tailWord_2609508, baseEnd_2609508] using wordTrace_append hprefix tailTrace_2609508
  have hstable : (prefixWord ++ tailWord_2609508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609508).length < 2 ^ (prefixWord ++ tailWord_2609508).sum := by decide
  have hdescent : baseEnd_2609508 < baseStart_2609508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609512 : List Nat := [2, 1, 4, 2, 2, 1, 4, 2, 5]
def baseStart_2609512 : Nat := 118140960795 + 2609512 * 2 ^ 59
def prefixEnd_2609512 : Nat := 4983230072969 + 3 ^ 40 * 2609512 * 2
def baseEnd_2609512 : Nat := 148881547741722167333231

theorem tailTrace_2609512 : CollatzResearch.WordTrace tailWord_2609512 prefixEnd_2609512 148881547741722167333231 := by
  unfold tailWord_2609512
  simp only [CollatzResearch.WordTrace]
  refine ⟨47588360861095584006587395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63451147814794112008783193 47588360861095584006587395)
  ·
    refine ⟨71382541291643376009881093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47588360861095584006587395 71382541291643376009881093)
    ·
      refine ⟨13384226492183133001852705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71382541291643376009881093 13384226492183133001852705)
      ·
        refine ⟨10038169869137349751389529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13384226492183133001852705 10038169869137349751389529)
        ·
          refine ⟨7528627401853012313542147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10038169869137349751389529 7528627401853012313542147)
          ·
            refine ⟨11292941102779518470313221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7528627401853012313542147 11292941102779518470313221)
            ·
              refine ⟨2117426456771159713183729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11292941102779518470313221 2117426456771159713183729)
              ·
                refine ⟨1588069842578369784887797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2117426456771159713183729 1588069842578369784887797)
                ·
                  refine ⟨148881547741722167333231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1588069842578369784887797 148881547741722167333231)
                  ·
                    rfl

theorem cell23_2609512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 2, 5].length) (baseStart_2609512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609512 prefixEnd_2609512 := by exact prefixLift 2609512
  have htrace : WordTrace (prefixWord ++ tailWord_2609512) baseStart_2609512 baseEnd_2609512 := by
    simpa [prefixWord, tailWord_2609512, baseEnd_2609512] using wordTrace_append hprefix tailTrace_2609512
  have hstable : (prefixWord ++ tailWord_2609512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609512).length < 2 ^ (prefixWord ++ tailWord_2609512).sum := by decide
  have hdescent : baseEnd_2609512 < baseStart_2609512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609521 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 2, 8]
def baseStart_2609521 : Nat := 118140960795 + 2609521 * 2 ^ 59
def prefixEnd_2609521 : Nat := 4983230072969 + 3 ^ 40 * 2609521 * 2
def baseEnd_2609521 : Nat := 446646183667129990262179

theorem tailTrace_2609521 : CollatzResearch.WordTrace tailWord_2609521 prefixEnd_2609521 446646183667129990262179 := by
  unfold tailWord_2609521
  simp only [CollatzResearch.WordTrace]
  refine ⟨95177049979158562550252417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63451366652772375033501611 95177049979158562550252417)
  ·
    refine ⟨71382787484368921912689313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95177049979158562550252417 71382787484368921912689313)
    ·
      refine ⟨53537090613276691434516985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71382787484368921912689313 53537090613276691434516985)
      ·
        refine ⟨40152817959957518575887739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53537090613276691434516985 40152817959957518575887739)
        ·
          refine ⟨60229226939936277863831609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40152817959957518575887739 60229226939936277863831609)
          ·
            refine ⟨45171920204952208397873707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60229226939936277863831609 45171920204952208397873707)
            ·
              refine ⟨67757880307428312596810561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45171920204952208397873707 67757880307428312596810561)
              ·
                refine ⟨50818410230571234447607921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67757880307428312596810561 50818410230571234447607921)
                ·
                  refine ⟨38113807672928425835705941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50818410230571234447607921 38113807672928425835705941)
                  ·
                    refine ⟨446646183667129990262179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38113807672928425835705941 446646183667129990262179)
                    ·
                      rfl

theorem cell23_2609521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 8].length) (baseStart_2609521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609521 prefixEnd_2609521 := by exact prefixLift 2609521
  have htrace : WordTrace (prefixWord ++ tailWord_2609521) baseStart_2609521 baseEnd_2609521 := by
    simpa [prefixWord, tailWord_2609521, baseEnd_2609521] using wordTrace_append hprefix tailTrace_2609521
  have hstable : (prefixWord ++ tailWord_2609521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609521).length < 2 ^ (prefixWord ++ tailWord_2609521).sum := by decide
  have hdescent : baseEnd_2609521 < baseStart_2609521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609545 : List Nat := [1, 2, 1, 1, 6, 1, 3, 1, 2, 1, 4]
def baseStart_2609545 : Nat := 118140960795 + 2609545 * 2 ^ 59
def prefixEnd_2609545 : Nat := 4983230072969 + 3 ^ 40 * 2609545 * 2
def baseEnd_2609545 : Nat := 1339950874537097876886427

theorem tailTrace_2609545 : CollatzResearch.WordTrace tailWord_2609545 prefixEnd_2609545 1339950874537097876886427 := by
  unfold tailWord_2609545
  simp only [CollatzResearch.WordTrace]
  refine ⟨95177925331071614649126089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63451950220714409766084059 95177925331071614649126089)
  ·
    refine ⟨71383443998303710986844567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95177925331071614649126089 71383443998303710986844567)
    ·
      refine ⟨107075165997455566480266851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71383443998303710986844567 107075165997455566480266851)
      ·
        refine ⟨160612748996183349720400277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107075165997455566480266851 160612748996183349720400277)
        ·
          refine ⟨7528722609196094518143763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 160612748996183349720400277 7528722609196094518143763)
          ·
            refine ⟨11293083913794141777215645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7528722609196094518143763 11293083913794141777215645)
            ·
              refine ⟨4234906467672803166455867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11293083913794141777215645 4234906467672803166455867)
              ·
                refine ⟨6352359701509204749683801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4234906467672803166455867 6352359701509204749683801)
                ·
                  refine ⟨4764269776131903562262851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6352359701509204749683801 4764269776131903562262851)
                  ·
                    refine ⟨7146404664197855343394277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4764269776131903562262851 7146404664197855343394277)
                    ·
                      refine ⟨1339950874537097876886427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7146404664197855343394277 1339950874537097876886427)
                      ·
                        rfl

theorem cell23_2609545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 1, 4].length) (baseStart_2609545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609545 prefixEnd_2609545 := by exact prefixLift 2609545
  have htrace : WordTrace (prefixWord ++ tailWord_2609545) baseStart_2609545 baseEnd_2609545 := by
    simpa [prefixWord, tailWord_2609545, baseEnd_2609545] using wordTrace_append hprefix tailTrace_2609545
  have hstable : (prefixWord ++ tailWord_2609545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609545).length < 2 ^ (prefixWord ++ tailWord_2609545).sum := by decide
  have hdescent : baseEnd_2609545 < baseStart_2609545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609568 : List Nat := [2, 1, 1, 4, 1, 4, 1, 1, 8]
def baseStart_2609568 : Nat := 118140960795 + 2609568 * 2 ^ 59
def prefixEnd_2609568 : Nat := 4983230072969 + 3 ^ 40 * 2609568 * 2
def baseEnd_2609568 : Nat := 148884742732461254099869

theorem tailTrace_2609568 : CollatzResearch.WordTrace tailWord_2609568 prefixEnd_2609568 148884742732461254099869 := by
  unfold tailWord_2609568
  simp only [CollatzResearch.WordTrace]
  refine ⟨47589382104994144788606679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63452509473325526384808905 47589382104994144788606679)
  ·
    refine ⟨71384073157491217182910019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47589382104994144788606679 71384073157491217182910019)
    ·
      refine ⟨107076109736236825774365029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71384073157491217182910019 107076109736236825774365029)
      ·
        refine ⟨20076770575544404832693443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107076109736236825774365029 20076770575544404832693443)
        ·
          refine ⟨30115155863316607249040165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20076770575544404832693443 30115155863316607249040165)
          ·
            refine ⟨5646591724371863859195031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30115155863316607249040165 5646591724371863859195031)
            ·
              refine ⟨8469887586557795788792547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5646591724371863859195031 8469887586557795788792547)
              ·
                refine ⟨12704831379836693683188821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8469887586557795788792547 12704831379836693683188821)
                ·
                  refine ⟨148884742732461254099869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12704831379836693683188821 148884742732461254099869)
                  ·
                    rfl

theorem cell23_2609568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 8].length) (baseStart_2609568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609568 prefixEnd_2609568 := by exact prefixLift 2609568
  have htrace : WordTrace (prefixWord ++ tailWord_2609568) baseStart_2609568 baseEnd_2609568 := by
    simpa [prefixWord, tailWord_2609568, baseEnd_2609568] using wordTrace_append hprefix tailTrace_2609568
  have hstable : (prefixWord ++ tailWord_2609568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609568).length < 2 ^ (prefixWord ++ tailWord_2609568).sum := by decide
  have hdescent : baseEnd_2609568 < baseStart_2609568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609572 : List Nat := [2, 3, 1, 2, 1, 1, 4, 4, 1, 4]
def baseStart_2609572 : Nat := 118140960795 + 2609572 * 2 ^ 59
def prefixEnd_2609572 : Nat := 4983230072969 + 3 ^ 40 * 2609572 * 2
def baseEnd_2609572 : Nat := 446654912838256423749601

theorem tailTrace_2609572 : CollatzResearch.WordTrace tailWord_2609572 prefixEnd_2609572 446654912838256423749601 := by
  unfold tailWord_2609572
  simp only [CollatzResearch.WordTrace]
  refine ⟨47589455050986899130179485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63452606734649198840239313 47589455050986899130179485)
  ·
    refine ⟨17846045644120087173817307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47589455050986899130179485 17846045644120087173817307)
    ·
      refine ⟨26769068466180130760725961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17846045644120087173817307 26769068466180130760725961)
      ·
        refine ⟨20076801349635098070544471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26769068466180130760725961 20076801349635098070544471)
        ·
          refine ⟨30115202024452647105816707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20076801349635098070544471 30115202024452647105816707)
          ·
            refine ⟨45172803036678970658725061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30115202024452647105816707 45172803036678970658725061)
            ·
              refine ⟨8469900569377306998510949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45172803036678970658725061 8469900569377306998510949)
              ·
                refine ⟨1588106356758245062220803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8469900569377306998510949 1588106356758245062220803)
                ·
                  refine ⟨2382159535137367593331205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1588106356758245062220803 2382159535137367593331205)
                  ·
                    refine ⟨446654912838256423749601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2382159535137367593331205 446654912838256423749601)
                    ·
                      rfl

theorem cell23_2609572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 4, 1, 4].length) (baseStart_2609572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609572 prefixEnd_2609572 := by exact prefixLift 2609572
  have htrace : WordTrace (prefixWord ++ tailWord_2609572) baseStart_2609572 baseEnd_2609572 := by
    simpa [prefixWord, tailWord_2609572, baseEnd_2609572] using wordTrace_append hprefix tailTrace_2609572
  have hstable : (prefixWord ++ tailWord_2609572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609572).length < 2 ^ (prefixWord ++ tailWord_2609572).sum := by decide
  have hdescent : baseEnd_2609572 < baseStart_2609572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609605 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 8, 3, 2]
def baseStart_2609605 : Nat := 118140960795 + 2609605 * 2 ^ 59
def prefixEnd_2609605 : Nat := 4983230072969 + 3 ^ 40 * 2609605 * 2
def baseEnd_2609605 : Nat := 1339981683376367642136151

theorem tailTrace_2609605 : CollatzResearch.WordTrace tailWord_2609605 prefixEnd_2609605 1339981683376367642136151 := by
  unfold tailWord_2609605
  simp only [CollatzResearch.WordTrace]
  refine ⟨95180113710854244896310269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63453409140569496597540179 95180113710854244896310269)
  ·
    refine ⟨35692542641570341836116351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95180113710854244896310269 35692542641570341836116351)
    ·
      refine ⟨53538813962355512754174527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35692542641570341836116351 53538813962355512754174527)
      ·
        refine ⟨80308220943533269131261791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53538813962355512754174527 80308220943533269131261791)
        ·
          refine ⟨120462331415299903696892687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80308220943533269131261791 120462331415299903696892687)
          ·
            refine ⟨180693497122949855545339031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120462331415299903696892687 180693497122949855545339031)
            ·
              refine ⟨271040245684424783318008547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180693497122949855545339031 271040245684424783318008547)
              ·
                refine ⟨406560368526637174977012821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271040245684424783318008547 406560368526637174977012821)
                ·
                  refine ⟨4764379318671529394261869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 406560368526637174977012821 4764379318671529394261869)
                  ·
                    refine ⟨1786642244501823522848201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4764379318671529394261869 1786642244501823522848201)
                    ·
                      refine ⟨1339981683376367642136151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1786642244501823522848201 1339981683376367642136151)
                      ·
                        rfl

theorem cell23_2609605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 3, 2].length) (baseStart_2609605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609605 prefixEnd_2609605 := by exact prefixLift 2609605
  have htrace : WordTrace (prefixWord ++ tailWord_2609605) baseStart_2609605 baseEnd_2609605 := by
    simpa [prefixWord, tailWord_2609605, baseEnd_2609605] using wordTrace_append hprefix tailTrace_2609605
  have hstable : (prefixWord ++ tailWord_2609605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609605).length < 2 ^ (prefixWord ++ tailWord_2609605).sum := by decide
  have hdescent : baseEnd_2609605 < baseStart_2609605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609648 : List Nat := [2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 6]
def baseStart_2609648 : Nat := 118140960795 + 2609648 * 2 ^ 59
def prefixEnd_2609648 : Nat := 4983230072969 + 3 ^ 40 * 2609648 * 2
def baseEnd_2609648 : Nat := 1340003763044510973898453

theorem tailTrace_2609648 : CollatzResearch.WordTrace tailWord_2609648 prefixEnd_2609648 1340003763044510973898453 := by
  unfold tailWord_2609648
  simp only [CollatzResearch.WordTrace]
  refine ⟨47590841024849231620062799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63454454699798975493417065 47590841024849231620062799)
  ·
    refine ⟨71386261537273847430094199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47590841024849231620062799 71386261537273847430094199)
    ·
      refine ⟨107079392305910771145141299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71386261537273847430094199 107079392305910771145141299)
      ·
        refine ⟨160619088458866156717711949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107079392305910771145141299 160619088458866156717711949)
        ·
          refine ⟨60232158172074808769141981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160619088458866156717711949 60232158172074808769141981)
          ·
            refine ⟨22587059314528053288428243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60232158172074808769141981 22587059314528053288428243)
            ·
              refine ⟨33880588971792079932642365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22587059314528053288428243 33880588971792079932642365)
              ·
                refine ⟨12705220864422029974740887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33880588971792079932642365 12705220864422029974740887)
                ·
                  refine ⟨19057831296633044962111331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12705220864422029974740887 19057831296633044962111331)
                  ·
                    refine ⟨28586746944949567443166997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19057831296633044962111331 28586746944949567443166997)
                    ·
                      refine ⟨1340003763044510973898453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28586746944949567443166997 1340003763044510973898453)
                      ·
                        rfl

theorem cell23_2609648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 6].length) (baseStart_2609648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609648 prefixEnd_2609648 := by exact prefixLift 2609648
  have htrace : WordTrace (prefixWord ++ tailWord_2609648) baseStart_2609648 baseEnd_2609648 := by
    simpa [prefixWord, tailWord_2609648, baseEnd_2609648] using wordTrace_append hprefix tailTrace_2609648
  have hstable : (prefixWord ++ tailWord_2609648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609648).length < 2 ^ (prefixWord ++ tailWord_2609648).sum := by decide
  have hdescent : baseEnd_2609648 < baseStart_2609648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609665 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 3, 2, 4]
def baseStart_2609665 : Nat := 118140960795 + 2609665 * 2 ^ 59
def prefixEnd_2609665 : Nat := 4983230072969 + 3 ^ 40 * 2609665 * 2
def baseEnd_2609665 : Nat := 1340012492215637407385875

theorem tailTrace_2609665 : CollatzResearch.WordTrace tailWord_2609665 prefixEnd_2609665 1340012492215637407385875 := by
  unfold tailWord_2609665
  simp only [CollatzResearch.WordTrace]
  refine ⟨95182302090636875143494449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63454868060424583428996299 95182302090636875143494449)
  ·
    refine ⟨71386726567977656357620837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95182302090636875143494449 71386726567977656357620837)
    ·
      refine ⟨13385011231495810567053907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71386726567977656357620837 13385011231495810567053907)
      ·
        refine ⟨20077516847243715850580861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13385011231495810567053907 20077516847243715850580861)
        ·
          refine ⟨7529068817716393443967823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20077516847243715850580861 7529068817716393443967823)
          ·
            refine ⟨11293603226574590165951735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7529068817716393443967823 11293603226574590165951735)
            ·
              refine ⟨16940404839861885248927603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11293603226574590165951735 16940404839861885248927603)
              ·
                refine ⟨25410607259792827873391405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16940404839861885248927603 25410607259792827873391405)
                ·
                  refine ⟨9528977722422310452521777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25410607259792827873391405 9528977722422310452521777)
                  ·
                    refine ⟨7146733291816732839391333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9528977722422310452521777 7146733291816732839391333)
                    ·
                      refine ⟨1340012492215637407385875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7146733291816732839391333 1340012492215637407385875)
                      ·
                        rfl

theorem cell23_2609665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_2609665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609665 prefixEnd_2609665 := by exact prefixLift 2609665
  have htrace : WordTrace (prefixWord ++ tailWord_2609665) baseStart_2609665 baseEnd_2609665 := by
    simpa [prefixWord, tailWord_2609665, baseEnd_2609665] using wordTrace_append hprefix tailTrace_2609665
  have hstable : (prefixWord ++ tailWord_2609665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609665).length < 2 ^ (prefixWord ++ tailWord_2609665).sum := by decide
  have hdescent : baseEnd_2609665 < baseStart_2609665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609666 : List Nat := [3, 4, 1, 2, 2, 1, 3, 1, 1, 5]
def baseStart_2609666 : Nat := 118140960795 + 2609666 * 2 ^ 59
def prefixEnd_2609666 : Nat := 4983230072969 + 3 ^ 40 * 2609666 * 2
def baseEnd_2609666 : Nat := 446671001898763967824457

theorem tailTrace_2609666 : CollatzResearch.WordTrace tailWord_2609666 prefixEnd_2609666 446671001898763967824457 := by
  unfold tailWord_2609666
  simp only [CollatzResearch.WordTrace]
  refine ⟨23795584640908313078570213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63454892375755501542853901 23795584640908313078570213)
  ·
    refine ⟨4461672120170308702231915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23795584640908313078570213 4461672120170308702231915)
    ·
      refine ⟨6692508180255463053347873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4461672120170308702231915 6692508180255463053347873)
      ·
        refine ⟨5019381135191597290010905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6692508180255463053347873 5019381135191597290010905)
        ·
          refine ⟨3764535851393697967508179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5019381135191597290010905 3764535851393697967508179)
          ·
            refine ⟨5646803777090546951262269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3764535851393697967508179 5646803777090546951262269)
            ·
              refine ⟨2117551416408955106723351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5646803777090546951262269 2117551416408955106723351)
              ·
                refine ⟨3176327124613432660085027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2117551416408955106723351 3176327124613432660085027)
                ·
                  refine ⟨4764490686920148990127541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3176327124613432660085027 4764490686920148990127541)
                  ·
                    refine ⟨446671001898763967824457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4764490686920148990127541 446671001898763967824457)
                    ·
                      rfl

theorem cell23_2609666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_2609666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609666 prefixEnd_2609666 := by exact prefixLift 2609666
  have htrace : WordTrace (prefixWord ++ tailWord_2609666) baseStart_2609666 baseEnd_2609666 := by
    simpa [prefixWord, tailWord_2609666, baseEnd_2609666] using wordTrace_append hprefix tailTrace_2609666
  have hstable : (prefixWord ++ tailWord_2609666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609666).length < 2 ^ (prefixWord ++ tailWord_2609666).sum := by decide
  have hdescent : baseEnd_2609666 < baseStart_2609666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609685 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 3, 3, 3]
def baseStart_2609685 : Nat := 118140960795 + 2609685 * 2 ^ 59
def prefixEnd_2609685 : Nat := 4983230072969 + 3 ^ 40 * 2609685 * 2
def baseEnd_2609685 : Nat := 1340022761828727329135783

theorem tailTrace_2609685 : CollatzResearch.WordTrace tailWord_2609685 prefixEnd_2609685 1340022761828727329135783 := by
  unfold tailWord_2609685
  simp only [CollatzResearch.WordTrace]
  refine ⟨95183031550564418559222509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63455354367042945706148339 95183031550564418559222509)
  ·
    refine ⟨35693636831461656959708441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95183031550564418559222509 35693636831461656959708441)
    ·
      refine ⟨26770227623596242719781331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35693636831461656959708441 26770227623596242719781331)
      ·
        refine ⟨40155341435394364079671997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26770227623596242719781331 40155341435394364079671997)
        ·
          refine ⟨15058253038272886529876999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40155341435394364079671997 15058253038272886529876999)
          ·
            refine ⟨22587379557409329794815499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15058253038272886529876999 22587379557409329794815499)
            ·
              refine ⟨33881069336113994692223249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22587379557409329794815499 33881069336113994692223249)
              ·
                refine ⟨25410802002085496019167437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33881069336113994692223249 25410802002085496019167437)
                ·
                  refine ⟨9529050750782061007187789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25410802002085496019167437 9529050750782061007187789)
                  ·
                    refine ⟨3573394031543272877695421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9529050750782061007187789 3573394031543272877695421)
                    ·
                      refine ⟨1340022761828727329135783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3573394031543272877695421 1340022761828727329135783)
                      ·
                        rfl

theorem cell23_2609685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_2609685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609685 prefixEnd_2609685 := by exact prefixLift 2609685
  have htrace : WordTrace (prefixWord ++ tailWord_2609685) baseStart_2609685 baseEnd_2609685 := by
    simpa [prefixWord, tailWord_2609685, baseEnd_2609685] using wordTrace_append hprefix tailTrace_2609685
  have hstable : (prefixWord ++ tailWord_2609685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609685).length < 2 ^ (prefixWord ++ tailWord_2609685).sum := by decide
  have hdescent : baseEnd_2609685 < baseStart_2609685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609703 : List Nat := [1, 1, 7, 2, 1, 1, 1, 2, 3, 2, 2]
def baseStart_2609703 : Nat := 118140960795 + 2609703 * 2 ^ 59
def prefixEnd_2609703 : Nat := 4983230072969 + 3 ^ 40 * 2609703 * 2
def baseEnd_2609703 : Nat := 1340032004480508258710701

theorem tailTrace_2609703 : CollatzResearch.WordTrace tailWord_2609703 prefixEnd_2609703 1340032004480508258710701 := by
  unfold tailWord_2609703
  simp only [CollatzResearch.WordTrace]
  refine ⟨95183688064499207633377763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63455792042999471755585175 95183688064499207633377763)
  ·
    refine ⟨142775532096748811450066645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95183688064499207633377763 142775532096748811450066645)
    ·
      refine ⟨3346301533517550268360937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 142775532096748811450066645 3346301533517550268360937)
      ·
        refine ⟨2509726150138162701270703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3346301533517550268360937 2509726150138162701270703)
        ·
          refine ⟨3764589225207244051906055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2509726150138162701270703 3764589225207244051906055)
          ·
            refine ⟨5646883837810866077859083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3764589225207244051906055 5646883837810866077859083)
            ·
              refine ⟨8470325756716299116788625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5646883837810866077859083 8470325756716299116788625)
              ·
                refine ⟨6352744317537224337591469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8470325756716299116788625 6352744317537224337591469)
                ·
                  refine ⟨2382279119076459126596801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6352744317537224337591469 2382279119076459126596801)
                  ·
                    refine ⟨1786709339307344344947601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2382279119076459126596801 1786709339307344344947601)
                    ·
                      refine ⟨1340032004480508258710701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1786709339307344344947601 1340032004480508258710701)
                      ·
                        rfl

theorem cell23_2609703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_2609703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609703 prefixEnd_2609703 := by exact prefixLift 2609703
  have htrace : WordTrace (prefixWord ++ tailWord_2609703) baseStart_2609703 baseEnd_2609703 := by
    simpa [prefixWord, tailWord_2609703, baseEnd_2609703] using wordTrace_append hprefix tailTrace_2609703
  have hstable : (prefixWord ++ tailWord_2609703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609703).length < 2 ^ (prefixWord ++ tailWord_2609703).sum := by decide
  have hdescent : baseEnd_2609703 < baseStart_2609703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609712 : List Nat := [2, 1, 1, 1, 2, 3, 4, 1, 3, 3, 2]
def baseStart_2609712 : Nat := 118140960795 + 2609712 * 2 ^ 59
def prefixEnd_2609712 : Nat := 4983230072969 + 3 ^ 40 * 2609712 * 2
def baseEnd_2609712 : Nat := 1340036625806398723498159

theorem tailTrace_2609712 : CollatzResearch.WordTrace tailWord_2609712 prefixEnd_2609712 1340036625806398723498159 := by
  unfold tailWord_2609712
  simp only [CollatzResearch.WordTrace]
  refine ⟨47592008160733301085227695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63456010880977734780303593 47592008160733301085227695)
  ·
    refine ⟨71388012241099951627841543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47592008160733301085227695 71388012241099951627841543)
    ·
      refine ⟨107082018361649927441762315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71388012241099951627841543 107082018361649927441762315)
      ·
        refine ⟨160623027542474891162643473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107082018361649927441762315 160623027542474891162643473)
        ·
          refine ⟨120467270656856168371982605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160623027542474891162643473 120467270656856168371982605)
          ·
            refine ⟨45175226496321063139493477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120467270656856168371982605 45175226496321063139493477)
            ·
              refine ⟨8470354968060199338655027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45175226496321063139493477 8470354968060199338655027)
              ·
                refine ⟨12705532452090299007982541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8470354968060199338655027 12705532452090299007982541)
                ·
                  refine ⟨4764574669533862127993453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12705532452090299007982541 4764574669533862127993453)
                  ·
                    refine ⟨1786715501075198297997545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4764574669533862127993453 1786715501075198297997545)
                    ·
                      refine ⟨1340036625806398723498159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1786715501075198297997545 1340036625806398723498159)
                      ·
                        rfl

theorem cell23_2609712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 3, 3, 2].length) (baseStart_2609712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609712 prefixEnd_2609712 := by exact prefixLift 2609712
  have htrace : WordTrace (prefixWord ++ tailWord_2609712) baseStart_2609712 baseEnd_2609712 := by
    simpa [prefixWord, tailWord_2609712, baseEnd_2609712] using wordTrace_append hprefix tailTrace_2609712
  have hstable : (prefixWord ++ tailWord_2609712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609712).length < 2 ^ (prefixWord ++ tailWord_2609712).sum := by decide
  have hdescent : baseEnd_2609712 < baseStart_2609712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609735 : List Nat := [1, 1, 4, 1, 4, 1, 1, 2, 2, 6]
def baseStart_2609735 : Nat := 118140960795 + 2609735 * 2 ^ 59
def prefixEnd_2609735 : Nat := 4983230072969 + 3 ^ 40 * 2609735 * 2
def baseEnd_2609735 : Nat := 446682811953817377836851

theorem tailTrace_2609735 : CollatzResearch.WordTrace tailWord_2609735 prefixEnd_2609735 446682811953817377836851 := by
  unfold tailWord_2609735
  simp only [CollatzResearch.WordTrace]
  refine ⟨95184855200383277098542659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63456570133588851399028439 95184855200383277098542659)
  ·
    refine ⟨142777282800574915647813989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95184855200383277098542659 142777282800574915647813989)
    ·
      refine ⟨26770740525107796683965123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142777282800574915647813989 26770740525107796683965123)
      ·
        refine ⟨40156110787661695025947685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26770740525107796683965123 40156110787661695025947685)
        ·
          refine ⟨7529270772686567817365191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40156110787661695025947685 7529270772686567817365191)
          ·
            refine ⟨11293906159029851726047787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7529270772686567817365191 11293906159029851726047787)
            ·
              refine ⟨16940859238544777589071681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11293906159029851726047787 16940859238544777589071681)
              ·
                refine ⟨12705644428908583191803761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16940859238544777589071681 12705644428908583191803761)
                ·
                  refine ⟨9529233321681437393852821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12705644428908583191803761 9529233321681437393852821)
                  ·
                    refine ⟨446682811953817377836851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9529233321681437393852821 446682811953817377836851)
                    ·
                      rfl

theorem cell23_2609735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_2609735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609735 prefixEnd_2609735 := by exact prefixLift 2609735
  have htrace : WordTrace (prefixWord ++ tailWord_2609735) baseStart_2609735 baseEnd_2609735 := by
    simpa [prefixWord, tailWord_2609735, baseEnd_2609735] using wordTrace_append hprefix tailTrace_2609735
  have hstable : (prefixWord ++ tailWord_2609735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609735).length < 2 ^ (prefixWord ++ tailWord_2609735).sum := by decide
  have hdescent : baseEnd_2609735 < baseStart_2609735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609742 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2]
def baseStart_2609742 : Nat := 118140960795 + 2609742 * 2 ^ 59
def prefixEnd_2609742 : Nat := 4983230072969 + 3 ^ 40 * 2609742 * 2
def baseEnd_2609742 : Nat := 1340052030226033606123021

theorem tailTrace_2609742 : CollatzResearch.WordTrace tailWord_2609742 prefixEnd_2609742 1340052030226033606123021 := by
  unfold tailWord_2609742
  simp only [CollatzResearch.WordTrace]
  refine ⟨11898138813919739661755935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63456740340905278196031653 11898138813919739661755935)
  ·
    refine ⟨17847208220879609492633903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11898138813919739661755935 17847208220879609492633903)
    ·
      refine ⟨26770812331319414238950855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17847208220879609492633903 26770812331319414238950855)
      ·
        refine ⟨40156218496979121358426283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26770812331319414238950855 40156218496979121358426283)
        ·
          refine ⟨60234327745468682037639425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40156218496979121358426283 60234327745468682037639425)
          ·
            refine ⟨45175745809101511528229569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60234327745468682037639425 45175745809101511528229569)
            ·
              refine ⟨33881809356826133646172177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45175745809101511528229569 33881809356826133646172177)
              ·
                refine ⟨25411357017619600234629133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33881809356826133646172177 25411357017619600234629133)
                ·
                  refine ⟨9529258881607350087985925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25411357017619600234629133 9529258881607350087985925)
                  ·
                    refine ⟨1786736040301378141497361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9529258881607350087985925 1786736040301378141497361)
                    ·
                      refine ⟨1340052030226033606123021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1786736040301378141497361 1340052030226033606123021)
                      ·
                        rfl

theorem cell23_2609742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2].length) (baseStart_2609742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609742 prefixEnd_2609742 := by exact prefixLift 2609742
  have htrace : WordTrace (prefixWord ++ tailWord_2609742) baseStart_2609742 baseEnd_2609742 := by
    simpa [prefixWord, tailWord_2609742, baseEnd_2609742] using wordTrace_append hprefix tailTrace_2609742
  have hstable : (prefixWord ++ tailWord_2609742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609742).length < 2 ^ (prefixWord ++ tailWord_2609742).sum := by decide
  have hdescent : baseEnd_2609742 < baseStart_2609742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609759 : List Nat := [1, 1, 2, 3, 1, 1, 1, 7, 2, 2, 2]
def baseStart_2609759 : Nat := 118140960795 + 2609759 * 2 ^ 59
def prefixEnd_2609759 : Nat := 4983230072969 + 3 ^ 40 * 2609759 * 2
def baseEnd_2609759 : Nat := 1340060759397160039610443

theorem tailTrace_2609759 : CollatzResearch.WordTrace tailWord_2609759 prefixEnd_2609759 1340060759397160039610443 := by
  unfold tailWord_2609759
  simp only [CollatzResearch.WordTrace]
  refine ⟨95185730552296329197416331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63457153701530886131610887 95185730552296329197416331)
  ·
    refine ⟨142778595828444493796124497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95185730552296329197416331 142778595828444493796124497)
    ·
      refine ⟨107083946871333370347093373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142778595828444493796124497 107083946871333370347093373)
      ·
        refine ⟨40156480076750013880160015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107083946871333370347093373 40156480076750013880160015)
        ·
          refine ⟨60234720115125020820240023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40156480076750013880160015 60234720115125020820240023)
          ·
            refine ⟨90352080172687531230360035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60234720115125020820240023 90352080172687531230360035)
            ·
              refine ⟨135528120259031296845540053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90352080172687531230360035 135528120259031296845540053)
              ·
                refine ⟨3176440318571046019817345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 135528120259031296845540053 3176440318571046019817345)
                ·
                  refine ⟨2382330238928284514863009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3176440318571046019817345 2382330238928284514863009)
                  ·
                    refine ⟨1786747679196213386147257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2382330238928284514863009 1786747679196213386147257)
                    ·
                      refine ⟨1340060759397160039610443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1786747679196213386147257 1340060759397160039610443)
                      ·
                        rfl

theorem cell23_2609759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 2, 2, 2].length) (baseStart_2609759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609759 prefixEnd_2609759 := by exact prefixLift 2609759
  have htrace : WordTrace (prefixWord ++ tailWord_2609759) baseStart_2609759 baseEnd_2609759 := by
    simpa [prefixWord, tailWord_2609759, baseEnd_2609759] using wordTrace_append hprefix tailTrace_2609759
  have hstable : (prefixWord ++ tailWord_2609759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609759).length < 2 ^ (prefixWord ++ tailWord_2609759).sum := by decide
  have hdescent : baseEnd_2609759 < baseStart_2609759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609775 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 1, 5, 3]
def baseStart_2609775 : Nat := 118140960795 + 2609775 * 2 ^ 59
def prefixEnd_2609775 : Nat := 4983230072969 + 3 ^ 40 * 2609775 * 2
def baseEnd_2609775 : Nat := 1340068975087631977010369

theorem tailTrace_2609775 : CollatzResearch.WordTrace tailWord_2609775 prefixEnd_2609775 1340068975087631977010369 := by
  unfold tailWord_2609775
  simp only [CollatzResearch.WordTrace]
  refine ⟨95186314120238363929998779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63457542746825575953332519 95186314120238363929998779)
  ·
    refine ⟨142779471180357545894998169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95186314120238363929998779 142779471180357545894998169)
    ·
      refine ⟨107084603385268159421248627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142779471180357545894998169 107084603385268159421248627)
      ·
        refine ⟨160626905077902239131872941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107084603385268159421248627 160626905077902239131872941)
        ·
          refine ⟨60235089404213339674452353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160626905077902239131872941 60235089404213339674452353)
          ·
            refine ⟨45176317053160004755839265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60235089404213339674452353 45176317053160004755839265)
            ·
              refine ⟨33882237789870003566879449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45176317053160004755839265 33882237789870003566879449)
              ·
                refine ⟨25411678342402502675159587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33882237789870003566879449 25411678342402502675159587)
                ·
                  refine ⟨38117517513603754012739381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25411678342402502675159587 38117517513603754012739381)
                  ·
                    refine ⟨3573517266900351938694317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38117517513603754012739381 3573517266900351938694317)
                    ·
                      refine ⟨1340068975087631977010369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3573517266900351938694317 1340068975087631977010369)
                      ·
                        rfl

theorem cell23_2609775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 5, 3].length) (baseStart_2609775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609775 prefixEnd_2609775 := by exact prefixLift 2609775
  have htrace : WordTrace (prefixWord ++ tailWord_2609775) baseStart_2609775 baseEnd_2609775 := by
    simpa [prefixWord, tailWord_2609775, baseEnd_2609775] using wordTrace_append hprefix tailTrace_2609775
  have hstable : (prefixWord ++ tailWord_2609775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609775).length < 2 ^ (prefixWord ++ tailWord_2609775).sum := by decide
  have hdescent : baseEnd_2609775 < baseStart_2609775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609795 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 4, 5]
def baseStart_2609795 : Nat := 118140960795 + 2609795 * 2 ^ 59
def prefixEnd_2609795 : Nat := 4983230072969 + 3 ^ 40 * 2609795 * 2
def baseEnd_2609795 : Nat := 446693081566907299586759

theorem tailTrace_2609795 : CollatzResearch.WordTrace tailWord_2609795 prefixEnd_2609795 446693081566907299586759 := by
  unfold tailWord_2609795
  simp only [CollatzResearch.WordTrace]
  refine ⟨95187043580165907345726839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63458029053443938230484559 95187043580165907345726839)
  ·
    refine ⟨142780565370248861018590259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95187043580165907345726839 142780565370248861018590259)
    ·
      refine ⟨214170848055373291527885389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142780565370248861018590259 214170848055373291527885389)
      ·
        refine ⟨80314068020764984322957021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214170848055373291527885389 80314068020764984322957021)
        ·
          refine ⟨30117775507786869121108883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80314068020764984322957021 30117775507786869121108883)
          ·
            refine ⟨45176663261680303681663325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30117775507786869121108883 45176663261680303681663325)
            ·
              refine ⟨16941248723130113880623747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45176663261680303681663325 16941248723130113880623747)
              ·
                refine ⟨25411873084695170820935621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16941248723130113880623747 25411873084695170820935621)
                ·
                  refine ⟨4764726203380344528925429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25411873084695170820935621 4764726203380344528925429)
                  ·
                    refine ⟨446693081566907299586759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4764726203380344528925429 446693081566907299586759)
                    ·
                      rfl

theorem cell23_2609795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 5].length) (baseStart_2609795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609795 prefixEnd_2609795 := by exact prefixLift 2609795
  have htrace : WordTrace (prefixWord ++ tailWord_2609795) baseStart_2609795 baseEnd_2609795 := by
    simpa [prefixWord, tailWord_2609795, baseEnd_2609795] using wordTrace_append hprefix tailTrace_2609795
  have hstable : (prefixWord ++ tailWord_2609795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609795).length < 2 ^ (prefixWord ++ tailWord_2609795).sum := by decide
  have hdescent : baseEnd_2609795 < baseStart_2609795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609799 : List Nat := [1, 1, 4, 2, 1, 2, 5, 2, 5]
def baseStart_2609799 : Nat := 118140960795 + 2609799 * 2 ^ 59
def prefixEnd_2609799 : Nat := 4983230072969 + 3 ^ 40 * 2609799 * 2
def baseEnd_2609799 : Nat := 148897922069259987012251

theorem tailTrace_2609799 : CollatzResearch.WordTrace tailWord_2609799 prefixEnd_2609799 148897922069259987012251 := by
  unfold tailWord_2609799
  simp only [CollatzResearch.WordTrace]
  refine ⟨95187189472151416028872451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63458126314767610685914967 95187189472151416028872451)
  ·
    refine ⟨142780784208227124043308677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95187189472151416028872451 142780784208227124043308677)
    ·
      refine ⟨26771397039042585758120377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142780784208227124043308677 26771397039042585758120377)
      ·
        refine ⟨20078547779281939318590283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26771397039042585758120377 20078547779281939318590283)
        ·
          refine ⟨30117821668922908977885425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20078547779281939318590283 30117821668922908977885425)
          ·
            refine ⟨22588366251692181733414069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30117821668922908977885425 22588366251692181733414069)
            ·
              refine ⟨2117659336096142037507569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22588366251692181733414069 2117659336096142037507569)
              ·
                refine ⟨1588244502072106528130677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2117659336096142037507569 1588244502072106528130677)
                ·
                  refine ⟨148897922069259987012251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1588244502072106528130677 148897922069259987012251)
                  ·
                    rfl

theorem cell23_2609799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 2, 5].length) (baseStart_2609799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609799 prefixEnd_2609799 := by exact prefixLift 2609799
  have htrace : WordTrace (prefixWord ++ tailWord_2609799) baseStart_2609799 baseEnd_2609799 := by
    simpa [prefixWord, tailWord_2609799, baseEnd_2609799] using wordTrace_append hprefix tailTrace_2609799
  have hstable : (prefixWord ++ tailWord_2609799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609799).length < 2 ^ (prefixWord ++ tailWord_2609799).sum := by decide
  have hdescent : baseEnd_2609799 < baseStart_2609799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609810 : List Nat := [3, 2, 3, 1, 2, 3, 2, 1, 2, 2, 2]
def baseStart_2609810 : Nat := 118140960795 + 2609810 * 2 ^ 59
def prefixEnd_2609810 : Nat := 4983230072969 + 3 ^ 40 * 2609810 * 2
def baseEnd_2609810 : Nat := 1340086946910539340072709

theorem tailTrace_2609810 : CollatzResearch.WordTrace tailWord_2609810 prefixEnd_2609810 1340086946910539340072709 := by
  unfold tailWord_2609810
  simp only [CollatzResearch.WordTrace]
  refine ⟨23796897668777891226880721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63458393783407709938348589 23796897668777891226880721)
  ·
    refine ⟨17847673251583418420160541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23796897668777891226880721 17847673251583418420160541)
    ·
      refine ⟨6692877469343781907560203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17847673251583418420160541 6692877469343781907560203)
      ·
        refine ⟨10039316204015672861340305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6692877469343781907560203 10039316204015672861340305)
        ·
          refine ⟨7529487153011754646005229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10039316204015672861340305 7529487153011754646005229)
          ·
            refine ⟨2823557682379407992251961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7529487153011754646005229 2823557682379407992251961)
            ·
              refine ⟨2117668261784555994188971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2823557682379407992251961 2117668261784555994188971)
              ·
                refine ⟨3176502392676833991283457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2117668261784555994188971 3176502392676833991283457)
                ·
                  refine ⟨2382376794507625493462593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3176502392676833991283457 2382376794507625493462593)
                  ·
                    refine ⟨1786782595880719120096945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2382376794507625493462593 1786782595880719120096945)
                    ·
                      refine ⟨1340086946910539340072709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1786782595880719120096945 1340086946910539340072709)
                      ·
                        rfl

theorem cell23_2609810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_2609810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609810 prefixEnd_2609810 := by exact prefixLift 2609810
  have htrace : WordTrace (prefixWord ++ tailWord_2609810) baseStart_2609810 baseEnd_2609810 := by
    simpa [prefixWord, tailWord_2609810, baseEnd_2609810] using wordTrace_append hprefix tailTrace_2609810
  have hstable : (prefixWord ++ tailWord_2609810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609810).length < 2 ^ (prefixWord ++ tailWord_2609810).sum := by decide
  have hdescent : baseEnd_2609810 < baseStart_2609810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609822 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_2609822 : Nat := 118140960795 + 2609822 * 2 ^ 59
def prefixEnd_2609822 : Nat := 4983230072969 + 3 ^ 40 * 2609822 * 2
def baseEnd_2609822 : Nat := 1340093108678393293122653

theorem tailTrace_2609822 : CollatzResearch.WordTrace tailWord_2609822 prefixEnd_2609822 1340093108678393293122653 := by
  unfold tailWord_2609822
  simp only [CollatzResearch.WordTrace]
  refine ⟨11898503543883511369619965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63458685567378727304639813 11898503543883511369619965)
  ·
    refine ⟨4461938828956316763607487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11898503543883511369619965 4461938828956316763607487)
    ·
      refine ⟨6692908243434475145411231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4461938828956316763607487 6692908243434475145411231)
      ·
        refine ⟨10039362365151712718116847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6692908243434475145411231 10039362365151712718116847)
        ·
          refine ⟨15059043547727569077175271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10039362365151712718116847 15059043547727569077175271)
          ·
            refine ⟨22588565321591353615762907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15059043547727569077175271 22588565321591353615762907)
            ·
              refine ⟨33882847982387030423644361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22588565321591353615762907 33882847982387030423644361)
              ·
                refine ⟨25412135986790272817733271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33882847982387030423644361 25412135986790272817733271)
                ·
                  refine ⟨38118203980185409226599907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25412135986790272817733271 38118203980185409226599907)
                  ·
                    refine ⟨57177305970278113839899861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38118203980185409226599907 57177305970278113839899861)
                    ·
                      refine ⟨1340093108678393293122653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 57177305970278113839899861 1340093108678393293122653)
                      ·
                        rfl

theorem cell23_2609822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_2609822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609822 prefixEnd_2609822 := by exact prefixLift 2609822
  have htrace : WordTrace (prefixWord ++ tailWord_2609822) baseStart_2609822 baseEnd_2609822 := by
    simpa [prefixWord, tailWord_2609822, baseEnd_2609822] using wordTrace_append hprefix tailTrace_2609822
  have hstable : (prefixWord ++ tailWord_2609822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609822).length < 2 ^ (prefixWord ++ tailWord_2609822).sum := by decide
  have hdescent : baseEnd_2609822 < baseStart_2609822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609876 : List Nat := [2, 4, 1, 3, 2, 1, 1, 2, 3, 4]
def baseStart_2609876 : Nat := 118140960795 + 2609876 * 2 ^ 59
def prefixEnd_2609876 : Nat := 4983230072969 + 3 ^ 40 * 2609876 * 2
def baseEnd_2609876 : Nat := 446706945544578693949135

theorem tailTrace_2609876 : CollatzResearch.WordTrace tailWord_2609876 prefixEnd_2609876 446706945544578693949135 := by
  unfold tailWord_2609876
  simp only [CollatzResearch.WordTrace]
  refine ⟨47594998946436229089712741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63459998595248305452950321 47594998946436229089712741)
  ·
    refine ⟨8924062302456792954321139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47594998946436229089712741 8924062302456792954321139)
    ·
      refine ⟨13386093453685189431481709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8924062302456792954321139 13386093453685189431481709)
      ·
        refine ⟨5019785045131946036805641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13386093453685189431481709 5019785045131946036805641)
        ·
          refine ⟨3764838783848959527604231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5019785045131946036805641 3764838783848959527604231)
          ·
            refine ⟨5647258175773439291406347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3764838783848959527604231 5647258175773439291406347)
            ·
              refine ⟨8470887263660158937109521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5647258175773439291406347 8470887263660158937109521)
              ·
                refine ⟨6353165447745119202832141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8470887263660158937109521 6353165447745119202832141)
                ·
                  refine ⟨2382437042904419701062053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6353165447745119202832141 2382437042904419701062053)
                  ·
                    refine ⟨446706945544578693949135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2382437042904419701062053 446706945544578693949135)
                    ·
                      rfl

theorem cell23_2609876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_2609876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609876 prefixEnd_2609876 := by exact prefixLift 2609876
  have htrace : WordTrace (prefixWord ++ tailWord_2609876) baseStart_2609876 baseEnd_2609876 := by
    simpa [prefixWord, tailWord_2609876, baseEnd_2609876] using wordTrace_append hprefix tailTrace_2609876
  have hstable : (prefixWord ++ tailWord_2609876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609876).length < 2 ^ (prefixWord ++ tailWord_2609876).sum := by decide
  have hdescent : baseEnd_2609876 < baseStart_2609876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609916 : List Nat := [2, 2, 2, 1, 3, 3, 2, 1, 3, 1, 3]
def baseStart_2609916 : Nat := 118140960795 + 2609916 * 2 ^ 59
def prefixEnd_2609916 : Nat := 4983230072969 + 3 ^ 40 * 2609916 * 2
def baseEnd_2609916 : Nat := 1340141375859915925347221

theorem tailTrace_2609916 : CollatzResearch.WordTrace tailWord_2609916 prefixEnd_2609916 1340141375859915925347221 := by
  unfold tailWord_2609916
  simp only [CollatzResearch.WordTrace]
  refine ⟨47595728406363772505440801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63460971208485030007254401 47595728406363772505440801)
  ·
    refine ⟨35696796304772829379080601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47595728406363772505440801 35696796304772829379080601)
    ·
      refine ⟨26772597228579622034310451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35696796304772829379080601 26772597228579622034310451)
      ·
        refine ⟨40158895842869433051465677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26772597228579622034310451 40158895842869433051465677)
        ·
          refine ⟨15059585941076037394299629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40158895842869433051465677 15059585941076037394299629)
          ·
            refine ⟨5647344727903514022862361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15059585941076037394299629 5647344727903514022862361)
            ·
              refine ⟨4235508545927635517146771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5647344727903514022862361 4235508545927635517146771)
              ·
                refine ⟨6353262818891453275720157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4235508545927635517146771 6353262818891453275720157)
                ·
                  refine ⟨2382473557084294978395059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6353262818891453275720157 2382473557084294978395059)
                  ·
                    refine ⟨3573710335626442467592589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2382473557084294978395059 3573710335626442467592589)
                    ·
                      refine ⟨1340141375859915925347221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3573710335626442467592589 1340141375859915925347221)
                      ·
                        rfl

theorem cell23_2609916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 3, 1, 3].length) (baseStart_2609916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609916 prefixEnd_2609916 := by exact prefixLift 2609916
  have htrace : WordTrace (prefixWord ++ tailWord_2609916) baseStart_2609916 baseEnd_2609916 := by
    simpa [prefixWord, tailWord_2609916, baseEnd_2609916] using wordTrace_append hprefix tailTrace_2609916
  have hstable : (prefixWord ++ tailWord_2609916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609916).length < 2 ^ (prefixWord ++ tailWord_2609916).sum := by decide
  have hdescent : baseEnd_2609916 < baseStart_2609916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609939 : List Nat := [1, 1, 1, 2, 1, 3, 6, 2, 1, 1, 4]
def baseStart_2609939 : Nat := 118140960795 + 2609939 * 2 ^ 59
def prefixEnd_2609939 : Nat := 4983230072969 + 3 ^ 40 * 2609939 * 2
def baseEnd_2609939 : Nat := 1340153185914969335359615

theorem tailTrace_2609939 : CollatzResearch.WordTrace tailWord_2609939 prefixEnd_2609939 1340153185914969335359615 := by
  unfold tailWord_2609939
  simp only [CollatzResearch.WordTrace]
  refine ⟨95192295691644219938968871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63461530461096146625979247 95192295691644219938968871)
  ·
    refine ⟨142788443537466329908453307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95192295691644219938968871 142788443537466329908453307)
    ·
      refine ⟨214182665306199494862679961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142788443537466329908453307 214182665306199494862679961)
      ·
        refine ⟨160636998979649621147009971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214182665306199494862679961 160636998979649621147009971)
        ·
          refine ⟨240955498469474431720514957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160636998979649621147009971 240955498469474431720514957)
          ·
            refine ⟨90358311926052911895193109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 240955498469474431720514957 90358311926052911895193109)
            ·
              refine ⟨4235545871533730245087177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90358311926052911895193109 4235545871533730245087177)
              ·
                refine ⟨3176659403650297683815383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4235545871533730245087177 3176659403650297683815383)
                ·
                  refine ⟨4764989105475446525723075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3176659403650297683815383 4764989105475446525723075)
                  ·
                    refine ⟨7147483658213169788584613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4764989105475446525723075 7147483658213169788584613)
                    ·
                      refine ⟨1340153185914969335359615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7147483658213169788584613 1340153185914969335359615)
                      ·
                        rfl

theorem cell23_2609939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 1, 4].length) (baseStart_2609939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609939 prefixEnd_2609939 := by exact prefixLift 2609939
  have htrace : WordTrace (prefixWord ++ tailWord_2609939) baseStart_2609939 baseEnd_2609939 := by
    simpa [prefixWord, tailWord_2609939, baseEnd_2609939] using wordTrace_append hprefix tailTrace_2609939
  have hstable : (prefixWord ++ tailWord_2609939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609939).length < 2 ^ (prefixWord ++ tailWord_2609939).sum := by decide
  have hdescent : baseEnd_2609939 < baseStart_2609939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609966 : List Nat := [4, 1, 3, 2, 1, 1, 2, 1, 4, 4]
def baseStart_2609966 : Nat := 118140960795 + 2609966 * 2 ^ 59
def prefixEnd_2609966 : Nat := 4983230072969 + 3 ^ 40 * 2609966 * 2
def baseEnd_2609966 : Nat := 446722349964213576573997

theorem tailTrace_2609966 : CollatzResearch.WordTrace tailWord_2609966 prefixEnd_2609966 446722349964213576573997 := by
  unfold tailWord_2609966
  simp only [CollatzResearch.WordTrace]
  refine ⟨11899160057818300443775219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63462186975030935700134501 11899160057818300443775219)
  ·
    refine ⟨17848740086727450665662829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11899160057818300443775219 17848740086727450665662829)
    ·
      refine ⟨6693277532522793999623561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17848740086727450665662829 6693277532522793999623561)
      ·
        refine ⟨5019958149392095499717671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6693277532522793999623561 5019958149392095499717671)
        ·
          refine ⟨7529937224088143249576507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5019958149392095499717671 7529937224088143249576507)
          ·
            refine ⟨11294905836132214874364761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7529937224088143249576507 11294905836132214874364761)
            ·
              refine ⟨8471179377099161155773571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11294905836132214874364761 8471179377099161155773571)
              ·
                refine ⟨12706769065648741733660357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8471179377099161155773571 12706769065648741733660357)
                ·
                  refine ⟨2382519199809139075061317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12706769065648741733660357 2382519199809139075061317)
                  ·
                    refine ⟨446722349964213576573997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2382519199809139075061317 446722349964213576573997)
                    ·
                      rfl

theorem cell23_2609966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_2609966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609966 prefixEnd_2609966 := by exact prefixLift 2609966
  have htrace : WordTrace (prefixWord ++ tailWord_2609966) baseStart_2609966 baseEnd_2609966 := by
    simpa [prefixWord, tailWord_2609966, baseEnd_2609966] using wordTrace_append hprefix tailTrace_2609966
  have hstable : (prefixWord ++ tailWord_2609966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609966).length < 2 ^ (prefixWord ++ tailWord_2609966).sum := by decide
  have hdescent : baseEnd_2609966 < baseStart_2609966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609973 : List Nat := [1, 3, 3, 1, 3, 1, 3, 1, 3, 2, 2]
def baseStart_2609973 : Nat := 118140960795 + 2609973 * 2 ^ 59
def prefixEnd_2609973 : Nat := 4983230072969 + 3 ^ 40 * 2609973 * 2
def baseEnd_2609973 : Nat := 1340170644257222202334459

theorem tailTrace_2609973 : CollatzResearch.WordTrace tailWord_2609973 prefixEnd_2609973 1340170644257222202334459 := by
  unfold tailWord_2609973
  simp only [CollatzResearch.WordTrace]
  refine ⟨95193535773521043745706573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63462357182347362497137715 95193535773521043745706573)
  ·
    refine ⟨35697575915070391404639965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95193535773521043745706573 35697575915070391404639965)
    ·
      refine ⟨13386590968151396776739987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35697575915070391404639965 13386590968151396776739987)
      ·
        refine ⟨20079886452227095165109981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13386590968151396776739987 20079886452227095165109981)
        ·
          refine ⟨7529957419585160686916243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20079886452227095165109981 7529957419585160686916243)
          ·
            refine ⟨11294936129377741030374365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7529957419585160686916243 11294936129377741030374365)
            ·
              refine ⟨4235601048516652886390387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11294936129377741030374365 4235601048516652886390387)
              ·
                refine ⟨6353401572774979329585581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4235601048516652886390387 6353401572774979329585581)
                ·
                  refine ⟨2382525589790617248594593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6353401572774979329585581 2382525589790617248594593)
                  ·
                    refine ⟨1786894192342962936445945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2382525589790617248594593 1786894192342962936445945)
                    ·
                      refine ⟨1340170644257222202334459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1786894192342962936445945 1340170644257222202334459)
                      ·
                        rfl

theorem cell23_2609973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_2609973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609973 prefixEnd_2609973 := by exact prefixLift 2609973
  have htrace : WordTrace (prefixWord ++ tailWord_2609973) baseStart_2609973 baseEnd_2609973 := by
    simpa [prefixWord, tailWord_2609973, baseEnd_2609973] using wordTrace_append hprefix tailTrace_2609973
  have hstable : (prefixWord ++ tailWord_2609973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609973).length < 2 ^ (prefixWord ++ tailWord_2609973).sum := by decide
  have hdescent : baseEnd_2609973 < baseStart_2609973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609983 : List Nat := [1, 1, 2, 2, 5, 3, 2, 1, 2, 4]
def baseStart_2609983 : Nat := 118140960795 + 2609983 * 2 ^ 59
def prefixEnd_2609983 : Nat := 4983230072969 + 3 ^ 40 * 2609983 * 2
def baseEnd_2609983 : Nat := 446725259687922387736471

theorem tailTrace_2609983 : CollatzResearch.WordTrace tailWord_2609983 prefixEnd_2609983 446725259687922387736471 := by
  unfold tailWord_2609983
  simp only [CollatzResearch.WordTrace]
  refine ⟨95193900503484815453570603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63462600335656543635713735 95193900503484815453570603)
  ·
    refine ⟨142790850755227223180355905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95193900503484815453570603 142790850755227223180355905)
    ·
      refine ⟨107093138066420417385266929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142790850755227223180355905 107093138066420417385266929)
      ·
        refine ⟨80319853549815313038950197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107093138066420417385266929 80319853549815313038950197)
        ·
          refine ⟨7529986270295185597401581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80319853549815313038950197 7529986270295185597401581)
          ·
            refine ⟨2823744851360694599025593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7529986270295185597401581 2823744851360694599025593)
            ·
              refine ⟨2117808638520520949269195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2823744851360694599025593 2117808638520520949269195)
              ·
                refine ⟨3176712957780781423903793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2117808638520520949269195 3176712957780781423903793)
                ·
                  refine ⟨2382534718335586067927845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3176712957780781423903793 2382534718335586067927845)
                  ·
                    refine ⟨446725259687922387736471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2382534718335586067927845 446725259687922387736471)
                    ·
                      rfl

theorem cell23_2609983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 1, 2, 4].length) (baseStart_2609983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609983 prefixEnd_2609983 := by exact prefixLift 2609983
  have htrace : WordTrace (prefixWord ++ tailWord_2609983) baseStart_2609983 baseEnd_2609983 := by
    simpa [prefixWord, tailWord_2609983, baseEnd_2609983] using wordTrace_append hprefix tailTrace_2609983
  have hstable : (prefixWord ++ tailWord_2609983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609983).length < 2 ^ (prefixWord ++ tailWord_2609983).sum := by decide
  have hdescent : baseEnd_2609983 < baseStart_2609983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609989 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 6, 1, 3]
def baseStart_2609989 : Nat := 118140960795 + 2609989 * 2 ^ 59
def prefixEnd_2609989 : Nat := 4983230072969 + 3 ^ 40 * 2609989 * 2
def baseEnd_2609989 : Nat := 1340178859947694139734385

theorem tailTrace_2609989 : CollatzResearch.WordTrace tailWord_2609989 prefixEnd_2609989 1340178859947694139734385 := by
  unfold tailWord_2609989
  simp only [CollatzResearch.WordTrace]
  refine ⟨95194119341463078478289021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63462746227642052318859347 95194119341463078478289021)
  ·
    refine ⟨35697794753048654429358383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95194119341463078478289021 35697794753048654429358383)
    ·
      refine ⟨53546692129572981644037575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35697794753048654429358383 53546692129572981644037575)
      ·
        refine ⟨80320038194359472466056363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53546692129572981644037575 80320038194359472466056363)
        ·
          refine ⟨120480057291539208699084545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80320038194359472466056363 120480057291539208699084545)
          ·
            refine ⟨90360042968654406524313409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120480057291539208699084545 90360042968654406524313409)
            ·
              refine ⟨67770032226490804893235057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90360042968654406524313409 67770032226490804893235057)
              ·
                refine ⟨50827524169868103669926293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67770032226490804893235057 50827524169868103669926293)
                ·
                  refine ⟨2382540195462567359527795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50827524169868103669926293 2382540195462567359527795)
                  ·
                    refine ⟨3573810293193851039291693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2382540195462567359527795 3573810293193851039291693)
                    ·
                      refine ⟨1340178859947694139734385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3573810293193851039291693 1340178859947694139734385)
                      ·
                        rfl

theorem cell23_2609989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 6, 1, 3].length) (baseStart_2609989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2609989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2609989 prefixEnd_2609989 := by exact prefixLift 2609989
  have htrace : WordTrace (prefixWord ++ tailWord_2609989) baseStart_2609989 baseEnd_2609989 := by
    simpa [prefixWord, tailWord_2609989, baseEnd_2609989] using wordTrace_append hprefix tailTrace_2609989
  have hstable : (prefixWord ++ tailWord_2609989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609989).length < 2 ^ (prefixWord ++ tailWord_2609989).sum := by decide
  have hdescent : baseEnd_2609989 < baseStart_2609989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610023 : List Nat := [1, 1, 5, 1, 2, 3, 2, 2, 2, 1, 3]
def baseStart_2610023 : Nat := 118140960795 + 2610023 * 2 ^ 59
def prefixEnd_2610023 : Nat := 4983230072969 + 3 ^ 40 * 2610023 * 2
def baseEnd_2610023 : Nat := 1340196318289947006709229

theorem tailTrace_2610023 : CollatzResearch.WordTrace tailWord_2610023 prefixEnd_2610023 1340196318289947006709229 := by
  unfold tailWord_2610023
  simp only [CollatzResearch.WordTrace]
  refine ⟨95195359423339902285026723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63463572948893268190017815 95195359423339902285026723)
  ·
    refine ⟨142793039135009853427540085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95195359423339902285026723 142793039135009853427540085)
    ·
      refine ⟨13386847418907173758831883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 142793039135009853427540085 13386847418907173758831883)
      ·
        refine ⟨20080271128360760638247825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13386847418907173758831883 20080271128360760638247825)
        ·
          refine ⟨15060203346270570478685869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20080271128360760638247825 15060203346270570478685869)
          ·
            refine ⟨5647576254851463929507201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15060203346270570478685869 5647576254851463929507201)
            ·
              refine ⟨4235682191138597947130401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5647576254851463929507201 4235682191138597947130401)
              ·
                refine ⟨3176761643353948460347801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4235682191138597947130401 3176761643353948460347801)
                ·
                  refine ⟨2382571232515461345260851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3176761643353948460347801 2382571232515461345260851)
                  ·
                    refine ⟨3573856848773192017891277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2382571232515461345260851 3573856848773192017891277)
                    ·
                      refine ⟨1340196318289947006709229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3573856848773192017891277 1340196318289947006709229)
                      ·
                        rfl

theorem cell23_2610023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_2610023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610023 prefixEnd_2610023 := by exact prefixLift 2610023
  have htrace : WordTrace (prefixWord ++ tailWord_2610023) baseStart_2610023 baseEnd_2610023 := by
    simpa [prefixWord, tailWord_2610023, baseEnd_2610023] using wordTrace_append hprefix tailTrace_2610023
  have hstable : (prefixWord ++ tailWord_2610023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610023).length < 2 ^ (prefixWord ++ tailWord_2610023).sum := by decide
  have hdescent : baseEnd_2610023 < baseStart_2610023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610032 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 5]
def baseStart_2610032 : Nat := 118140960795 + 2610032 * 2 ^ 59
def prefixEnd_2610032 : Nat := 4983230072969 + 3 ^ 40 * 2610032 * 2
def baseEnd_2610032 : Nat := 1340200939615837471496687

theorem tailTrace_2610032 : CollatzResearch.WordTrace tailWord_2610032 prefixEnd_2610032 1340200939615837471496687 := by
  unfold tailWord_2610032
  simp only [CollatzResearch.WordTrace]
  refine ⟨47597843840153648411052175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63463791786871531214736233 47597843840153648411052175)
  ·
    refine ⟨71396765760230472616578263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47597843840153648411052175 71396765760230472616578263)
    ·
      refine ⟨107095148640345708924867395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71396765760230472616578263 107095148640345708924867395)
      ·
        refine ⟨160642722960518563387301093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107095148640345708924867395 160642722960518563387301093)
        ·
          refine ⟨30120510555097230635118955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 160642722960518563387301093 30120510555097230635118955)
          ·
            refine ⟨45180765832645845952678433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30120510555097230635118955 45180765832645845952678433)
            ·
              refine ⟨33885574374484384464508825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45180765832645845952678433 33885574374484384464508825)
              ·
                refine ⟨25414180780863288348381619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33885574374484384464508825 25414180780863288348381619)
                ·
                  refine ⟨38121271171294932522572429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25414180780863288348381619 38121271171294932522572429)
                  ·
                    refine ⟨14295476689235599695964661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38121271171294932522572429 14295476689235599695964661)
                    ·
                      refine ⟨1340200939615837471496687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14295476689235599695964661 1340200939615837471496687)
                      ·
                        rfl

theorem cell23_2610032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 5].length) (baseStart_2610032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610032 prefixEnd_2610032 := by exact prefixLift 2610032
  have htrace : WordTrace (prefixWord ++ tailWord_2610032) baseStart_2610032 baseEnd_2610032 := by
    simpa [prefixWord, tailWord_2610032, baseEnd_2610032] using wordTrace_append hprefix tailTrace_2610032
  have hstable : (prefixWord ++ tailWord_2610032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610032).length < 2 ^ (prefixWord ++ tailWord_2610032).sum := by decide
  have hdescent : baseEnd_2610032 < baseStart_2610032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610097 : List Nat := [1, 2, 2, 4, 3, 1, 3, 1, 2, 2, 2]
def baseStart_2610097 : Nat := 118140960795 + 2610097 * 2 ^ 59
def prefixEnd_2610097 : Nat := 4983230072969 + 3 ^ 40 * 2610097 * 2
def baseEnd_2610097 : Nat := 1340234315858379717183889

theorem tailTrace_2610097 : CollatzResearch.WordTrace tailWord_2610097 prefixEnd_2610097 1340234315858379717183889 := by
  unfold tailWord_2610097
  simp only [CollatzResearch.WordTrace]
  refine ⟨95198058425071812923220545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63465372283381208615480363 95198058425071812923220545)
  ·
    refine ⟨71398543818803859692415409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95198058425071812923220545 71398543818803859692415409)
    ·
      refine ⟨53548907864102894769311557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71398543818803859692415409 53548907864102894769311557)
      ·
        refine ⟨10040420224519292769245917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53548907864102894769311557 10040420224519292769245917)
        ·
          refine ⟨3765157584194734788467219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10040420224519292769245917 3765157584194734788467219)
          ·
            refine ⟨5647736376292102182700829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3765157584194734788467219 5647736376292102182700829)
            ·
              refine ⟨2117901141109538318512811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5647736376292102182700829 2117901141109538318512811)
              ·
                refine ⟨3176851711664307477769217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2117901141109538318512811 3176851711664307477769217)
                ·
                  refine ⟨2382638783748230608326913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3176851711664307477769217 2382638783748230608326913)
                  ·
                    refine ⟨1786979087811172956245185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2382638783748230608326913 1786979087811172956245185)
                    ·
                      refine ⟨1340234315858379717183889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1786979087811172956245185 1340234315858379717183889)
                      ·
                        rfl

theorem cell23_2610097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_2610097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610097 prefixEnd_2610097 := by exact prefixLift 2610097
  have htrace : WordTrace (prefixWord ++ tailWord_2610097) baseStart_2610097 baseEnd_2610097 := by
    simpa [prefixWord, tailWord_2610097, baseEnd_2610097] using wordTrace_append hprefix tailTrace_2610097
  have hstable : (prefixWord ++ tailWord_2610097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610097).length < 2 ^ (prefixWord ++ tailWord_2610097).sum := by decide
  have hdescent : baseEnd_2610097 < baseStart_2610097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610119 : List Nat := [1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 4]
def baseStart_2610119 : Nat := 118140960795 + 2610119 * 2 ^ 59
def prefixEnd_2610119 : Nat := 4983230072969 + 3 ^ 40 * 2610119 * 2
def baseEnd_2610119 : Nat := 1340245612432778631108787

theorem tailTrace_2610119 : CollatzResearch.WordTrace tailWord_2610119 prefixEnd_2610119 1340245612432778631108787 := by
  unfold tailWord_2610119
  simp only [CollatzResearch.WordTrace]
  refine ⟨95198860830992110680521411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63465907220661407120347607 95198860830992110680521411)
  ·
    refine ⟨142798291246488166020782117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95198860830992110680521411 142798291246488166020782117)
    ·
      refine ⟨26774679608716531128896647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142798291246488166020782117 26774679608716531128896647)
      ·
        refine ⟨40162019413074796693344971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26774679608716531128896647 40162019413074796693344971)
        ·
          refine ⟨60243029119612195040017457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40162019413074796693344971 60243029119612195040017457)
          ·
            refine ⟨45182271839709146280013093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60243029119612195040017457 45182271839709146280013093)
            ·
              refine ⟨8471675969945464927502455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45182271839709146280013093 8471675969945464927502455)
              ·
                refine ⟨12707513954918197391253683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8471675969945464927502455 12707513954918197391253683)
                ·
                  refine ⟨19061270932377296086880525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12707513954918197391253683 19061270932377296086880525)
                  ·
                    refine ⟨7147976599641486032580197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19061270932377296086880525 7147976599641486032580197)
                    ·
                      refine ⟨1340245612432778631108787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7147976599641486032580197 1340245612432778631108787)
                      ·
                        rfl

theorem cell23_2610119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_2610119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610119 prefixEnd_2610119 := by exact prefixLift 2610119
  have htrace : WordTrace (prefixWord ++ tailWord_2610119) baseStart_2610119 baseEnd_2610119 := by
    simpa [prefixWord, tailWord_2610119, baseEnd_2610119] using wordTrace_append hprefix tailTrace_2610119
  have hstable : (prefixWord ++ tailWord_2610119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610119).length < 2 ^ (prefixWord ++ tailWord_2610119).sum := by decide
  have hdescent : baseEnd_2610119 < baseStart_2610119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610120 : List Nat := [2, 1, 3, 1, 6, 1, 1, 3, 5]
def baseStart_2610120 : Nat := 118140960795 + 2610120 * 2 ^ 59
def prefixEnd_2610120 : Nat := 4983230072969 + 3 ^ 40 * 2610120 * 2
def baseEnd_2610120 : Nat := 148916236212603680799587

theorem tailTrace_2610120 : CollatzResearch.WordTrace tailWord_2610120 prefixEnd_2610120 148916236212603680799587 := by
  unfold tailWord_2610120
  simp only [CollatzResearch.WordTrace]
  refine ⟨47599448651994243925653907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63465931535992325234205209 47599448651994243925653907)
  ·
    refine ⟨71399172977991365888480861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47599448651994243925653907 71399172977991365888480861)
    ·
      refine ⟨26774689866746762208180323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71399172977991365888480861 26774689866746762208180323)
      ·
        refine ⟨40162034800120143312270485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26774689866746762208180323 40162034800120143312270485)
        ·
          refine ⟨1882595381255631717762679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40162034800120143312270485 1882595381255631717762679)
          ·
            refine ⟨2823893071883447576644019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1882595381255631717762679 2823893071883447576644019)
            ·
              refine ⟨4235839607825171364966029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2823893071883447576644019 4235839607825171364966029)
              ·
                refine ⟨1588439852934439261862261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4235839607825171364966029 1588439852934439261862261)
                ·
                  refine ⟨148916236212603680799587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1588439852934439261862261 148916236212603680799587)
                  ·
                    rfl

theorem cell23_2610120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 3, 5].length) (baseStart_2610120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610120 prefixEnd_2610120 := by exact prefixLift 2610120
  have htrace : WordTrace (prefixWord ++ tailWord_2610120) baseStart_2610120 baseEnd_2610120 := by
    simpa [prefixWord, tailWord_2610120, baseEnd_2610120] using wordTrace_append hprefix tailTrace_2610120
  have hstable : (prefixWord ++ tailWord_2610120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610120).length < 2 ^ (prefixWord ++ tailWord_2610120).sum := by decide
  have hdescent : baseEnd_2610120 < baseStart_2610120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610136 : List Nat := [2, 1, 2, 2, 2, 4, 1, 2, 2, 1, 4]
def baseStart_2610136 : Nat := 118140960795 + 2610136 * 2 ^ 59
def prefixEnd_2610136 : Nat := 4983230072969 + 3 ^ 40 * 2610136 * 2
def baseEnd_2610136 : Nat := 1340254341603905064596209

theorem tailTrace_2610136 : CollatzResearch.WordTrace tailWord_2610136 prefixEnd_2610136 1340254341603905064596209 := by
  unfold tailWord_2610136
  simp only [CollatzResearch.WordTrace]
  refine ⟨47599740435965261291945131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63466320581287015055926841 47599740435965261291945131)
  ·
    refine ⟨71399610653947891937917697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47599740435965261291945131 71399610653947891937917697)
    ·
      refine ⟨53549707990460918953438273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71399610653947891937917697 53549707990460918953438273)
      ·
        refine ⟨40162280992845689215078705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53549707990460918953438273 40162280992845689215078705)
        ·
          refine ⟨30121710744634266911309029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40162280992845689215078705 30121710744634266911309029)
          ·
            refine ⟨5647820764618925045870443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30121710744634266911309029 5647820764618925045870443)
            ·
              refine ⟨8471731146928387568805665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5647820764618925045870443 8471731146928387568805665)
              ·
                refine ⟨6353798360196290676604249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8471731146928387568805665 6353798360196290676604249)
                ·
                  refine ⟨4765348770147218007453187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6353798360196290676604249 4765348770147218007453187)
                  ·
                    refine ⟨7148023155220827011179781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4765348770147218007453187 7148023155220827011179781)
                    ·
                      refine ⟨1340254341603905064596209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7148023155220827011179781 1340254341603905064596209)
                      ·
                        rfl

theorem cell23_2610136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_2610136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610136 prefixEnd_2610136 := by exact prefixLift 2610136
  have htrace : WordTrace (prefixWord ++ tailWord_2610136) baseStart_2610136 baseEnd_2610136 := by
    simpa [prefixWord, tailWord_2610136, baseEnd_2610136] using wordTrace_append hprefix tailTrace_2610136
  have hstable : (prefixWord ++ tailWord_2610136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610136).length < 2 ^ (prefixWord ++ tailWord_2610136).sum := by decide
  have hdescent : baseEnd_2610136 < baseStart_2610136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610197 : List Nat := [1, 3, 2, 1, 4, 3, 2, 2, 1, 4]
def baseStart_2610197 : Nat := 118140960795 + 2610197 * 2 ^ 59
def prefixEnd_2610197 : Nat := 4983230072969 + 3 ^ 40 * 2610197 * 2
def baseEnd_2610197 : Nat := 446761887974609775311143

theorem tailTrace_2610197 : CollatzResearch.WordTrace tailWord_2610197 prefixEnd_2610197 446761887974609775311143 := by
  unfold tailWord_2610197
  simp only [CollatzResearch.WordTrace]
  refine ⟨95201705724709530001860845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63467803816473020001240563 95201705724709530001860845)
  ·
    refine ⟨35700639646766073750697817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95201705724709530001860845 35700639646766073750697817)
    ·
      refine ⟨26775479735074555313023363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35700639646766073750697817 26775479735074555313023363)
      ·
        refine ⟨40163219602611832969535045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26775479735074555313023363 40163219602611832969535045)
        ·
          refine ⟨7530603675489718681787821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40163219602611832969535045 7530603675489718681787821)
          ·
            refine ⟨2823976378308644505670433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7530603675489718681787821 2823976378308644505670433)
            ·
              refine ⟨2117982283731483379252825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2823976378308644505670433 2117982283731483379252825)
              ·
                refine ⟨1588486712798612534439619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2117982283731483379252825 1588486712798612534439619)
                ·
                  refine ⟨2382730069197918801659429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1588486712798612534439619 2382730069197918801659429)
                  ·
                    refine ⟨446761887974609775311143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2382730069197918801659429 446761887974609775311143)
                    ·
                      rfl

theorem cell23_2610197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 2, 2, 1, 4].length) (baseStart_2610197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610197 prefixEnd_2610197 := by exact prefixLift 2610197
  have htrace : WordTrace (prefixWord ++ tailWord_2610197) baseStart_2610197 baseEnd_2610197 := by
    simpa [prefixWord, tailWord_2610197, baseEnd_2610197] using wordTrace_append hprefix tailTrace_2610197
  have hstable : (prefixWord ++ tailWord_2610197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610197).length < 2 ^ (prefixWord ++ tailWord_2610197).sum := by decide
  have hdescent : baseEnd_2610197 < baseStart_2610197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610226 : List Nat := [3, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4]
def baseStart_2610226 : Nat := 118140960795 + 2610226 * 2 ^ 59
def prefixEnd_2610226 : Nat := 4983230072969 + 3 ^ 40 * 2610226 * 2
def baseEnd_2610226 : Nat := 1340300554862809712470795

theorem tailTrace_2610226 : CollatzResearch.WordTrace tailWord_2610226 prefixEnd_2610226 1340300554862809712470795 := by
  unfold tailWord_2610226
  simp only [CollatzResearch.WordTrace]
  refine ⟨23800690860401116988666633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63468508961069645303111021 23800690860401116988666633)
  ·
    refine ⟨17850518145300837741499975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23800690860401116988666633 17850518145300837741499975)
    ·
      refine ⟨26775777217951256612249963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17850518145300837741499975 26775777217951256612249963)
      ·
        refine ⟨40163665826926884918374945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26775777217951256612249963 40163665826926884918374945)
        ·
          refine ⟨30122749370195163688781209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40163665826926884918374945 30122749370195163688781209)
          ·
            refine ⟨22592062027646372766585907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30122749370195163688781209 22592062027646372766585907)
            ·
              refine ⟨33888093041469559149878861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22592062027646372766585907 33888093041469559149878861)
              ·
                refine ⟨12708034890551084681204573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33888093041469559149878861 12708034890551084681204573)
                ·
                  refine ⟨4765513083956656755451715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12708034890551084681204573 4765513083956656755451715)
                  ·
                    refine ⟨7148269625934985133177573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4765513083956656755451715 7148269625934985133177573)
                    ·
                      refine ⟨1340300554862809712470795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7148269625934985133177573 1340300554862809712470795)
                      ·
                        rfl

theorem cell23_2610226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_2610226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610226 prefixEnd_2610226 := by exact prefixLift 2610226
  have htrace : WordTrace (prefixWord ++ tailWord_2610226) baseStart_2610226 baseEnd_2610226 := by
    simpa [prefixWord, tailWord_2610226, baseEnd_2610226] using wordTrace_append hprefix tailTrace_2610226
  have hstable : (prefixWord ++ tailWord_2610226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610226).length < 2 ^ (prefixWord ++ tailWord_2610226).sum := by decide
  have hdescent : baseEnd_2610226 < baseStart_2610226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610230 : List Nat := [5, 1, 2, 1, 1, 3, 1, 1, 1, 5, 2]
def baseStart_2610230 : Nat := 118140960795 + 2610230 * 2 ^ 59
def prefixEnd_2610230 : Nat := 4983230072969 + 3 ^ 40 * 2610230 * 2
def baseEnd_2610230 : Nat := 1340302608785427696820777

theorem tailTrace_2610230 : CollatzResearch.WordTrace tailWord_2610230 prefixEnd_2610230 1340302608785427696820777 := by
  unfold tailWord_2610230
  simp only [CollatzResearch.WordTrace]
  refine ⟨5950181833349373539863259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63468606222393317758541429 5950181833349373539863259)
  ·
    refine ⟨8925272750024060309794889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5950181833349373539863259 8925272750024060309794889)
    ·
      refine ⟨6693954562518045232346167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8925272750024060309794889 6693954562518045232346167)
      ·
        refine ⟨10040931843777067848519251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6693954562518045232346167 10040931843777067848519251)
        ·
          refine ⟨15061397765665601772778877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10040931843777067848519251 15061397765665601772778877)
          ·
            refine ⟨5648024162124600664792079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15061397765665601772778877 5648024162124600664792079)
            ·
              refine ⟨8472036243186900997188119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5648024162124600664792079 8472036243186900997188119)
              ·
                refine ⟨12708054364780351495782179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8472036243186900997188119 12708054364780351495782179)
                ·
                  refine ⟨19062081547170527243673269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12708054364780351495782179 19062081547170527243673269)
                  ·
                    refine ⟨1787070145047236929094369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19062081547170527243673269 1787070145047236929094369)
                    ·
                      refine ⟨1340302608785427696820777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1787070145047236929094369 1340302608785427696820777)
                      ·
                        rfl

theorem cell23_2610230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_2610230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610230 prefixEnd_2610230 := by exact prefixLift 2610230
  have htrace : WordTrace (prefixWord ++ tailWord_2610230) baseStart_2610230 baseEnd_2610230 := by
    simpa [prefixWord, tailWord_2610230, baseEnd_2610230] using wordTrace_append hprefix tailTrace_2610230
  have hstable : (prefixWord ++ tailWord_2610230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610230).length < 2 ^ (prefixWord ++ tailWord_2610230).sum := by decide
  have hdescent : baseEnd_2610230 < baseStart_2610230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610236 : List Nat := [2, 2, 2, 2, 2, 2, 2, 2, 1, 6]
def baseStart_2610236 : Nat := 118140960795 + 2610236 * 2 ^ 59
def prefixEnd_2610236 : Nat := 4983230072969 + 3 ^ 40 * 2610236 * 2
def baseEnd_2610236 : Nat := 446768563223118224448583

theorem tailTrace_2610236 : CollatzResearch.WordTrace tailWord_2610236 prefixEnd_2610236 446768563223118224448583 := by
  unfold tailWord_2610236
  simp only [CollatzResearch.WordTrace]
  refine ⟨47601564085784119831265281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63468752114378826441687041 47601564085784119831265281)
  ·
    refine ⟨35701173064338089873448961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47601564085784119831265281 35701173064338089873448961)
    ·
      refine ⟨26775879798253567405086721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35701173064338089873448961 26775879798253567405086721)
      ·
        refine ⟨20081909848690175553815041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26775879798253567405086721 20081909848690175553815041)
        ·
          refine ⟨15061432386517631665361281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20081909848690175553815041 15061432386517631665361281)
          ·
            refine ⟨11296074289888223749020961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15061432386517631665361281 11296074289888223749020961)
            ·
              refine ⟨8472055717416167811765721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11296074289888223749020961 8472055717416167811765721)
              ·
                refine ⟨6354041788062125858824291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8472055717416167811765721 6354041788062125858824291)
                ·
                  refine ⟨9531062682093188788236437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6354041788062125858824291 9531062682093188788236437)
                  ·
                    refine ⟨446768563223118224448583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9531062682093188788236437 446768563223118224448583)
                    ·
                      rfl

theorem cell23_2610236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_2610236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610236 prefixEnd_2610236 := by exact prefixLift 2610236
  have htrace : WordTrace (prefixWord ++ tailWord_2610236) baseStart_2610236 baseEnd_2610236 := by
    simpa [prefixWord, tailWord_2610236, baseEnd_2610236] using wordTrace_append hprefix tailTrace_2610236
  have hstable : (prefixWord ++ tailWord_2610236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610236).length < 2 ^ (prefixWord ++ tailWord_2610236).sum := by decide
  have hdescent : baseEnd_2610236 < baseStart_2610236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610237 : List Nat := [1, 4, 1, 3, 1, 3, 2, 3, 1, 1, 3]
def baseStart_2610237 : Nat := 118140960795 + 2610237 * 2 ^ 59
def prefixEnd_2610237 : Nat := 4983230072969 + 3 ^ 40 * 2610237 * 2
def baseEnd_2610237 : Nat := 1340306203150009169433245

theorem tailTrace_2610237 : CollatzResearch.WordTrace tailWord_2610237 prefixEnd_2610237 1340306203150009169433245 := by
  unfold tailWord_2610237
  simp only [CollatzResearch.WordTrace]
  refine ⟨95203164644564616833316965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63468776429709744555544643 95203164644564616833316965)
  ·
    refine ⟨17850593370855865656246931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95203164644564616833316965 17850593370855865656246931)
    ·
      refine ⟨26775890056283798484370397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17850593370855865656246931 26775890056283798484370397)
      ·
        refine ⟨10040958771106424431638899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26775890056283798484370397 10040958771106424431638899)
        ·
          refine ⟨15061438156659636647458349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10040958771106424431638899 15061438156659636647458349)
          ·
            refine ⟨5648039308747363742796881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15061438156659636647458349 5648039308747363742796881)
            ·
              refine ⟨4236029481560522807097661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5648039308747363742796881 4236029481560522807097661)
              ·
                refine ⟨1588511055585196052661623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4236029481560522807097661 1588511055585196052661623)
                ·
                  refine ⟨2382766583377794078992435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1588511055585196052661623 2382766583377794078992435)
                  ·
                    refine ⟨3574149875066691118488653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2382766583377794078992435 3574149875066691118488653)
                    ·
                      refine ⟨1340306203150009169433245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3574149875066691118488653 1340306203150009169433245)
                      ·
                        rfl

theorem cell23_2610237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_2610237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610237 prefixEnd_2610237 := by exact prefixLift 2610237
  have htrace : WordTrace (prefixWord ++ tailWord_2610237) baseStart_2610237 baseEnd_2610237 := by
    simpa [prefixWord, tailWord_2610237, baseEnd_2610237] using wordTrace_append hprefix tailTrace_2610237
  have hstable : (prefixWord ++ tailWord_2610237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610237).length < 2 ^ (prefixWord ++ tailWord_2610237).sum := by decide
  have hdescent : baseEnd_2610237 < baseStart_2610237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610239 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 6]
def baseStart_2610239 : Nat := 118140960795 + 2610239 * 2 ^ 59
def prefixEnd_2610239 : Nat := 4983230072969 + 3 ^ 40 * 2610239 * 2
def baseEnd_2610239 : Nat := 1340307230111318161608235

theorem tailTrace_2610239 : CollatzResearch.WordTrace tailWord_2610239 prefixEnd_2610239 1340307230111318161608235 := by
  unfold tailWord_2610239
  simp only [CollatzResearch.WordTrace]
  refine ⟨95203237590557371174889771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63468825060371580783259847 95203237590557371174889771)
  ·
    refine ⟨142804856385836056762334657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95203237590557371174889771 142804856385836056762334657)
    ·
      refine ⟨107103642289377042571750993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142804856385836056762334657 107103642289377042571750993)
      ·
        refine ⟨80327731717032781928813245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107103642289377042571750993 80327731717032781928813245)
        ·
          refine ⟨30122899393887293223304967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80327731717032781928813245 30122899393887293223304967)
          ·
            refine ⟨45184349090830939834957451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30122899393887293223304967 45184349090830939834957451)
            ·
              refine ⟨67776523636246409752436177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45184349090830939834957451 67776523636246409752436177)
              ·
                refine ⟨50832392727184807314327133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67776523636246409752436177 50832392727184807314327133)
                ·
                  refine ⟨19062147272694302742872675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50832392727184807314327133 19062147272694302742872675)
                  ·
                    refine ⟨28593220909041454114309013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19062147272694302742872675 28593220909041454114309013)
                    ·
                      refine ⟨1340307230111318161608235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28593220909041454114309013 1340307230111318161608235)
                      ·
                        rfl

theorem cell23_2610239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_2610239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610239 prefixEnd_2610239 := by exact prefixLift 2610239
  have htrace : WordTrace (prefixWord ++ tailWord_2610239) baseStart_2610239 baseEnd_2610239 := by
    simpa [prefixWord, tailWord_2610239, baseEnd_2610239] using wordTrace_append hprefix tailTrace_2610239
  have hstable : (prefixWord ++ tailWord_2610239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610239).length < 2 ^ (prefixWord ++ tailWord_2610239).sum := by decide
  have hdescent : baseEnd_2610239 < baseStart_2610239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610243 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 5, 2, 2]
def baseStart_2610243 : Nat := 118140960795 + 2610243 * 2 ^ 59
def prefixEnd_2610243 : Nat := 4983230072969 + 3 ^ 40 * 2610243 * 2
def baseEnd_2610243 : Nat := 1340309284033936145958217

theorem tailTrace_2610243 : CollatzResearch.WordTrace tailWord_2610243 prefixEnd_2610243 1340309284033936145958217 := by
  unfold tailWord_2610243
  simp only [CollatzResearch.WordTrace]
  refine ⟨95203383482542879858035383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63468922321695253238690255 95203383482542879858035383)
  ·
    refine ⟨142805075223814319787053075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95203383482542879858035383 142805075223814319787053075)
    ·
      refine ⟨214207612835721479680579613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142805075223814319787053075 214207612835721479680579613)
      ·
        refine ⟨80327854813395554880217355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214207612835721479680579613 80327854813395554880217355)
        ·
          refine ⟨120491782220093332320326033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80327854813395554880217355 120491782220093332320326033)
          ·
            refine ⟨90368836665069999240244525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120491782220093332320326033 90368836665069999240244525)
            ·
              refine ⟨33888313749401249715091697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90368836665069999240244525 33888313749401249715091697)
              ·
                refine ⟨25416235312050937286318773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33888313749401249715091697 25416235312050937286318773)
                ·
                  refine ⟨2382772060504775370592385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25416235312050937286318773 2382772060504775370592385)
                  ·
                    refine ⟨1787079045378581527944289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2382772060504775370592385 1787079045378581527944289)
                    ·
                      refine ⟨1340309284033936145958217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1787079045378581527944289 1340309284033936145958217)
                      ·
                        rfl

theorem cell23_2610243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 5, 2, 2].length) (baseStart_2610243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610243 prefixEnd_2610243 := by exact prefixLift 2610243
  have htrace : WordTrace (prefixWord ++ tailWord_2610243) baseStart_2610243 baseEnd_2610243 := by
    simpa [prefixWord, tailWord_2610243, baseEnd_2610243] using wordTrace_append hprefix tailTrace_2610243
  have hstable : (prefixWord ++ tailWord_2610243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610243).length < 2 ^ (prefixWord ++ tailWord_2610243).sum := by decide
  have hdescent : baseEnd_2610243 < baseStart_2610243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610260 : List Nat := [2, 4, 1, 1, 1, 1, 3, 3, 3, 2, 2]
def baseStart_2610260 : Nat := 118140960795 + 2610260 * 2 ^ 59
def prefixEnd_2610260 : Nat := 4983230072969 + 3 ^ 40 * 2610260 * 2
def baseEnd_2610260 : Nat := 1340318013205062579445639

theorem tailTrace_2610260 : CollatzResearch.WordTrace tailWord_2610260 prefixEnd_2610260 1340318013205062579445639 := by
  unfold tailWord_2610260
  simp only [CollatzResearch.WordTrace]
  refine ⟨47602001761740645880702117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63469335682320861174269489 47602001761740645880702117)
  ·
    refine ⟨8925375330326371102631647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47602001761740645880702117 8925375330326371102631647)
    ·
      refine ⟨13388062995489556653947471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8925375330326371102631647 13388062995489556653947471)
      ·
        refine ⟨20082094493234334980921207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13388062995489556653947471 20082094493234334980921207)
        ·
          refine ⟨30123141739851502471381811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20082094493234334980921207 30123141739851502471381811)
          ·
            refine ⟨45184712609777253707072717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30123141739851502471381811 45184712609777253707072717)
            ·
              refine ⟨16944267228666470140152269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45184712609777253707072717 16944267228666470140152269)
              ·
                refine ⟨6354100210749926302557101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16944267228666470140152269 6354100210749926302557101)
                ·
                  refine ⟨2382787579031222363458913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6354100210749926302557101 2382787579031222363458913)
                  ·
                    refine ⟨1787090684273416772594185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2382787579031222363458913 1787090684273416772594185)
                    ·
                      refine ⟨1340318013205062579445639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1787090684273416772594185 1340318013205062579445639)
                      ·
                        rfl

theorem cell23_2610260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_2610260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610260 prefixEnd_2610260 := by exact prefixLift 2610260
  have htrace : WordTrace (prefixWord ++ tailWord_2610260) baseStart_2610260 baseEnd_2610260 := by
    simpa [prefixWord, tailWord_2610260, baseEnd_2610260] using wordTrace_append hprefix tailTrace_2610260
  have hstable : (prefixWord ++ tailWord_2610260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610260).length < 2 ^ (prefixWord ++ tailWord_2610260).sum := by decide
  have hdescent : baseEnd_2610260 < baseStart_2610260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610299 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 8]
def baseStart_2610299 : Nat := 118140960795 + 2610299 * 2 ^ 59
def prefixEnd_2610299 : Nat := 4983230072969 + 3 ^ 40 * 2610299 * 2
def baseEnd_2610299 : Nat := 1340338038950587926857959

theorem tailTrace_2610299 : CollatzResearch.WordTrace tailWord_2610299 prefixEnd_2610299 1340338038950587926857959 := by
  unfold tailWord_2610299
  simp only [CollatzResearch.WordTrace]
  refine ⟨95205425970340001422073951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63470283980226667614715967 95205425970340001422073951)
  ·
    refine ⟨142808138955510002133110927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95205425970340001422073951 142808138955510002133110927)
    ·
      refine ⟨214212208433265003199666391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142808138955510002133110927 214212208433265003199666391)
      ·
        refine ⟨321318312649897504799499587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214212208433265003199666391 321318312649897504799499587)
        ·
          refine ⟨481977468974846257199249381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321318312649897504799499587 481977468974846257199249381)
          ·
            refine ⟨90370775432783673224859259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 481977468974846257199249381 90370775432783673224859259)
            ·
              refine ⟨135556163149175509837288889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90370775432783673224859259 135556163149175509837288889)
              ·
                refine ⟨101667122361881632377966667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135556163149175509837288889 101667122361881632377966667)
                ·
                  refine ⟨152500683542822448566950001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101667122361881632377966667 152500683542822448566950001)
                  ·
                    refine ⟨114375512657116836425212501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 152500683542822448566950001 114375512657116836425212501)
                    ·
                      refine ⟨1340338038950587926857959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 114375512657116836425212501 1340338038950587926857959)
                      ·
                        rfl

theorem cell23_2610299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 8].length) (baseStart_2610299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610299 prefixEnd_2610299 := by exact prefixLift 2610299
  have htrace : WordTrace (prefixWord ++ tailWord_2610299) baseStart_2610299 baseEnd_2610299 := by
    simpa [prefixWord, tailWord_2610299, baseEnd_2610299] using wordTrace_append hprefix tailTrace_2610299
  have hstable : (prefixWord ++ tailWord_2610299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610299).length < 2 ^ (prefixWord ++ tailWord_2610299).sum := by decide
  have hdescent : baseEnd_2610299 < baseStart_2610299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610327 : List Nat := [1, 1, 3, 3, 3, 1, 4, 1, 2, 1, 3]
def baseStart_2610327 : Nat := 118140960795 + 2610327 * 2 ^ 59
def prefixEnd_2610327 : Nat := 4983230072969 + 3 ^ 40 * 2610327 * 2
def baseEnd_2610327 : Nat := 1340352416408913817307831

theorem tailTrace_2610327 : CollatzResearch.WordTrace tailWord_2610327 prefixEnd_2610327 1340352416408913817307831 := by
  unfold tailWord_2610327
  simp only [CollatzResearch.WordTrace]
  refine ⟨95206447214238562204093235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63470964809492374802728823 95206447214238562204093235)
  ·
    refine ⟨142809670821357843306139853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95206447214238562204093235 142809670821357843306139853)
    ·
      refine ⟨53553626558009191239802445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142809670821357843306139853 53553626558009191239802445)
      ·
        refine ⟨20082609959253446714925917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53553626558009191239802445 20082609959253446714925917)
        ·
          refine ⟨7530978734720042518097219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20082609959253446714925917 7530978734720042518097219)
          ·
            refine ⟨11296468102080063777145829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7530978734720042518097219 11296468102080063777145829)
            ·
              refine ⟨2118087769140011958214843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11296468102080063777145829 2118087769140011958214843)
              ·
                refine ⟨3177131653710017937322265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2118087769140011958214843 3177131653710017937322265)
                ·
                  refine ⟨2382848740282513452991699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3177131653710017937322265 2382848740282513452991699)
                  ·
                    refine ⟨3574273110423770179487549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2382848740282513452991699 3574273110423770179487549)
                    ·
                      refine ⟨1340352416408913817307831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3574273110423770179487549 1340352416408913817307831)
                      ·
                        rfl

theorem cell23_2610327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_2610327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610327 prefixEnd_2610327 := by exact prefixLift 2610327
  have htrace : WordTrace (prefixWord ++ tailWord_2610327) baseStart_2610327 baseEnd_2610327 := by
    simpa [prefixWord, tailWord_2610327, baseEnd_2610327] using wordTrace_append hprefix tailTrace_2610327
  have hstable : (prefixWord ++ tailWord_2610327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610327).length < 2 ^ (prefixWord ++ tailWord_2610327).sum := by decide
  have hdescent : baseEnd_2610327 < baseStart_2610327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610336 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 5]
def baseStart_2610336 : Nat := 118140960795 + 2610336 * 2 ^ 59
def prefixEnd_2610336 : Nat := 4983230072969 + 3 ^ 40 * 2610336 * 2
def baseEnd_2610336 : Nat := 1340357037734804282095289

theorem tailTrace_2610336 : CollatzResearch.WordTrace tailWord_2610336 prefixEnd_2610336 1340357037734804282095289 := by
  unfold tailWord_2610336
  simp only [CollatzResearch.WordTrace]
  refine ⟨47603387735602978370585431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63471183647470637827447241 47603387735602978370585431)
  ·
    refine ⟨71405081603404467555878147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47603387735602978370585431 71405081603404467555878147)
    ·
      refine ⟨107107622405106701333817221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71405081603404467555878147 107107622405106701333817221)
      ·
        refine ⟨20082679200957506500090729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107107622405106701333817221 20082679200957506500090729)
        ·
          refine ⟨15062009400718129875068047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20082679200957506500090729 15062009400718129875068047)
          ·
            refine ⟨22593014101077194812602071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15062009400718129875068047 22593014101077194812602071)
            ·
              refine ⟨33889521151615792218903107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22593014101077194812602071 33889521151615792218903107)
              ·
                refine ⟨50834281727423688328354661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33889521151615792218903107 50834281727423688328354661)
                ·
                  refine ⟨9531427823891941561566499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50834281727423688328354661 9531427823891941561566499)
                  ·
                    refine ⟨14297141735837912342349749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9531427823891941561566499 14297141735837912342349749)
                    ·
                      refine ⟨1340357037734804282095289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14297141735837912342349749 1340357037734804282095289)
                      ·
                        rfl

theorem cell23_2610336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_2610336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610336 prefixEnd_2610336 := by exact prefixLift 2610336
  have htrace : WordTrace (prefixWord ++ tailWord_2610336) baseStart_2610336 baseEnd_2610336 := by
    simpa [prefixWord, tailWord_2610336, baseEnd_2610336] using wordTrace_append hprefix tailTrace_2610336
  have hstable : (prefixWord ++ tailWord_2610336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610336).length < 2 ^ (prefixWord ++ tailWord_2610336).sum := by decide
  have hdescent : baseEnd_2610336 < baseStart_2610336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610353 : List Nat := [1, 2, 2, 5, 1, 1, 2, 1, 2, 1, 5]
def baseStart_2610353 : Nat := 118140960795 + 2610353 * 2 ^ 59
def prefixEnd_2610353 : Nat := 4983230072969 + 3 ^ 40 * 2610353 * 2
def baseEnd_2610353 : Nat := 1340365766905930715582711

theorem tailTrace_2610353 : CollatzResearch.WordTrace tailWord_2610353 prefixEnd_2610353 1340365766905930715582711 := by
  unfold tailWord_2610353
  simp only [CollatzResearch.WordTrace]
  refine ⟨95207395512144368644539713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63471597008096245763026475 95207395512144368644539713)
  ·
    refine ⟨71405546634108276483404785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95207395512144368644539713 71405546634108276483404785)
    ·
      refine ⟨53554159975581207362553589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71405546634108276483404785 53554159975581207362553589)
      ·
        refine ⟨5020702497710738190239399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53554159975581207362553589 5020702497710738190239399)
        ·
          refine ⟨7531053746566107285359099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5020702497710738190239399 7531053746566107285359099)
          ·
            refine ⟨11296580619849160928038649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7531053746566107285359099 11296580619849160928038649)
            ·
              refine ⟨8472435464886870696028987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11296580619849160928038649 8472435464886870696028987)
              ·
                refine ⟨12708653197330306044043481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8472435464886870696028987 12708653197330306044043481)
                ·
                  refine ⟨9531489897997729533032611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12708653197330306044043481 9531489897997729533032611)
                  ·
                    refine ⟨14297234846996594299548917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9531489897997729533032611 14297234846996594299548917)
                    ·
                      refine ⟨1340365766905930715582711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14297234846996594299548917 1340365766905930715582711)
                      ·
                        rfl

theorem cell23_2610353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_2610353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610353 prefixEnd_2610353 := by exact prefixLift 2610353
  have htrace : WordTrace (prefixWord ++ tailWord_2610353) baseStart_2610353 baseEnd_2610353 := by
    simpa [prefixWord, tailWord_2610353, baseEnd_2610353] using wordTrace_append hprefix tailTrace_2610353
  have hstable : (prefixWord ++ tailWord_2610353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610353).length < 2 ^ (prefixWord ++ tailWord_2610353).sum := by decide
  have hdescent : baseEnd_2610353 < baseStart_2610353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610393 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 4, 5, 2]
def baseStart_2610393 : Nat := 118140960795 + 2610393 * 2 ^ 59
def prefixEnd_2610393 : Nat := 4983230072969 + 3 ^ 40 * 2610393 * 2
def baseEnd_2610393 : Nat := 1340386306132110559082527

theorem tailTrace_2610393 : CollatzResearch.WordTrace tailWord_2610393 prefixEnd_2610393 1340386306132110559082527 := by
  unfold tailWord_2610393
  simp only [CollatzResearch.WordTrace]
  refine ⟨95208854431999455475995833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63472569621332970317330555 95208854431999455475995833)
  ·
    refine ⟨71406640823999591606996875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95208854431999455475995833 71406640823999591606996875)
    ·
      refine ⟨107109961235999387410495313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71406640823999591606996875 107109961235999387410495313)
      ·
        refine ⟨80332470926999540557871485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107109961235999387410495313 80332470926999540557871485)
        ·
          refine ⟨30124676597624827709201807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80332470926999540557871485 30124676597624827709201807)
          ·
            refine ⟨45187014896437241563802711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30124676597624827709201807 45187014896437241563802711)
            ·
              refine ⟨67780522344655862345704067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45187014896437241563802711 67780522344655862345704067)
              ·
                refine ⟨101670783516983793518556101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67780522344655862345704067 101670783516983793518556101)
                ·
                  refine ⟨19063271909434461284729269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101670783516983793518556101 19063271909434461284729269)
                  ·
                    refine ⟨1787181741509480745443369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19063271909434461284729269 1787181741509480745443369)
                    ·
                      refine ⟨1340386306132110559082527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1787181741509480745443369 1340386306132110559082527)
                      ·
                        rfl

theorem cell23_2610393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 5, 2].length) (baseStart_2610393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610393 prefixEnd_2610393 := by exact prefixLift 2610393
  have htrace : WordTrace (prefixWord ++ tailWord_2610393) baseStart_2610393 baseEnd_2610393 := by
    simpa [prefixWord, tailWord_2610393, baseEnd_2610393] using wordTrace_append hprefix tailTrace_2610393
  have hstable : (prefixWord ++ tailWord_2610393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610393).length < 2 ^ (prefixWord ++ tailWord_2610393).sum := by decide
  have hdescent : baseEnd_2610393 < baseStart_2610393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610407 : List Nat := [1, 1, 5, 3, 2, 1, 2, 3, 5]
def baseStart_2610407 : Nat := 118140960795 + 2610407 * 2 ^ 59
def prefixEnd_2610407 : Nat := 4983230072969 + 3 ^ 40 * 2610407 * 2
def baseEnd_2610407 : Nat := 148932610540141500478607

theorem tailTrace_2610407 : CollatzResearch.WordTrace tailWord_2610407 prefixEnd_2610407 148932610540141500478607 := by
  unfold tailWord_2610407
  simp only [CollatzResearch.WordTrace]
  refine ⟨95209365053948735867005475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63472910035965823911336983 95209365053948735867005475)
  ·
    refine ⟨142814047580923103800508213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95209365053948735867005475 142814047580923103800508213)
    ·
      refine ⟨13388816960711540981297645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 142814047580923103800508213 13388816960711540981297645)
      ·
        refine ⟨5020806360266827867986617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13388816960711540981297645 5020806360266827867986617)
        ·
          refine ⟨3765604770200120900989963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5020806360266827867986617 3765604770200120900989963)
          ·
            refine ⟨5648407155300181351484945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3765604770200120900989963 5648407155300181351484945)
            ·
              refine ⟨4236305366475136013613709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5648407155300181351484945 4236305366475136013613709)
              ·
                refine ⟨1588614512428176005105141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4236305366475136013613709 1588614512428176005105141)
                ·
                  refine ⟨148932610540141500478607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1588614512428176005105141 148932610540141500478607)
                  ·
                    rfl

theorem cell23_2610407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 3, 5].length) (baseStart_2610407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610407 prefixEnd_2610407 := by exact prefixLift 2610407
  have htrace : WordTrace (prefixWord ++ tailWord_2610407) baseStart_2610407 baseEnd_2610407 := by
    simpa [prefixWord, tailWord_2610407, baseEnd_2610407] using wordTrace_append hprefix tailTrace_2610407
  have hstable : (prefixWord ++ tailWord_2610407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610407).length < 2 ^ (prefixWord ++ tailWord_2610407).sum := by decide
  have hdescent : baseEnd_2610407 < baseStart_2610407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610423 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 3, 6, 2]
def baseStart_2610423 : Nat := 118140960795 + 2610423 * 2 ^ 59
def prefixEnd_2610423 : Nat := 4983230072969 + 3 ^ 40 * 2610423 * 2
def baseEnd_2610423 : Nat := 1340401710551745441707389

theorem tailTrace_2610423 : CollatzResearch.WordTrace tailWord_2610423 prefixEnd_2610423 1340401710551745441707389 := by
  unfold tailWord_2610423
  simp only [CollatzResearch.WordTrace]
  refine ⟨95209948621890770599587923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63473299081260513733058615 95209948621890770599587923)
  ·
    refine ⟨142814922932836155899381885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95209948621890770599587923 142814922932836155899381885)
    ·
      refine ⟨53555596099813558462268207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142814922932836155899381885 53555596099813558462268207)
      ·
        refine ⟨80333394149720337693402311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53555596099813558462268207 80333394149720337693402311)
        ·
          refine ⟨120500091224580506540103467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80333394149720337693402311 120500091224580506540103467)
          ·
            refine ⟨180750136836870759810155201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120500091224580506540103467 180750136836870759810155201)
            ·
              refine ⟨135562602627653069857616401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180750136836870759810155201 135562602627653069857616401)
              ·
                refine ⟨101671951970739802393212301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135562602627653069857616401 101671951970739802393212301)
                ·
                  refine ⟨38126981989027425897454613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101671951970739802393212301 38126981989027425897454613)
                  ·
                    refine ⟨1787202280735660588943185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38126981989027425897454613 1787202280735660588943185)
                    ·
                      refine ⟨1340401710551745441707389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1787202280735660588943185 1340401710551745441707389)
                      ·
                        rfl

theorem cell23_2610423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 6, 2].length) (baseStart_2610423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610423 prefixEnd_2610423 := by exact prefixLift 2610423
  have htrace : WordTrace (prefixWord ++ tailWord_2610423) baseStart_2610423 baseEnd_2610423 := by
    simpa [prefixWord, tailWord_2610423, baseEnd_2610423] using wordTrace_append hprefix tailTrace_2610423
  have hstable : (prefixWord ++ tailWord_2610423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610423).length < 2 ^ (prefixWord ++ tailWord_2610423).sum := by decide
  have hdescent : baseEnd_2610423 < baseStart_2610423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610443 : List Nat := [1, 1, 1, 1, 5, 3, 1, 2, 1, 4, 3]
def baseStart_2610443 : Nat := 118140960795 + 2610443 * 2 ^ 59
def prefixEnd_2610443 : Nat := 4983230072969 + 3 ^ 40 * 2610443 * 2
def baseEnd_2610443 : Nat := 1340411980164835363457297

theorem tailTrace_2610443 : CollatzResearch.WordTrace tailWord_2610443 prefixEnd_2610443 1340411980164835363457297 := by
  unfold tailWord_2610443
  simp only [CollatzResearch.WordTrace]
  refine ⟨95210678081818314015315983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63473785387878876010210655 95210678081818314015315983)
  ·
    refine ⟨142816017122727471022973975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95210678081818314015315983 142816017122727471022973975)
    ·
      refine ⟨214224025684091206534460963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142816017122727471022973975 214224025684091206534460963)
      ·
        refine ⟨321336038526136809801691445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214224025684091206534460963 321336038526136809801691445)
        ·
          refine ⟨30125253611825325918908573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 321336038526136809801691445 30125253611825325918908573)
          ·
            refine ⟨11296970104434497219590715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30125253611825325918908573 11296970104434497219590715)
            ·
              refine ⟨16945455156651745829386073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11296970104434497219590715 16945455156651745829386073)
              ·
                refine ⟨12709091367488809372039555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16945455156651745829386073 12709091367488809372039555)
                ·
                  refine ⟨19063637051233214058059333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12709091367488809372039555 19063637051233214058059333)
                  ·
                    refine ⟨3574431947106227635886125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19063637051233214058059333 3574431947106227635886125)
                    ·
                      refine ⟨1340411980164835363457297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3574431947106227635886125 1340411980164835363457297)
                      ·
                        rfl

theorem cell23_2610443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 4, 3].length) (baseStart_2610443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610443 prefixEnd_2610443 := by exact prefixLift 2610443
  have htrace : WordTrace (prefixWord ++ tailWord_2610443) baseStart_2610443 baseEnd_2610443 := by
    simpa [prefixWord, tailWord_2610443, baseEnd_2610443] using wordTrace_append hprefix tailTrace_2610443
  have hstable : (prefixWord ++ tailWord_2610443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610443).length < 2 ^ (prefixWord ++ tailWord_2610443).sum := by decide
  have hdescent : baseEnd_2610443 < baseStart_2610443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610467 : List Nat := [1, 1, 1, 4, 2, 3, 3, 3, 1, 4]
def baseStart_2610467 : Nat := 118140960795 + 2610467 * 2 ^ 59
def prefixEnd_2610467 : Nat := 4983230072969 + 3 ^ 40 * 2610467 * 2
def baseEnd_2610467 : Nat := 446808101233514423185729

theorem tailTrace_2610467 : CollatzResearch.WordTrace tailWord_2610467 prefixEnd_2610467 446808101233514423185729 := by
  unfold tailWord_2610467
  simp only [CollatzResearch.WordTrace]
  refine ⟨95211553433731366114189655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63474368955820910742793103 95211553433731366114189655)
  ·
    refine ⟨142817330150597049171284483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95211553433731366114189655 142817330150597049171284483)
    ·
      refine ⟨214225995225895573756926725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142817330150597049171284483 214225995225895573756926725)
      ·
        refine ⟨40167374104855420079423761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 214225995225895573756926725 40167374104855420079423761)
        ·
          refine ⟨30125530578641565059567821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40167374104855420079423761 30125530578641565059567821)
          ·
            refine ⟨11297073966990586897337933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30125530578641565059567821 11297073966990586897337933)
            ·
              refine ⟨4236402737621470086501725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11297073966990586897337933 4236402737621470086501725)
              ·
                refine ⟨1588651026608051282438147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4236402737621470086501725 1588651026608051282438147)
                ·
                  refine ⟨2382976539912076923657221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1588651026608051282438147 2382976539912076923657221)
                  ·
                    refine ⟨446808101233514423185729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2382976539912076923657221 446808101233514423185729)
                    ·
                      rfl

theorem cell23_2610467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 3, 1, 4].length) (baseStart_2610467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610467 prefixEnd_2610467 := by exact prefixLift 2610467
  have htrace : WordTrace (prefixWord ++ tailWord_2610467) baseStart_2610467 baseEnd_2610467 := by
    simpa [prefixWord, tailWord_2610467, baseEnd_2610467] using wordTrace_append hprefix tailTrace_2610467
  have hstable : (prefixWord ++ tailWord_2610467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610467).length < 2 ^ (prefixWord ++ tailWord_2610467).sum := by decide
  have hdescent : baseEnd_2610467 < baseStart_2610467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610477 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_2610477 : Nat := 118140960795 + 2610477 * 2 ^ 59
def prefixEnd_2610477 : Nat := 4983230072969 + 3 ^ 40 * 2610477 * 2
def baseEnd_2610477 : Nat := 1340429438507088230432141

theorem tailTrace_2610477 : CollatzResearch.WordTrace tailWord_2610477 prefixEnd_2610477 1340429438507088230432141 := by
  unfold tailWord_2610477
  simp only [CollatzResearch.WordTrace]
  refine ⟨95211918163695137822053685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63474612109130091881369123 95211918163695137822053685)
  ·
    refine ⟨8926117327846419170817533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95211918163695137822053685 8926117327846419170817533)
    ·
      refine ⟨3347293997942407189056575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8926117327846419170817533 3347293997942407189056575)
      ·
        refine ⟨5020940996913610783584863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3347293997942407189056575 5020940996913610783584863)
        ·
          refine ⟨7531411495370416175377295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5020940996913610783584863 7531411495370416175377295)
          ·
            refine ⟨11297117243055624263065943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7531411495370416175377295 11297117243055624263065943)
            ·
              refine ⟨16945675864583436394598915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11297117243055624263065943 16945675864583436394598915)
              ·
                refine ⟨25418513796875154591898373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16945675864583436394598915 25418513796875154591898373)
                ·
                  refine ⟨4765971336914091485980945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25418513796875154591898373 4765971336914091485980945)
                  ·
                    refine ⟨3574478502685568614485709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4765971336914091485980945 3574478502685568614485709)
                    ·
                      refine ⟨1340429438507088230432141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3574478502685568614485709 1340429438507088230432141)
                      ·
                        rfl

theorem cell23_2610477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_2610477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610477 prefixEnd_2610477 := by exact prefixLift 2610477
  have htrace : WordTrace (prefixWord ++ tailWord_2610477) baseStart_2610477 baseEnd_2610477 := by
    simpa [prefixWord, tailWord_2610477, baseEnd_2610477] using wordTrace_append hprefix tailTrace_2610477
  have hstable : (prefixWord ++ tailWord_2610477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610477).length < 2 ^ (prefixWord ++ tailWord_2610477).sum := by decide
  have hdescent : baseEnd_2610477 < baseStart_2610477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610497 : List Nat := [1, 2, 5, 2, 1, 1, 4, 1, 6]
def baseStart_2610497 : Nat := 118140960795 + 2610497 * 2 ^ 59
def prefixEnd_2610497 : Nat := 4983230072969 + 3 ^ 40 * 2610497 * 2
def baseEnd_2610497 : Nat := 148937745346686461353561

theorem tailTrace_2610497 : CollatzResearch.WordTrace tailWord_2610497 prefixEnd_2610497 148937745346686461353561 := by
  unfold tailWord_2610497
  simp only [CollatzResearch.WordTrace]
  refine ⟨95212647623622681237781745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63475098415748454158521163 95212647623622681237781745)
  ·
    refine ⟨71409485717717010928336309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95212647623622681237781745 71409485717717010928336309)
    ·
      refine ⟨6694639286035969774531529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71409485717717010928336309 6694639286035969774531529)
      ·
        refine ⟨5020979464526977330898647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6694639286035969774531529 5020979464526977330898647)
        ·
          refine ⟨7531469196790465996347971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5020979464526977330898647 7531469196790465996347971)
          ·
            refine ⟨11297203795185698994521957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7531469196790465996347971 11297203795185698994521957)
            ·
              refine ⟨2118225711597318561472867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11297203795185698994521957 2118225711597318561472867)
              ·
                refine ⟨3177338567395977842209301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2118225711597318561472867 3177338567395977842209301)
                ·
                  refine ⟨148937745346686461353561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3177338567395977842209301 148937745346686461353561)
                  ·
                    rfl

theorem cell23_2610497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 6].length) (baseStart_2610497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610497 prefixEnd_2610497 := by exact prefixLift 2610497
  have htrace : WordTrace (prefixWord ++ tailWord_2610497) baseStart_2610497 baseEnd_2610497 := by
    simpa [prefixWord, tailWord_2610497, baseEnd_2610497] using wordTrace_append hprefix tailTrace_2610497
  have hstable : (prefixWord ++ tailWord_2610497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610497).length < 2 ^ (prefixWord ++ tailWord_2610497).sum := by decide
  have hdescent : baseEnd_2610497 < baseStart_2610497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610517 : List Nat := [1, 3, 2, 2, 3, 1, 1, 3, 2, 3, 2]
def baseStart_2610517 : Nat := 118140960795 + 2610517 * 2 ^ 59
def prefixEnd_2610517 : Nat := 4983230072969 + 3 ^ 40 * 2610517 * 2
def baseEnd_2610517 : Nat := 1340449977733268073931957

theorem tailTrace_2610517 : CollatzResearch.WordTrace tailWord_2610517 prefixEnd_2610517 1340449977733268073931957 := by
  unfold tailWord_2610517
  simp only [CollatzResearch.WordTrace]
  refine ⟨95213377083550224653509805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63475584722366816435673203 95213377083550224653509805)
  ·
    refine ⟨35705016406331334245066177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95213377083550224653509805 35705016406331334245066177)
    ·
      refine ⟨26778762304748500683799633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35705016406331334245066177 26778762304748500683799633)
      ·
        refine ⟨20084071728561375512849725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26778762304748500683799633 20084071728561375512849725)
        ·
          refine ⟨7531526898210515817318647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20084071728561375512849725 7531526898210515817318647)
          ·
            refine ⟨11297290347315773725977971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7531526898210515817318647 11297290347315773725977971)
            ·
              refine ⟨16945935520973660588966957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11297290347315773725977971 16945935520973660588966957)
              ·
                refine ⟨6354725820365122720862609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16945935520973660588966957 6354725820365122720862609)
                ·
                  refine ⟨4766044365273842040646957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6354725820365122720862609 4766044365273842040646957)
                  ·
                    refine ⟨1787266636977690765242609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4766044365273842040646957 1787266636977690765242609)
                    ·
                      refine ⟨1340449977733268073931957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1787266636977690765242609 1340449977733268073931957)
                      ·
                        rfl

theorem cell23_2610517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_2610517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610517 prefixEnd_2610517 := by exact prefixLift 2610517
  have htrace : WordTrace (prefixWord ++ tailWord_2610517) baseStart_2610517 baseEnd_2610517 := by
    simpa [prefixWord, tailWord_2610517, baseEnd_2610517] using wordTrace_append hprefix tailTrace_2610517
  have hstable : (prefixWord ++ tailWord_2610517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610517).length < 2 ^ (prefixWord ++ tailWord_2610517).sum := by decide
  have hdescent : baseEnd_2610517 < baseStart_2610517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610541 : List Nat := [1, 5, 1, 1, 1, 3, 4, 2, 1, 1, 3]
def baseStart_2610541 : Nat := 118140960795 + 2610541 * 2 ^ 59
def prefixEnd_2610541 : Nat := 4983230072969 + 3 ^ 40 * 2610541 * 2
def baseEnd_2610541 : Nat := 1340462301268975980031847

theorem tailTrace_2610541 : CollatzResearch.WordTrace tailWord_2610541 prefixEnd_2610541 1340462301268975980031847 := by
  unfold tailWord_2610541
  simp only [CollatzResearch.WordTrace]
  refine ⟨95214252435463276752383477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63476168290308851168255651 95214252435463276752383477)
  ·
    refine ⟨8926336165824682195535951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95214252435463276752383477 8926336165824682195535951)
    ·
      refine ⟨13389504248737023293303927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8926336165824682195535951 13389504248737023293303927)
      ·
        refine ⟨20084256373105534939955891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13389504248737023293303927 20084256373105534939955891)
        ·
          refine ⟨30126384559658302409933837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20084256373105534939955891 30126384559658302409933837)
          ·
            refine ⟨11297394209871863403725189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30126384559658302409933837 11297394209871863403725189)
            ·
              refine ⟨2118261414350974388198473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11297394209871863403725189 2118261414350974388198473)
              ·
                refine ⟨1588696060763230791148855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2118261414350974388198473 1588696060763230791148855)
                ·
                  refine ⟨2383044091144846186723283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1588696060763230791148855 2383044091144846186723283)
                  ·
                    refine ⟨3574566136717269280084925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2383044091144846186723283 3574566136717269280084925)
                    ·
                      refine ⟨1340462301268975980031847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3574566136717269280084925 1340462301268975980031847)
                      ·
                        rfl

theorem cell23_2610541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_2610541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610541 prefixEnd_2610541 := by exact prefixLift 2610541
  have htrace : WordTrace (prefixWord ++ tailWord_2610541) baseStart_2610541 baseEnd_2610541 := by
    simpa [prefixWord, tailWord_2610541, baseEnd_2610541] using wordTrace_append hprefix tailTrace_2610541
  have hstable : (prefixWord ++ tailWord_2610541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610541).length < 2 ^ (prefixWord ++ tailWord_2610541).sum := by decide
  have hdescent : baseEnd_2610541 < baseStart_2610541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610543 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 4]
def baseStart_2610543 : Nat := 118140960795 + 2610543 * 2 ^ 59
def prefixEnd_2610543 : Nat := 4983230072969 + 3 ^ 40 * 2610543 * 2
def baseEnd_2610543 : Nat := 1340463328230284972206837

theorem tailTrace_2610543 : CollatzResearch.WordTrace tailWord_2610543 prefixEnd_2610543 1340463328230284972206837 := by
  unfold tailWord_2610543
  simp only [CollatzResearch.WordTrace]
  refine ⟨95214325381456031093956283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63476216920970687395970855 95214325381456031093956283)
  ·
    refine ⟨142821488072184046640934425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95214325381456031093956283 142821488072184046640934425)
    ·
      refine ⟨107116116054138034980700819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142821488072184046640934425 107116116054138034980700819)
      ·
        refine ⟨160674174081207052471051229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107116116054138034980700819 160674174081207052471051229)
        ·
          refine ⟨60252815280452644676644211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160674174081207052471051229 60252815280452644676644211)
          ·
            refine ⟨90379222920678967014966317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60252815280452644676644211 90379222920678967014966317)
            ·
              refine ⟨33892208595254612630612369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90379222920678967014966317 33892208595254612630612369)
              ·
                refine ⟨25419156446440959472959277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33892208595254612630612369 25419156446440959472959277)
                ·
                  refine ⟨9532183667415359802359729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25419156446440959472959277 9532183667415359802359729)
                  ·
                    refine ⟨7149137750561519851769797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9532183667415359802359729 7149137750561519851769797)
                    ·
                      refine ⟨1340463328230284972206837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7149137750561519851769797 1340463328230284972206837)
                      ·
                        rfl

theorem cell23_2610543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 4].length) (baseStart_2610543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610543 prefixEnd_2610543 := by exact prefixLift 2610543
  have htrace : WordTrace (prefixWord ++ tailWord_2610543) baseStart_2610543 baseEnd_2610543 := by
    simpa [prefixWord, tailWord_2610543, baseEnd_2610543] using wordTrace_append hprefix tailTrace_2610543
  have hstable : (prefixWord ++ tailWord_2610543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610543).length < 2 ^ (prefixWord ++ tailWord_2610543).sum := by decide
  have hdescent : baseEnd_2610543 < baseStart_2610543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610553 : List Nat := [1, 2, 1, 3, 2, 1, 5, 8]
def baseStart_2610553 : Nat := 118140960795 + 2610553 * 2 ^ 59
def prefixEnd_2610553 : Nat := 4983230072969 + 3 ^ 40 * 2610553 * 2
def baseEnd_2610553 : Nat := 49646980112475182706733

theorem tailTrace_2610553 : CollatzResearch.WordTrace tailWord_2610553 prefixEnd_2610553 49646980112475182706733 := by
  unfold tailWord_2610553
  simp only [CollatzResearch.WordTrace]
  refine ⟨95214690111419802801820313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63476460074279868534546875 95214690111419802801820313)
  ·
    refine ⟨71411017583564852101365235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95214690111419802801820313 71411017583564852101365235)
    ·
      refine ⟨107116526375347278152047853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71411017583564852101365235 107116526375347278152047853)
      ·
        refine ⟨40168697390755229307017945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107116526375347278152047853 40168697390755229307017945)
        ·
          refine ⟨30126523043066421980263459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40168697390755229307017945 30126523043066421980263459)
          ·
            refine ⟨45189784564599632970395189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30126523043066421980263459 45189784564599632970395189)
            ·
              refine ⟨4236542302931215590974549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45189784564599632970395189 4236542302931215590974549)
              ·
                refine ⟨49646980112475182706733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4236542302931215590974549 49646980112475182706733)
                ·
                  rfl

theorem cell23_2610553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 8].length) (baseStart_2610553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610553 prefixEnd_2610553 := by exact prefixLift 2610553
  have htrace : WordTrace (prefixWord ++ tailWord_2610553) baseStart_2610553 baseEnd_2610553 := by
    simpa [prefixWord, tailWord_2610553, baseEnd_2610553] using wordTrace_append hprefix tailTrace_2610553
  have hstable : (prefixWord ++ tailWord_2610553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610553).length < 2 ^ (prefixWord ++ tailWord_2610553).sum := by decide
  have hdescent : baseEnd_2610553 < baseStart_2610553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610564 : List Nat := [2, 3, 2, 1, 1, 4, 1, 2, 3, 2, 2]
def baseStart_2610564 : Nat := 118140960795 + 2610564 * 2 ^ 59
def prefixEnd_2610564 : Nat := 4983230072969 + 3 ^ 40 * 2610564 * 2
def baseEnd_2610564 : Nat := 1340474111324029390044241

theorem tailTrace_2610564 : CollatzResearch.WordTrace tailWord_2610564 prefixEnd_2610564 1340474111324029390044241 := by
  unfold tailWord_2610564
  simp only [CollatzResearch.WordTrace]
  refine ⟨47607545657189975840235373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63476727542919967786980497 47607545657189975840235373)
  ·
    refine ⟨17852829621446240940088265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47607545657189975840235373 17852829621446240940088265)
    ·
      refine ⟨13389622216084680705066199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17852829621446240940088265 13389622216084680705066199)
      ·
        refine ⟨20084433324127021057599299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13389622216084680705066199 20084433324127021057599299)
        ·
          refine ⟨30126649986190531586398949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20084433324127021057599299 30126649986190531586398949)
          ·
            refine ⟨5648746872410724672449803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30126649986190531586398949 5648746872410724672449803)
            ·
              refine ⟨8473120308616087008674705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5648746872410724672449803 8473120308616087008674705)
              ·
                refine ⟨6354840231462065256506029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8473120308616087008674705 6354840231462065256506029)
                ·
                  refine ⟨2383065086798274471189761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6354840231462065256506029 2383065086798274471189761)
                  ·
                    refine ⟨1787298815098705853392321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2383065086798274471189761 1787298815098705853392321)
                    ·
                      refine ⟨1340474111324029390044241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1787298815098705853392321 1340474111324029390044241)
                      ·
                        rfl

theorem cell23_2610564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_2610564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610564 prefixEnd_2610564 := by exact prefixLift 2610564
  have htrace : WordTrace (prefixWord ++ tailWord_2610564) baseStart_2610564 baseEnd_2610564 := by
    simpa [prefixWord, tailWord_2610564, baseEnd_2610564] using wordTrace_append hprefix tailTrace_2610564
  have hstable : (prefixWord ++ tailWord_2610564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610564).length < 2 ^ (prefixWord ++ tailWord_2610564).sum := by decide
  have hdescent : baseEnd_2610564 < baseStart_2610564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610578 : List Nat := [3, 2, 3, 3, 2, 1, 2, 1, 1, 5]
def baseStart_2610578 : Nat := 118140960795 + 2610578 * 2 ^ 59
def prefixEnd_2610578 : Nat := 4983230072969 + 3 ^ 40 * 2610578 * 2
def baseEnd_2610578 : Nat := 446827100017730778423059

theorem tailTrace_2610578 : CollatzResearch.WordTrace tailWord_2610578 prefixEnd_2610578 446827100017730778423059 := by
  unfold tailWord_2610578
  simp only [CollatzResearch.WordTrace]
  refine ⟨23803900484082308017870097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63477067957552821380986925 23803900484082308017870097)
  ·
    refine ⟨17852925363061731013402573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23803900484082308017870097 17852925363061731013402573)
    ·
      refine ⟨6694847011148149130025965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17852925363061731013402573 6694847011148149130025965)
      ·
        refine ⟨2510567629180555923759737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6694847011148149130025965 2510567629180555923759737)
        ·
          refine ⟨1882925721885416942819803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2510567629180555923759737 1882925721885416942819803)
          ·
            refine ⟨2824388582828125414229705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1882925721885416942819803 2824388582828125414229705)
            ·
              refine ⟨2118291437121094060672279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2824388582828125414229705 2118291437121094060672279)
              ·
                refine ⟨3177437155681641091008419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2118291437121094060672279 3177437155681641091008419)
                ·
                  refine ⟨4766155733522461636512629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3177437155681641091008419 4766155733522461636512629)
                  ·
                    refine ⟨446827100017730778423059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4766155733522461636512629 446827100017730778423059)
                    ·
                      rfl

theorem cell23_2610578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_2610578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610578 prefixEnd_2610578 := by exact prefixLift 2610578
  have htrace : WordTrace (prefixWord ++ tailWord_2610578) baseStart_2610578 baseEnd_2610578 := by
    simpa [prefixWord, tailWord_2610578, baseEnd_2610578] using wordTrace_append hprefix tailTrace_2610578
  have hstable : (prefixWord ++ tailWord_2610578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610578).length < 2 ^ (prefixWord ++ tailWord_2610578).sum := by decide
  have hdescent : baseEnd_2610578 < baseStart_2610578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610584 : List Nat := [2, 1, 2, 5, 2, 1, 1, 3, 1, 2, 3]
def baseStart_2610584 : Nat := 118140960795 + 2610584 * 2 ^ 59
def prefixEnd_2610584 : Nat := 4983230072969 + 3 ^ 40 * 2610584 * 2
def baseEnd_2610584 : Nat := 1340484380937119311794149

theorem tailTrace_2610584 : CollatzResearch.WordTrace tailWord_2610584 prefixEnd_2610584 1340484380937119311794149 := by
  unfold tailWord_2610584
  simp only [CollatzResearch.WordTrace]
  refine ⟨47607910387153747548099403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63477213849538330064132537 47607910387153747548099403)
  ·
    refine ⟨71411865580730621322149105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47607910387153747548099403 71411865580730621322149105)
    ·
      refine ⟨53558899185547965991611829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71411865580730621322149105 53558899185547965991611829)
      ·
        refine ⟨5021146798645121811713609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53558899185547965991611829 5021146798645121811713609)
        ·
          refine ⟨3765860098983841358785207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5021146798645121811713609 3765860098983841358785207)
          ·
            refine ⟨5648790148475762038177811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3765860098983841358785207 5648790148475762038177811)
            ·
              refine ⟨8473185222713643057266717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5648790148475762038177811 8473185222713643057266717)
              ·
                refine ⟨3177444458517616146475019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8473185222713643057266717 3177444458517616146475019)
                ·
                  refine ⟨4766166687776424219712529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3177444458517616146475019 4766166687776424219712529)
                  ·
                    refine ⟨3574625015832318164784397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4766166687776424219712529 3574625015832318164784397)
                    ·
                      refine ⟨1340484380937119311794149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3574625015832318164784397 1340484380937119311794149)
                      ·
                        rfl

theorem cell23_2610584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_2610584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610584 prefixEnd_2610584 := by exact prefixLift 2610584
  have htrace : WordTrace (prefixWord ++ tailWord_2610584) baseStart_2610584 baseEnd_2610584 := by
    simpa [prefixWord, tailWord_2610584, baseEnd_2610584] using wordTrace_append hprefix tailTrace_2610584
  have hstable : (prefixWord ++ tailWord_2610584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610584).length < 2 ^ (prefixWord ++ tailWord_2610584).sum := by decide
  have hdescent : baseEnd_2610584 < baseStart_2610584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610597 : List Nat := [1, 3, 1, 2, 1, 1, 2, 6, 2, 1, 3]
def baseStart_2610597 : Nat := 118140960795 + 2610597 * 2 ^ 59
def prefixEnd_2610597 : Nat := 4983230072969 + 3 ^ 40 * 2610597 * 2
def baseEnd_2610597 : Nat := 1340491056185627760931589

theorem tailTrace_2610597 : CollatzResearch.WordTrace tailWord_2610597 prefixEnd_2610597 1340491056185627760931589 := by
  unfold tailWord_2610597
  simp only [CollatzResearch.WordTrace]
  refine ⟨95216294923260398316422045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63477529948840265544281363 95216294923260398316422045)
  ·
    refine ⟨35706110596222649368658267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95216294923260398316422045 35706110596222649368658267)
    ·
      refine ⟨53559165894333974052987401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35706110596222649368658267 53559165894333974052987401)
      ·
        refine ⟨40169374420750480539740551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53559165894333974052987401 40169374420750480539740551)
        ·
          refine ⟨60254061631125720809610827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40169374420750480539740551 60254061631125720809610827)
          ·
            refine ⟨90381092446688581214416241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60254061631125720809610827 90381092446688581214416241)
            ·
              refine ⟨67785819335016435910812181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90381092446688581214416241 67785819335016435910812181)
              ·
                refine ⟨3177460281328895433319321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 67785819335016435910812181 3177460281328895433319321)
                ·
                  refine ⟨2383095210996671574989491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3177460281328895433319321 2383095210996671574989491)
                  ·
                    refine ⟨3574642816495007362484237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2383095210996671574989491 3574642816495007362484237)
                    ·
                      refine ⟨1340491056185627760931589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3574642816495007362484237 1340491056185627760931589)
                      ·
                        rfl

theorem cell23_2610597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 2, 1, 3].length) (baseStart_2610597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610597 prefixEnd_2610597 := by exact prefixLift 2610597
  have htrace : WordTrace (prefixWord ++ tailWord_2610597) baseStart_2610597 baseEnd_2610597 := by
    simpa [prefixWord, tailWord_2610597, baseEnd_2610597] using wordTrace_append hprefix tailTrace_2610597
  have hstable : (prefixWord ++ tailWord_2610597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610597).length < 2 ^ (prefixWord ++ tailWord_2610597).sum := by decide
  have hdescent : baseEnd_2610597 < baseStart_2610597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610603 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 4]
def baseStart_2610603 : Nat := 118140960795 + 2610603 * 2 ^ 59
def prefixEnd_2610603 : Nat := 4983230072969 + 3 ^ 40 * 2610603 * 2
def baseEnd_2610603 : Nat := 1340494137069554737456561

theorem tailTrace_2610603 : CollatzResearch.WordTrace tailWord_2610603 prefixEnd_2610603 1340494137069554737456561 := by
  unfold tailWord_2610603
  simp only [CollatzResearch.WordTrace]
  refine ⟨95216513761238661341140463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63477675840825774227426975 95216513761238661341140463)
  ·
    refine ⟨142824770641857992011710695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95216513761238661341140463 142824770641857992011710695)
    ·
      refine ⟨214237155962786988017566043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142824770641857992011710695 214237155962786988017566043)
      ·
        refine ⟨321355733944180482026349065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214237155962786988017566043 321355733944180482026349065)
        ·
          refine ⟨241016800458135361519761799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321355733944180482026349065 241016800458135361519761799)
          ·
            refine ⟨361525200687203042279642699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241016800458135361519761799 361525200687203042279642699)
            ·
              refine ⟨542287801030804563419464049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361525200687203042279642699 542287801030804563419464049)
              ·
                refine ⟨406715850773103422564598037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 542287801030804563419464049 406715850773103422564598037)
                ·
                  refine ⟨19064805504989222932715533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 406715850773103422564598037 19064805504989222932715533)
                  ·
                    refine ⟨7149302064370958599768325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19064805504989222932715533 7149302064370958599768325)
                    ·
                      refine ⟨1340494137069554737456561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7149302064370958599768325 1340494137069554737456561)
                      ·
                        rfl

theorem cell23_2610603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 4].length) (baseStart_2610603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610603 prefixEnd_2610603 := by exact prefixLift 2610603
  have htrace : WordTrace (prefixWord ++ tailWord_2610603) baseStart_2610603 baseEnd_2610603 := by
    simpa [prefixWord, tailWord_2610603, baseEnd_2610603] using wordTrace_append hprefix tailTrace_2610603
  have hstable : (prefixWord ++ tailWord_2610603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610603).length < 2 ^ (prefixWord ++ tailWord_2610603).sum := by decide
  have hdescent : baseEnd_2610603 < baseStart_2610603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610623 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 5]
def baseStart_2610623 : Nat := 118140960795 + 2610623 * 2 ^ 59
def prefixEnd_2610623 : Nat := 4983230072969 + 3 ^ 40 * 2610623 * 2
def baseEnd_2610623 : Nat := 1340504406682644659206469

theorem tailTrace_2610623 : CollatzResearch.WordTrace tailWord_2610623 prefixEnd_2610623 1340504406682644659206469 := by
  unfold tailWord_2610623
  simp only [CollatzResearch.WordTrace]
  refine ⟨95217243221166204756868523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63478162147444136504579015 95217243221166204756868523)
  ·
    refine ⟨142825864831749307135302785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95217243221166204756868523 142825864831749307135302785)
    ·
      refine ⟨107119398623811980351477089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142825864831749307135302785 107119398623811980351477089)
      ·
        refine ⟨80339548967858985263607817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107119398623811980351477089 80339548967858985263607817)
        ·
          refine ⟨60254661725894238947705863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80339548967858985263607817 60254661725894238947705863)
          ·
            refine ⟨90381992588841358421558795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60254661725894238947705863 90381992588841358421558795)
            ·
              refine ⟨135572988883262037632338193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90381992588841358421558795 135572988883262037632338193)
              ·
                refine ⟨101679741662446528224253645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135572988883262037632338193 101679741662446528224253645)
                ·
                  refine ⟨38129903123417448084095117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101679741662446528224253645 38129903123417448084095117)
                  ·
                    refine ⟨14298713671281543031535669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38129903123417448084095117 14298713671281543031535669)
                    ·
                      refine ⟨1340504406682644659206469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14298713671281543031535669 1340504406682644659206469)
                      ·
                        rfl

theorem cell23_2610623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_2610623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610623 prefixEnd_2610623 := by exact prefixLift 2610623
  have htrace : WordTrace (prefixWord ++ tailWord_2610623) baseStart_2610623 baseEnd_2610623 := by
    simpa [prefixWord, tailWord_2610623, baseEnd_2610623] using wordTrace_append hprefix tailTrace_2610623
  have hstable : (prefixWord ++ tailWord_2610623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610623).length < 2 ^ (prefixWord ++ tailWord_2610623).sum := by decide
  have hdescent : baseEnd_2610623 < baseStart_2610623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610671 : List Nat := [1, 1, 2, 1, 4, 1, 6, 1, 2, 2, 2]
def baseStart_2610671 : Nat := 118140960795 + 2610671 * 2 ^ 59
def prefixEnd_2610671 : Nat := 4983230072969 + 3 ^ 40 * 2610671 * 2
def baseEnd_2610671 : Nat := 1340529053754060471406249

theorem tailTrace_2610671 : CollatzResearch.WordTrace tailWord_2610671 prefixEnd_2610671 1340529053754060471406249 := by
  unfold tailWord_2610671
  simp only [CollatzResearch.WordTrace]
  refine ⟨95218993924992308954615867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63479329283328205969743911 95218993924992308954615867)
  ·
    refine ⟨142828490887488463431923801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95218993924992308954615867 142828490887488463431923801)
    ·
      refine ⟨107121368165616347573942851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142828490887488463431923801 107121368165616347573942851)
      ·
        refine ⟨160682052248424521360914277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107121368165616347573942851 160682052248424521360914277)
        ·
          refine ⟨30127884796579597755171427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 160682052248424521360914277 30127884796579597755171427)
          ·
            refine ⟨45191827194869396632757141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30127884796579597755171427 45191827194869396632757141)
            ·
              refine ⟨2118366899759502967160491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 45191827194869396632757141 2118366899759502967160491)
              ·
                refine ⟨3177550349639254450740737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2118366899759502967160491 3177550349639254450740737)
                ·
                  refine ⟨2383162762229440838055553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3177550349639254450740737 2383162762229440838055553)
                  ·
                    refine ⟨1787372071672080628541665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2383162762229440838055553 1787372071672080628541665)
                    ·
                      refine ⟨1340529053754060471406249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1787372071672080628541665 1340529053754060471406249)
                      ·
                        rfl

theorem cell23_2610671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 2, 2, 2].length) (baseStart_2610671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610671 prefixEnd_2610671 := by exact prefixLift 2610671
  have htrace : WordTrace (prefixWord ++ tailWord_2610671) baseStart_2610671 baseEnd_2610671 := by
    simpa [prefixWord, tailWord_2610671, baseEnd_2610671] using wordTrace_append hprefix tailTrace_2610671
  have hstable : (prefixWord ++ tailWord_2610671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610671).length < 2 ^ (prefixWord ++ tailWord_2610671).sum := by decide
  have hdescent : baseEnd_2610671 < baseStart_2610671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610718 : List Nat := [4, 3, 3, 1, 1, 1, 1, 1, 2, 2, 4]
def baseStart_2610718 : Nat := 118140960795 + 2610718 * 2 ^ 59
def prefixEnd_2610718 : Nat := 4983230072969 + 3 ^ 40 * 2610718 * 2
def baseEnd_2610718 : Nat := 1340553187344821787518533

theorem tailTrace_2610718 : CollatzResearch.WordTrace tailWord_2610718 prefixEnd_2610718 1340553187344821787518533 := by
  unfold tailWord_2610718
  simp only [CollatzResearch.WordTrace]
  refine ⟨11902588519477754497697101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63480472103881357321051205 11902588519477754497697101)
  ·
    refine ⟨4463470694804157936636413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11902588519477754497697101 4463470694804157936636413)
    ·
      refine ⟨1673801510551559226238655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4463470694804157936636413 1673801510551559226238655)
      ·
        refine ⟨2510702265827338839357983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1673801510551559226238655 2510702265827338839357983)
        ·
          refine ⟨3766053398741008259036975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2510702265827338839357983 3766053398741008259036975)
          ·
            refine ⟨5649080098111512388555463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3766053398741008259036975 5649080098111512388555463)
            ·
              refine ⟨8473620147167268582833195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5649080098111512388555463 8473620147167268582833195)
              ·
                refine ⟨12710430220750902874249793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8473620147167268582833195 12710430220750902874249793)
                ·
                  refine ⟨9532822665563177155687345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12710430220750902874249793 9532822665563177155687345)
                  ·
                    refine ⟨7149616999172382866765509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9532822665563177155687345 7149616999172382866765509)
                    ·
                      refine ⟨1340553187344821787518533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7149616999172382866765509 1340553187344821787518533)
                      ·
                        rfl

theorem cell23_2610718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_2610718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610718 prefixEnd_2610718 := by exact prefixLift 2610718
  have htrace : WordTrace (prefixWord ++ tailWord_2610718) baseStart_2610718 baseEnd_2610718 := by
    simpa [prefixWord, tailWord_2610718, baseEnd_2610718] using wordTrace_append hprefix tailTrace_2610718
  have hstable : (prefixWord ++ tailWord_2610718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610718).length < 2 ^ (prefixWord ++ tailWord_2610718).sum := by decide
  have hdescent : baseEnd_2610718 < baseStart_2610718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610744 : List Nat := [2, 1, 2, 1, 4, 4, 1, 1, 2, 1, 4]
def baseStart_2610744 : Nat := 118140960795 + 2610744 * 2 ^ 59
def prefixEnd_2610744 : Nat := 4983230072969 + 3 ^ 40 * 2610744 * 2
def baseEnd_2610744 : Nat := 1340566537841838685793413

theorem tailTrace_2610744 : CollatzResearch.WordTrace tailWord_2610744 prefixEnd_2610744 1340566537841838685793413 := by
  unfold tailWord_2610744
  simp only [CollatzResearch.WordTrace]
  refine ⟨47610828226863921211011643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63481104302485228281348857 47610828226863921211011643)
  ·
    refine ⟨71416242340295881816517465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47610828226863921211011643 71416242340295881816517465)
    ·
      refine ⟨53562181755221911362388099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71416242340295881816517465 53562181755221911362388099)
      ·
        refine ⟨80343272632832867043582149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53562181755221911362388099 80343272632832867043582149)
        ·
          refine ⟨15064363618656162570671653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80343272632832867043582149 15064363618656162570671653)
          ·
            refine ⟨2824568178498030482000935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15064363618656162570671653 2824568178498030482000935)
            ·
              refine ⟨4236852267747045723001403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2824568178498030482000935 4236852267747045723001403)
              ·
                refine ⟨6355278401620568584502105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4236852267747045723001403 6355278401620568584502105)
                ·
                  refine ⟨4766458801215426438376579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6355278401620568584502105 4766458801215426438376579)
                  ·
                    refine ⟨7149688201823139657564869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4766458801215426438376579 7149688201823139657564869)
                    ·
                      refine ⟨1340566537841838685793413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7149688201823139657564869 1340566537841838685793413)
                      ·
                        rfl

theorem cell23_2610744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 2, 1, 4].length) (baseStart_2610744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610744 prefixEnd_2610744 := by exact prefixLift 2610744
  have htrace : WordTrace (prefixWord ++ tailWord_2610744) baseStart_2610744 baseEnd_2610744 := by
    simpa [prefixWord, tailWord_2610744, baseEnd_2610744] using wordTrace_append hprefix tailTrace_2610744
  have hstable : (prefixWord ++ tailWord_2610744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610744).length < 2 ^ (prefixWord ++ tailWord_2610744).sum := by decide
  have hdescent : baseEnd_2610744 < baseStart_2610744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610827 : List Nat := [1, 1, 1, 1, 4, 1, 3, 3, 4, 4]
def baseStart_2610827 : Nat := 118140960795 + 2610827 * 2 ^ 59
def prefixEnd_2610827 : Nat := 4983230072969 + 3 ^ 40 * 2610827 * 2
def baseEnd_2610827 : Nat := 446869718912053953685177

theorem tailTrace_2610827 : CollatzResearch.WordTrace tailWord_2610827 prefixEnd_2610827 446869718912053953685177 := by
  unfold tailWord_2610827
  simp only [CollatzResearch.WordTrace]
  refine ⟨95224683712427147597294735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63483122474951431731529823 95224683712427147597294735)
  ·
    refine ⟨142837025568640721395942103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95224683712427147597294735 142837025568640721395942103)
    ·
      refine ⟨214255538352961082093913155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142837025568640721395942103 214255538352961082093913155)
      ·
        refine ⟨321383307529441623140869733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214255538352961082093913155 321383307529441623140869733)
        ·
          refine ⟨60259370161770304338913075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 321383307529441623140869733 60259370161770304338913075)
          ·
            refine ⟨90389055242655456508369613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60259370161770304338913075 90389055242655456508369613)
            ·
              refine ⟨33895895715995796190638605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90389055242655456508369613 33895895715995796190638605)
              ·
                refine ⟨12710960893498423571489477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33895895715995796190638605 12710960893498423571489477)
                ·
                  refine ⟨2383305167530954419654277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12710960893498423571489477 2383305167530954419654277)
                  ·
                    refine ⟨446869718912053953685177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2383305167530954419654277 446869718912053953685177)
                    ·
                      rfl

theorem cell23_2610827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 4, 4].length) (baseStart_2610827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610827 prefixEnd_2610827 := by exact prefixLift 2610827
  have htrace : WordTrace (prefixWord ++ tailWord_2610827) baseStart_2610827 baseEnd_2610827 := by
    simpa [prefixWord, tailWord_2610827, baseEnd_2610827] using wordTrace_append hprefix tailTrace_2610827
  have hstable : (prefixWord ++ tailWord_2610827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610827).length < 2 ^ (prefixWord ++ tailWord_2610827).sum := by decide
  have hdescent : baseEnd_2610827 < baseStart_2610827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610828 : List Nat := [2, 2, 1, 2, 1, 1, 7, 2, 1, 1, 3]
def baseStart_2610828 : Nat := 118140960795 + 2610828 * 2 ^ 59
def prefixEnd_2610828 : Nat := 4983230072969 + 3 ^ 40 * 2610828 * 2
def baseEnd_2610828 : Nat := 1340609670216816357143027

theorem tailTrace_2610828 : CollatzResearch.WordTrace tailWord_2610828 prefixEnd_2610828 1340609670216816357143027 := by
  unfold tailWord_2610828
  simp only [CollatzResearch.WordTrace]
  refine ⟨47612360092711762384040569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63483146790282349845387425 47612360092711762384040569)
  ·
    refine ⟨35709270069533821788030427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47612360092711762384040569 35709270069533821788030427)
    ·
      refine ⟨53563905104300732682045641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35709270069533821788030427 53563905104300732682045641)
      ·
        refine ⟨40172928828225549511534231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53563905104300732682045641 40172928828225549511534231)
        ·
          refine ⟨60259393242338324267301347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40172928828225549511534231 60259393242338324267301347)
          ·
            refine ⟨90389089863507486400952021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60259393242338324267301347 90389089863507486400952021)
            ·
              refine ⟨2118494293675956712522313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 90389089863507486400952021 2118494293675956712522313)
              ·
                refine ⟨1588870720256967534391735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2118494293675956712522313 1588870720256967534391735)
                ·
                  refine ⟨2383306080385451301587603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1588870720256967534391735 2383306080385451301587603)
                  ·
                    refine ⟨3574959120578176952381405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2383306080385451301587603 3574959120578176952381405)
                    ·
                      refine ⟨1340609670216816357143027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3574959120578176952381405 1340609670216816357143027)
                      ·
                        rfl

theorem cell23_2610828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 2, 1, 1, 3].length) (baseStart_2610828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610828 prefixEnd_2610828 := by exact prefixLift 2610828
  have htrace : WordTrace (prefixWord ++ tailWord_2610828) baseStart_2610828 baseEnd_2610828 := by
    simpa [prefixWord, tailWord_2610828, baseEnd_2610828] using wordTrace_append hprefix tailTrace_2610828
  have hstable : (prefixWord ++ tailWord_2610828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610828).length < 2 ^ (prefixWord ++ tailWord_2610828).sum := by decide
  have hdescent : baseEnd_2610828 < baseStart_2610828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610884 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 3, 3, 3]
def baseStart_2610884 : Nat := 118140960795 + 2610884 * 2 ^ 59
def prefixEnd_2610884 : Nat := 4983230072969 + 3 ^ 40 * 2610884 * 2
def baseEnd_2610884 : Nat := 1340638425133468138042769

theorem tailTrace_2610884 : CollatzResearch.WordTrace tailWord_2610884 prefixEnd_2610884 1340638425133468138042769 := by
  unfold tailWord_2610884
  simp only [CollatzResearch.WordTrace]
  refine ⟨47613381336610323166059853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63484508448813764221413137 47613381336610323166059853)
  ·
    refine ⟨17855018001228871187272445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47613381336610323166059853 17855018001228871187272445)
    ·
      refine ⟨6695631750460826695227167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17855018001228871187272445 6695631750460826695227167)
      ·
        refine ⟨10043447625691240042840751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6695631750460826695227167 10043447625691240042840751)
        ·
          refine ⟨15065171438536860064261127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10043447625691240042840751 15065171438536860064261127)
          ·
            refine ⟨22597757157805290096391691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15065171438536860064261127 22597757157805290096391691)
            ·
              refine ⟨33896635736707935144587537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22597757157805290096391691 33896635736707935144587537)
              ·
                refine ⟨25422476802530951358440653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33896635736707935144587537 25422476802530951358440653)
                ·
                  refine ⟨9533428800949106759415245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25422476802530951358440653 9533428800949106759415245)
                  ·
                    refine ⟨3575035800355915034780717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9533428800949106759415245 3575035800355915034780717)
                    ·
                      refine ⟨1340638425133468138042769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3575035800355915034780717 1340638425133468138042769)
                      ·
                        rfl

theorem cell23_2610884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_2610884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610884 prefixEnd_2610884 := by exact prefixLift 2610884
  have htrace : WordTrace (prefixWord ++ tailWord_2610884) baseStart_2610884 baseEnd_2610884 := by
    simpa [prefixWord, tailWord_2610884, baseEnd_2610884] using wordTrace_append hprefix tailTrace_2610884
  have hstable : (prefixWord ++ tailWord_2610884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610884).length < 2 ^ (prefixWord ++ tailWord_2610884).sum := by decide
  have hdescent : baseEnd_2610884 < baseStart_2610884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610902 : List Nat := [5, 2, 1, 3, 1, 1, 1, 2, 3, 2, 2]
def baseStart_2610902 : Nat := 118140960795 + 2610902 * 2 ^ 59
def prefixEnd_2610902 : Nat := 4983230072969 + 3 ^ 40 * 2610902 * 2
def baseEnd_2610902 : Nat := 1340647667785249067617687

theorem tailTrace_2610902 : CollatzResearch.WordTrace tailWord_2610902 prefixEnd_2610902 1340647667785249067617687 := by
  unfold tailWord_2610902
  simp only [CollatzResearch.WordTrace]
  refine ⟨5951713699197214712892185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63484946124770290270849973 5951713699197214712892185)
  ·
    refine ⟨4463785274397911034669139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5951713699197214712892185 4463785274397911034669139)
    ·
      refine ⟨6695677911596866552003709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4463785274397911034669139 6695677911596866552003709)
      ·
        refine ⟨2510879216848824957001391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6695677911596866552003709 2510879216848824957001391)
        ·
          refine ⟨3766318825273237435502087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2510879216848824957001391 3766318825273237435502087)
          ·
            refine ⟨5649478237909856153253131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3766318825273237435502087 5649478237909856153253131)
            ·
              refine ⟨8474217356864784229879697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5649478237909856153253131 8474217356864784229879697)
              ·
                refine ⟨6355663017648588172409773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8474217356864784229879697 6355663017648588172409773)
                ·
                  refine ⟨2383373631618220564653665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6355663017648588172409773 2383373631618220564653665)
                  ·
                    refine ⟨1787530223713665423490249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2383373631618220564653665 1787530223713665423490249)
                    ·
                      refine ⟨1340647667785249067617687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1787530223713665423490249 1340647667785249067617687)
                      ·
                        rfl

theorem cell23_2610902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_2610902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610902 prefixEnd_2610902 := by exact prefixLift 2610902
  have htrace : WordTrace (prefixWord ++ tailWord_2610902) baseStart_2610902 baseEnd_2610902 := by
    simpa [prefixWord, tailWord_2610902, baseEnd_2610902] using wordTrace_append hprefix tailTrace_2610902
  have hstable : (prefixWord ++ tailWord_2610902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610902).length < 2 ^ (prefixWord ++ tailWord_2610902).sum := by decide
  have hdescent : baseEnd_2610902 < baseStart_2610902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610911 : List Nat := [1, 1, 2, 3, 2, 2, 2, 4, 1, 3, 2]
def baseStart_2610911 : Nat := 118140960795 + 2610911 * 2 ^ 59
def prefixEnd_2610911 : Nat := 4983230072969 + 3 ^ 40 * 2610911 * 2
def baseEnd_2610911 : Nat := 1340652289111139532405145

theorem tailTrace_2610911 : CollatzResearch.WordTrace tailWord_2610911 prefixEnd_2610911 1340652289111139532405145 := by
  unfold tailWord_2610911
  simp only [CollatzResearch.WordTrace]
  refine ⟨95227747444122829943352587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63485164962748553295568391 95227747444122829943352587)
  ·
    refine ⟨142841621166184244915028881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95227747444122829943352587 142841621166184244915028881)
    ·
      refine ⟨107131215874638183686271661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142841621166184244915028881 107131215874638183686271661)
      ·
        refine ⟨40174205952989318882351873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107131215874638183686271661 40174205952989318882351873)
        ·
          refine ⟨30130654464741989161763905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40174205952989318882351873 30130654464741989161763905)
          ·
            refine ⟨22597990848556491871322929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30130654464741989161763905 22597990848556491871322929)
            ·
              refine ⟨16948493136417368903492197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22597990848556491871322929 16948493136417368903492197)
              ·
                refine ⟨3177842463078256669404787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16948493136417368903492197 3177842463078256669404787)
                ·
                  refine ⟨4766763694617385004107181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3177842463078256669404787 4766763694617385004107181)
                  ·
                    refine ⟨1787536385481519376540193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4766763694617385004107181 1787536385481519376540193)
                    ·
                      refine ⟨1340652289111139532405145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1787536385481519376540193 1340652289111139532405145)
                      ·
                        rfl

theorem cell23_2610911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 3, 2].length) (baseStart_2610911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610911 prefixEnd_2610911 := by exact prefixLift 2610911
  have htrace : WordTrace (prefixWord ++ tailWord_2610911) baseStart_2610911 baseEnd_2610911 := by
    simpa [prefixWord, tailWord_2610911, baseEnd_2610911] using wordTrace_append hprefix tailTrace_2610911
  have hstable : (prefixWord ++ tailWord_2610911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610911).length < 2 ^ (prefixWord ++ tailWord_2610911).sum := by decide
  have hdescent : baseEnd_2610911 < baseStart_2610911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610917 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 1, 8]
def baseStart_2610917 : Nat := 118140960795 + 2610917 * 2 ^ 59
def prefixEnd_2610917 : Nat := 4983230072969 + 3 ^ 40 * 2610917 * 2
def baseEnd_2610917 : Nat := 446885123331688836310039

theorem tailTrace_2610917 : CollatzResearch.WordTrace tailWord_2610917 prefixEnd_2610917 446885123331688836310039 := by
  unfold tailWord_2610917
  simp only [CollatzResearch.WordTrace]
  refine ⟨95227966282101092968071005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63485310854734061978714003 95227966282101092968071005)
  ·
    refine ⟨35710487355787909863026627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95227966282101092968071005 35710487355787909863026627)
    ·
      refine ⟨53565731033681864794539941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35710487355787909863026627 53565731033681864794539941)
      ·
        refine ⟨10043574568815349648976239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53565731033681864794539941 10043574568815349648976239)
        ·
          refine ⟨15065361853223024473464359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10043574568815349648976239 15065361853223024473464359)
          ·
            refine ⟨22598042779834536710196539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15065361853223024473464359 22598042779834536710196539)
            ·
              refine ⟨33897064169751805065294809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22598042779834536710196539 33897064169751805065294809)
              ·
                refine ⟨25422798127313853798971107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33897064169751805065294809 25422798127313853798971107)
                ·
                  refine ⟨38134197190970780698456661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25422798127313853798971107 38134197190970780698456661)
                  ·
                    refine ⟨446885123331688836310039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38134197190970780698456661 446885123331688836310039)
                    ·
                      rfl

theorem cell23_2610917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 8].length) (baseStart_2610917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610917 prefixEnd_2610917 := by exact prefixLift 2610917
  have htrace : WordTrace (prefixWord ++ tailWord_2610917) baseStart_2610917 baseEnd_2610917 := by
    simpa [prefixWord, tailWord_2610917, baseEnd_2610917] using wordTrace_append hprefix tailTrace_2610917
  have hstable : (prefixWord ++ tailWord_2610917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610917).length < 2 ^ (prefixWord ++ tailWord_2610917).sum := by decide
  have hdescent : baseEnd_2610917 < baseStart_2610917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610927 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 5]
def baseStart_2610927 : Nat := 118140960795 + 2610927 * 2 ^ 59
def prefixEnd_2610927 : Nat := 4983230072969 + 3 ^ 40 * 2610927 * 2
def baseEnd_2610927 : Nat := 1340660504801611469805071

theorem tailTrace_2610927 : CollatzResearch.WordTrace tailWord_2610927 prefixEnd_2610927 1340660504801611469805071 := by
  unfold tailWord_2610927
  simp only [CollatzResearch.WordTrace]
  refine ⟨95228331012064864675935035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63485554008043243117290023 95228331012064864675935035)
  ·
    refine ⟨142842496518097297013902553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95228331012064864675935035 142842496518097297013902553)
    ·
      refine ⟨107131872388572972760426915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142842496518097297013902553 107131872388572972760426915)
      ·
        refine ⟨160697808582859459140640373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107131872388572972760426915 160697808582859459140640373)
        ·
          refine ⟨15065419554643074294435035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 160697808582859459140640373 15065419554643074294435035)
          ·
            refine ⟨22598129331964611441652553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15065419554643074294435035 22598129331964611441652553)
            ·
              refine ⟨16948596998973458581239415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22598129331964611441652553 16948596998973458581239415)
              ·
                refine ⟨25422895498460187871859123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16948596998973458581239415 25422895498460187871859123)
                ·
                  refine ⟨38134343247690281807788685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25422895498460187871859123 38134343247690281807788685)
                  ·
                    refine ⟨14300378717883855677920757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38134343247690281807788685 14300378717883855677920757)
                    ·
                      refine ⟨1340660504801611469805071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14300378717883855677920757 1340660504801611469805071)
                      ·
                        rfl

theorem cell23_2610927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 5].length) (baseStart_2610927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610927 prefixEnd_2610927 := by exact prefixLift 2610927
  have htrace : WordTrace (prefixWord ++ tailWord_2610927) baseStart_2610927 baseEnd_2610927 := by
    simpa [prefixWord, tailWord_2610927, baseEnd_2610927] using wordTrace_append hprefix tailTrace_2610927
  have hstable : (prefixWord ++ tailWord_2610927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610927).length < 2 ^ (prefixWord ++ tailWord_2610927).sum := by decide
  have hdescent : baseEnd_2610927 < baseStart_2610927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610934 : List Nat := [5, 1, 1, 1, 1, 3, 1, 2, 2, 6]
def baseStart_2610934 : Nat := 118140960795 + 2610934 * 2 ^ 59
def prefixEnd_2610934 : Nat := 4983230072969 + 3 ^ 40 * 2610934 * 2
def baseEnd_2610934 : Nat := 446888033055397647472513

theorem tailTrace_2610934 : CollatzResearch.WordTrace tailWord_2610934 prefixEnd_2610934 446888033055397647472513 := by
  unfold tailWord_2610934
  simp only [CollatzResearch.WordTrace]
  refine ⟨5951786645189969054464991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63485724215359669914293237 5951786645189969054464991)
  ·
    refine ⟨8927679967784953581697487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5951786645189969054464991 8927679967784953581697487)
    ·
      refine ⟨13391519951677430372546231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8927679967784953581697487 13391519951677430372546231)
      ·
        refine ⟨20087279927516145558819347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13391519951677430372546231 20087279927516145558819347)
        ·
          refine ⟨30130919891274218338229021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20087279927516145558819347 30130919891274218338229021)
          ·
            refine ⟨11299094959227831876835883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30130919891274218338229021 11299094959227831876835883)
            ·
              refine ⟨16948642438841747815253825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11299094959227831876835883 16948642438841747815253825)
              ·
                refine ⟨12711481829131310861440369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16948642438841747815253825 12711481829131310861440369)
                ·
                  refine ⟨9533611371848483146080277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12711481829131310861440369 9533611371848483146080277)
                  ·
                    refine ⟨446888033055397647472513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9533611371848483146080277 446888033055397647472513)
                    ·
                      rfl

theorem cell23_2610934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_2610934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610934 prefixEnd_2610934 := by exact prefixLift 2610934
  have htrace : WordTrace (prefixWord ++ tailWord_2610934) baseStart_2610934 baseEnd_2610934 := by
    simpa [prefixWord, tailWord_2610934, baseEnd_2610934] using wordTrace_append hprefix tailTrace_2610934
  have hstable : (prefixWord ++ tailWord_2610934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610934).length < 2 ^ (prefixWord ++ tailWord_2610934).sum := by decide
  have hdescent : baseEnd_2610934 < baseStart_2610934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610947 : List Nat := [1, 1, 1, 3, 2, 2, 3, 3, 7]
def baseStart_2610947 : Nat := 118140960795 + 2610947 * 2 ^ 59
def prefixEnd_2610947 : Nat := 4983230072969 + 3 ^ 40 * 2610947 * 2
def baseEnd_2610947 : Nat := 148963419379411265728331

theorem tailTrace_2610947 : CollatzResearch.WordTrace tailWord_2610947 prefixEnd_2610947 148963419379411265728331 := by
  unfold tailWord_2610947
  simp only [CollatzResearch.WordTrace]
  refine ⟨95229060471992408091663095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63486040314661605394442063 95229060471992408091663095)
  ·
    refine ⟨142843590707988612137494643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95229060471992408091663095 142843590707988612137494643)
    ·
      refine ⟨214265386061982918206241965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142843590707988612137494643 214265386061982918206241965)
      ·
        refine ⟨80349519773243594327340737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214265386061982918206241965 80349519773243594327340737)
        ·
          refine ⟨60262139829932695745505553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80349519773243594327340737 60262139829932695745505553)
          ·
            refine ⟨45196604872449521809129165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60262139829932695745505553 45196604872449521809129165)
            ·
              refine ⟨16948726827168570678423437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45196604872449521809129165 16948726827168570678423437)
              ·
                refine ⟨6355772560188214004408789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16948726827168570678423437 6355772560188214004408789)
                ·
                  refine ⟨148963419379411265728331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6355772560188214004408789 148963419379411265728331)
                  ·
                    rfl

theorem cell23_2610947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 7].length) (baseStart_2610947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610947 prefixEnd_2610947 := by exact prefixLift 2610947
  have htrace : WordTrace (prefixWord ++ tailWord_2610947) baseStart_2610947 baseEnd_2610947 := by
    simpa [prefixWord, tailWord_2610947, baseEnd_2610947] using wordTrace_append hprefix tailTrace_2610947
  have hstable : (prefixWord ++ tailWord_2610947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610947).length < 2 ^ (prefixWord ++ tailWord_2610947).sum := by decide
  have hdescent : baseEnd_2610947 < baseStart_2610947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610954 : List Nat := [3, 1, 2, 2, 1, 3, 2, 1, 2, 2, 4]
def baseStart_2610954 : Nat := 118140960795 + 2610954 * 2 ^ 59
def prefixEnd_2610954 : Nat := 4983230072969 + 3 ^ 40 * 2610954 * 2
def baseEnd_2610954 : Nat := 1340674368779282864167447

theorem tailTrace_2610954 : CollatzResearch.WordTrace tailWord_2610954 prefixEnd_2610954 1340674368779282864167447 := by
  unfold tailWord_2610954
  simp only [CollatzResearch.WordTrace]
  refine ⟨23807328945741762071791979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63486210521978032191445277 23807328945741762071791979)
  ·
    refine ⟨35710993418612643107687969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23807328945741762071791979 35710993418612643107687969)
    ·
      refine ⟨26783245063959482330765977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35710993418612643107687969 26783245063959482330765977)
      ·
        refine ⟨20087433797969611748074483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26783245063959482330765977 20087433797969611748074483)
        ·
          refine ⟨30131150696954417622111725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20087433797969611748074483 30131150696954417622111725)
          ·
            refine ⟨11299181511357906608291897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30131150696954417622111725 11299181511357906608291897)
            ·
              refine ⟨8474386133518429956218923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11299181511357906608291897 8474386133518429956218923)
              ·
                refine ⟨12711579200277644934328385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8474386133518429956218923 12711579200277644934328385)
                ·
                  refine ⟨9533684400208233700746289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12711579200277644934328385 9533684400208233700746289)
                  ·
                    refine ⟨7150263300156175275559717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9533684400208233700746289 7150263300156175275559717)
                    ·
                      refine ⟨1340674368779282864167447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7150263300156175275559717 1340674368779282864167447)
                      ·
                        rfl

theorem cell23_2610954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_2610954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610954 prefixEnd_2610954 := by exact prefixLift 2610954
  have htrace : WordTrace (prefixWord ++ tailWord_2610954) baseStart_2610954 baseEnd_2610954 := by
    simpa [prefixWord, tailWord_2610954, baseEnd_2610954] using wordTrace_append hprefix tailTrace_2610954
  have hstable : (prefixWord ++ tailWord_2610954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610954).length < 2 ^ (prefixWord ++ tailWord_2610954).sum := by decide
  have hdescent : baseEnd_2610954 < baseStart_2610954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610958 : List Nat := [4, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2]
def baseStart_2610958 : Nat := 118140960795 + 2610958 * 2 ^ 59
def prefixEnd_2610958 : Nat := 4983230072969 + 3 ^ 40 * 2610958 * 2
def baseEnd_2610958 : Nat := 1340676422701900848517429

theorem tailTrace_2610958 : CollatzResearch.WordTrace tailWord_2610958 prefixEnd_2610958 1340676422701900848517429 := by
  unfold tailWord_2610958
  simp only [CollatzResearch.WordTrace]
  refine ⟨11903682709369069621289191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63486307783301704646875685 11903682709369069621289191)
  ·
    refine ⟨17855524064053604431933787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11903682709369069621289191 17855524064053604431933787)
    ·
      refine ⟨26783286096080406647900681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17855524064053604431933787 26783286096080406647900681)
      ·
        refine ⟨20087464572060304985925511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26783286096080406647900681 20087464572060304985925511)
        ·
          refine ⟨30131196858090457478888267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20087464572060304985925511 30131196858090457478888267)
          ·
            refine ⟨45196795287135686218332401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30131196858090457478888267 45196795287135686218332401)
            ·
              refine ⟨33897596465351764663749301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45196795287135686218332401 33897596465351764663749301)
              ·
                refine ⟨3177899668626727937226497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33897596465351764663749301 3177899668626727937226497)
                ·
                  refine ⟨2383424751470045952919873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3177899668626727937226497 2383424751470045952919873)
                  ·
                    refine ⟨1787568563602534464689905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2383424751470045952919873 1787568563602534464689905)
                    ·
                      refine ⟨1340676422701900848517429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1787568563602534464689905 1340676422701900848517429)
                      ·
                        rfl

theorem cell23_2610958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_2610958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610958 prefixEnd_2610958 := by exact prefixLift 2610958
  have htrace : WordTrace (prefixWord ++ tailWord_2610958) baseStart_2610958 baseEnd_2610958 := by
    simpa [prefixWord, tailWord_2610958, baseEnd_2610958] using wordTrace_append hprefix tailTrace_2610958
  have hstable : (prefixWord ++ tailWord_2610958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610958).length < 2 ^ (prefixWord ++ tailWord_2610958).sum := by decide
  have hdescent : baseEnd_2610958 < baseStart_2610958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610981 : List Nat := [1, 3, 1, 2, 3, 2, 3, 3, 5]
def baseStart_2610981 : Nat := 118140960795 + 2610981 * 2 ^ 59
def prefixEnd_2610981 : Nat := 4983230072969 + 3 ^ 40 * 2610981 * 2
def baseEnd_2610981 : Nat := 148965359195217139836647

theorem tailTrace_2610981 : CollatzResearch.WordTrace tailWord_2610981 prefixEnd_2610981 148965359195217139836647 := by
  unfold tailWord_2610981
  simp only [CollatzResearch.WordTrace]
  refine ⟨95230300553869231898400797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63486867035912821265600531 95230300553869231898400797)
  ·
    refine ⟨35711362707700961961900299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95230300553869231898400797 35711362707700961961900299)
    ·
      refine ⟨53567044061551442942850449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35711362707700961961900299 53567044061551442942850449)
      ·
        refine ⟨40175283046163582207137837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53567044061551442942850449 40175283046163582207137837)
        ·
          refine ⟨15065731142311343327676689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40175283046163582207137837 15065731142311343327676689)
          ·
            refine ⟨11299298356733507495757517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15065731142311343327676689 11299298356733507495757517)
            ·
              refine ⟨4237236883775065310909069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11299298356733507495757517 4237236883775065310909069)
              ·
                refine ⟨1588963831415649491590901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4237236883775065310909069 1588963831415649491590901)
                ·
                  refine ⟨148965359195217139836647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1588963831415649491590901 148965359195217139836647)
                  ·
                    rfl

theorem cell23_2610981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 3, 5].length) (baseStart_2610981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610981 prefixEnd_2610981 := by exact prefixLift 2610981
  have htrace : WordTrace (prefixWord ++ tailWord_2610981) baseStart_2610981 baseEnd_2610981 := by
    simpa [prefixWord, tailWord_2610981, baseEnd_2610981] using wordTrace_append hprefix tailTrace_2610981
  have hstable : (prefixWord ++ tailWord_2610981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610981).length < 2 ^ (prefixWord ++ tailWord_2610981).sum := by decide
  have hdescent : baseEnd_2610981 < baseStart_2610981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610994 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 4, 5]
def baseStart_2610994 : Nat := 118140960795 + 2610994 * 2 ^ 59
def prefixEnd_2610994 : Nat := 4983230072969 + 3 ^ 40 * 2610994 * 2
def baseEnd_2610994 : Nat := 446898302668487569222421

theorem tailTrace_2610994 : CollatzResearch.WordTrace tailWord_2610994 prefixEnd_2610994 446898302668487569222421 := by
  unfold tailWord_2610994
  simp only [CollatzResearch.WordTrace]
  refine ⟨23807693675705533779656009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63487183135214756745749357 23807693675705533779656009)
  ·
    refine ⟨17855770256779150334742007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23807693675705533779656009 17855770256779150334742007)
    ·
      refine ⟨26783655385168725502113011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17855770256779150334742007 26783655385168725502113011)
      ·
        refine ⟨40175483077753088253169517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26783655385168725502113011 40175483077753088253169517)
        ·
          refine ⟨15065806154157408094938569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40175483077753088253169517 15065806154157408094938569)
          ·
            refine ⟨11299354615618056071203927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15065806154157408094938569 11299354615618056071203927)
            ·
              refine ⟨16949031923427084106805891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11299354615618056071203927 16949031923427084106805891)
              ·
                refine ⟨25423547885140626160208837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16949031923427084106805891 25423547885140626160208837)
                ·
                  refine ⟨4766915228463867405039157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25423547885140626160208837 4766915228463867405039157)
                  ·
                    refine ⟨446898302668487569222421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4766915228463867405039157 446898302668487569222421)
                    ·
                      rfl

theorem cell23_2610994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_2610994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610994 prefixEnd_2610994 := by exact prefixLift 2610994
  have htrace : WordTrace (prefixWord ++ tailWord_2610994) baseStart_2610994 baseEnd_2610994 := by
    simpa [prefixWord, tailWord_2610994, baseEnd_2610994] using wordTrace_append hprefix tailTrace_2610994
  have hstable : (prefixWord ++ tailWord_2610994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610994).length < 2 ^ (prefixWord ++ tailWord_2610994).sum := by decide
  have hdescent : baseEnd_2610994 < baseStart_2610994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610998 : List Nat := [5, 1, 2, 2, 1, 3, 1, 1, 7]
def baseStart_2610998 : Nat := 118140960795 + 2610998 * 2 ^ 59
def prefixEnd_2610998 : Nat := 4983230072969 + 3 ^ 40 * 2610998 * 2
def baseEnd_2610998 : Nat := 148966329103120076890805

theorem tailTrace_2610998 : CollatzResearch.WordTrace tailWord_2610998 prefixEnd_2610998 148966329103120076890805 := by
  unfold tailWord_2610998
  simp only [CollatzResearch.WordTrace]
  refine ⟨5951932537175477737610603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63487280396538429201179765 5951932537175477737610603)
  ·
    refine ⟨8927898805763216606415905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5951932537175477737610603 8927898805763216606415905)
    ·
      refine ⟨6695924104322412454811929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8927898805763216606415905 6695924104322412454811929)
      ·
        refine ⟨5021943078241809341108947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6695924104322412454811929 5021943078241809341108947)
        ·
          refine ⟨7532914617362714011663421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5021943078241809341108947 7532914617362714011663421)
          ·
            refine ⟨2824842981511017754373783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7532914617362714011663421 2824842981511017754373783)
            ·
              refine ⟨4237264472266526631560675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2824842981511017754373783 4237264472266526631560675)
              ·
                refine ⟨6355896708399789947341013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4237264472266526631560675 6355896708399789947341013)
                ·
                  refine ⟨148966329103120076890805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6355896708399789947341013 148966329103120076890805)
                  ·
                    rfl

theorem cell23_2610998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_2610998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2610998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2610998 prefixEnd_2610998 := by exact prefixLift 2610998
  have htrace : WordTrace (prefixWord ++ tailWord_2610998) baseStart_2610998 baseEnd_2610998 := by
    simpa [prefixWord, tailWord_2610998, baseEnd_2610998] using wordTrace_append hprefix tailTrace_2610998
  have hstable : (prefixWord ++ tailWord_2610998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610998).length < 2 ^ (prefixWord ++ tailWord_2610998).sum := by decide
  have hdescent : baseEnd_2610998 < baseStart_2610998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611024 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 5, 4]
def baseStart_2611024 : Nat := 118140960795 + 2611024 * 2 ^ 59
def prefixEnd_2611024 : Nat := 4983230072969 + 3 ^ 40 * 2611024 * 2
def baseEnd_2611024 : Nat := 446903437475032530097375

theorem tailTrace_2611024 : CollatzResearch.WordTrace tailWord_2611024 prefixEnd_2611024 446903437475032530097375 := by
  unfold tailWord_2611024
  simp only [CollatzResearch.WordTrace]
  refine ⟨47615934446356725121108063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63487912595142300161477417 47615934446356725121108063)
  ·
    refine ⟨71423901669535087681662095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47615934446356725121108063 71423901669535087681662095)
    ·
      refine ⟨107135852504302631522493143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71423901669535087681662095 107135852504302631522493143)
      ·
        refine ⟨160703778756453947283739715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107135852504302631522493143 160703778756453947283739715)
        ·
          refine ⟨241055668134680920925609573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160703778756453947283739715 241055668134680920925609573)
          ·
            refine ⟨45197937775252672673551795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 241055668134680920925609573 45197937775252672673551795)
            ·
              refine ⟨67796906662879009010327693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45197937775252672673551795 67796906662879009010327693)
              ·
                refine ⟨25423839998579628378872885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67796906662879009010327693 25423839998579628378872885)
                ·
                  refine ⟨2383484999866840160519333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25423839998579628378872885 2383484999866840160519333)
                  ·
                    refine ⟨446903437475032530097375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2383484999866840160519333 446903437475032530097375)
                    ·
                      rfl

theorem cell23_2611024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 5, 4].length) (baseStart_2611024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611024 prefixEnd_2611024 := by exact prefixLift 2611024
  have htrace : WordTrace (prefixWord ++ tailWord_2611024) baseStart_2611024 baseEnd_2611024 := by
    simpa [prefixWord, tailWord_2611024, baseEnd_2611024] using wordTrace_append hprefix tailTrace_2611024
  have hstable : (prefixWord ++ tailWord_2611024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611024).length < 2 ^ (prefixWord ++ tailWord_2611024).sum := by decide
  have hdescent : baseEnd_2611024 < baseStart_2611024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611027 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 6]
def baseStart_2611027 : Nat := 118140960795 + 2611027 * 2 ^ 59
def prefixEnd_2611027 : Nat := 4983230072969 + 3 ^ 40 * 2611027 * 2
def baseEnd_2611027 : Nat := 1340711852867061078554611

theorem tailTrace_2611027 : CollatzResearch.WordTrace tailWord_2611027 prefixEnd_2611027 1340711852867061078554611 := by
  unfold tailWord_2611027
  simp only [CollatzResearch.WordTrace]
  refine ⟨95231978311702581754575335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63487985541135054503050223 95231978311702581754575335)
  ·
    refine ⟨142847967467553872631863003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95231978311702581754575335 142847967467553872631863003)
    ·
      refine ⟨214271951201330808947794505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142847967467553872631863003 214271951201330808947794505)
      ·
        refine ⟨160703963400998106710845879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214271951201330808947794505 160703963400998106710845879)
        ·
          refine ⟨241055945101497160066268819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160703963400998106710845879 241055945101497160066268819)
          ·
            refine ⟨361583917652245740099403229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241055945101497160066268819 361583917652245740099403229)
            ·
              refine ⟨135593969119592152537276211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 361583917652245740099403229 135593969119592152537276211)
              ·
                refine ⟨203390953679388228805914317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135593969119592152537276211 203390953679388228805914317)
                ·
                  refine ⟨76271607629770585802217869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 203390953679388228805914317 76271607629770585802217869)
                  ·
                    refine ⟨28601852861163969675831701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 76271607629770585802217869 28601852861163969675831701)
                    ·
                      refine ⟨1340711852867061078554611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28601852861163969675831701 1340711852867061078554611)
                      ·
                        rfl

theorem cell23_2611027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 6].length) (baseStart_2611027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611027 prefixEnd_2611027 := by exact prefixLift 2611027
  have htrace : WordTrace (prefixWord ++ tailWord_2611027) baseStart_2611027 baseEnd_2611027 := by
    simpa [prefixWord, tailWord_2611027, baseEnd_2611027] using wordTrace_append hprefix tailTrace_2611027
  have hstable : (prefixWord ++ tailWord_2611027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611027).length < 2 ^ (prefixWord ++ tailWord_2611027).sum := by decide
  have hdescent : baseEnd_2611027 < baseStart_2611027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611105 : List Nat := [1, 2, 3, 4, 3, 1, 1, 2, 6]
def baseStart_2611105 : Nat := 118140960795 + 2611105 * 2 ^ 59
def prefixEnd_2611105 : Nat := 4983230072969 + 3 ^ 40 * 2611105 * 2
def baseEnd_2611105 : Nat := 148972433817567974819917

theorem tailTrace_2611105 : CollatzResearch.WordTrace tailWord_2611105 prefixEnd_2611105 148972433817567974819917 := by
  unfold tailWord_2611105
  simp only [CollatzResearch.WordTrace]
  refine ⟨95234823205420001075914769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63489882136946667383943179 95234823205420001075914769)
  ·
    refine ⟨71426117404065000806936077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95234823205420001075914769 71426117404065000806936077)
    ·
      refine ⟨26784794026524375302601029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71426117404065000806936077 26784794026524375302601029)
      ·
        refine ⟨5022148879973320369237693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26784794026524375302601029 5022148879973320369237693)
        ·
          refine ⟨1883305829989995138464135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5022148879973320369237693 1883305829989995138464135)
          ·
            refine ⟨2824958744984992707696203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1883305829989995138464135 2824958744984992707696203)
            ·
              refine ⟨4237438117477489061544305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2824958744984992707696203 4237438117477489061544305)
              ·
                refine ⟨3178078588108116796158229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4237438117477489061544305 3178078588108116796158229)
                ·
                  refine ⟨148972433817567974819917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3178078588108116796158229 148972433817567974819917)
                  ·
                    rfl

theorem cell23_2611105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 6].length) (baseStart_2611105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611105 prefixEnd_2611105 := by exact prefixLift 2611105
  have htrace : WordTrace (prefixWord ++ tailWord_2611105) baseStart_2611105 baseEnd_2611105 := by
    simpa [prefixWord, tailWord_2611105, baseEnd_2611105] using wordTrace_append hprefix tailTrace_2611105
  have hstable : (prefixWord ++ tailWord_2611105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611105).length < 2 ^ (prefixWord ++ tailWord_2611105).sum := by decide
  have hdescent : baseEnd_2611105 < baseStart_2611105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611161 : List Nat := [1, 2, 1, 2, 6, 2, 9]
def baseStart_2611161 : Nat := 118140960795 + 2611161 * 2 ^ 59
def prefixEnd_2611161 : Nat := 4983230072969 + 3 ^ 40 * 2611161 * 2
def baseEnd_2611161 : Nat := 16552847645367451287395

theorem tailTrace_2611161 : CollatzResearch.WordTrace tailWord_2611161 prefixEnd_2611161 16552847645367451287395 := by
  unfold tailWord_2611161
  simp only [CollatzResearch.WordTrace]
  refine ⟨95236865693217122639953337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63491243795478081759968891 95236865693217122639953337)
  ·
    refine ⟨71427649269912841979965003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95236865693217122639953337 71427649269912841979965003)
    ·
      refine ⟨107141473904869262969947505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71427649269912841979965003 107141473904869262969947505)
      ·
        refine ⟨80356105428651947227460629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107141473904869262969947505 80356105428651947227460629)
        ·
          refine ⟨3766692441968060026287217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 80356105428651947227460629 3766692441968060026287217)
          ·
            refine ⟨2825019331476045019715413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3766692441968060026287217 2825019331476045019715413)
            ·
              refine ⟨16552847645367451287395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2825019331476045019715413 16552847645367451287395)
              ·
                rfl

theorem cell23_2611161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 9].length) (baseStart_2611161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611161 prefixEnd_2611161 := by exact prefixLift 2611161
  have htrace : WordTrace (prefixWord ++ tailWord_2611161) baseStart_2611161 baseEnd_2611161 := by
    simpa [prefixWord, tailWord_2611161, baseEnd_2611161] using wordTrace_append hprefix tailTrace_2611161
  have hstable : (prefixWord ++ tailWord_2611161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611161).length < 2 ^ (prefixWord ++ tailWord_2611161).sum := by decide
  have hdescent : baseEnd_2611161 < baseStart_2611161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611182 : List Nat := [4, 1, 2, 1, 3, 3, 2, 1, 2, 4]
def baseStart_2611182 : Nat := 118140960795 + 2611182 * 2 ^ 59
def prefixEnd_2611182 : Nat := 4983230072969 + 3 ^ 40 * 2611182 * 2
def baseEnd_2611182 : Nat := 446930480789502657372133

theorem tailTrace_2611182 : CollatzResearch.WordTrace tailWord_2611182 prefixEnd_2611182 446930480789502657372133 := by
  unfold tailWord_2611182
  simp only [CollatzResearch.WordTrace]
  refine ⟨11904703953267630403308475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63491754417427362150978533 11904703953267630403308475)
  ·
    refine ⟨17857055929901445604962713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11904703953267630403308475 17857055929901445604962713)
    ·
      refine ⟨13392791947426084203722035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17857055929901445604962713 13392791947426084203722035)
      ·
        refine ⟨20089187921139126305583053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13392791947426084203722035 20089187921139126305583053)
        ·
          refine ⟨7533445470427172364593645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20089187921139126305583053 7533445470427172364593645)
          ·
            refine ⟨2825042051410189636722617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7533445470427172364593645 2825042051410189636722617)
            ·
              refine ⟨2118781538557642227541963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2825042051410189636722617 2118781538557642227541963)
              ·
                refine ⟨3178172307836463341312945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2118781538557642227541963 3178172307836463341312945)
                ·
                  refine ⟨2383629230877347505984709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3178172307836463341312945 2383629230877347505984709)
                  ·
                    refine ⟨446930480789502657372133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2383629230877347505984709 446930480789502657372133)
                    ·
                      rfl

theorem cell23_2611182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_2611182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611182 prefixEnd_2611182 := by exact prefixLift 2611182
  have htrace : WordTrace (prefixWord ++ tailWord_2611182) baseStart_2611182 baseEnd_2611182 := by
    simpa [prefixWord, tailWord_2611182, baseEnd_2611182] using wordTrace_append hprefix tailTrace_2611182
  have hstable : (prefixWord ++ tailWord_2611182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611182).length < 2 ^ (prefixWord ++ tailWord_2611182).sum := by decide
  have hdescent : baseEnd_2611182 < baseStart_2611182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611194 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 1, 1, 10]
def baseStart_2611194 : Nat := 118140960795 + 2611194 * 2 ^ 59
def prefixEnd_2611194 : Nat := 4983230072969 + 3 ^ 40 * 2611194 * 2
def baseEnd_2611194 : Nat := 1340797604136361925166343

theorem tailTrace_2611194 : CollatzResearch.WordTrace tailWord_2611194 prefixEnd_2611194 1340797604136361925166343 := by
  unfold tailWord_2611194
  simp only [CollatzResearch.WordTrace]
  refine ⟨23809517325524392318976159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63492046201398379517269757 23809517325524392318976159)
  ·
    refine ⟨35714275988286588478464239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23809517325524392318976159 35714275988286588478464239)
    ·
      refine ⟨53571413982429882717696359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35714275988286588478464239 53571413982429882717696359)
      ·
        refine ⟨80357120973644824076544539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53571413982429882717696359 80357120973644824076544539)
        ·
          refine ⟨120535681460467236114816809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80357120973644824076544539 120535681460467236114816809)
          ·
            refine ⟨90401761095350427086112607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120535681460467236114816809 90401761095350427086112607)
            ·
              refine ⟨135602641643025640629168911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90401761095350427086112607 135602641643025640629168911)
              ·
                refine ⟨203403962464538460943753367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135602641643025640629168911 203403962464538460943753367)
                ·
                  refine ⟨305105943696807691415630051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 203403962464538460943753367 305105943696807691415630051)
                  ·
                    refine ⟨457658915545211537123445077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 305105943696807691415630051 457658915545211537123445077)
                    ·
                      refine ⟨1340797604136361925166343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 457658915545211537123445077 1340797604136361925166343)
                      ·
                        rfl

theorem cell23_2611194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_2611194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611194 prefixEnd_2611194 := by exact prefixLift 2611194
  have htrace : WordTrace (prefixWord ++ tailWord_2611194) baseStart_2611194 baseEnd_2611194 := by
    simpa [prefixWord, tailWord_2611194, baseEnd_2611194] using wordTrace_append hprefix tailTrace_2611194
  have hstable : (prefixWord ++ tailWord_2611194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611194).length < 2 ^ (prefixWord ++ tailWord_2611194).sum := by decide
  have hdescent : baseEnd_2611194 < baseStart_2611194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611223 : List Nat := [1, 1, 3, 5, 3, 1, 2, 2, 1, 2, 2]
def baseStart_2611223 : Nat := 118140960795 + 2611223 * 2 ^ 59
def prefixEnd_2611223 : Nat := 4983230072969 + 3 ^ 40 * 2611223 * 2
def baseEnd_2611223 : Nat := 1340812495075342311703711

theorem tailTrace_2611223 : CollatzResearch.WordTrace tailWord_2611223 prefixEnd_2611223 1340812495075342311703711 := by
  unfold tailWord_2611223
  simp only [CollatzResearch.WordTrace]
  refine ⟨95239127018992507228710323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63492751345995004819140215 95239127018992507228710323)
  ·
    refine ⟨142858690528488760843065485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95239127018992507228710323 142858690528488760843065485)
    ·
      refine ⟨53572008948183285316149557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142858690528488760843065485 53572008948183285316149557)
      ·
        refine ⟨5022375838892182998389021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53572008948183285316149557 5022375838892182998389021)
        ·
          refine ⟨1883390939584568624395883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5022375838892182998389021 1883390939584568624395883)
          ·
            refine ⟨2825086409376852936593825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1883390939584568624395883 2825086409376852936593825)
            ·
              refine ⟨2118814807032639702445369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2825086409376852936593825 2118814807032639702445369)
              ·
                refine ⟨1589111105274479776834027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2118814807032639702445369 1589111105274479776834027)
                ·
                  refine ⟨2383666657911719665251041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1589111105274479776834027 2383666657911719665251041)
                  ·
                    refine ⟨1787749993433789748938281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2383666657911719665251041 1787749993433789748938281)
                    ·
                      refine ⟨1340812495075342311703711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1787749993433789748938281 1340812495075342311703711)
                      ·
                        rfl

theorem cell23_2611223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_2611223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611223 prefixEnd_2611223 := by exact prefixLift 2611223
  have htrace : WordTrace (prefixWord ++ tailWord_2611223) baseStart_2611223 baseEnd_2611223 := by
    simpa [prefixWord, tailWord_2611223, baseEnd_2611223] using wordTrace_append hprefix tailTrace_2611223
  have hstable : (prefixWord ++ tailWord_2611223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611223).length < 2 ^ (prefixWord ++ tailWord_2611223).sum := by decide
  have hdescent : baseEnd_2611223 < baseStart_2611223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611231 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 1, 6, 3]
def baseStart_2611231 : Nat := 118140960795 + 2611231 * 2 ^ 59
def prefixEnd_2611231 : Nat := 4983230072969 + 3 ^ 40 * 2611231 * 2
def baseEnd_2611231 : Nat := 1340816602920578280403673

theorem tailTrace_2611231 : CollatzResearch.WordTrace tailWord_2611231 prefixEnd_2611231 1340816602920578280403673 := by
  unfold tailWord_2611231
  simp only [CollatzResearch.WordTrace]
  refine ⟨95239418802963524595001547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63492945868642349730001031 95239418802963524595001547)
  ·
    refine ⟨142859128204445286892502321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95239418802963524595001547 142859128204445286892502321)
    ·
      refine ⟨107144346153333965169376741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142859128204445286892502321 107144346153333965169376741)
      ·
        refine ⟨20089564903750118469258139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107144346153333965169376741 20089564903750118469258139)
        ·
          refine ⟨30134347355625177703887209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20089564903750118469258139 30134347355625177703887209)
          ·
            refine ⟨22600760516718883277915407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30134347355625177703887209 22600760516718883277915407)
            ·
              refine ⟨33901140775078324916873111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22600760516718883277915407 33901140775078324916873111)
              ·
                refine ⟨50851711162617487375309667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33901140775078324916873111 50851711162617487375309667)
                ·
                  refine ⟨76277566743926231062964501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50851711162617487375309667 76277566743926231062964501)
                  ·
                    refine ⟨3575510941121542081076461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 76277566743926231062964501 3575510941121542081076461)
                    ·
                      refine ⟨1340816602920578280403673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3575510941121542081076461 1340816602920578280403673)
                      ·
                        rfl

theorem cell23_2611231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_2611231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611231 prefixEnd_2611231 := by exact prefixLift 2611231
  have htrace : WordTrace (prefixWord ++ tailWord_2611231) baseStart_2611231 baseEnd_2611231 := by
    simpa [prefixWord, tailWord_2611231, baseEnd_2611231] using wordTrace_append hprefix tailTrace_2611231
  have hstable : (prefixWord ++ tailWord_2611231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611231).length < 2 ^ (prefixWord ++ tailWord_2611231).sum := by decide
  have hdescent : baseEnd_2611231 < baseStart_2611231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611278 : List Nat := [4, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3]
def baseStart_2611278 : Nat := 118140960795 + 2611278 * 2 ^ 59
def prefixEnd_2611278 : Nat := 4983230072969 + 3 ^ 40 * 2611278 * 2
def baseEnd_2611278 : Nat := 1340840736511339596515957

theorem tailTrace_2611278 : CollatzResearch.WordTrace tailWord_2611278 prefixEnd_2611278 1340840736511339596515957 := by
  unfold tailWord_2611278
  simp only [CollatzResearch.WordTrace]
  refine ⟨11905141629224156452745311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63494088689195501081308325 11905141629224156452745311)
  ·
    refine ⟨17857712443836234679117967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11905141629224156452745311 17857712443836234679117967)
    ·
      refine ⟨26786568665754352018676951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17857712443836234679117967 26786568665754352018676951)
      ·
        refine ⟨40179852998631528028015427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26786568665754352018676951 40179852998631528028015427)
        ·
          refine ⟨60269779497947292042023141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40179852998631528028015427 60269779497947292042023141)
          ·
            refine ⟨11300583655865117257879339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60269779497947292042023141 11300583655865117257879339)
            ·
              refine ⟨16950875483797675886819009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11300583655865117257879339 16950875483797675886819009)
              ·
                refine ⟨12713156612848256915114257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16950875483797675886819009 12713156612848256915114257)
                ·
                  refine ⟨9534867459636192686335693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12713156612848256915114257 9534867459636192686335693)
                  ·
                    refine ⟨3575575297363572257375885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9534867459636192686335693 3575575297363572257375885)
                    ·
                      refine ⟨1340840736511339596515957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3575575297363572257375885 1340840736511339596515957)
                      ·
                        rfl

theorem cell23_2611278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_2611278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611278 prefixEnd_2611278 := by exact prefixLift 2611278
  have htrace : WordTrace (prefixWord ++ tailWord_2611278) baseStart_2611278 baseEnd_2611278 := by
    simpa [prefixWord, tailWord_2611278, baseEnd_2611278] using wordTrace_append hprefix tailTrace_2611278
  have hstable : (prefixWord ++ tailWord_2611278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611278).length < 2 ^ (prefixWord ++ tailWord_2611278).sum := by decide
  have hdescent : baseEnd_2611278 < baseStart_2611278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611281 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 4, 5]
def baseStart_2611281 : Nat := 118140960795 + 2611281 * 2 ^ 59
def prefixEnd_2611281 : Nat := 4983230072969 + 3 ^ 40 * 2611281 * 2
def baseEnd_2611281 : Nat := 446947425651101028259481

theorem tailTrace_2611281 : CollatzResearch.WordTrace tailWord_2611281 prefixEnd_2611281 446947425651101028259481 := by
  unfold tailWord_2611281
  simp only [CollatzResearch.WordTrace]
  refine ⟨95241242452782383134321697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63494161635188255422881131 95241242452782383134321697)
  ·
    refine ⟨71430931839586787350741273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95241242452782383134321697 71430931839586787350741273)
    ·
      refine ⟨53573198879690090513055955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71430931839586787350741273 53573198879690090513055955)
      ·
        refine ⟨80359798319535135769583933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53573198879690090513055955 80359798319535135769583933)
        ·
          refine ⟨30134924369825675913593975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80359798319535135769583933 30134924369825675913593975)
          ·
            refine ⟨45202386554738513870390963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30134924369825675913593975 45202386554738513870390963)
            ·
              refine ⟨67803579832107770805586445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45202386554738513870390963 67803579832107770805586445)
              ·
                refine ⟨25426342437040414052094917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67803579832107770805586445 25426342437040414052094917)
                ·
                  refine ⟨4767439206945077634767797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25426342437040414052094917 4767439206945077634767797)
                  ·
                    refine ⟨446947425651101028259481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4767439206945077634767797 446947425651101028259481)
                    ·
                      rfl

theorem cell23_2611281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 5].length) (baseStart_2611281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611281 prefixEnd_2611281 := by exact prefixLift 2611281
  have htrace : WordTrace (prefixWord ++ tailWord_2611281) baseStart_2611281 baseEnd_2611281 := by
    simpa [prefixWord, tailWord_2611281, baseEnd_2611281] using wordTrace_append hprefix tailTrace_2611281
  have hstable : (prefixWord ++ tailWord_2611281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611281).length < 2 ^ (prefixWord ++ tailWord_2611281).sum := by decide
  have hdescent : baseEnd_2611281 < baseStart_2611281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611396 : List Nat := [2, 3, 3, 1, 2, 3, 2, 2, 1, 4]
def baseStart_2611396 : Nat := 118140960795 + 2611396 * 2 ^ 59
def prefixEnd_2611396 : Nat := 4983230072969 + 3 ^ 40 * 2611396 * 2
def baseEnd_2611396 : Nat := 446967109076190044946805

theorem tailTrace_2611396 : CollatzResearch.WordTrace tailWord_2611396 prefixEnd_2611396 446967109076190044946805 := by
  unfold tailWord_2611396
  simp only [CollatzResearch.WordTrace]
  refine ⟨47622718423682878887379021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63496957898243838516505361 47622718423682878887379021)
  ·
    refine ⟨17858519408881079582767133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47622718423682878887379021 17858519408881079582767133)
    ·
      refine ⟨6696944778330404843537675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17858519408881079582767133 6696944778330404843537675)
      ·
        refine ⟨10045417167495607265306513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6696944778330404843537675 10045417167495607265306513)
        ·
          refine ⟨7534062875621705448979885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10045417167495607265306513 7534062875621705448979885)
          ·
            refine ⟨2825273578358139543367457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7534062875621705448979885 2825273578358139543367457)
            ·
              refine ⟨2118955183768604657525593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2825273578358139543367457 2118955183768604657525593)
              ·
                refine ⟨1589216387826453493144195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2118955183768604657525593 1589216387826453493144195)
                ·
                  refine ⟨2383824581739680239716293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1589216387826453493144195 2383824581739680239716293)
                  ·
                    refine ⟨446967109076190044946805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2383824581739680239716293 446967109076190044946805)
                    ·
                      rfl

theorem cell23_2611396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_2611396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611396 prefixEnd_2611396 := by exact prefixLift 2611396
  have htrace : WordTrace (prefixWord ++ tailWord_2611396) baseStart_2611396 baseEnd_2611396 := by
    simpa [prefixWord, tailWord_2611396, baseEnd_2611396] using wordTrace_append hprefix tailTrace_2611396
  have hstable : (prefixWord ++ tailWord_2611396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611396).length < 2 ^ (prefixWord ++ tailWord_2611396).sum := by decide
  have hdescent : baseEnd_2611396 < baseStart_2611396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611418 : List Nat := [3, 1, 1, 2, 2, 1, 3, 3, 1, 6]
def baseStart_2611418 : Nat := 118140960795 + 2611418 * 2 ^ 59
def prefixEnd_2611418 : Nat := 4983230072969 + 3 ^ 40 * 2611418 * 2
def baseEnd_2611418 : Nat := 446970874600989682921771

theorem tailTrace_2611418 : CollatzResearch.WordTrace tailWord_2611418 prefixEnd_2611418 446970874600989682921771 := by
  unfold tailWord_2611418
  simp only [CollatzResearch.WordTrace]
  refine ⟨23811559813321513883014727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63497492835524037021372605 23811559813321513883014727)
  ·
    refine ⟨35717339719982270824522091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23811559813321513883014727 35717339719982270824522091)
    ·
      refine ⟨53576009579973406236783137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35717339719982270824522091 53576009579973406236783137)
      ·
        refine ⟨40182007184980054677587353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53576009579973406236783137 40182007184980054677587353)
        ·
          refine ⟨30136505388735041008190515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40182007184980054677587353 30136505388735041008190515)
          ·
            refine ⟨45204758083102561512285773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30136505388735041008190515 45204758083102561512285773)
            ·
              refine ⟨16951784281163460567107165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45204758083102561512285773 16951784281163460567107165)
              ·
                refine ⟨6356919105436297712665187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16951784281163460567107165 6356919105436297712665187)
                ·
                  refine ⟨9535378658154446568997781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6356919105436297712665187 9535378658154446568997781)
                  ·
                    refine ⟨446970874600989682921771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9535378658154446568997781 446970874600989682921771)
                    ·
                      rfl

theorem cell23_2611418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 1, 6].length) (baseStart_2611418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611418 prefixEnd_2611418 := by exact prefixLift 2611418
  have htrace : WordTrace (prefixWord ++ tailWord_2611418) baseStart_2611418 baseEnd_2611418 := by
    simpa [prefixWord, tailWord_2611418, baseEnd_2611418] using wordTrace_append hprefix tailTrace_2611418
  have hstable : (prefixWord ++ tailWord_2611418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611418).length < 2 ^ (prefixWord ++ tailWord_2611418).sum := by decide
  have hdescent : baseEnd_2611418 < baseStart_2611418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611425 : List Nat := [1, 2, 3, 1, 3, 1, 2, 4, 1, 1, 4]
def baseStart_2611425 : Nat := 118140960795 + 2611425 * 2 ^ 59
def prefixEnd_2611425 : Nat := 4983230072969 + 3 ^ 40 * 2611425 * 2
def baseEnd_2611425 : Nat := 1340916218167550521377781

theorem tailTrace_2611425 : CollatzResearch.WordTrace tailWord_2611425 prefixEnd_2611425 1340916218167550521377781 := by
  unfold tailWord_2611425
  simp only [CollatzResearch.WordTrace]
  refine ⟨95246494564260695727563729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63497663042840463818375819 95246494564260695727563729)
  ·
    refine ⟨71434870923195521795672797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95246494564260695727563729 71434870923195521795672797)
    ·
      refine ⟨26788076596198320673377299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71434870923195521795672797 26788076596198320673377299)
      ·
        refine ⟨40182114894297481010065949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26788076596198320673377299 40182114894297481010065949)
        ·
          refine ⟨15068293085361555378774731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40182114894297481010065949 15068293085361555378774731)
          ·
            refine ⟨22602439628042333068162097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15068293085361555378774731 22602439628042333068162097)
            ·
              refine ⟨16951829721031749801121573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22602439628042333068162097 16951829721031749801121573)
              ·
                refine ⟨3178468072693453087710295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16951829721031749801121573 3178468072693453087710295)
                ·
                  refine ⟨4767702109040179631565443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3178468072693453087710295 4767702109040179631565443)
                  ·
                    refine ⟨7151553163560269447348165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4767702109040179631565443 7151553163560269447348165)
                    ·
                      refine ⟨1340916218167550521377781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7151553163560269447348165 1340916218167550521377781)
                      ·
                        rfl

theorem cell23_2611425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_2611425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611425 prefixEnd_2611425 := by exact prefixLift 2611425
  have htrace : WordTrace (prefixWord ++ tailWord_2611425) baseStart_2611425 baseEnd_2611425 := by
    simpa [prefixWord, tailWord_2611425, baseEnd_2611425] using wordTrace_append hprefix tailTrace_2611425
  have hstable : (prefixWord ++ tailWord_2611425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611425).length < 2 ^ (prefixWord ++ tailWord_2611425).sum := by decide
  have hdescent : baseEnd_2611425 < baseStart_2611425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611429 : List Nat := [1, 3, 1, 4, 2, 3, 1, 1, 2, 3, 2]
def baseStart_2611429 : Nat := 118140960795 + 2611429 * 2 ^ 59
def prefixEnd_2611429 : Nat := 4983230072969 + 3 ^ 40 * 2611429 * 2
def baseEnd_2611429 : Nat := 1340918272090168505727763

theorem tailTrace_2611429 : CollatzResearch.WordTrace tailWord_2611429 prefixEnd_2611429 1340918272090168505727763 := by
  unfold tailWord_2611429
  simp only [CollatzResearch.WordTrace]
  refine ⟨95246640456246204410709341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63497760304164136273806227 95246640456246204410709341)
  ·
    refine ⟨35717490171092326654016003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95246640456246204410709341 35717490171092326654016003)
    ·
      refine ⟨53576235256638489981024005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35717490171092326654016003 53576235256638489981024005)
      ·
        refine ⟨10045544110619716871442001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53576235256638489981024005 10045544110619716871442001)
        ·
          refine ⟨7534158082964787653581501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10045544110619716871442001 7534158082964787653581501)
          ·
            refine ⟨2825309281111795370093063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7534158082964787653581501 2825309281111795370093063)
            ·
              refine ⟨4237963921667693055139595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2825309281111795370093063 4237963921667693055139595)
              ·
                refine ⟨6356945882501539582709393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4237963921667693055139595 6356945882501539582709393)
                ·
                  refine ⟨4767709411876154687032045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6356945882501539582709393 4767709411876154687032045)
                  ·
                    refine ⟨1787891029453558007637017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4767709411876154687032045 1787891029453558007637017)
                    ·
                      refine ⟨1340918272090168505727763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1787891029453558007637017 1340918272090168505727763)
                      ·
                        rfl

theorem cell23_2611429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_2611429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611429 prefixEnd_2611429 := by exact prefixLift 2611429
  have htrace : WordTrace (prefixWord ++ tailWord_2611429) baseStart_2611429 baseEnd_2611429 := by
    simpa [prefixWord, tailWord_2611429, baseEnd_2611429] using wordTrace_append hprefix tailTrace_2611429
  have hstable : (prefixWord ++ tailWord_2611429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611429).length < 2 ^ (prefixWord ++ tailWord_2611429).sum := by decide
  have hdescent : baseEnd_2611429 < baseStart_2611429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611438 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 3, 1, 6]
def baseStart_2611438 : Nat := 118140960795 + 2611438 * 2 ^ 59
def prefixEnd_2611438 : Nat := 4983230072969 + 3 ^ 40 * 2611438 * 2
def baseEnd_2611438 : Nat := 1340922893416058970515221

theorem tailTrace_2611438 : CollatzResearch.WordTrace tailWord_2611438 prefixEnd_2611438 1340922893416058970515221 := by
  unfold tailWord_2611438
  simp only [CollatzResearch.WordTrace]
  refine ⟨11905871089151699868473371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63497979142142399298524645 11905871089151699868473371)
  ·
    refine ⟨17858806633727549802710057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11905871089151699868473371 17858806633727549802710057)
    ·
      refine ⟨13394104975295662352032543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17858806633727549802710057 13394104975295662352032543)
      ·
        refine ⟨20091157462943493528048815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13394104975295662352032543 20091157462943493528048815)
        ·
          refine ⟨30136736194415240292073223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20091157462943493528048815 30136736194415240292073223)
          ·
            refine ⟨45205104291622860438109835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30136736194415240292073223 45205104291622860438109835)
            ·
              refine ⟨67807656437434290657164753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45205104291622860438109835 67807656437434290657164753)
              ·
                refine ⟨50855742328075717992873565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67807656437434290657164753 50855742328075717992873565)
                ·
                  refine ⟨19070903373028394247327587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50855742328075717992873565 19070903373028394247327587)
                  ·
                    refine ⟨28606355059542591370991381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19070903373028394247327587 28606355059542591370991381)
                    ·
                      refine ⟨1340922893416058970515221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28606355059542591370991381 1340922893416058970515221)
                      ·
                        rfl

theorem cell23_2611438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_2611438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611438 prefixEnd_2611438 := by exact prefixLift 2611438
  have htrace : WordTrace (prefixWord ++ tailWord_2611438) baseStart_2611438 baseEnd_2611438 := by
    simpa [prefixWord, tailWord_2611438, baseEnd_2611438] using wordTrace_append hprefix tailTrace_2611438
  have hstable : (prefixWord ++ tailWord_2611438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611438).length < 2 ^ (prefixWord ++ tailWord_2611438).sum := by decide
  have hdescent : baseEnd_2611438 < baseStart_2611438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611442 : List Nat := [3, 2, 1, 3, 2, 2, 1, 3, 1, 1, 4]
def baseStart_2611442 : Nat := 118140960795 + 2611442 * 2 ^ 59
def prefixEnd_2611442 : Nat := 4983230072969 + 3 ^ 40 * 2611442 * 2
def baseEnd_2611442 : Nat := 1340924947338676954865203

theorem tailTrace_2611442 : CollatzResearch.WordTrace tailWord_2611442 prefixEnd_2611442 1340924947338676954865203 := by
  unfold tailWord_2611442
  simp only [CollatzResearch.WordTrace]
  refine ⟨23811778651299776907733145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63498076403466071753955053 23811778651299776907733145)
  ·
    refine ⟨17858833988474832680799859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23811778651299776907733145 17858833988474832680799859)
    ·
      refine ⟨26788250982712249021199789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17858833988474832680799859 26788250982712249021199789)
      ·
        refine ⟨10045594118517093382949921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26788250982712249021199789 10045594118517093382949921)
        ·
          refine ⟨7534195588887820037212441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10045594118517093382949921 7534195588887820037212441)
          ·
            refine ⟨5650646691665865027909331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7534195588887820037212441 5650646691665865027909331)
            ·
              refine ⟨8475970037498797541863997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5650646691665865027909331 8475970037498797541863997)
              ·
                refine ⟨3178488764062049078198999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8475970037498797541863997 3178488764062049078198999)
                ·
                  refine ⟨4767733146093073617298499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3178488764062049078198999 4767733146093073617298499)
                  ·
                    refine ⟨7151599719139610425947749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4767733146093073617298499 7151599719139610425947749)
                    ·
                      refine ⟨1340924947338676954865203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7151599719139610425947749 1340924947338676954865203)
                      ·
                        rfl

theorem cell23_2611442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_2611442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611442 prefixEnd_2611442 := by exact prefixLift 2611442
  have htrace : WordTrace (prefixWord ++ tailWord_2611442) baseStart_2611442 baseEnd_2611442 := by
    simpa [prefixWord, tailWord_2611442, baseEnd_2611442] using wordTrace_append hprefix tailTrace_2611442
  have hstable : (prefixWord ++ tailWord_2611442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611442).length < 2 ^ (prefixWord ++ tailWord_2611442).sum := by decide
  have hdescent : baseEnd_2611442 < baseStart_2611442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611452 : List Nat := [2, 2, 2, 1, 4, 1, 3, 2, 2, 4]
def baseStart_2611452 : Nat := 118140960795 + 2611452 * 2 ^ 59
def prefixEnd_2611452 : Nat := 4983230072969 + 3 ^ 40 * 2611452 * 2
def baseEnd_2611452 : Nat := 446976694048407305246719

theorem tailTrace_2611452 : CollatzResearch.WordTrace tailWord_2611452 prefixEnd_2611452 446976694048407305246719 := by
  unfold tailWord_2611452
  simp only [CollatzResearch.WordTrace]
  refine ⟨47623739667581439669398305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63498319556775252892531073 47623739667581439669398305)
  ·
    refine ⟨35717804750686079752048729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47623739667581439669398305 35717804750686079752048729)
    ·
      refine ⟨26788353563014559814036547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35717804750686079752048729 26788353563014559814036547)
      ·
        refine ⟨40182530344521839721054821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26788353563014559814036547 40182530344521839721054821)
        ·
          refine ⟨7534224439597844947697779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40182530344521839721054821 7534224439597844947697779)
          ·
            refine ⟨11301336659396767421546669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7534224439597844947697779 11301336659396767421546669)
            ·
              refine ⟨4238001247273787783080001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11301336659396767421546669 4238001247273787783080001)
              ·
                refine ⟨3178500935455340837310001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4238001247273787783080001 3178500935455340837310001)
                ·
                  refine ⟨2383875701591505627982501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3178500935455340837310001 2383875701591505627982501)
                  ·
                    refine ⟨446976694048407305246719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2383875701591505627982501 446976694048407305246719)
                    ·
                      rfl

theorem cell23_2611452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_2611452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611452 prefixEnd_2611452 := by exact prefixLift 2611452
  have htrace : WordTrace (prefixWord ++ tailWord_2611452) baseStart_2611452 baseEnd_2611452 := by
    simpa [prefixWord, tailWord_2611452, baseEnd_2611452] using wordTrace_append hprefix tailTrace_2611452
  have hstable : (prefixWord ++ tailWord_2611452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611452).length < 2 ^ (prefixWord ++ tailWord_2611452).sum := by decide
  have hdescent : baseEnd_2611452 < baseStart_2611452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611459 : List Nat := [1, 1, 1, 3, 2, 3, 1, 6, 1, 2, 2]
def baseStart_2611459 : Nat := 118140960795 + 2611459 * 2 ^ 59
def prefixEnd_2611459 : Nat := 4983230072969 + 3 ^ 40 * 2611459 * 2
def baseEnd_2611459 : Nat := 1340933676509803388352625

theorem tailTrace_2611459 : CollatzResearch.WordTrace tailWord_2611459 prefixEnd_2611459 1340933676509803388352625 := by
  unfold tailWord_2611459
  simp only [CollatzResearch.WordTrace]
  refine ⟨95247734646137519534301431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63498489764091679689534287 95247734646137519534301431)
  ·
    refine ⟨142871601969206279301452147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95247734646137519534301431 142871601969206279301452147)
    ·
      refine ⟨214307402953809418952178221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142871601969206279301452147 214307402953809418952178221)
      ·
        refine ⟨80365276107678532107066833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214307402953809418952178221 80365276107678532107066833)
        ·
          refine ⟨60273957080758899080300125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80365276107678532107066833 60273957080758899080300125)
          ·
            refine ⟨22602733905284587155112547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60273957080758899080300125 22602733905284587155112547)
            ·
              refine ⟨33904100857926880732668821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22602733905284587155112547 33904100857926880732668821)
              ·
                refine ⟨1589254727715322534343851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33904100857926880732668821 1589254727715322534343851)
                ·
                  refine ⟨2383882091572983801515777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1589254727715322534343851 2383882091572983801515777)
                  ·
                    refine ⟨1787911568679737851136833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2383882091572983801515777 1787911568679737851136833)
                    ·
                      refine ⟨1340933676509803388352625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1787911568679737851136833 1340933676509803388352625)
                      ·
                        rfl

theorem cell23_2611459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 6, 1, 2, 2].length) (baseStart_2611459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611459 prefixEnd_2611459 := by exact prefixLift 2611459
  have htrace : WordTrace (prefixWord ++ tailWord_2611459) baseStart_2611459 baseEnd_2611459 := by
    simpa [prefixWord, tailWord_2611459, baseEnd_2611459] using wordTrace_append hprefix tailTrace_2611459
  have hstable : (prefixWord ++ tailWord_2611459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611459).length < 2 ^ (prefixWord ++ tailWord_2611459).sum := by decide
  have hdescent : baseEnd_2611459 < baseStart_2611459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611482 : List Nat := [3, 1, 1, 3, 4, 2, 2, 7]
def baseStart_2611482 : Nat := 118140960795 + 2611482 * 2 ^ 59
def prefixEnd_2611482 : Nat := 4983230072969 + 3 ^ 40 * 2611482 * 2
def baseEnd_2611482 : Nat := 49664647650550251791297

theorem tailTrace_2611482 : CollatzResearch.WordTrace tailWord_2611482 prefixEnd_2611482 49664647650550251791297 := by
  unfold tailWord_2611482
  simp only [CollatzResearch.WordTrace]
  refine ⟨23812143381263548615597175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63499049016702796308259133 23812143381263548615597175)
  ·
    refine ⟨35718215071895322923395763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23812143381263548615597175 35718215071895322923395763)
    ·
      refine ⟨53577322607842984385093645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35718215071895322923395763 53577322607842984385093645)
      ·
        refine ⟨20091495977941119144410117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53577322607842984385093645 20091495977941119144410117)
        ·
          refine ⟨3767155495863959839576897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20091495977941119144410117 3767155495863959839576897)
          ·
            refine ⟨2825366621897969879682673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3767155495863959839576897 2825366621897969879682673)
            ·
              refine ⟨2119024966423477409762005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2825366621897969879682673 2119024966423477409762005)
              ·
                refine ⟨49664647650550251791297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2119024966423477409762005 49664647650550251791297)
                ·
                  rfl

theorem cell23_2611482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 7].length) (baseStart_2611482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611482 prefixEnd_2611482 := by exact prefixLift 2611482
  have htrace : WordTrace (prefixWord ++ tailWord_2611482) baseStart_2611482 baseEnd_2611482 := by
    simpa [prefixWord, tailWord_2611482, baseEnd_2611482] using wordTrace_append hprefix tailTrace_2611482
  have hstable : (prefixWord ++ tailWord_2611482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611482).length < 2 ^ (prefixWord ++ tailWord_2611482).sum := by decide
  have hdescent : baseEnd_2611482 < baseStart_2611482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611492 : List Nat := [2, 3, 1, 3, 1, 2, 1, 2, 4, 1, 3]
def baseStart_2611492 : Nat := 118140960795 + 2611492 * 2 ^ 59
def prefixEnd_2611492 : Nat := 4983230072969 + 3 ^ 40 * 2611492 * 2
def baseEnd_2611492 : Nat := 1340950621371401759239973

theorem tailTrace_2611492 : CollatzResearch.WordTrace tailWord_2611492 prefixEnd_2611492 1340950621371401759239973 := by
  unfold tailWord_2611492
  simp only [CollatzResearch.WordTrace]
  refine ⟨47624469127508983085126365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63499292170011977446835153 47624469127508983085126365)
  ·
    refine ⟨17859175922815868656922387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47624469127508983085126365 17859175922815868656922387)
    ·
      refine ⟨26788763884223802985383581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17859175922815868656922387 26788763884223802985383581)
      ·
        refine ⟨10045786456583926119518843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26788763884223802985383581 10045786456583926119518843)
        ·
          refine ⟨15068679684875889179278265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10045786456583926119518843 15068679684875889179278265)
          ·
            refine ⟨11301509763656916884458699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15068679684875889179278265 11301509763656916884458699)
            ·
              refine ⟨16952264645485375326688049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11301509763656916884458699 16952264645485375326688049)
              ·
                refine ⟨12714198484114031495016037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16952264645485375326688049 12714198484114031495016037)
                ·
                  refine ⟨2383912215771380905315507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12714198484114031495016037 2383912215771380905315507)
                  ·
                    refine ⟨3575868323657071357973261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2383912215771380905315507 3575868323657071357973261)
                    ·
                      refine ⟨1340950621371401759239973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3575868323657071357973261 1340950621371401759239973)
                      ·
                        rfl

theorem cell23_2611492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_2611492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611492 prefixEnd_2611492 := by exact prefixLift 2611492
  have htrace : WordTrace (prefixWord ++ tailWord_2611492) baseStart_2611492 baseEnd_2611492 := by
    simpa [prefixWord, tailWord_2611492, baseEnd_2611492] using wordTrace_append hprefix tailTrace_2611492
  have hstable : (prefixWord ++ tailWord_2611492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611492).length < 2 ^ (prefixWord ++ tailWord_2611492).sum := by decide
  have hdescent : baseEnd_2611492 < baseStart_2611492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611493 : List Nat := [1, 3, 1, 2, 5, 2, 1, 3, 1, 2, 2]
def baseStart_2611493 : Nat := 118140960795 + 2611493 * 2 ^ 59
def prefixEnd_2611493 : Nat := 4983230072969 + 3 ^ 40 * 2611493 * 2
def baseEnd_2611493 : Nat := 1340951134852056255327469

theorem tailTrace_2611493 : CollatzResearch.WordTrace tailWord_2611493 prefixEnd_2611493 1340951134852056255327469 := by
  unfold tailWord_2611493
  simp only [CollatzResearch.WordTrace]
  refine ⟨95248974728014343341039133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63499316485342895560692755 95248974728014343341039133)
  ·
    refine ⟨35718365523005378752889675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95248974728014343341039133 35718365523005378752889675)
    ·
      refine ⟨53577548284508068129334513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35718365523005378752889675 53577548284508068129334513)
      ·
        refine ⟨40183161213381051097000885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53577548284508068129334513 40183161213381051097000885)
        ·
          refine ⟨3767171363754473540343833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40183161213381051097000885 3767171363754473540343833)
          ·
            refine ⟨2825378522815855155257875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3767171363754473540343833 2825378522815855155257875)
            ·
              refine ⟨4238067784223782732886813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2825378522815855155257875 4238067784223782732886813)
              ·
                refine ⟨1589275419083918524832555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4238067784223782732886813 1589275419083918524832555)
                ·
                  refine ⟨2383913128625877787248833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1589275419083918524832555 2383913128625877787248833)
                  ·
                    refine ⟨1787934846469408340436625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2383913128625877787248833 1787934846469408340436625)
                    ·
                      refine ⟨1340951134852056255327469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1787934846469408340436625 1340951134852056255327469)
                      ·
                        rfl

theorem cell23_2611493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 3, 1, 2, 2].length) (baseStart_2611493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611493 prefixEnd_2611493 := by exact prefixLift 2611493
  have htrace : WordTrace (prefixWord ++ tailWord_2611493) baseStart_2611493 baseEnd_2611493 := by
    simpa [prefixWord, tailWord_2611493, baseEnd_2611493] using wordTrace_append hprefix tailTrace_2611493
  have hstable : (prefixWord ++ tailWord_2611493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611493).length < 2 ^ (prefixWord ++ tailWord_2611493).sum := by decide
  have hdescent : baseEnd_2611493 < baseStart_2611493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611532 : List Nat := [2, 2, 1, 3, 2, 1, 2, 3, 1, 4, 2]
def baseStart_2611532 : Nat := 118140960795 + 2611532 * 2 ^ 59
def prefixEnd_2611532 : Nat := 4983230072969 + 3 ^ 40 * 2611532 * 2
def baseEnd_2611532 : Nat := 1340971160597581602739789

theorem tailTrace_2611532 : CollatzResearch.WordTrace tailWord_2611532 prefixEnd_2611532 1340971160597581602739789 := by
  unfold tailWord_2611532
  simp only [CollatzResearch.WordTrace]
  refine ⟨47625198587436526500854425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63500264783248702001139233 47625198587436526500854425)
  ·
    refine ⟨35718898940577394875640819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47625198587436526500854425 35718898940577394875640819)
    ·
      refine ⟨53578348410866092313461229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35718898940577394875640819 53578348410866092313461229)
      ·
        refine ⟨20091880654074784617547961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53578348410866092313461229 20091880654074784617547961)
        ·
          refine ⟨15068910490556088463160971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20091880654074784617547961 15068910490556088463160971)
          ·
            refine ⟨22603365735834132694741457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15068910490556088463160971 22603365735834132694741457)
            ·
              refine ⟨16952524301875599521056093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22603365735834132694741457 16952524301875599521056093)
              ·
                refine ⟨6357196613203349820396035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16952524301875599521056093 6357196613203349820396035)
                ·
                  refine ⟨9535794919805024730594053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6357196613203349820396035 9535794919805024730594053)
                  ·
                    refine ⟨1787961547463442136986385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9535794919805024730594053 1787961547463442136986385)
                    ·
                      refine ⟨1340971160597581602739789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1787961547463442136986385 1340971160597581602739789)
                      ·
                        rfl

theorem cell23_2611532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_2611532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611532 prefixEnd_2611532 := by exact prefixLift 2611532
  have htrace : WordTrace (prefixWord ++ tailWord_2611532) baseStart_2611532 baseEnd_2611532 := by
    simpa [prefixWord, tailWord_2611532, baseEnd_2611532] using wordTrace_append hprefix tailTrace_2611532
  have hstable : (prefixWord ++ tailWord_2611532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611532).length < 2 ^ (prefixWord ++ tailWord_2611532).sum := by decide
  have hdescent : baseEnd_2611532 < baseStart_2611532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611592 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 2, 5, 2]
def baseStart_2611592 : Nat := 118140960795 + 2611592 * 2 ^ 59
def prefixEnd_2611592 : Nat := 4983230072969 + 3 ^ 40 * 2611592 * 2
def baseEnd_2611592 : Nat := 1341001969436851367989513

theorem tailTrace_2611592 : CollatzResearch.WordTrace tailWord_2611592 prefixEnd_2611592 1341001969436851367989513 := by
  unfold tailWord_2611592
  simp only [CollatzResearch.WordTrace]
  refine ⟨47626292777327841624446515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63501723703103788832595353 47626292777327841624446515)
  ·
    refine ⟨71439439165991762436669773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47626292777327841624446515 71439439165991762436669773)
    ·
      refine ⟨26789789687246910913751165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71439439165991762436669773 26789789687246910913751165)
      ·
        refine ⟨10046171132717591592656687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26789789687246910913751165 10046171132717591592656687)
        ·
          refine ⟨15069256699076387388985031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10046171132717591592656687 15069256699076387388985031)
          ·
            refine ⟨22603885048614581083477547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15069256699076387388985031 22603885048614581083477547)
            ·
              refine ⟨33905827572921871625216321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22603885048614581083477547 33905827572921871625216321)
              ·
                refine ⟨25429370679691403718912241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33905827572921871625216321 25429370679691403718912241)
                ·
                  refine ⟨19072028009768552789184181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25429370679691403718912241 19072028009768552789184181)
                  ·
                    refine ⟨1788002625915801823986017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19072028009768552789184181 1788002625915801823986017)
                    ·
                      refine ⟨1341001969436851367989513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1788002625915801823986017 1341001969436851367989513)
                      ·
                        rfl

theorem cell23_2611592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_2611592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611592 prefixEnd_2611592 := by exact prefixLift 2611592
  have htrace : WordTrace (prefixWord ++ tailWord_2611592) baseStart_2611592 baseEnd_2611592 := by
    simpa [prefixWord, tailWord_2611592, baseEnd_2611592] using wordTrace_append hprefix tailTrace_2611592
  have hstable : (prefixWord ++ tailWord_2611592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611592).length < 2 ^ (prefixWord ++ tailWord_2611592).sum := by decide
  have hdescent : baseEnd_2611592 < baseStart_2611592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611683 : List Nat := [1, 1, 1, 6, 3, 1, 3, 2, 1, 4]
def baseStart_2611683 : Nat := 118140960795 + 2611683 * 2 ^ 59
def prefixEnd_2611683 : Nat := 4983230072969 + 3 ^ 40 * 2611683 * 2
def baseEnd_2611683 : Nat := 447016232058803503983865

theorem tailTrace_2611683 : CollatzResearch.WordTrace tailWord_2611683 prefixEnd_2611683 447016232058803503983865 := by
  unfold tailWord_2611683
  simp only [CollatzResearch.WordTrace]
  refine ⟨95255904597326005790455703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63503936398217337193637135 95255904597326005790455703)
  ·
    refine ⟨142883856895989008685683555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95255904597326005790455703 142883856895989008685683555)
    ·
      refine ⟨214325785343983513028525333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142883856895989008685683555 214325785343983513028525333)
      ·
        refine ⟨10046521187999227173212125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 214325785343983513028525333 10046521187999227173212125)
        ·
          refine ⟨3767445445499710189954547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10046521187999227173212125 3767445445499710189954547)
          ·
            refine ⟨5651168168249565284931821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3767445445499710189954547 5651168168249565284931821)
            ·
              refine ⟨2119188063093586981849433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5651168168249565284931821 2119188063093586981849433)
              ·
                refine ⟨1589391047320190236387075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2119188063093586981849433 1589391047320190236387075)
                ·
                  refine ⟨2384086570980285354580613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1589391047320190236387075 2384086570980285354580613)
                  ·
                    refine ⟨447016232058803503983865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2384086570980285354580613 447016232058803503983865)
                    ·
                      rfl

theorem cell23_2611683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 2, 1, 4].length) (baseStart_2611683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611683 prefixEnd_2611683 := by exact prefixLift 2611683
  have htrace : WordTrace (prefixWord ++ tailWord_2611683) baseStart_2611683 baseEnd_2611683 := by
    simpa [prefixWord, tailWord_2611683, baseEnd_2611683] using wordTrace_append hprefix tailTrace_2611683
  have hstable : (prefixWord ++ tailWord_2611683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611683).length < 2 ^ (prefixWord ++ tailWord_2611683).sum := by decide
  have hdescent : baseEnd_2611683 < baseStart_2611683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611695 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 4]
def baseStart_2611695 : Nat := 118140960795 + 2611695 * 2 ^ 59
def prefixEnd_2611695 : Nat := 4983230072969 + 3 ^ 40 * 2611695 * 2
def baseEnd_2611695 : Nat := 1341054857944264465001539

theorem tailTrace_2611695 : CollatzResearch.WordTrace tailWord_2611695 prefixEnd_2611695 1341054857944264465001539 := by
  unfold tailWord_2611695
  simp only [CollatzResearch.WordTrace]
  refine ⟨95256342273282531839892539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63504228182188354559928359 95256342273282531839892539)
  ·
    refine ⟨142884513409923797759838809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95256342273282531839892539 142884513409923797759838809)
    ·
      refine ⟨107163385057442848319879107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142884513409923797759838809 107163385057442848319879107)
      ·
        refine ⟨160745077586164272479818661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107163385057442848319879107 160745077586164272479818661)
        ·
          refine ⟨30139702047405801089965999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 160745077586164272479818661 30139702047405801089965999)
          ·
            refine ⟨45209553071108701634948999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30139702047405801089965999 45209553071108701634948999)
            ·
              refine ⟨67814329606663052452423499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45209553071108701634948999 67814329606663052452423499)
              ·
                refine ⟨101721494409994578678635249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67814329606663052452423499 101721494409994578678635249)
                ·
                  refine ⟨76291120807495934008976437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101721494409994578678635249 76291120807495934008976437)
                  ·
                    refine ⟨7152292575702743813341541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 76291120807495934008976437 7152292575702743813341541)
                    ·
                      refine ⟨1341054857944264465001539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7152292575702743813341541 1341054857944264465001539)
                      ·
                        rfl

theorem cell23_2611695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 4].length) (baseStart_2611695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611695 prefixEnd_2611695 := by exact prefixLift 2611695
  have htrace : WordTrace (prefixWord ++ tailWord_2611695) baseStart_2611695 baseEnd_2611695 := by
    simpa [prefixWord, tailWord_2611695, baseEnd_2611695] using wordTrace_append hprefix tailTrace_2611695
  have hstable : (prefixWord ++ tailWord_2611695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611695).length < 2 ^ (prefixWord ++ tailWord_2611695).sum := by decide
  have hdescent : baseEnd_2611695 < baseStart_2611695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611716 : List Nat := [2, 3, 2, 3, 1, 1, 1, 3, 2, 3, 2]
def baseStart_2611716 : Nat := 118140960795 + 2611716 * 2 ^ 59
def prefixEnd_2611716 : Nat := 4983230072969 + 3 ^ 40 * 2611716 * 2
def baseEnd_2611716 : Nat := 1341065641038008882838943

theorem tailTrace_2611716 : CollatzResearch.WordTrace tailWord_2611716 prefixEnd_2611716 1341065641038008882838943 := by
  unfold tailWord_2611716
  simp only [CollatzResearch.WordTrace]
  refine ⟨47628554103103226213203501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63504738804137634950938001 47628554103103226213203501)
  ·
    refine ⟨17860707788663709829951313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47628554103103226213203501 17860707788663709829951313)
    ·
      refine ⟨13395530841497782372463485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17860707788663709829951313 13395530841497782372463485)
      ·
        refine ⟨5023324065561668389673807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13395530841497782372463485 5023324065561668389673807)
        ·
          refine ⟨7534986098342502584510711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5023324065561668389673807 7534986098342502584510711)
          ·
            refine ⟨11302479147513753876766067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7534986098342502584510711 11302479147513753876766067)
            ·
              refine ⟨16953718721270630815149101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11302479147513753876766067 16953718721270630815149101)
              ·
                refine ⟨6357644520476486555680913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16953718721270630815149101 6357644520476486555680913)
                ·
                  refine ⟨4768233390357364916760685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6357644520476486555680913 4768233390357364916760685)
                  ·
                    refine ⟨1788087521384011843785257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4768233390357364916760685 1788087521384011843785257)
                    ·
                      refine ⟨1341065641038008882838943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1788087521384011843785257 1341065641038008882838943)
                      ·
                        rfl

theorem cell23_2611716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_2611716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611716 prefixEnd_2611716 := by exact prefixLift 2611716
  have htrace : WordTrace (prefixWord ++ tailWord_2611716) baseStart_2611716 baseEnd_2611716 := by
    simpa [prefixWord, tailWord_2611716, baseEnd_2611716] using wordTrace_append hprefix tailTrace_2611716
  have hstable : (prefixWord ++ tailWord_2611716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611716).length < 2 ^ (prefixWord ++ tailWord_2611716).sum := by decide
  have hdescent : baseEnd_2611716 < baseStart_2611716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611722 : List Nat := [3, 1, 2, 2, 2, 1, 3, 2, 1, 6]
def baseStart_2611722 : Nat := 118140960795 + 2611722 * 2 ^ 59
def prefixEnd_2611722 : Nat := 4983230072969 + 3 ^ 40 * 2611722 * 2
def baseEnd_2611722 : Nat := 447022907307311953121305

theorem tailTrace_2611722 : CollatzResearch.WordTrace tailWord_2611722 prefixEnd_2611722 447022907307311953121305 := by
  unfold tailWord_2611722
  simp only [CollatzResearch.WordTrace]
  refine ⟨23814331761046178862781355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63504884696123143634083613 23814331761046178862781355)
  ·
    refine ⟨35721497641569268294172033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23814331761046178862781355 35721497641569268294172033)
    ·
      refine ⟨26791123231176951220629025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35721497641569268294172033 26791123231176951220629025)
      ·
        refine ⟨20093342423382713415471769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26791123231176951220629025 20093342423382713415471769)
        ·
          refine ⟨15070006817537035061603827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20093342423382713415471769 15070006817537035061603827)
          ·
            refine ⟨22605010226305552592405741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15070006817537035061603827 22605010226305552592405741)
            ·
              refine ⟨8476878834864582222152153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22605010226305552592405741 8476878834864582222152153)
              ·
                refine ⟨6357659126148436666614115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8476878834864582222152153 6357659126148436666614115)
                ·
                  refine ⟨9536488689222654999921173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6357659126148436666614115 9536488689222654999921173)
                  ·
                    refine ⟨447022907307311953121305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9536488689222654999921173 447022907307311953121305)
                    ·
                      rfl

theorem cell23_2611722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_2611722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611722 prefixEnd_2611722 := by exact prefixLift 2611722
  have htrace : WordTrace (prefixWord ++ tailWord_2611722) baseStart_2611722 baseEnd_2611722 := by
    simpa [prefixWord, tailWord_2611722, baseEnd_2611722] using wordTrace_append hprefix tailTrace_2611722
  have hstable : (prefixWord ++ tailWord_2611722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611722).length < 2 ^ (prefixWord ++ tailWord_2611722).sum := by decide
  have hdescent : baseEnd_2611722 < baseStart_2611722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611726 : List Nat := [4, 1, 1, 2, 3, 2, 3, 1, 1, 5]
def baseStart_2611726 : Nat := 118140960795 + 2611726 * 2 ^ 59
def prefixEnd_2611726 : Nat := 4983230072969 + 3 ^ 40 * 2611726 * 2
def baseEnd_2611726 : Nat := 447023591948184614571299

theorem tailTrace_2611726 : CollatzResearch.WordTrace tailWord_2611726 prefixEnd_2611726 447023591948184614571299 := by
  unfold tailWord_2611726
  simp only [CollatzResearch.WordTrace]
  refine ⟨11907184117021278016783879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63504981957446816089514021 11907184117021278016783879)
  ·
    refine ⟨17860776175531917025175819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11907184117021278016783879 17860776175531917025175819)
    ·
      refine ⟨26791164263297875537763729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17860776175531917025175819 26791164263297875537763729)
      ·
        refine ⟨20093373197473406653322797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26791164263297875537763729 20093373197473406653322797)
        ·
          refine ⟨7535014949052527494996049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20093373197473406653322797 7535014949052527494996049)
          ·
            refine ⟨5651261211789395621247037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7535014949052527494996049 5651261211789395621247037)
            ·
              refine ⟨2119222954421023357967639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5651261211789395621247037 2119222954421023357967639)
              ·
                refine ⟨3178834431631535036951459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2119222954421023357967639 3178834431631535036951459)
                ·
                  refine ⟨4768251647447302555427189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3178834431631535036951459 4768251647447302555427189)
                  ·
                    refine ⟨447023591948184614571299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4768251647447302555427189 447023591948184614571299)
                    ·
                      rfl

theorem cell23_2611726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 1, 5].length) (baseStart_2611726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611726 prefixEnd_2611726 := by exact prefixLift 2611726
  have htrace : WordTrace (prefixWord ++ tailWord_2611726) baseStart_2611726 baseEnd_2611726 := by
    simpa [prefixWord, tailWord_2611726, baseEnd_2611726] using wordTrace_append hprefix tailTrace_2611726
  have hstable : (prefixWord ++ tailWord_2611726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611726).length < 2 ^ (prefixWord ++ tailWord_2611726).sum := by decide
  have hdescent : baseEnd_2611726 < baseStart_2611726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611729 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 7, 2, 2]
def baseStart_2611729 : Nat := 118140960795 + 2611729 * 2 ^ 59
def prefixEnd_2611729 : Nat := 4983230072969 + 3 ^ 40 * 2611729 * 2
def baseEnd_2611729 : Nat := 1341072316286517331976383

theorem tailTrace_2611729 : CollatzResearch.WordTrace tailWord_2611729 prefixEnd_2611729 1341072316286517331976383 := by
  unfold tailWord_2611729
  simp only [CollatzResearch.WordTrace]
  refine ⟨95257582355159355646630241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63505054903439570431086827 95257582355159355646630241)
  ·
    refine ⟨71443186766369516734972681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95257582355159355646630241 71443186766369516734972681)
    ·
      refine ⟨53582390074777137551229511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71443186766369516734972681 53582390074777137551229511)
      ·
        refine ⟨80373585112165706326844267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53582390074777137551229511 80373585112165706326844267)
        ·
          refine ⟨120560377668248559490266401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80373585112165706326844267 120560377668248559490266401)
          ·
            refine ⟨90420283251186419617699801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120560377668248559490266401 90420283251186419617699801)
            ·
              refine ⟨67815212438389814713274851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90420283251186419617699801 67815212438389814713274851)
              ·
                refine ⟨101722818657584722069912277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67815212438389814713274851 101722818657584722069912277)
                ·
                  refine ⟨2384128562287141923513569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 101722818657584722069912277 2384128562287141923513569)
                  ·
                    refine ⟨1788096421715356442635177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2384128562287141923513569 1788096421715356442635177)
                    ·
                      refine ⟨1341072316286517331976383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1788096421715356442635177 1341072316286517331976383)
                      ·
                        rfl

theorem cell23_2611729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 7, 2, 2].length) (baseStart_2611729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611729 prefixEnd_2611729 := by exact prefixLift 2611729
  have htrace : WordTrace (prefixWord ++ tailWord_2611729) baseStart_2611729 baseEnd_2611729 := by
    simpa [prefixWord, tailWord_2611729, baseEnd_2611729] using wordTrace_append hprefix tailTrace_2611729
  have hstable : (prefixWord ++ tailWord_2611729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611729).length < 2 ^ (prefixWord ++ tailWord_2611729).sum := by decide
  have hdescent : baseEnd_2611729 < baseStart_2611729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611740 : List Nat := [2, 2, 3, 1, 2, 4, 2, 2, 1, 1, 3]
def baseStart_2611740 : Nat := 118140960795 + 2611740 * 2 ^ 59
def prefixEnd_2611740 : Nat := 4983230072969 + 3 ^ 40 * 2611740 * 2
def baseEnd_2611740 : Nat := 1341077964573716788938833

theorem tailTrace_2611740 : CollatzResearch.WordTrace tailWord_2611740 prefixEnd_2611740 1341077964573716788938833 := by
  unfold tailWord_2611740
  simp only [CollatzResearch.WordTrace]
  refine ⟨47628991779059752262640337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63505322372079669683520449 47628991779059752262640337)
  ·
    refine ⟨35721743834294814196980253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47628991779059752262640337 35721743834294814196980253)
    ·
      refine ⟨13395653937860555323867595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35721743834294814196980253 13395653937860555323867595)
      ·
        refine ⟨20093480906790832985801393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13395653937860555323867595 20093480906790832985801393)
        ·
          refine ⟨15070110680093124739351045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20093480906790832985801393 15070110680093124739351045)
          ·
            refine ⟨2825645752517460888628321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15070110680093124739351045 2825645752517460888628321)
            ·
              refine ⟨2119234314388095666471241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2825645752517460888628321 2119234314388095666471241)
              ·
                refine ⟨1589425735791071749853431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2119234314388095666471241 1589425735791071749853431)
                ·
                  refine ⟨2384138603686607624780147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1589425735791071749853431 2384138603686607624780147)
                  ·
                    refine ⟨3576207905529911437170221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2384138603686607624780147 3576207905529911437170221)
                    ·
                      refine ⟨1341077964573716788938833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3576207905529911437170221 1341077964573716788938833)
                      ·
                        rfl

theorem cell23_2611740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_2611740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611740 prefixEnd_2611740 := by exact prefixLift 2611740
  have htrace : WordTrace (prefixWord ++ tailWord_2611740) baseStart_2611740 baseEnd_2611740 := by
    simpa [prefixWord, tailWord_2611740, baseEnd_2611740] using wordTrace_append hprefix tailTrace_2611740
  have hstable : (prefixWord ++ tailWord_2611740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611740).length < 2 ^ (prefixWord ++ tailWord_2611740).sum := by decide
  have hdescent : baseEnd_2611740 < baseStart_2611740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611746 : List Nat := [3, 3, 1, 1, 1, 1, 1, 5, 3, 2, 2]
def baseStart_2611746 : Nat := 118140960795 + 2611746 * 2 ^ 59
def prefixEnd_2611746 : Nat := 4983230072969 + 3 ^ 40 * 2611746 * 2
def baseEnd_2611746 : Nat := 1341081045457643765463805

theorem tailTrace_2611746 : CollatzResearch.WordTrace tailWord_2611746 prefixEnd_2611746 1341081045457643765463805 := by
  unfold tailWord_2611746
  simp only [CollatzResearch.WordTrace]
  refine ⟨23814550599024441887499773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63505468264065178366666061 23814550599024441887499773)
  ·
    refine ⟨8930456474634165707812415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23814550599024441887499773 8930456474634165707812415)
    ·
      refine ⟨13395684711951248561718623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8930456474634165707812415 13395684711951248561718623)
      ·
        refine ⟨20093527067926872842577935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13395684711951248561718623 20093527067926872842577935)
        ·
          refine ⟨30140290601890309263866903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20093527067926872842577935 30140290601890309263866903)
          ·
            refine ⟨45210435902835463895800355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30140290601890309263866903 45210435902835463895800355)
            ·
              refine ⟨67815653854253195843700533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45210435902835463895800355 67815653854253195843700533)
              ·
                refine ⟨6357717548836237110346925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67815653854253195843700533 6357717548836237110346925)
                ·
                  refine ⟨2384144080813588916380097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6357717548836237110346925 2384144080813588916380097)
                  ·
                    refine ⟨1788108060610191687285073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2384144080813588916380097 1788108060610191687285073)
                    ·
                      refine ⟨1341081045457643765463805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1788108060610191687285073 1341081045457643765463805)
                      ·
                        rfl

theorem cell23_2611746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_2611746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611746 prefixEnd_2611746 := by exact prefixLift 2611746
  have htrace : WordTrace (prefixWord ++ tailWord_2611746) baseStart_2611746 baseEnd_2611746 := by
    simpa [prefixWord, tailWord_2611746, baseEnd_2611746] using wordTrace_append hprefix tailTrace_2611746
  have hstable : (prefixWord ++ tailWord_2611746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611746).length < 2 ^ (prefixWord ++ tailWord_2611746).sum := by decide
  have hdescent : baseEnd_2611746 < baseStart_2611746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611755 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 6]
def baseStart_2611755 : Nat := 118140960795 + 2611755 * 2 ^ 59
def prefixEnd_2611755 : Nat := 4983230072969 + 3 ^ 40 * 2611755 * 2
def baseEnd_2611755 : Nat := 1341085666783534230251263

theorem tailTrace_2611755 : CollatzResearch.WordTrace tailWord_2611755 prefixEnd_2611755 1341085666783534230251263 := by
  unfold tailWord_2611755
  simp only [CollatzResearch.WordTrace]
  refine ⟨95258530653065162087076719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63505687102043441391384479 95258530653065162087076719)
  ·
    refine ⟨142887795979597743130615079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95258530653065162087076719 142887795979597743130615079)
    ·
      refine ⟨214331693969396614695922619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142887795979597743130615079 214331693969396614695922619)
      ·
        refine ⟨321497540954094922043883929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214331693969396614695922619 321497540954094922043883929)
        ·
          refine ⟨241123155715571191532912947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321497540954094922043883929 241123155715571191532912947)
          ·
            refine ⟨361684733573356787299369421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241123155715571191532912947 361684733573356787299369421)
            ·
              refine ⟨135631775090008795237263533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 361684733573356787299369421 135631775090008795237263533)
              ·
                refine ⟨50861915658753298213973825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135631775090008795237263533 50861915658753298213973825)
                ·
                  refine ⟨38146436744064973660480369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50861915658753298213973825 38146436744064973660480369)
                  ·
                    refine ⟨28609827558048730245360277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38146436744064973660480369 28609827558048730245360277)
                    ·
                      refine ⟨1341085666783534230251263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28609827558048730245360277 1341085666783534230251263)
                      ·
                        rfl

theorem cell23_2611755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 6].length) (baseStart_2611755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611755 prefixEnd_2611755 := by exact prefixLift 2611755
  have htrace : WordTrace (prefixWord ++ tailWord_2611755) baseStart_2611755 baseEnd_2611755 := by
    simpa [prefixWord, tailWord_2611755, baseEnd_2611755] using wordTrace_append hprefix tailTrace_2611755
  have hstable : (prefixWord ++ tailWord_2611755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611755).length < 2 ^ (prefixWord ++ tailWord_2611755).sum := by decide
  have hdescent : baseEnd_2611755 < baseStart_2611755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611766 : List Nat := [5, 1, 2, 1, 2, 1, 2, 1, 3, 2, 3]
def baseStart_2611766 : Nat := 118140960795 + 2611766 * 2 ^ 59
def prefixEnd_2611766 : Nat := 4983230072969 + 3 ^ 40 * 2611766 * 2
def baseEnd_2611766 : Nat := 1341091315070733687213713

theorem tailTrace_2611766 : CollatzResearch.WordTrace tailWord_2611766 prefixEnd_2611766 1341091315070733687213713 := by
  unfold tailWord_2611766
  simp only [CollatzResearch.WordTrace]
  refine ⟨5953683241001581935357947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63505954570683540643818101 5953683241001581935357947)
  ·
    refine ⟨8930524861502372903036921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5953683241001581935357947 8930524861502372903036921)
    ·
      refine ⟨6697893646126779677277691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8930524861502372903036921 6697893646126779677277691)
      ·
        refine ⟨10046840469190169515916537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6697893646126779677277691 10046840469190169515916537)
        ·
          refine ⟨7535130351892627136937403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10046840469190169515916537 7535130351892627136937403)
          ·
            refine ⟨11302695527838940705406105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7535130351892627136937403 11302695527838940705406105)
            ·
              refine ⟨8477021645879205529054579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11302695527838940705406105 8477021645879205529054579)
              ·
                refine ⟨12715532468818808293581869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8477021645879205529054579 12715532468818808293581869)
                ·
                  refine ⟨4768324675807053110093201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12715532468818808293581869 4768324675807053110093201)
                  ·
                    refine ⟨3576243506855289832569901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4768324675807053110093201 3576243506855289832569901)
                    ·
                      refine ⟨1341091315070733687213713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3576243506855289832569901 1341091315070733687213713)
                      ·
                        rfl

theorem cell23_2611766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_2611766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611766 prefixEnd_2611766 := by exact prefixLift 2611766
  have htrace : WordTrace (prefixWord ++ tailWord_2611766) baseStart_2611766 baseEnd_2611766 := by
    simpa [prefixWord, tailWord_2611766, baseEnd_2611766] using wordTrace_append hprefix tailTrace_2611766
  have hstable : (prefixWord ++ tailWord_2611766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611766).length < 2 ^ (prefixWord ++ tailWord_2611766).sum := by decide
  have hdescent : baseEnd_2611766 < baseStart_2611766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611780 : List Nat := [2, 3, 5, 1, 1, 1, 1, 3, 1, 1, 4]
def baseStart_2611780 : Nat := 118140960795 + 2611780 * 2 ^ 59
def prefixEnd_2611780 : Nat := 4983230072969 + 3 ^ 40 * 2611780 * 2
def baseEnd_2611780 : Nat := 1341098503799896632438649

theorem tailTrace_2611780 : CollatzResearch.WordTrace tailWord_2611780 prefixEnd_2611780 1341098503799896632438649 := by
  unfold tailWord_2611780
  simp only [CollatzResearch.WordTrace]
  refine ⟨47629721238987295678368397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63506294985316394237824529 47629721238987295678368397)
  ·
    refine ⟨17861145464620235879388149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47629721238987295678368397 17861145464620235879388149)
    ·
      refine ⟨1674482387308147113692639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17861145464620235879388149 1674482387308147113692639)
      ·
        refine ⟨2511723580962220670538959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1674482387308147113692639 2511723580962220670538959)
        ·
          refine ⟨3767585371443331005808439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2511723580962220670538959 3767585371443331005808439)
          ·
            refine ⟨5651378057164996508712659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3767585371443331005808439 5651378057164996508712659)
            ·
              refine ⟨8477067085747494763068989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5651378057164996508712659 8477067085747494763068989)
              ·
                refine ⟨3178900157155310536150871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8477067085747494763068989 3178900157155310536150871)
                ·
                  refine ⟨4768350235732965804226307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3178900157155310536150871 4768350235732965804226307)
                  ·
                    refine ⟨7152525353599448706339461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4768350235732965804226307 7152525353599448706339461)
                    ·
                      refine ⟨1341098503799896632438649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7152525353599448706339461 1341098503799896632438649)
                      ·
                        rfl

theorem cell23_2611780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_2611780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611780 prefixEnd_2611780 := by exact prefixLift 2611780
  have htrace : WordTrace (prefixWord ++ tailWord_2611780) baseStart_2611780 baseEnd_2611780 := by
    simpa [prefixWord, tailWord_2611780, baseEnd_2611780] using wordTrace_append hprefix tailTrace_2611780
  have hstable : (prefixWord ++ tailWord_2611780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611780).length < 2 ^ (prefixWord ++ tailWord_2611780).sum := by decide
  have hdescent : baseEnd_2611780 < baseStart_2611780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611783 : List Nat := [1, 1, 4, 1, 4, 3, 2, 1, 1, 2, 3]
def baseStart_2611783 : Nat := 118140960795 + 2611783 * 2 ^ 59
def prefixEnd_2611783 : Nat := 4983230072969 + 3 ^ 40 * 2611783 * 2
def baseEnd_2611783 : Nat := 1341100044241860120701135

theorem tailTrace_2611783 : CollatzResearch.WordTrace tailWord_2611783 prefixEnd_2611783 1341100044241860120701135 := by
  unfold tailWord_2611783
  simp only [CollatzResearch.WordTrace]
  refine ⟨95259551896963722869096003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63506367931309148579397335 95259551896963722869096003)
  ·
    refine ⟨142889327845445584303644005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95259551896963722869096003 142889327845445584303644005)
    ·
      refine ⟨26791748971021047056933251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142889327845445584303644005 26791748971021047056933251)
      ·
        refine ⟨40187623456531570585399877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26791748971021047056933251 40187623456531570585399877)
        ·
          refine ⟨7535179398099669484762477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40187623456531570585399877 7535179398099669484762477)
          ·
            refine ⟨2825692274287376056785929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7535179398099669484762477 2825692274287376056785929)
            ·
              refine ⟨2119269205715532042589447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2825692274287376056785929 2119269205715532042589447)
              ·
                refine ⟨3178903808573298063884171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2119269205715532042589447 3178903808573298063884171)
                ·
                  refine ⟨4768355712859947095826257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3178903808573298063884171 4768355712859947095826257)
                  ·
                    refine ⟨3576266784644960321869693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4768355712859947095826257 3576266784644960321869693)
                    ·
                      refine ⟨1341100044241860120701135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3576266784644960321869693 1341100044241860120701135)
                      ·
                        rfl

theorem cell23_2611783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 1, 2, 3].length) (baseStart_2611783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611783 prefixEnd_2611783 := by exact prefixLift 2611783
  have htrace : WordTrace (prefixWord ++ tailWord_2611783) baseStart_2611783 baseEnd_2611783 := by
    simpa [prefixWord, tailWord_2611783, baseEnd_2611783] using wordTrace_append hprefix tailTrace_2611783
  have hstable : (prefixWord ++ tailWord_2611783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611783).length < 2 ^ (prefixWord ++ tailWord_2611783).sum := by decide
  have hdescent : baseEnd_2611783 < baseStart_2611783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611796 : List Nat := [2, 4, 1, 1, 1, 4, 1, 1, 4, 1, 3]
def baseStart_2611796 : Nat := 118140960795 + 2611796 * 2 ^ 59
def prefixEnd_2611796 : Nat := 4983230072969 + 3 ^ 40 * 2611796 * 2
def baseEnd_2611796 : Nat := 1341106719490368569838575

theorem tailTrace_2611796 : CollatzResearch.WordTrace tailWord_2611796 prefixEnd_2611796 1341106719490368569838575 := by
  unfold tailWord_2611796
  simp only [CollatzResearch.WordTrace]
  refine ⟨47630013022958313044659621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63506684030611084059546161 47630013022958313044659621)
  ·
    refine ⟨8930627441804683695873679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47630013022958313044659621 8930627441804683695873679)
    ·
      refine ⟨13395941162707025543810519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8930627441804683695873679 13395941162707025543810519)
      ·
        refine ⟨20093911744060538315715779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13395941162707025543810519 20093911744060538315715779)
        ·
          refine ⟨30140867616090807473573669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20093911744060538315715779 30140867616090807473573669)
          ·
            refine ⟨5651412678017026401295063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30140867616090807473573669 5651412678017026401295063)
            ·
              refine ⟨8477119017025539601942595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5651412678017026401295063 8477119017025539601942595)
              ·
                refine ⟨12715678525538309402913893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8477119017025539601942595 12715678525538309402913893)
                ·
                  refine ⟨2384189723538433013046355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12715678525538309402913893 2384189723538433013046355)
                  ·
                    refine ⟨3576284585307649519569533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2384189723538433013046355 3576284585307649519569533)
                    ·
                      refine ⟨1341106719490368569838575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3576284585307649519569533 1341106719490368569838575)
                      ·
                        rfl

theorem cell23_2611796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_2611796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611796 prefixEnd_2611796 := by exact prefixLift 2611796
  have htrace : WordTrace (prefixWord ++ tailWord_2611796) baseStart_2611796 baseEnd_2611796 := by
    simpa [prefixWord, tailWord_2611796, baseEnd_2611796] using wordTrace_append hprefix tailTrace_2611796
  have hstable : (prefixWord ++ tailWord_2611796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611796).length < 2 ^ (prefixWord ++ tailWord_2611796).sum := by decide
  have hdescent : baseEnd_2611796 < baseStart_2611796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611810 : List Nat := [3, 3, 2, 3, 2, 1, 1, 1, 1, 2, 4]
def baseStart_2611810 : Nat := 118140960795 + 2611810 * 2 ^ 59
def prefixEnd_2611810 : Nat := 4983230072969 + 3 ^ 40 * 2611810 * 2
def baseEnd_2611810 : Nat := 1341113908219531515063511

theorem tailTrace_2611810 : CollatzResearch.WordTrace tailWord_2611810 prefixEnd_2611810 1341113908219531515063511 := by
  unfold tailWord_2611810
  simp only [CollatzResearch.WordTrace]
  refine ⟨23815134166966476620082221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63507024445243937653552589 23815134166966476620082221)
  ·
    refine ⟨8930675312612428732530833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23815134166966476620082221 8930675312612428732530833)
    ·
      refine ⟨6698006484459321549398125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8930675312612428732530833 6698006484459321549398125)
      ·
        refine ⟨2511752431672245581024297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6698006484459321549398125 2511752431672245581024297)
        ·
          refine ⟨1883814323754184185768223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2511752431672245581024297 1883814323754184185768223)
          ·
            refine ⟨2825721485631276278652335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1883814323754184185768223 2825721485631276278652335)
            ·
              refine ⟨4238582228446914417978503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2825721485631276278652335 4238582228446914417978503)
              ·
                refine ⟨6357873342670371626967755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4238582228446914417978503 6357873342670371626967755)
                ·
                  refine ⟨9536810014005557440451633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6357873342670371626967755 9536810014005557440451633)
                  ·
                    refine ⟨7152607510504168080338725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9536810014005557440451633 7152607510504168080338725)
                    ·
                      refine ⟨1341113908219531515063511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7152607510504168080338725 1341113908219531515063511)
                      ·
                        rfl

theorem cell23_2611810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_2611810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611810 prefixEnd_2611810 := by exact prefixLift 2611810
  have htrace : WordTrace (prefixWord ++ tailWord_2611810) baseStart_2611810 baseEnd_2611810 := by
    simpa [prefixWord, tailWord_2611810, baseEnd_2611810] using wordTrace_append hprefix tailTrace_2611810
  have hstable : (prefixWord ++ tailWord_2611810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611810).length < 2 ^ (prefixWord ++ tailWord_2611810).sum := by decide
  have hdescent : baseEnd_2611810 < baseStart_2611810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611812 : List Nat := [2, 3, 1, 1, 2, 2, 1, 3, 2, 6]
def baseStart_2611812 : Nat := 118140960795 + 2611812 * 2 ^ 59
def prefixEnd_2611812 : Nat := 4983230072969 + 3 ^ 40 * 2611812 * 2
def baseEnd_2611812 : Nat := 447038311726946835746167

theorem tailTrace_2611812 : CollatzResearch.WordTrace tailWord_2611812 prefixEnd_2611812 447038311726946835746167 := by
  unfold tailWord_2611812
  simp only [CollatzResearch.WordTrace]
  refine ⟨47630304806929330410950845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63507073075905773881267793 47630304806929330410950845)
  ·
    refine ⟨17861364302598498904106567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47630304806929330410950845 17861364302598498904106567)
    ·
      refine ⟨26792046453897748356159851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17861364302598498904106567 26792046453897748356159851)
      ·
        refine ⟨40188069680846622534239777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26792046453897748356159851 40188069680846622534239777)
        ·
          refine ⟨30141052260634966900679833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40188069680846622534239777 30141052260634966900679833)
          ·
            refine ⟨22605789195476225175509875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30141052260634966900679833 22605789195476225175509875)
            ·
              refine ⟨33908683793214337763264813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22605789195476225175509875 33908683793214337763264813)
              ·
                refine ⟨12715756422455376661224305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33908683793214337763264813 12715756422455376661224305)
                ·
                  refine ⟨9536817316841532495918229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12715756422455376661224305 9536817316841532495918229)
                  ·
                    refine ⟨447038311726946835746167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9536817316841532495918229 447038311726946835746167)
                    ·
                      rfl

theorem cell23_2611812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_2611812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611812 prefixEnd_2611812 := by exact prefixLift 2611812
  have htrace : WordTrace (prefixWord ++ tailWord_2611812) baseStart_2611812 baseEnd_2611812 := by
    simpa [prefixWord, tailWord_2611812, baseEnd_2611812] using wordTrace_append hprefix tailTrace_2611812
  have hstable : (prefixWord ++ tailWord_2611812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611812).length < 2 ^ (prefixWord ++ tailWord_2611812).sum := by decide
  have hdescent : baseEnd_2611812 < baseStart_2611812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611813 : List Nat := [1, 3, 1, 3, 5, 1, 1, 1, 1, 3, 3]
def baseStart_2611813 : Nat := 118140960795 + 2611813 * 2 ^ 59
def prefixEnd_2611813 : Nat := 4983230072969 + 3 ^ 40 * 2611813 * 2
def baseEnd_2611813 : Nat := 1341115448661495003325997

theorem tailTrace_2611813 : CollatzResearch.WordTrace tailWord_2611813 prefixEnd_2611813 1341115448661495003325997 := by
  unfold tailWord_2611813
  simp only [CollatzResearch.WordTrace]
  refine ⟨95260646086855037992688093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63507097391236691995125395 95260646086855037992688093)
  ·
    refine ⟨35722742282570639247258035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95260646086855037992688093 35722742282570639247258035)
    ·
      refine ⟨53584113423855958870887053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35722742282570639247258035 53584113423855958870887053)
      ·
        refine ⟨20094042533945984576582645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53584113423855958870887053 20094042533945984576582645)
        ·
          refine ⟨1883816487557436054054623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20094042533945984576582645 1883816487557436054054623)
          ·
            refine ⟨2825724731336154081081935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1883816487557436054054623 2825724731336154081081935)
            ·
              refine ⟨4238587097004231121622903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2825724731336154081081935 4238587097004231121622903)
              ·
                refine ⟨6357880645506346682434355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4238587097004231121622903 6357880645506346682434355)
                ·
                  refine ⟨9536820968259520023651533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6357880645506346682434355 9536820968259520023651533)
                  ·
                    refine ⟨3576307863097320008869325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9536820968259520023651533 3576307863097320008869325)
                    ·
                      refine ⟨1341115448661495003325997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3576307863097320008869325 1341115448661495003325997)
                      ·
                        rfl

theorem cell23_2611813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_2611813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611813 prefixEnd_2611813 := by exact prefixLift 2611813
  have htrace : WordTrace (prefixWord ++ tailWord_2611813) baseStart_2611813 baseEnd_2611813 := by
    simpa [prefixWord, tailWord_2611813, baseEnd_2611813] using wordTrace_append hprefix tailTrace_2611813
  have hstable : (prefixWord ++ tailWord_2611813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611813).length < 2 ^ (prefixWord ++ tailWord_2611813).sum := by decide
  have hdescent : baseEnd_2611813 < baseStart_2611813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611819 : List Nat := [1, 1, 1, 1, 2, 2, 1, 7, 1, 4, 2]
def baseStart_2611819 : Nat := 118140960795 + 2611819 * 2 ^ 59
def prefixEnd_2611819 : Nat := 4983230072969 + 3 ^ 40 * 2611819 * 2
def baseEnd_2611819 : Nat := 1341118529545421979850969

theorem tailTrace_2611819 : CollatzResearch.WordTrace tailWord_2611819 prefixEnd_2611819 1341118529545421979850969 := by
  unfold tailWord_2611819
  simp only [CollatzResearch.WordTrace]
  refine ⟨95260864924833301017406511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63507243283222200678271007 95260864924833301017406511)
  ·
    refine ⟨142891297387249951526109767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95260864924833301017406511 142891297387249951526109767)
    ·
      refine ⟨214336946080874927289164651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142891297387249951526109767 214336946080874927289164651)
      ·
        refine ⟨321505419121312390933746977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214336946080874927289164651 321505419121312390933746977)
        ·
          refine ⟨241129064340984293200310233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321505419121312390933746977 241129064340984293200310233)
          ·
            refine ⟨180846798255738219900232675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241129064340984293200310233 180846798255738219900232675)
            ·
              refine ⟨271270197383607329850349013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180846798255738219900232675 271270197383607329850349013)
              ·
                refine ⟨6357895251178296793367555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 271270197383607329850349013 6357895251178296793367555)
                ·
                  refine ⟨9536842876767445190051333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6357895251178296793367555 9536842876767445190051333)
                  ·
                    refine ⟨1788158039393895973134625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9536842876767445190051333 1788158039393895973134625)
                    ·
                      refine ⟨1341118529545421979850969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1788158039393895973134625 1341118529545421979850969)
                      ·
                        rfl

theorem cell23_2611819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 4, 2].length) (baseStart_2611819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611819 prefixEnd_2611819 := by exact prefixLift 2611819
  have htrace : WordTrace (prefixWord ++ tailWord_2611819) baseStart_2611819 baseEnd_2611819 := by
    simpa [prefixWord, tailWord_2611819, baseEnd_2611819] using wordTrace_append hprefix tailTrace_2611819
  have hstable : (prefixWord ++ tailWord_2611819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611819).length < 2 ^ (prefixWord ++ tailWord_2611819).sum := by decide
  have hdescent : baseEnd_2611819 < baseStart_2611819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611836 : List Nat := [2, 2, 2, 1, 1, 2, 3, 2, 4, 2, 2]
def baseStart_2611836 : Nat := 118140960795 + 2611836 * 2 ^ 59
def prefixEnd_2611836 : Nat := 4983230072969 + 3 ^ 40 * 2611836 * 2
def baseEnd_2611836 : Nat := 1341127258716548413338391

theorem tailTrace_2611836 : CollatzResearch.WordTrace tailWord_2611836 prefixEnd_2611836 1341127258716548413338391 := by
  unfold tailWord_2611836
  simp only [CollatzResearch.WordTrace]
  refine ⟨47630742482885856460387681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63507656643847808613850241 47630742482885856460387681)
  ·
    refine ⟨35723056862164392345290761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47630742482885856460387681 35723056862164392345290761)
    ·
      refine ⟨26792292646623294258968071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35723056862164392345290761 26792292646623294258968071)
      ·
        refine ⟨40188438969934941388452107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26792292646623294258968071 40188438969934941388452107)
        ·
          refine ⟨60282658454902412082678161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40188438969934941388452107 60282658454902412082678161)
          ·
            refine ⟨45211993841176809062008621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60282658454902412082678161 45211993841176809062008621)
            ·
              refine ⟨16954497690441303398253233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45211993841176809062008621 16954497690441303398253233)
              ·
                refine ⟨12715873267830977548689925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16954497690441303398253233 12715873267830977548689925)
                ·
                  refine ⟨2384226237718308290379361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12715873267830977548689925 2384226237718308290379361)
                  ·
                    refine ⟨1788169678288731217784521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2384226237718308290379361 1788169678288731217784521)
                    ·
                      refine ⟨1341127258716548413338391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1788169678288731217784521 1341127258716548413338391)
                      ·
                        rfl

theorem cell23_2611836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 4, 2, 2].length) (baseStart_2611836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611836 prefixEnd_2611836 := by exact prefixLift 2611836
  have htrace : WordTrace (prefixWord ++ tailWord_2611836) baseStart_2611836 baseEnd_2611836 := by
    simpa [prefixWord, tailWord_2611836, baseEnd_2611836] using wordTrace_append hprefix tailTrace_2611836
  have hstable : (prefixWord ++ tailWord_2611836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611836).length < 2 ^ (prefixWord ++ tailWord_2611836).sum := by decide
  have hdescent : baseEnd_2611836 < baseStart_2611836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611869 : List Nat := [1, 4, 2, 1, 1, 1, 2, 3, 2, 3, 3]
def baseStart_2611869 : Nat := 118140960795 + 2611869 * 2 ^ 59
def prefixEnd_2611869 : Nat := 4983230072969 + 3 ^ 40 * 2611869 * 2
def baseEnd_2611869 : Nat := 1341144203578146784225739

theorem tailTrace_2611869 : CollatzResearch.WordTrace tailWord_2611869 prefixEnd_2611869 1341144203578146784225739 := by
  unfold tailWord_2611869
  simp only [CollatzResearch.WordTrace]
  refine ⟨95262688574652159556726661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63508459049768106371151107 95262688574652159556726661)
  ·
    refine ⟨17861754107747279916886249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95262688574652159556726661 17861754107747279916886249)
    ·
      refine ⟨13396315580810459937664687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17861754107747279916886249 13396315580810459937664687)
      ·
        refine ⟨20094473371215689906497031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13396315580810459937664687 20094473371215689906497031)
        ·
          refine ⟨30141710056823534859745547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20094473371215689906497031 30141710056823534859745547)
          ·
            refine ⟨45212565085235302289618321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30141710056823534859745547 45212565085235302289618321)
            ·
              refine ⟨33909423813926476717213741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45212565085235302289618321 33909423813926476717213741)
              ·
                refine ⟨12716033930222428768955153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33909423813926476717213741 12716033930222428768955153)
                ·
                  refine ⟨9537025447666821576716365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12716033930222428768955153 9537025447666821576716365)
                  ·
                    refine ⟨3576384542875058091268637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9537025447666821576716365 3576384542875058091268637)
                    ·
                      refine ⟨1341144203578146784225739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3576384542875058091268637 1341144203578146784225739)
                      ·
                        rfl

theorem cell23_2611869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_2611869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611869 prefixEnd_2611869 := by exact prefixLift 2611869
  have htrace : WordTrace (prefixWord ++ tailWord_2611869) baseStart_2611869 baseEnd_2611869 := by
    simpa [prefixWord, tailWord_2611869, baseEnd_2611869] using wordTrace_append hprefix tailTrace_2611869
  have hstable : (prefixWord ++ tailWord_2611869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611869).length < 2 ^ (prefixWord ++ tailWord_2611869).sum := by decide
  have hdescent : baseEnd_2611869 < baseStart_2611869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611870 : List Nat := [4, 3, 1, 1, 1, 1, 3, 3, 2, 2, 2]
def baseStart_2611870 : Nat := 118140960795 + 2611870 * 2 ^ 59
def prefixEnd_2611870 : Nat := 4983230072969 + 3 ^ 40 * 2611870 * 2
def baseEnd_2611870 : Nat := 1341144717058801280313235

theorem tailTrace_2611870 : CollatzResearch.WordTrace tailWord_2611870 prefixEnd_2611870 1341144717058801280313235 := by
  unfold tailWord_2611870
  simp only [CollatzResearch.WordTrace]
  refine ⟨11907840630956067090939133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63508483365099024485008709 11907840630956067090939133)
  ·
    refine ⟨4465440236608525159102175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11907840630956067090939133 4465440236608525159102175)
    ·
      refine ⟨6698160354912787738653263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4465440236608525159102175 6698160354912787738653263)
      ·
        refine ⟨10047240532369181607979895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6698160354912787738653263 10047240532369181607979895)
        ·
          refine ⟨15070860798553772411969843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10047240532369181607979895 15070860798553772411969843)
          ·
            refine ⟨22606291197830658617954765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15070860798553772411969843 22606291197830658617954765)
            ·
              refine ⟨8477359199186496981733037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22606291197830658617954765 8477359199186496981733037)
              ·
                refine ⟨3179009699694936368149889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8477359199186496981733037 3179009699694936368149889)
                ·
                  refine ⟨2384257274771202276112417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3179009699694936368149889 2384257274771202276112417)
                  ·
                    refine ⟨1788192956078401707084313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2384257274771202276112417 1788192956078401707084313)
                    ·
                      refine ⟨1341144717058801280313235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1788192956078401707084313 1341144717058801280313235)
                      ·
                        rfl

theorem cell23_2611870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_2611870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611870 prefixEnd_2611870 := by exact prefixLift 2611870
  have htrace : WordTrace (prefixWord ++ tailWord_2611870) baseStart_2611870 baseEnd_2611870 := by
    simpa [prefixWord, tailWord_2611870, baseEnd_2611870] using wordTrace_append hprefix tailTrace_2611870
  have hstable : (prefixWord ++ tailWord_2611870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611870).length < 2 ^ (prefixWord ++ tailWord_2611870).sum := by decide
  have hdescent : baseEnd_2611870 < baseStart_2611870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611929 : List Nat := [1, 2, 1, 2, 3, 2, 2, 2, 1, 4, 3]
def baseStart_2611929 : Nat := 118140960795 + 2611929 * 2 ^ 59
def prefixEnd_2611929 : Nat := 4983230072969 + 3 ^ 40 * 2611929 * 2
def baseEnd_2611929 : Nat := 1341175012417416549475463

theorem tailTrace_2611929 : CollatzResearch.WordTrace tailWord_2611929 prefixEnd_2611929 1341175012417416549475463 := by
  unfold tailWord_2611929
  simp only [CollatzResearch.WordTrace]
  refine ⟨95264876954434789803910841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63509917969623193202607227 95264876954434789803910841)
  ·
    refine ⟨71448657715826092352933131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95264876954434789803910841 71448657715826092352933131)
    ·
      refine ⟨107172986573739138529399697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71448657715826092352933131 107172986573739138529399697)
      ·
        refine ⟨80379739930304353897049773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107172986573739138529399697 80379739930304353897049773)
        ·
          refine ⟨30142402473864132711393665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80379739930304353897049773 30142402473864132711393665)
          ·
            refine ⟨22606801855398099533545249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30142402473864132711393665 22606801855398099533545249)
            ·
              refine ⟨16955101391548574650158937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22606801855398099533545249 16955101391548574650158937)
              ·
                refine ⟨12716326043661430987619203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16955101391548574650158937 12716326043661430987619203)
                ·
                  refine ⟨19074489065492146481428805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12716326043661430987619203 19074489065492146481428805)
                  ·
                    refine ⟨3576466699779777465267901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19074489065492146481428805 3576466699779777465267901)
                    ·
                      refine ⟨1341175012417416549475463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3576466699779777465267901 1341175012417416549475463)
                      ·
                        rfl

theorem cell23_2611929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 4, 3].length) (baseStart_2611929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611929 prefixEnd_2611929 := by exact prefixLift 2611929
  have htrace : WordTrace (prefixWord ++ tailWord_2611929) baseStart_2611929 baseEnd_2611929 := by
    simpa [prefixWord, tailWord_2611929, baseEnd_2611929] using wordTrace_append hprefix tailTrace_2611929
  have hstable : (prefixWord ++ tailWord_2611929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611929).length < 2 ^ (prefixWord ++ tailWord_2611929).sum := by decide
  have hdescent : baseEnd_2611929 < baseStart_2611929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611949 : List Nat := [1, 5, 1, 2, 1, 1, 2, 2, 8]
def baseStart_2611949 : Nat := 118140960795 + 2611949 * 2 ^ 59
def prefixEnd_2611949 : Nat := 4983230072969 + 3 ^ 40 * 2611949 * 2
def baseEnd_2611949 : Nat := 149020586892278496802819

theorem tailTrace_2611949 : CollatzResearch.WordTrace tailWord_2611949 prefixEnd_2611949 149020586892278496802819 := by
  unfold tailWord_2611949
  simp only [CollatzResearch.WordTrace]
  refine ⟨95265606414362333219638901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63510404276241555479759267 95265606414362333219638901)
  ·
    refine ⟨8931150601346468739341147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95265606414362333219638901 8931150601346468739341147)
    ·
      refine ⟨13396725902019703109011721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8931150601346468739341147 13396725902019703109011721)
      ·
        refine ⟨10047544426514777331758791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13396725902019703109011721 10047544426514777331758791)
        ·
          refine ⟨15071316639772165997638187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10047544426514777331758791 15071316639772165997638187)
          ·
            refine ⟨22606974959658248996457281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15071316639772165997638187 22606974959658248996457281)
            ·
              refine ⟨16955231219743686747342961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22606974959658248996457281 16955231219743686747342961)
              ·
                refine ⟨12716423414807765060507221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16955231219743686747342961 12716423414807765060507221)
                ·
                  refine ⟨149020586892278496802819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12716423414807765060507221 149020586892278496802819)
                  ·
                    rfl

theorem cell23_2611949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_2611949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611949 prefixEnd_2611949 := by exact prefixLift 2611949
  have htrace : WordTrace (prefixWord ++ tailWord_2611949) baseStart_2611949 baseEnd_2611949 := by
    simpa [prefixWord, tailWord_2611949, baseEnd_2611949] using wordTrace_append hprefix tailTrace_2611949
  have hstable : (prefixWord ++ tailWord_2611949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611949).length < 2 ^ (prefixWord ++ tailWord_2611949).sum := by decide
  have hdescent : baseEnd_2611949 < baseStart_2611949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611953 : List Nat := [1, 2, 2, 2, 2, 2, 4, 3, 1, 4]
def baseStart_2611953 : Nat := 118140960795 + 2611953 * 2 ^ 59
def prefixEnd_2611953 : Nat := 4983230072969 + 3 ^ 40 * 2611953 * 2
def baseEnd_2611953 : Nat := 447062445317708151858451

theorem tailTrace_2611953 : CollatzResearch.WordTrace tailWord_2611953 prefixEnd_2611953 447062445317708151858451 := by
  unfold tailWord_2611953
  simp only [CollatzResearch.WordTrace]
  refine ⟨95265752306347841902784513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63510501537565227935189675 95265752306347841902784513)
  ·
    refine ⟨71449314229760881427088385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95265752306347841902784513 71449314229760881427088385)
    ·
      refine ⟨53586985672320661070316289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71449314229760881427088385 53586985672320661070316289)
      ·
        refine ⟨40190239254240495802737217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53586985672320661070316289 40190239254240495802737217)
        ·
          refine ⟨30142679440680371852052913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40190239254240495802737217 30142679440680371852052913)
          ·
            refine ⟨22607009580510278889039685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30142679440680371852052913 22607009580510278889039685)
            ·
              refine ⟨4238814296345677291694941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22607009580510278889039685 4238814296345677291694941)
              ·
                refine ⟨1589555361129628984385603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4238814296345677291694941 1589555361129628984385603)
                ·
                  refine ⟨2384333041694443476578405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1589555361129628984385603 2384333041694443476578405)
                  ·
                    refine ⟨447062445317708151858451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2384333041694443476578405 447062445317708151858451)
                    ·
                      rfl

theorem cell23_2611953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 3, 1, 4].length) (baseStart_2611953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611953 prefixEnd_2611953 := by exact prefixLift 2611953
  have htrace : WordTrace (prefixWord ++ tailWord_2611953) baseStart_2611953 baseEnd_2611953 := by
    simpa [prefixWord, tailWord_2611953, baseEnd_2611953] using wordTrace_append hprefix tailTrace_2611953
  have hstable : (prefixWord ++ tailWord_2611953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611953).length < 2 ^ (prefixWord ++ tailWord_2611953).sum := by decide
  have hdescent : baseEnd_2611953 < baseStart_2611953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611966 : List Nat := [4, 2, 2, 1, 2, 2, 1, 1, 8]
def baseStart_2611966 : Nat := 118140960795 + 2611966 * 2 ^ 59
def prefixEnd_2611966 : Nat := 4983230072969 + 3 ^ 40 * 2611966 * 2
def baseEnd_2611966 : Nat := 149021556800181433856977

theorem tailTrace_2611966 : CollatzResearch.WordTrace tailWord_2611966 prefixEnd_2611966 149021556800181433856977 := by
  unfold tailWord_2611966
  simp only [CollatzResearch.WordTrace]
  refine ⟨11908278306912593140375969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63510817636867163415338501 11908278306912593140375969)
  ·
    refine ⟨8931208730184444855281977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11908278306912593140375969 8931208730184444855281977)
    ·
      refine ⟨6698406547638333641461483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8931208730184444855281977 6698406547638333641461483)
      ·
        refine ⟨10047609821457500462192225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6698406547638333641461483 10047609821457500462192225)
        ·
          refine ⟨7535707366093125346644169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10047609821457500462192225 7535707366093125346644169)
          ·
            refine ⟨5651780524569844009983127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7535707366093125346644169 5651780524569844009983127)
            ·
              refine ⟨8477670786854766014974691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5651780524569844009983127 8477670786854766014974691)
              ·
                refine ⟨12716506180282149022462037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8477670786854766014974691 12716506180282149022462037)
                ·
                  refine ⟨149021556800181433856977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12716506180282149022462037 149021556800181433856977)
                  ·
                    rfl

theorem cell23_2611966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_2611966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611966 prefixEnd_2611966 := by exact prefixLift 2611966
  have htrace : WordTrace (prefixWord ++ tailWord_2611966) baseStart_2611966 baseEnd_2611966 := by
    simpa [prefixWord, tailWord_2611966, baseEnd_2611966] using wordTrace_append hprefix tailTrace_2611966
  have hstable : (prefixWord ++ tailWord_2611966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611966).length < 2 ^ (prefixWord ++ tailWord_2611966).sum := by decide
  have hdescent : baseEnd_2611966 < baseStart_2611966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611970 : List Nat := [3, 4, 1, 1, 1, 2, 2, 4, 1, 4]
def baseStart_2611970 : Nat := 118140960795 + 2611970 * 2 ^ 59
def prefixEnd_2611970 : Nat := 4983230072969 + 3 ^ 40 * 2611970 * 2
def baseEnd_2611970 : Nat := 447065355041416963020925

theorem tailTrace_2611970 : CollatzResearch.WordTrace tailWord_2611970 prefixEnd_2611970 447065355041416963020925 := by
  unfold tailWord_2611970
  simp only [CollatzResearch.WordTrace]
  refine ⟨23816593086821563451538341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63510914898190835870768909 23816593086821563451538341)
  ·
    refine ⟨4465611203779043147163439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23816593086821563451538341 4465611203779043147163439)
    ·
      refine ⟨6698416805668564720745159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4465611203779043147163439 6698416805668564720745159)
      ·
        refine ⟨10047625208502847081117739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6698416805668564720745159 10047625208502847081117739)
        ·
          refine ⟨15071437812754270621676609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10047625208502847081117739 15071437812754270621676609)
          ·
            refine ⟨11303578359565702966257457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15071437812754270621676609 11303578359565702966257457)
            ·
              refine ⟨8477683769674277224693093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11303578359565702966257457 8477683769674277224693093)
              ·
                refine ⟨1589565706813926979629955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8477683769674277224693093 1589565706813926979629955)
                ·
                  refine ⟨2384348560220890469444933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1589565706813926979629955 2384348560220890469444933)
                  ·
                    refine ⟨447065355041416963020925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2384348560220890469444933 447065355041416963020925)
                    ·
                      rfl

theorem cell23_2611970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_2611970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611970 prefixEnd_2611970 := by exact prefixLift 2611970
  have htrace : WordTrace (prefixWord ++ tailWord_2611970) baseStart_2611970 baseEnd_2611970 := by
    simpa [prefixWord, tailWord_2611970, baseEnd_2611970] using wordTrace_append hprefix tailTrace_2611970
  have hstable : (prefixWord ++ tailWord_2611970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611970).length < 2 ^ (prefixWord ++ tailWord_2611970).sum := by decide
  have hdescent : baseEnd_2611970 < baseStart_2611970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611996 : List Nat := [2, 2, 3, 1, 1, 3, 1, 4, 1, 5]
def baseStart_2611996 : Nat := 118140960795 + 2611996 * 2 ^ 59
def prefixEnd_2611996 : Nat := 4983230072969 + 3 ^ 40 * 2611996 * 2
def baseEnd_2611996 : Nat := 447069805207089262445885

theorem tailTrace_2611996 : CollatzResearch.WordTrace tailWord_2611996 prefixEnd_2611996 447069805207089262445885 := by
  unfold tailWord_2611996
  simp only [CollatzResearch.WordTrace]
  refine ⟨47633660322596030123299921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63511547096794706831066561 47633660322596030123299921)
  ·
    refine ⟨35725245241947022592474941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47633660322596030123299921 35725245241947022592474941)
    ·
      refine ⟨13396966965730133472178103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35725245241947022592474941 13396966965730133472178103)
      ·
        refine ⟨20095450448595200208267155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13396966965730133472178103 20095450448595200208267155)
        ·
          refine ⟨30143175672892800312400733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20095450448595200208267155 30143175672892800312400733)
          ·
            refine ⟨11303690877334800117150275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30143175672892800312400733 11303690877334800117150275)
            ·
              refine ⟨16955536316002200175725413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11303690877334800117150275 16955536316002200175725413)
              ·
                refine ⟨3179163059250412532948515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16955536316002200175725413 3179163059250412532948515)
                ·
                  refine ⟨4768744588875618799422773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3179163059250412532948515 4768744588875618799422773)
                  ·
                    refine ⟨447069805207089262445885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4768744588875618799422773 447069805207089262445885)
                    ·
                      rfl

theorem cell23_2611996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_2611996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2611996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2611996 prefixEnd_2611996 := by exact prefixLift 2611996
  have htrace : WordTrace (prefixWord ++ tailWord_2611996) baseStart_2611996 baseEnd_2611996 := by
    simpa [prefixWord, tailWord_2611996, baseEnd_2611996] using wordTrace_append hprefix tailTrace_2611996
  have hstable : (prefixWord ++ tailWord_2611996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611996).length < 2 ^ (prefixWord ++ tailWord_2611996).sum := by decide
  have hdescent : baseEnd_2611996 < baseStart_2611996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612079 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 5]
def baseStart_2612079 : Nat := 118140960795 + 2612079 * 2 ^ 59
def prefixEnd_2612079 : Nat := 4983230072969 + 3 ^ 40 * 2612079 * 2
def baseEnd_2612079 : Nat := 1341252034515590962599773

theorem tailTrace_2612079 : CollatzResearch.WordTrace tailWord_2612079 prefixEnd_2612079 1341252034515590962599773 := by
  unfold tailWord_2612079
  simp only [CollatzResearch.WordTrace]
  refine ⟨95270347903891365421871291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63513565269260910281247527 95270347903891365421871291)
  ·
    refine ⟨142905521855837048132806937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95270347903891365421871291 142905521855837048132806937)
    ·
      refine ⟨107179141391877786099605203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142905521855837048132806937 107179141391877786099605203)
      ·
        refine ⟨160768712087816679149407805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107179141391877786099605203 160768712087816679149407805)
        ·
          refine ⟨60288267032931254681027927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160768712087816679149407805 60288267032931254681027927)
          ·
            refine ⟨90432400549396882021541891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60288267032931254681027927 90432400549396882021541891)
            ·
              refine ⟨135648600824095323032312837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90432400549396882021541891 135648600824095323032312837)
              ·
                refine ⟨25434112654517873068558657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 135648600824095323032312837 25434112654517873068558657)
                ·
                  refine ⟨19075584490888404801418993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25434112654517873068558657 19075584490888404801418993)
                  ·
                    refine ⟨14306688368166303601064245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19075584490888404801418993 14306688368166303601064245)
                    ·
                      refine ⟨1341252034515590962599773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14306688368166303601064245 1341252034515590962599773)
                      ·
                        rfl

theorem cell23_2612079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 5].length) (baseStart_2612079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612079 prefixEnd_2612079 := by exact prefixLift 2612079
  have htrace : WordTrace (prefixWord ++ tailWord_2612079) baseStart_2612079 baseEnd_2612079 := by
    simpa [prefixWord, tailWord_2612079, baseEnd_2612079] using wordTrace_append hprefix tailTrace_2612079
  have hstable : (prefixWord ++ tailWord_2612079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612079).length < 2 ^ (prefixWord ++ tailWord_2612079).sum := by decide
  have hdescent : baseEnd_2612079 < baseStart_2612079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612083 : List Nat := [1, 1, 1, 2, 2, 1, 5, 4, 2, 1, 3]
def baseStart_2612083 : Nat := 118140960795 + 2612083 * 2 ^ 59
def prefixEnd_2612083 : Nat := 4983230072969 + 3 ^ 40 * 2612083 * 2
def baseEnd_2612083 : Nat := 1341254088438208946949755

theorem tailTrace_2612083 : CollatzResearch.WordTrace tailWord_2612083 prefixEnd_2612083 1341254088438208946949755 := by
  unfold tailWord_2612083
  simp only [CollatzResearch.WordTrace]
  refine ⟨95270493795876874105016903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63513662530584582736677935 95270493795876874105016903)
  ·
    refine ⟨142905740693815311157525355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95270493795876874105016903 142905740693815311157525355)
    ·
      refine ⟨214358611040722966736288033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142905740693815311157525355 214358611040722966736288033)
      ·
        refine ⟨160768958280542225052216025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214358611040722966736288033 160768958280542225052216025)
        ·
          refine ⟨120576718710406668789162019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160768958280542225052216025 120576718710406668789162019)
          ·
            refine ⟨180865078065610003183743029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120576718710406668789162019 180865078065610003183743029)
            ·
              refine ⟨16956101068650937798475909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 180865078065610003183743029 16956101068650937798475909)
              ·
                refine ⟨3179268950372050837214233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16956101068650937798475909 3179268950372050837214233)
                ·
                  refine ⟨2384451712779038127910675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3179268950372050837214233 2384451712779038127910675)
                  ·
                    refine ⟨3576677569168557191866013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2384451712779038127910675 3576677569168557191866013)
                    ·
                      refine ⟨1341254088438208946949755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3576677569168557191866013 1341254088438208946949755)
                      ·
                        rfl

theorem cell23_2612083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 2, 1, 3].length) (baseStart_2612083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612083 prefixEnd_2612083 := by exact prefixLift 2612083
  have htrace : WordTrace (prefixWord ++ tailWord_2612083) baseStart_2612083 baseEnd_2612083 := by
    simpa [prefixWord, tailWord_2612083, baseEnd_2612083] using wordTrace_append hprefix tailTrace_2612083
  have hstable : (prefixWord ++ tailWord_2612083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612083).length < 2 ^ (prefixWord ++ tailWord_2612083).sum := by decide
  have hdescent : baseEnd_2612083 < baseStart_2612083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612093 : List Nat := [1, 4, 1, 1, 2, 1, 3, 2, 3, 3, 2]
def baseStart_2612093 : Nat := 118140960795 + 2612093 * 2 ^ 59
def prefixEnd_2612093 : Nat := 4983230072969 + 3 ^ 40 * 2612093 * 2
def baseEnd_2612093 : Nat := 1341259223244753907824709

theorem tailTrace_2612093 : CollatzResearch.WordTrace tailWord_2612093 prefixEnd_2612093 1341259223244753907824709 := by
  unfold tailWord_2612093
  simp only [CollatzResearch.WordTrace]
  refine ⟨95270858525840645812880933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63513905683893763875253955 95270858525840645812880933)
  ·
    refine ⟨17863285973595121089915175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95270858525840645812880933 17863285973595121089915175)
    ·
      refine ⟨26794928960392681634872763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17863285973595121089915175 26794928960392681634872763)
      ·
        refine ⟨40192393440589022452309145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26794928960392681634872763 40192393440589022452309145)
        ·
          refine ⟨30144295080441766839231859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40192393440589022452309145 30144295080441766839231859)
          ·
            refine ⟨45216442620662650258847789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30144295080441766839231859 45216442620662650258847789)
            ·
              refine ⟨16956165982748493847067921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45216442620662650258847789 16956165982748493847067921)
              ·
                refine ⟨12717124487061370385300941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16956165982748493847067921 12717124487061370385300941)
                ·
                  refine ⟨4768921682648013894487853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12717124487061370385300941 4768921682648013894487853)
                  ·
                    refine ⟨1788345630993005210432945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4768921682648013894487853 1788345630993005210432945)
                    ·
                      refine ⟨1341259223244753907824709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1788345630993005210432945 1341259223244753907824709)
                      ·
                        rfl

theorem cell23_2612093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 3, 2].length) (baseStart_2612093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612093 prefixEnd_2612093 := by exact prefixLift 2612093
  have htrace : WordTrace (prefixWord ++ tailWord_2612093) baseStart_2612093 baseEnd_2612093 := by
    simpa [prefixWord, tailWord_2612093, baseEnd_2612093] using wordTrace_append hprefix tailTrace_2612093
  have hstable : (prefixWord ++ tailWord_2612093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612093).length < 2 ^ (prefixWord ++ tailWord_2612093).sum := by decide
  have hdescent : baseEnd_2612093 < baseStart_2612093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612116 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 1, 8]
def baseStart_2612116 : Nat := 118140960795 + 2612116 * 2 ^ 59
def prefixEnd_2612116 : Nat := 4983230072969 + 3 ^ 40 * 2612116 * 2
def baseEnd_2612116 : Nat := 447090344433269105945701

theorem tailTrace_2612116 : CollatzResearch.WordTrace tailWord_2612116 prefixEnd_2612116 447090344433269105945701 := by
  unfold tailWord_2612116
  simp only [CollatzResearch.WordTrace]
  refine ⟨47635848702378660370484101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63514464936504880493978801 47635848702378660370484101)
  ·
    refine ⟨8931721631695998819465769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47635848702378660370484101 8931721631695998819465769)
    ·
      refine ⟨6698791223771999114599327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8931721631695998819465769 6698791223771999114599327)
      ·
        refine ⟨10048186835657998671898991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6698791223771999114599327 10048186835657998671898991)
        ·
          refine ⟨15072280253486998007848487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10048186835657998671898991 15072280253486998007848487)
          ·
            refine ⟨22608420380230497011772731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15072280253486998007848487 22608420380230497011772731)
            ·
              refine ⟨33912630570345745517659097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22608420380230497011772731 33912630570345745517659097)
              ·
                refine ⟨25434472927759309138244323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33912630570345745517659097 25434472927759309138244323)
                ·
                  refine ⟨38151709391638963707366485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25434472927759309138244323 38151709391638963707366485)
                  ·
                    refine ⟨447090344433269105945701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38151709391638963707366485 447090344433269105945701)
                    ·
                      rfl

theorem cell23_2612116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_2612116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612116 prefixEnd_2612116 := by exact prefixLift 2612116
  have htrace : WordTrace (prefixWord ++ tailWord_2612116) baseStart_2612116 baseEnd_2612116 := by
    simpa [prefixWord, tailWord_2612116, baseEnd_2612116] using wordTrace_append hprefix tailTrace_2612116
  have hstable : (prefixWord ++ tailWord_2612116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612116).length < 2 ^ (prefixWord ++ tailWord_2612116).sum := by decide
  have hdescent : baseEnd_2612116 < baseStart_2612116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612118 : List Nat := [5, 3, 1, 1, 1, 2, 2, 3, 1, 2, 2]
def baseStart_2612118 : Nat := 118140960795 + 2612118 * 2 ^ 59
def prefixEnd_2612118 : Nat := 4983230072969 + 3 ^ 40 * 2612118 * 2
def baseEnd_2612118 : Nat := 1341272060261116310012095

theorem tailTrace_2612118 : CollatzResearch.WordTrace tailWord_2612118 prefixEnd_2612118 1341272060261116310012095 := by
  unfold tailWord_2612118
  simp only [CollatzResearch.WordTrace]
  refine ⟨5954485646921879692658813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63514513567166716721694005 5954485646921879692658813)
  ·
    refine ⟨2232932117595704884747055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5954485646921879692658813 2232932117595704884747055)
    ·
      refine ⟨3349398176393557327120583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2232932117595704884747055 3349398176393557327120583)
      ·
        refine ⟨5024097264590335990680875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3349398176393557327120583 5024097264590335990680875)
        ·
          refine ⟨7536145896885503986021313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5024097264590335990680875 7536145896885503986021313)
          ·
            refine ⟨5652109422664127989515985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7536145896885503986021313 5652109422664127989515985)
            ·
              refine ⟨4239082066998095992136989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5652109422664127989515985 4239082066998095992136989)
              ·
                refine ⟨1589655775124285997051371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4239082066998095992136989 1589655775124285997051371)
                ·
                  refine ⟨2384483662686428995577057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1589655775124285997051371 2384483662686428995577057)
                  ·
                    refine ⟨1788362747014821746682793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2384483662686428995577057 1788362747014821746682793)
                    ·
                      refine ⟨1341272060261116310012095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1788362747014821746682793 1341272060261116310012095)
                      ·
                        rfl

theorem cell23_2612118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_2612118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612118 prefixEnd_2612118 := by exact prefixLift 2612118
  have htrace : WordTrace (prefixWord ++ tailWord_2612118) baseStart_2612118 baseEnd_2612118 := by
    simpa [prefixWord, tailWord_2612118, baseEnd_2612118] using wordTrace_append hprefix tailTrace_2612118
  have hstable : (prefixWord ++ tailWord_2612118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612118).length < 2 ^ (prefixWord ++ tailWord_2612118).sum := by decide
  have hdescent : baseEnd_2612118 < baseStart_2612118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612127 : List Nat := [1, 1, 2, 5, 2, 1, 4, 1, 1, 3, 2]
def baseStart_2612127 : Nat := 118140960795 + 2612127 * 2 ^ 59
def prefixEnd_2612127 : Nat := 4983230072969 + 3 ^ 40 * 2612127 * 2
def baseEnd_2612127 : Nat := 1341276681587006774799553

theorem tailTrace_2612127 : CollatzResearch.WordTrace tailWord_2612127 prefixEnd_2612127 1341276681587006774799553 := by
  unfold tailWord_2612127
  simp only [CollatzResearch.WordTrace]
  refine ⟨95272098607717469619618635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63514732405144979746412423 95272098607717469619618635)
  ·
    refine ⟨142908147911576204429427953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95272098607717469619618635 142908147911576204429427953)
    ·
      refine ⟨107181110933682153322070965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142908147911576204429427953 107181110933682153322070965)
      ·
        refine ⟨10048229150032701873944153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107181110933682153322070965 10048229150032701873944153)
        ·
          refine ⟨7536171862524526405458115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10048229150032701873944153 7536171862524526405458115)
          ·
            refine ⟨11304257793786789608187173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7536171862524526405458115 11304257793786789608187173)
            ·
              refine ⟨2119548336335023051535095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11304257793786789608187173 2119548336335023051535095)
              ·
                refine ⟨3179322504502534577302643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2119548336335023051535095 3179322504502534577302643)
                ·
                  refine ⟨4768983756753801865953965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3179322504502534577302643 4768983756753801865953965)
                  ·
                    refine ⟨1788368908782675699732737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4768983756753801865953965 1788368908782675699732737)
                    ·
                      refine ⟨1341276681587006774799553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1788368908782675699732737 1341276681587006774799553)
                      ·
                        rfl

theorem cell23_2612127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_2612127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612127 prefixEnd_2612127 := by exact prefixLift 2612127
  have htrace : WordTrace (prefixWord ++ tailWord_2612127) baseStart_2612127 baseEnd_2612127 := by
    simpa [prefixWord, tailWord_2612127, baseEnd_2612127] using wordTrace_append hprefix tailTrace_2612127
  have hstable : (prefixWord ++ tailWord_2612127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612127).length < 2 ^ (prefixWord ++ tailWord_2612127).sum := by decide
  have hdescent : baseEnd_2612127 < baseStart_2612127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612139 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 7]
def baseStart_2612139 : Nat := 118140960795 + 2612139 * 2 ^ 59
def prefixEnd_2612139 : Nat := 4983230072969 + 3 ^ 40 * 2612139 * 2
def baseEnd_2612139 : Nat := 1341282843354860727849497

theorem tailTrace_2612139 : CollatzResearch.WordTrace tailWord_2612139 prefixEnd_2612139 1341282843354860727849497 := by
  unfold tailWord_2612139
  simp only [CollatzResearch.WordTrace]
  refine ⟨95272536283673995669055471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63515024189115997112703647 95272536283673995669055471)
  ·
    refine ⟨142908804425510993503583207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95272536283673995669055471 142908804425510993503583207)
    ·
      refine ⟨214363206638266490255374811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142908804425510993503583207 214363206638266490255374811)
      ·
        refine ⟨321544809957399735383062217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214363206638266490255374811 321544809957399735383062217)
        ·
          refine ⟨241158607468049801537296663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321544809957399735383062217 241158607468049801537296663)
          ·
            refine ⟨361737911202074702305944995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241158607468049801537296663 361737911202074702305944995)
            ·
              refine ⟨542606866803112053458917493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361737911202074702305944995 542606866803112053458917493)
              ·
                refine ⟨50869393762791755011773515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 542606866803112053458917493 50869393762791755011773515)
                ·
                  refine ⟨76304090644187632517660273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50869393762791755011773515 76304090644187632517660273)
                  ·
                    refine ⟨57228067983140724388245205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76304090644187632517660273 57228067983140724388245205)
                    ·
                      refine ⟨1341282843354860727849497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 57228067983140724388245205 1341282843354860727849497)
                      ·
                        rfl

theorem cell23_2612139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 7].length) (baseStart_2612139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612139 prefixEnd_2612139 := by exact prefixLift 2612139
  have htrace : WordTrace (prefixWord ++ tailWord_2612139) baseStart_2612139 baseEnd_2612139 := by
    simpa [prefixWord, tailWord_2612139, baseEnd_2612139] using wordTrace_append hprefix tailTrace_2612139
  have hstable : (prefixWord ++ tailWord_2612139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612139).length < 2 ^ (prefixWord ++ tailWord_2612139).sum := by decide
  have hdescent : baseEnd_2612139 < baseStart_2612139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612157 : List Nat := [1, 4, 1, 2, 4, 2, 1, 1, 1, 4, 2]
def baseStart_2612157 : Nat := 118140960795 + 2612157 * 2 ^ 59
def prefixEnd_2612157 : Nat := 4983230072969 + 3 ^ 40 * 2612157 * 2
def baseEnd_2612157 : Nat := 1341292086006641657424415

theorem tailTrace_2612157 : CollatzResearch.WordTrace tailWord_2612157 prefixEnd_2612157 1341292086006641657424415 := by
  unfold tailWord_2612157
  simp only [CollatzResearch.WordTrace]
  refine ⟨95273192797608784743210725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63515461865072523162140483 95273192797608784743210725)
  ·
    refine ⟨17863723649551647139352011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95273192797608784743210725 17863723649551647139352011)
    ·
      refine ⟨26795585474327470709028017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17863723649551647139352011 26795585474327470709028017)
      ·
        refine ⟨20096689105745603031771013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26795585474327470709028017 20096689105745603031771013)
        ·
          refine ⟨3768129207327300568457065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20096689105745603031771013 3768129207327300568457065)
          ·
            refine ⟨2826096905495475426342799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3768129207327300568457065 2826096905495475426342799)
            ·
              refine ⟨4239145358243213139514199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2826096905495475426342799 4239145358243213139514199)
              ·
                refine ⟨6358718037364819709271299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4239145358243213139514199 6358718037364819709271299)
                ·
                  refine ⟨9538077056047229563906949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6358718037364819709271299 9538077056047229563906949)
                  ·
                    refine ⟨1788389448008855543232553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9538077056047229563906949 1788389448008855543232553)
                    ·
                      refine ⟨1341292086006641657424415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1788389448008855543232553 1341292086006641657424415)
                      ·
                        rfl

theorem cell23_2612157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_2612157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612157 prefixEnd_2612157 := by exact prefixLift 2612157
  have htrace : WordTrace (prefixWord ++ tailWord_2612157) baseStart_2612157 baseEnd_2612157 := by
    simpa [prefixWord, tailWord_2612157, baseEnd_2612157] using wordTrace_append hprefix tailTrace_2612157
  have hstable : (prefixWord ++ tailWord_2612157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612157).length < 2 ^ (prefixWord ++ tailWord_2612157).sum := by decide
  have hdescent : baseEnd_2612157 < baseStart_2612157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612176 : List Nat := [2, 1, 1, 1, 1, 2, 3, 5, 2, 5]
def baseStart_2612176 : Nat := 118140960795 + 2612176 * 2 ^ 59
def prefixEnd_2612176 : Nat := 4983230072969 + 3 ^ 40 * 2612176 * 2
def baseEnd_2612176 : Nat := 447100614046359027695609

theorem tailTrace_2612176 : CollatzResearch.WordTrace tailWord_2612176 prefixEnd_2612176 447100614046359027695609 := by
  unfold tailWord_2612176
  simp only [CollatzResearch.WordTrace]
  refine ⟨47636942892269975494076191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63515923856359967325434921 47636942892269975494076191)
  ·
    refine ⟨71455414338404963241114287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47636942892269975494076191 71455414338404963241114287)
    ·
      refine ⟨107183121507607444861671431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71455414338404963241114287 107183121507607444861671431)
      ·
        refine ⟨160774682261411167292507147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107183121507607444861671431 160774682261411167292507147)
        ·
          refine ⟨241162023392116750938760721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160774682261411167292507147 241162023392116750938760721)
          ·
            refine ⟨180871517544087563204070541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241162023392116750938760721 180871517544087563204070541)
            ·
              refine ⟨67826819079032836201526453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 180871517544087563204070541 67826819079032836201526453)
              ·
                refine ⟨6358764288659328393893105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67826819079032836201526453 6358764288659328393893105)
                ·
                  refine ⟨4769073216494496295419829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6358764288659328393893105 4769073216494496295419829)
                  ·
                    refine ⟨447100614046359027695609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4769073216494496295419829 447100614046359027695609)
                    ·
                      rfl

theorem cell23_2612176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 2, 5].length) (baseStart_2612176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612176 prefixEnd_2612176 := by exact prefixLift 2612176
  have htrace : WordTrace (prefixWord ++ tailWord_2612176) baseStart_2612176 baseEnd_2612176 := by
    simpa [prefixWord, tailWord_2612176, baseEnd_2612176] using wordTrace_append hprefix tailTrace_2612176
  have hstable : (prefixWord ++ tailWord_2612176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612176).length < 2 ^ (prefixWord ++ tailWord_2612176).sum := by decide
  have hdescent : baseEnd_2612176 < baseStart_2612176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612180 : List Nat := [2, 4, 1, 2, 1, 2, 3, 3, 5]
def baseStart_2612180 : Nat := 118140960795 + 2612180 * 2 ^ 59
def prefixEnd_2612180 : Nat := 4983230072969 + 3 ^ 40 * 2612180 * 2
def baseEnd_2612180 : Nat := 149033766229077229715201

theorem tailTrace_2612180 : CollatzResearch.WordTrace tailWord_2612180 prefixEnd_2612180 149033766229077229715201 := by
  unfold tailWord_2612180
  simp only [CollatzResearch.WordTrace]
  refine ⟨47637015838262729835648997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63516021117683639780865329 47637015838262729835648997)
  ·
    refine ⟨8931940469674261844184187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47637015838262729835648997 8931940469674261844184187)
    ·
      refine ⟨13397910704511392766276281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8931940469674261844184187 13397910704511392766276281)
      ·
        refine ⟨10048433028383544574707211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13397910704511392766276281 10048433028383544574707211)
        ·
          refine ⟨15072649542575316862060817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10048433028383544574707211 15072649542575316862060817)
          ·
            refine ⟨11304487156931487646545613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15072649542575316862060817 11304487156931487646545613)
            ·
              refine ⟨4239182683849307867454605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11304487156931487646545613 4239182683849307867454605)
              ·
                refine ⟨1589693506443490450295477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4239182683849307867454605 1589693506443490450295477)
                ·
                  refine ⟨149033766229077229715201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1589693506443490450295477 149033766229077229715201)
                  ·
                    rfl

theorem cell23_2612180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_2612180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612180 prefixEnd_2612180 := by exact prefixLift 2612180
  have htrace : WordTrace (prefixWord ++ tailWord_2612180) baseStart_2612180 baseEnd_2612180 := by
    simpa [prefixWord, tailWord_2612180, baseEnd_2612180] using wordTrace_append hprefix tailTrace_2612180
  have hstable : (prefixWord ++ tailWord_2612180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612180).length < 2 ^ (prefixWord ++ tailWord_2612180).sum := by decide
  have hdescent : baseEnd_2612180 < baseStart_2612180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612196 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 3, 3, 4]
def baseStart_2612196 : Nat := 118140960795 + 2612196 * 2 ^ 59
def prefixEnd_2612196 : Nat := 4983230072969 + 3 ^ 40 * 2612196 * 2
def baseEnd_2612196 : Nat := 1341312111752167004836735

theorem tailTrace_2612196 : CollatzResearch.WordTrace tailWord_2612196 prefixEnd_2612196 1341312111752167004836735 := by
  unfold tailWord_2612196
  simp only [CollatzResearch.WordTrace]
  refine ⟨47637307622233747201940221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63516410162978329602586961 47637307622233747201940221)
  ·
    refine ⟨17863990358337655200727583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47637307622233747201940221 17863990358337655200727583)
    ·
      refine ⟨26795985537506482801091375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17863990358337655200727583 26795985537506482801091375)
      ·
        refine ⟨40193978306259724201637063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26795985537506482801091375 40193978306259724201637063)
        ·
          refine ⟨60290967459389586302455595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40193978306259724201637063 60290967459389586302455595)
          ·
            refine ⟨90436451189084379453683393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60290967459389586302455595 90436451189084379453683393)
            ·
              refine ⟨67827338391813284590262545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90436451189084379453683393 67827338391813284590262545)
              ·
                refine ⟨50870503793859963442696909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67827338391813284590262545 50870503793859963442696909)
                ·
                  refine ⟨19076438922697486291011341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50870503793859963442696909 19076438922697486291011341)
                  ·
                    refine ⟨7153664596011557359129253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19076438922697486291011341 7153664596011557359129253)
                    ·
                      refine ⟨1341312111752167004836735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7153664596011557359129253 1341312111752167004836735)
                      ·
                        rfl

theorem cell23_2612196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_2612196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612196 prefixEnd_2612196 := by exact prefixLift 2612196
  have htrace : WordTrace (prefixWord ++ tailWord_2612196) baseStart_2612196 baseEnd_2612196 := by
    simpa [prefixWord, tailWord_2612196, baseEnd_2612196] using wordTrace_append hprefix tailTrace_2612196
  have hstable : (prefixWord ++ tailWord_2612196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612196).length < 2 ^ (prefixWord ++ tailWord_2612196).sum := by decide
  have hdescent : baseEnd_2612196 < baseStart_2612196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612197 : List Nat := [1, 3, 1, 6, 2, 1, 1, 1, 7]
def baseStart_2612197 : Nat := 118140960795 + 2612197 * 2 ^ 59
def prefixEnd_2612197 : Nat := 4983230072969 + 3 ^ 40 * 2612197 * 2
def baseEnd_2612197 : Nat := 149034736136980166769359

theorem tailTrace_2612197 : CollatzResearch.WordTrace tailWord_2612197 prefixEnd_2612197 149034736136980166769359 := by
  unfold tailWord_2612197
  simp only [CollatzResearch.WordTrace]
  refine ⟨95274651717463871574666845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63516434478309247716444563 95274651717463871574666845)
  ·
    refine ⟨35727994394048951840500067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95274651717463871574666845 35727994394048951840500067)
    ·
      refine ⟨53591991591073427760750101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35727994394048951840500067 53591991591073427760750101)
      ·
        refine ⟨2512124605831566926285161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 53591991591073427760750101 2512124605831566926285161)
        ·
          refine ⟨1884093454373675194713871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2512124605831566926285161 1884093454373675194713871)
          ·
            refine ⟨2826140181560512792070807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1884093454373675194713871 2826140181560512792070807)
            ·
              refine ⟨4239210272340769188106211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2826140181560512792070807 4239210272340769188106211)
              ·
                refine ⟨6358815408511153782159317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4239210272340769188106211 6358815408511153782159317)
                ·
                  refine ⟨149034736136980166769359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6358815408511153782159317 149034736136980166769359)
                  ·
                    rfl

theorem cell23_2612197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 7].length) (baseStart_2612197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612197 prefixEnd_2612197 := by exact prefixLift 2612197
  have htrace : WordTrace (prefixWord ++ tailWord_2612197) baseStart_2612197 baseEnd_2612197 := by
    simpa [prefixWord, tailWord_2612197, baseEnd_2612197] using wordTrace_append hprefix tailTrace_2612197
  have hstable : (prefixWord ++ tailWord_2612197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612197).length < 2 ^ (prefixWord ++ tailWord_2612197).sum := by decide
  have hdescent : baseEnd_2612197 < baseStart_2612197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612257 : List Nat := [1, 2, 3, 2, 3, 2, 1, 4, 1, 4]
def baseStart_2612257 : Nat := 118140960795 + 2612257 * 2 ^ 59
def prefixEnd_2612257 : Nat := 4983230072969 + 3 ^ 40 * 2612257 * 2
def baseEnd_2612257 : Nat := 447114478024030422057985

theorem tailTrace_2612257 : CollatzResearch.WordTrace tailWord_2612257 prefixEnd_2612257 447114478024030422057985 := by
  unfold tailWord_2612257
  simp only [CollatzResearch.WordTrace]
  refine ⟨95276840097246501821851025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63517893398164334547900683 95276840097246501821851025)
  ·
    refine ⟨71457630072934876366388269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95276840097246501821851025 71457630072934876366388269)
    ·
      refine ⟨26796611277350578637395601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71457630072934876366388269 26796611277350578637395601)
      ·
        refine ⟨20097458458012933978046701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26796611277350578637395601 20097458458012933978046701)
        ·
          refine ⟨7536546921754850241767513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20097458458012933978046701 7536546921754850241767513)
          ·
            refine ⟨5652410191316137681325635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7536546921754850241767513 5652410191316137681325635)
            ·
              refine ⟨8478615286974206521988453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5652410191316137681325635 8478615286974206521988453)
              ·
                refine ⟨1589740366307663722872835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8478615286974206521988453 1589740366307663722872835)
                ·
                  refine ⟨2384610549461495584309253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1589740366307663722872835 2384610549461495584309253)
                  ·
                    refine ⟨447114478024030422057985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2384610549461495584309253 447114478024030422057985)
                    ·
                      rfl

theorem cell23_2612257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 4, 1, 4].length) (baseStart_2612257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612257 prefixEnd_2612257 := by exact prefixLift 2612257
  have htrace : WordTrace (prefixWord ++ tailWord_2612257) baseStart_2612257 baseEnd_2612257 := by
    simpa [prefixWord, tailWord_2612257, baseEnd_2612257] using wordTrace_append hprefix tailTrace_2612257
  have hstable : (prefixWord ++ tailWord_2612257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612257).length < 2 ^ (prefixWord ++ tailWord_2612257).sum := by decide
  have hdescent : baseEnd_2612257 < baseStart_2612257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612280 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 5, 1, 3]
def baseStart_2612280 : Nat := 118140960795 + 2612280 * 2 ^ 59
def prefixEnd_2612280 : Nat := 4983230072969 + 3 ^ 40 * 2612280 * 2
def baseEnd_2612280 : Nat := 1341355244127144676186349

theorem tailTrace_2612280 : CollatzResearch.WordTrace tailWord_2612280 prefixEnd_2612280 1341355244127144676186349 := by
  unfold tailWord_2612280
  simp only [CollatzResearch.WordTrace]
  refine ⟨47638839488081588374969147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63518452650775451166625529 47638839488081588374969147)
  ·
    refine ⟨71458259232122382562453721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47638839488081588374969147 71458259232122382562453721)
    ·
      refine ⟨53593694424091786921840291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71458259232122382562453721 53593694424091786921840291)
      ·
        refine ⟨80390541636137680382760437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53593694424091786921840291 80390541636137680382760437)
        ·
          refine ⟨7536613278387907535883791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80390541636137680382760437 7536613278387907535883791)
          ·
            refine ⟨11304919917581861303825687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7536613278387907535883791 11304919917581861303825687)
            ·
              refine ⟨16957379876372791955738531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11304919917581861303825687 16957379876372791955738531)
              ·
                refine ⟨25436069814559187933607797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16957379876372791955738531 25436069814559187933607797)
                ·
                  refine ⟨2384631545114923868775731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25436069814559187933607797 2384631545114923868775731)
                  ·
                    refine ⟨3576947317672385803163597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2384631545114923868775731 3576947317672385803163597)
                    ·
                      refine ⟨1341355244127144676186349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3576947317672385803163597 1341355244127144676186349)
                      ·
                        rfl

theorem cell23_2612280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 5, 1, 3].length) (baseStart_2612280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612280 prefixEnd_2612280 := by exact prefixLift 2612280
  have htrace : WordTrace (prefixWord ++ tailWord_2612280) baseStart_2612280 baseEnd_2612280 := by
    simpa [prefixWord, tailWord_2612280, baseEnd_2612280] using wordTrace_append hprefix tailTrace_2612280
  have hstable : (prefixWord ++ tailWord_2612280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612280).length < 2 ^ (prefixWord ++ tailWord_2612280).sum := by decide
  have hdescent : baseEnd_2612280 < baseStart_2612280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612330 : List Nat := [3, 1, 3, 2, 2, 1, 3, 1, 1, 6]
def baseStart_2612330 : Nat := 118140960795 + 2612330 * 2 ^ 59
def prefixEnd_2612330 : Nat := 4983230072969 + 3 ^ 40 * 2612330 * 2
def baseEnd_2612330 : Nat := 447126972719956493520373

theorem tailTrace_2612330 : CollatzResearch.WordTrace tailWord_2612330 prefixEnd_2612330 447126972719956493520373 := by
  unfold tailWord_2612330
  simp only [CollatzResearch.WordTrace]
  refine ⟨23819875656495508822314611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63519668417321356859505629 23819875656495508822314611)
  ·
    refine ⟨35729813484743263233471917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23819875656495508822314611 35729813484743263233471917)
    ·
      refine ⟨13398680056778723712551969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35729813484743263233471917 13398680056778723712551969)
      ·
        refine ⟨10049010042584042784413977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13398680056778723712551969 10049010042584042784413977)
        ·
          refine ⟨7536757531938032088310483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10049010042584042784413977 7536757531938032088310483)
          ·
            refine ⟨11305136297907048132465725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7536757531938032088310483 11305136297907048132465725)
            ·
              refine ⟨4239426111715143049674647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11305136297907048132465725 4239426111715143049674647)
              ·
                refine ⟨6359139167572714574511971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4239426111715143049674647 6359139167572714574511971)
                ·
                  refine ⟨9538708751359071861767957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6359139167572714574511971 9538708751359071861767957)
                  ·
                    refine ⟨447126972719956493520373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9538708751359071861767957 447126972719956493520373)
                    ·
                      rfl

theorem cell23_2612330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_2612330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612330 prefixEnd_2612330 := by exact prefixLift 2612330
  have htrace : WordTrace (prefixWord ++ tailWord_2612330) baseStart_2612330 baseEnd_2612330 := by
    simpa [prefixWord, tailWord_2612330, baseEnd_2612330] using wordTrace_append hprefix tailTrace_2612330
  have hstable : (prefixWord ++ tailWord_2612330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612330).length < 2 ^ (prefixWord ++ tailWord_2612330).sum := by decide
  have hdescent : baseEnd_2612330 < baseStart_2612330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612360 : List Nat := [2, 1, 3, 4, 2, 2, 9]
def baseStart_2612360 : Nat := 118140960795 + 2612360 * 2 ^ 59
def prefixEnd_2612360 : Nat := 4983230072969 + 3 ^ 40 * 2612360 * 2
def baseEnd_2612360 : Nat := 16560448426907461273901

theorem tailTrace_2612360 : CollatzResearch.WordTrace tailWord_2612360 prefixEnd_2612360 16560448426907461273901 := by
  unfold tailWord_2612360
  simp only [CollatzResearch.WordTrace]
  refine ⟨47640298407936675206425267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63520397877248900275233689 47640298407936675206425267)
  ·
    refine ⟨71460447611905012809637901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47640298407936675206425267 71460447611905012809637901)
    ·
      refine ⟨26797667854464379803614213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71460447611905012809637901 26797667854464379803614213)
      ·
        refine ⟨5024562722712071213177665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26797667854464379803614213 5024562722712071213177665)
        ·
          refine ⟨3768422042034053409883249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5024562722712071213177665 3768422042034053409883249)
          ·
            refine ⟨2826316531525540057412437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3768422042034053409883249 2826316531525540057412437)
            ·
              refine ⟨16560448426907461273901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2826316531525540057412437 16560448426907461273901)
              ·
                rfl

theorem cell23_2612360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 9].length) (baseStart_2612360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612360 prefixEnd_2612360 := by exact prefixLift 2612360
  have htrace : WordTrace (prefixWord ++ tailWord_2612360) baseStart_2612360 baseEnd_2612360 := by
    simpa [prefixWord, tailWord_2612360, baseEnd_2612360] using wordTrace_append hprefix tailTrace_2612360
  have hstable : (prefixWord ++ tailWord_2612360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612360).length < 2 ^ (prefixWord ++ tailWord_2612360).sum := by decide
  have hdescent : baseEnd_2612360 < baseStart_2612360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612422 : List Nat := [6, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2]
def baseStart_2612422 : Nat := 118140960795 + 2612422 * 2 ^ 59
def prefixEnd_2612422 : Nat := 4983230072969 + 3 ^ 40 * 2612422 * 2
def baseEnd_2612422 : Nat := 1341428158380083120610697

theorem tailTrace_2612422 : CollatzResearch.WordTrace tailWord_2612422 prefixEnd_2612422 1341428158380083120610697 := by
  unfold tailWord_2612422
  simp only [CollatzResearch.WordTrace]
  refine ⟨2977589316926522968800235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 63521905427765823334405013 2977589316926522968800235)
  ·
    refine ⟨4466383975389784453200353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2977589316926522968800235 4466383975389784453200353)
    ·
      refine ⟨3349787981542338339900265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4466383975389784453200353 3349787981542338339900265)
      ·
        refine ⟨2512340986156753754925199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3349787981542338339900265 2512340986156753754925199)
        ·
          refine ⟨3768511479235130632387799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2512340986156753754925199 3768511479235130632387799)
          ·
            refine ⟨5652767218852695948581699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3768511479235130632387799 5652767218852695948581699)
            ·
              refine ⟨8479150828279043922872549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5652767218852695948581699 8479150828279043922872549)
              ·
                refine ⟨1589840780302320735538603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8479150828279043922872549 1589840780302320735538603)
                ·
                  refine ⟨2384761170453481103307905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1589840780302320735538603 2384761170453481103307905)
                  ·
                    refine ⟨1788570877840110827480929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2384761170453481103307905 1788570877840110827480929)
                    ·
                      refine ⟨1341428158380083120610697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1788570877840110827480929 1341428158380083120610697)
                      ·
                        rfl

theorem cell23_2612422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_2612422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612422 prefixEnd_2612422 := by exact prefixLift 2612422
  have htrace : WordTrace (prefixWord ++ tailWord_2612422) baseStart_2612422 baseEnd_2612422 := by
    simpa [prefixWord, tailWord_2612422, baseEnd_2612422] using wordTrace_append hprefix tailTrace_2612422
  have hstable : (prefixWord ++ tailWord_2612422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612422).length < 2 ^ (prefixWord ++ tailWord_2612422).sum := by decide
  have hdescent : baseEnd_2612422 < baseStart_2612422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612423 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 4]
def baseStart_2612423 : Nat := 118140960795 + 2612423 * 2 ^ 59
def prefixEnd_2612423 : Nat := 4983230072969 + 3 ^ 40 * 2612423 * 2
def baseEnd_2612423 : Nat := 1341428671860737616698191

theorem tailTrace_2612423 : CollatzResearch.WordTrace tailWord_2612423 prefixEnd_2612423 1341428671860737616698191 := by
  unfold tailWord_2612423
  simp only [CollatzResearch.WordTrace]
  refine ⟨95282894614645112172393923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63521929743096741448262615 95282894614645112172393923)
  ·
    refine ⟨142924341921967668258590885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95282894614645112172393923 142924341921967668258590885)
    ·
      refine ⟨26798314110368937798485791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142924341921967668258590885 26798314110368937798485791)
      ·
        refine ⟨40197471165553406697728687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26798314110368937798485791 40197471165553406697728687)
        ·
          refine ⟨60296206748330110046593031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40197471165553406697728687 60296206748330110046593031)
          ·
            refine ⟨90444310122495165069889547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60296206748330110046593031 90444310122495165069889547)
            ·
              refine ⟨135666465183742747604834321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90444310122495165069889547 135666465183742747604834321)
              ·
                refine ⟨101749848887807060703625741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135666465183742747604834321 101749848887807060703625741)
                ·
                  refine ⟨38156193332927647763859653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101749848887807060703625741 38156193332927647763859653)
                  ·
                    refine ⟨7154286249923933955723685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38156193332927647763859653 7154286249923933955723685)
                    ·
                      refine ⟨1341428671860737616698191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7154286249923933955723685 1341428671860737616698191)
                      ·
                        rfl

theorem cell23_2612423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_2612423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612423 prefixEnd_2612423 := by exact prefixLift 2612423
  have htrace : WordTrace (prefixWord ++ tailWord_2612423) baseStart_2612423 baseEnd_2612423 := by
    simpa [prefixWord, tailWord_2612423, baseEnd_2612423] using wordTrace_append hprefix tailTrace_2612423
  have hstable : (prefixWord ++ tailWord_2612423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612423).length < 2 ^ (prefixWord ++ tailWord_2612423).sum := by decide
  have hdescent : baseEnd_2612423 < baseStart_2612423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612433 : List Nat := [1, 2, 2, 1, 2, 2, 1, 5, 7]
def baseStart_2612433 : Nat := 118140960795 + 2612433 * 2 ^ 59
def prefixEnd_2612433 : Nat := 4983230072969 + 3 ^ 40 * 2612433 * 2
def baseEnd_2612433 : Nat := 149048200740809175285905

theorem tailTrace_2612433 : CollatzResearch.WordTrace tailWord_2612433 prefixEnd_2612433 149048200740809175285905 := by
  unfold tailWord_2612433
  simp only [CollatzResearch.WordTrace]
  refine ⟨95283259344608883880257953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63522172896405922586838635 95283259344608883880257953)
  ·
    refine ⟨71462444508456662910193465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95283259344608883880257953 71462444508456662910193465)
    ·
      refine ⟨53596833381342497182645099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71462444508456662910193465 53596833381342497182645099)
      ·
        refine ⟨80395250072013745773967649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53596833381342497182645099 80395250072013745773967649)
        ·
          refine ⟨60296437554010309330475737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80395250072013745773967649 60296437554010309330475737)
          ·
            refine ⟨45222328165507731997856803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60296437554010309330475737 45222328165507731997856803)
            ·
              refine ⟨67833492248261597996785205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45222328165507731997856803 67833492248261597996785205)
              ·
                refine ⟨6359389898274524812198613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67833492248261597996785205 6359389898274524812198613)
                ·
                  refine ⟨149048200740809175285905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6359389898274524812198613 149048200740809175285905)
                  ·
                    rfl

theorem cell23_2612433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 7].length) (baseStart_2612433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612433 prefixEnd_2612433 := by exact prefixLift 2612433
  have htrace : WordTrace (prefixWord ++ tailWord_2612433) baseStart_2612433 baseEnd_2612433 := by
    simpa [prefixWord, tailWord_2612433, baseEnd_2612433] using wordTrace_append hprefix tailTrace_2612433
  have hstable : (prefixWord ++ tailWord_2612433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612433).length < 2 ^ (prefixWord ++ tailWord_2612433).sum := by decide
  have hdescent : baseEnd_2612433 < baseStart_2612433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612467 : List Nat := [1, 1, 1, 2, 2, 6, 2, 3, 5]
def baseStart_2612467 : Nat := 118140960795 + 2612467 * 2 ^ 59
def prefixEnd_2612467 : Nat := 4983230072969 + 3 ^ 40 * 2612467 * 2
def baseEnd_2612467 : Nat := 149050140556615049394221

theorem tailTrace_2612467 : CollatzResearch.WordTrace tailWord_2612467 prefixEnd_2612467 149050140556615049394221 := by
  unfold tailWord_2612467
  simp only [CollatzResearch.WordTrace]
  refine ⟨95284499426485707686995655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63522999617657138457997103 95284499426485707686995655)
  ·
    refine ⟨142926749139728561530493483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95284499426485707686995655 142926749139728561530493483)
    ·
      refine ⟨214390123709592842295740225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142926749139728561530493483 214390123709592842295740225)
      ·
        refine ⟨160792592782194631721805169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214390123709592842295740225 160792592782194631721805169)
        ·
          refine ⟨120594444586645973791353877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160792592782194631721805169 120594444586645973791353877)
          ·
            refine ⟨5652864589999030021469713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 120594444586645973791353877 5652864589999030021469713)
            ·
              refine ⟨4239648442499272516102285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5652864589999030021469713 4239648442499272516102285)
              ·
                refine ⟨1589868165937227193538357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4239648442499272516102285 1589868165937227193538357)
                ·
                  refine ⟨149050140556615049394221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1589868165937227193538357 149050140556615049394221)
                  ·
                    rfl

theorem cell23_2612467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 3, 5].length) (baseStart_2612467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612467 prefixEnd_2612467 := by exact prefixLift 2612467
  have htrace : WordTrace (prefixWord ++ tailWord_2612467) baseStart_2612467 baseEnd_2612467 := by
    simpa [prefixWord, tailWord_2612467, baseEnd_2612467] using wordTrace_append hprefix tailTrace_2612467
  have hstable : (prefixWord ++ tailWord_2612467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612467).length < 2 ^ (prefixWord ++ tailWord_2612467).sum := by decide
  have hdescent : baseEnd_2612467 < baseStart_2612467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612478 : List Nat := [4, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2]
def baseStart_2612478 : Nat := 118140960795 + 2612478 * 2 ^ 59
def prefixEnd_2612478 : Nat := 4983230072969 + 3 ^ 40 * 2612478 * 2
def baseEnd_2612478 : Nat := 1341456913296734901510439

theorem tailTrace_2612478 : CollatzResearch.WordTrace tailWord_2612478 prefixEnd_2612478 1341456913296734901510439 := by
  unfold tailWord_2612478
  simp only [CollatzResearch.WordTrace]
  refine ⟨11910612578680732070705761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63523267086297237710430725 11910612578680732070705761)
  ·
    refine ⟨8932959434010549053029321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11910612578680732070705761 8932959434010549053029321)
    ·
      refine ⟨6699719575507911789771991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8932959434010549053029321 6699719575507911789771991)
      ·
        refine ⟨10049579363261867684657987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6699719575507911789771991 10049579363261867684657987)
        ·
          refine ⟨15074369044892801526986981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10049579363261867684657987 15074369044892801526986981)
          ·
            refine ⟨2826444195917400286310059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15074369044892801526986981 2826444195917400286310059)
            ·
              refine ⟨4239666293876100429465089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2826444195917400286310059 4239666293876100429465089)
              ·
                refine ⟨3179749720407075322098817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4239666293876100429465089 3179749720407075322098817)
                ·
                  refine ⟨2384812290305306491574113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3179749720407075322098817 2384812290305306491574113)
                  ·
                    refine ⟨1788609217728979868680585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2384812290305306491574113 1788609217728979868680585)
                    ·
                      refine ⟨1341456913296734901510439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1788609217728979868680585 1341456913296734901510439)
                      ·
                        rfl

theorem cell23_2612478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_2612478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612478 prefixEnd_2612478 := by exact prefixLift 2612478
  have htrace : WordTrace (prefixWord ++ tailWord_2612478) baseStart_2612478 baseEnd_2612478 := by
    simpa [prefixWord, tailWord_2612478, baseEnd_2612478] using wordTrace_append hprefix tailTrace_2612478
  have hstable : (prefixWord ++ tailWord_2612478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612478).length < 2 ^ (prefixWord ++ tailWord_2612478).sum := by decide
  have hdescent : baseEnd_2612478 < baseStart_2612478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612540 : List Nat := [2, 2, 2, 2, 1, 3, 2, 1, 8]
def baseStart_2612540 : Nat := 118140960795 + 2612540 * 2 ^ 59
def prefixEnd_2612540 : Nat := 4983230072969 + 3 ^ 40 * 2612540 * 2
def baseEnd_2612540 : Nat := 149054305455257073215017

theorem tailTrace_2612540 : CollatzResearch.WordTrace tailWord_2612540 prefixEnd_2612540 149054305455257073215017 := by
  unfold tailWord_2612540
  simp only [CollatzResearch.WordTrace]
  refine ⟨47643580977610620577201537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63524774636814160769602049 47643580977610620577201537)
  ·
    refine ⟨35732685733207965432901153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47643580977610620577201537 35732685733207965432901153)
    ·
      refine ⟨26799514299905974074675865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35732685733207965432901153 26799514299905974074675865)
      ·
        refine ⟨20099635724929480556006899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26799514299905974074675865 20099635724929480556006899)
        ·
          refine ⟨30149453587394220834010349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20099635724929480556006899 30149453587394220834010349)
          ·
            refine ⟨11306045095272832812753881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30149453587394220834010349 11306045095272832812753881)
            ·
              refine ⟨8479533821454624609565411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11306045095272832812753881 8479533821454624609565411)
              ·
                refine ⟨12719300732181936914348117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8479533821454624609565411 12719300732181936914348117)
                ·
                  refine ⟨149054305455257073215017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12719300732181936914348117 149054305455257073215017)
                  ·
                    rfl

theorem cell23_2612540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 8].length) (baseStart_2612540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612540 prefixEnd_2612540 := by exact prefixLift 2612540
  have htrace : WordTrace (prefixWord ++ tailWord_2612540) baseStart_2612540 baseEnd_2612540 := by
    simpa [prefixWord, tailWord_2612540, baseEnd_2612540] using wordTrace_append hprefix tailTrace_2612540
  have hstable : (prefixWord ++ tailWord_2612540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612540).length < 2 ^ (prefixWord ++ tailWord_2612540).sum := by decide
  have hdescent : baseEnd_2612540 < baseStart_2612540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612577 : List Nat := [1, 2, 3, 1, 1, 1, 1, 5, 1, 5, 2]
def baseStart_2612577 : Nat := 118140960795 + 2612577 * 2 ^ 59
def prefixEnd_2612577 : Nat := 4983230072969 + 3 ^ 40 * 2612577 * 2
def baseEnd_2612577 : Nat := 1341507747881530014172483

theorem tailTrace_2612577 : CollatzResearch.WordTrace tailWord_2612577 prefixEnd_2612577 1341507747881530014172483 := by
  unfold tailWord_2612577
  simp only [CollatzResearch.WordTrace]
  refine ⟨95288511456087196473499985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63525674304058130982333323 95288511456087196473499985)
  ·
    refine ⟨71466383592065397355124989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95288511456087196473499985 71466383592065397355124989)
    ·
      refine ⟨26799893847024524008171871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71466383592065397355124989 26799893847024524008171871)
      ·
        refine ⟨40199840770536786012257807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26799893847024524008171871 40199840770536786012257807)
        ·
          refine ⟨60299761155805179018386711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40199840770536786012257807 60299761155805179018386711)
          ·
            refine ⟨90449641733707768527580067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60299761155805179018386711 90449641733707768527580067)
            ·
              refine ⟨135674462600561652791370101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90449641733707768527580067 135674462600561652791370101)
              ·
                refine ⟨12719480868802654949190947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 135674462600561652791370101 12719480868802654949190947)
                ·
                  refine ⟨19079221303203982423786421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12719480868802654949190947 19079221303203982423786421)
                  ·
                    refine ⟨1788676997175373352229977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19079221303203982423786421 1788676997175373352229977)
                    ·
                      refine ⟨1341507747881530014172483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1788676997175373352229977 1341507747881530014172483)
                      ·
                        rfl

theorem cell23_2612577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 5, 2].length) (baseStart_2612577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612577 prefixEnd_2612577 := by exact prefixLift 2612577
  have htrace : WordTrace (prefixWord ++ tailWord_2612577) baseStart_2612577 baseEnd_2612577 := by
    simpa [prefixWord, tailWord_2612577, baseEnd_2612577] using wordTrace_append hprefix tailTrace_2612577
  have hstable : (prefixWord ++ tailWord_2612577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612577).length < 2 ^ (prefixWord ++ tailWord_2612577).sum := by decide
  have hdescent : baseEnd_2612577 < baseStart_2612577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612594 : List Nat := [3, 2, 1, 2, 1, 2, 1, 4, 2, 3, 2]
def baseStart_2612594 : Nat := 118140960795 + 2612594 * 2 ^ 59
def prefixEnd_2612594 : Nat := 4983230072969 + 3 ^ 40 * 2612594 * 2
def baseEnd_2612594 : Nat := 1341516477052656447659905

theorem tailTrace_2612594 : CollatzResearch.WordTrace tailWord_2612594 prefixEnd_2612594 1341516477052656447659905 := by
  unfold tailWord_2612594
  simp only [CollatzResearch.WordTrace]
  refine ⟨23822282874256402094217209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63526087664683738917912557 23822282874256402094217209)
  ·
    refine ⟨17866712155692301570662907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23822282874256402094217209 17866712155692301570662907)
    ·
      refine ⟨26800068233538452355994361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17866712155692301570662907 26800068233538452355994361)
      ·
        refine ⟨20100051175153839266995771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26800068233538452355994361 20100051175153839266995771)
        ·
          refine ⟨30150076762730758900493657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20100051175153839266995771 30150076762730758900493657)
          ·
            refine ⟨22612557572048069175370243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30150076762730758900493657 22612557572048069175370243)
            ·
              refine ⟨33918836358072103763055365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22612557572048069175370243 33918836358072103763055365)
              ·
                refine ⟨6359781817138519455572881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33918836358072103763055365 6359781817138519455572881)
                ·
                  refine ⟨4769836362853889591679661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6359781817138519455572881 4769836362853889591679661)
                  ·
                    refine ⟨1788688636070208596879873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4769836362853889591679661 1788688636070208596879873)
                    ·
                      refine ⟨1341516477052656447659905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1788688636070208596879873 1341516477052656447659905)
                      ·
                        rfl

theorem cell23_2612594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_2612594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612594 prefixEnd_2612594 := by exact prefixLift 2612594
  have htrace : WordTrace (prefixWord ++ tailWord_2612594) baseStart_2612594 baseEnd_2612594 := by
    simpa [prefixWord, tailWord_2612594, baseEnd_2612594] using wordTrace_append hprefix tailTrace_2612594
  have hstable : (prefixWord ++ tailWord_2612594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612594).length < 2 ^ (prefixWord ++ tailWord_2612594).sum := by decide
  have hdescent : baseEnd_2612594 < baseStart_2612594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612628 : List Nat := [2, 4, 2, 1, 2, 3, 1, 1, 2, 3, 2]
def baseStart_2612628 : Nat := 118140960795 + 2612628 * 2 ^ 59
def prefixEnd_2612628 : Nat := 4983230072969 + 3 ^ 40 * 2612628 * 2
def baseEnd_2612628 : Nat := 1341533935394909314634749

theorem tailTrace_2612628 : CollatzResearch.WordTrace tailWord_2612628 prefixEnd_2612628 1341533935394909314634749 := by
  unfold tailWord_2612628
  simp only [CollatzResearch.WordTrace]
  refine ⟨47645185789451216091803269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63526914385934954789071025 47645185789451216091803269)
  ·
    refine ⟨8933472335522103017213113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47645185789451216091803269 8933472335522103017213113)
    ·
      refine ⟨6700104251641577262909835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8933472335522103017213113 6700104251641577262909835)
      ·
        refine ⟨10050156377462365894364753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6700104251641577262909835 10050156377462365894364753)
        ·
          refine ⟨7537617283096774420773565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10050156377462365894364753 7537617283096774420773565)
          ·
            refine ⟨2826606481161290407790087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7537617283096774420773565 2826606481161290407790087)
            ·
              refine ⟨4239909721741935611685131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2826606481161290407790087 4239909721741935611685131)
              ·
                refine ⟨6359864582612903417527697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4239909721741935611685131 6359864582612903417527697)
                ·
                  refine ⟨4769898436959677563145773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6359864582612903417527697 4769898436959677563145773)
                  ·
                    refine ⟨1788711913859879086179665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4769898436959677563145773 1788711913859879086179665)
                    ·
                      refine ⟨1341533935394909314634749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1788711913859879086179665 1341533935394909314634749)
                      ·
                        rfl

theorem cell23_2612628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_2612628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612628 prefixEnd_2612628 := by exact prefixLift 2612628
  have htrace : WordTrace (prefixWord ++ tailWord_2612628) baseStart_2612628 baseEnd_2612628 := by
    simpa [prefixWord, tailWord_2612628, baseEnd_2612628] using wordTrace_append hprefix tailTrace_2612628
  have hstable : (prefixWord ++ tailWord_2612628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612628).length < 2 ^ (prefixWord ++ tailWord_2612628).sum := by decide
  have hdescent : baseEnd_2612628 < baseStart_2612628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612668 : List Nat := [2, 2, 2, 4, 2, 1, 3, 1, 2, 4]
def baseStart_2612668 : Nat := 118140960795 + 2612668 * 2 ^ 59
def prefixEnd_2612668 : Nat := 4983230072969 + 3 ^ 40 * 2612668 * 2
def baseEnd_2612668 : Nat := 447184824873696386044855

theorem tailTrace_2612668 : CollatzResearch.WordTrace tailWord_2612668 prefixEnd_2612668 447184824873696386044855 := by
  unfold tailWord_2612668
  simp only [CollatzResearch.WordTrace]
  refine ⟨47645915249378759507531329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63527886999171679343375105 47645915249378759507531329)
  ·
    refine ⟨35734436437034069630648497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47645915249378759507531329 35734436437034069630648497)
    ·
      refine ⟨26800827327775552222986373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35734436437034069630648497 26800827327775552222986373)
      ·
        refine ⟨5025155123957916041809945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26800827327775552222986373 5025155123957916041809945)
        ·
          refine ⟨3768866342968437031357459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5025155123957916041809945 3768866342968437031357459)
          ·
            refine ⟨5653299514452655547036189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3768866342968437031357459 5653299514452655547036189)
            ·
              refine ⟨2119987317919745830138571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5653299514452655547036189 2119987317919745830138571)
              ·
                refine ⟨3179980976879618745207857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2119987317919745830138571 3179980976879618745207857)
                ·
                  refine ⟨2384985732659714058905893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3179980976879618745207857 2384985732659714058905893)
                  ·
                    refine ⟨447184824873696386044855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2384985732659714058905893 447184824873696386044855)
                    ·
                      rfl

theorem cell23_2612668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 2, 4].length) (baseStart_2612668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612668 prefixEnd_2612668 := by exact prefixLift 2612668
  have htrace : WordTrace (prefixWord ++ tailWord_2612668) baseStart_2612668 baseEnd_2612668 := by
    simpa [prefixWord, tailWord_2612668, baseEnd_2612668] using wordTrace_append hprefix tailTrace_2612668
  have hstable : (prefixWord ++ tailWord_2612668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612668).length < 2 ^ (prefixWord ++ tailWord_2612668).sum := by decide
  have hdescent : baseEnd_2612668 < baseStart_2612668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612692 : List Nat := [2, 4, 1, 2, 3, 2, 1, 3, 1, 2, 2]
def baseStart_2612692 : Nat := 118140960795 + 2612692 * 2 ^ 59
def prefixEnd_2612692 : Nat := 4983230072969 + 3 ^ 40 * 2612692 * 2
def baseEnd_2612692 : Nat := 1341566798156797064234455

theorem tailTrace_2612692 : CollatzResearch.WordTrace tailWord_2612692 prefixEnd_2612692 1341566798156797064234455 := by
  unfold tailWord_2612692
  simp only [CollatzResearch.WordTrace]
  refine ⟨47646352925335285556968165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63528470567113714075957553 47646352925335285556968165)
  ·
    refine ⟨8933691173500366041931531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47646352925335285556968165 8933691173500366041931531)
    ·
      refine ⟨13400536760250549062897297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8933691173500366041931531 13400536760250549062897297)
      ·
        refine ⟨10050402570187911797172973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13400536760250549062897297 10050402570187911797172973)
        ·
          refine ⟨3768900963820466923939865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10050402570187911797172973 3768900963820466923939865)
          ·
            refine ⟨2826675722865350192954899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3768900963820466923939865 2826675722865350192954899)
            ·
              refine ⟨4240013584298025289432349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2826675722865350192954899 4240013584298025289432349)
              ·
                refine ⟨1590005094111759483537131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4240013584298025289432349 1590005094111759483537131)
                ·
                  refine ⟨2385007641167639225305697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1590005094111759483537131 2385007641167639225305697)
                  ·
                    refine ⟨1788755730875729418979273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2385007641167639225305697 1788755730875729418979273)
                    ·
                      refine ⟨1341566798156797064234455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1788755730875729418979273 1341566798156797064234455)
                      ·
                        rfl

theorem cell23_2612692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_2612692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612692 prefixEnd_2612692 := by exact prefixLift 2612692
  have htrace : WordTrace (prefixWord ++ tailWord_2612692) baseStart_2612692 baseEnd_2612692 := by
    simpa [prefixWord, tailWord_2612692, baseEnd_2612692] using wordTrace_append hprefix tailTrace_2612692
  have hstable : (prefixWord ++ tailWord_2612692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612692).length < 2 ^ (prefixWord ++ tailWord_2612692).sum := by decide
  have hdescent : baseEnd_2612692 < baseStart_2612692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612725 : List Nat := [1, 3, 5, 1, 1, 1, 4, 1, 2, 1, 3]
def baseStart_2612725 : Nat := 118140960795 + 2612725 * 2 ^ 59
def prefixEnd_2612725 : Nat := 4983230072969 + 3 ^ 40 * 2612725 * 2
def baseEnd_2612725 : Nat := 1341583743018395435121803

theorem tailTrace_2612725 : CollatzResearch.WordTrace tailWord_2612725 prefixEnd_2612725 1341583743018395435121803 := by
  unfold tailWord_2612725
  simp only [CollatzResearch.WordTrace]
  refine ⟨95293909459551017749887629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63529272973034011833258419 95293909459551017749887629)
  ·
    refine ⟨35735216047331631656207861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95293909459551017749887629 35735216047331631656207861)
    ·
      refine ⟨3350176504437340467769487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35735216047331631656207861 3350176504437340467769487)
      ·
        refine ⟨5025264756656010701654231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3350176504437340467769487 5025264756656010701654231)
        ·
          refine ⟨7537897134984016052481347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5025264756656010701654231 7537897134984016052481347)
          ·
            refine ⟨11306845702476024078722021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7537897134984016052481347 11306845702476024078722021)
            ·
              refine ⟨2120033569214254514760379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11306845702476024078722021 2120033569214254514760379)
              ·
                refine ⟨3180050353821381772140569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2120033569214254514760379 3180050353821381772140569)
                ·
                  refine ⟨2385037765366036329105427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3180050353821381772140569 2385037765366036329105427)
                  ·
                    refine ⟨3577556648049054493658141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2385037765366036329105427 3577556648049054493658141)
                    ·
                      refine ⟨1341583743018395435121803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3577556648049054493658141 1341583743018395435121803)
                      ·
                        rfl

theorem cell23_2612725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_2612725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612725 prefixEnd_2612725 := by exact prefixLift 2612725
  have htrace : WordTrace (prefixWord ++ tailWord_2612725) baseStart_2612725 baseEnd_2612725 := by
    simpa [prefixWord, tailWord_2612725, baseEnd_2612725] using wordTrace_append hprefix tailTrace_2612725
  have hstable : (prefixWord ++ tailWord_2612725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612725).length < 2 ^ (prefixWord ++ tailWord_2612725).sum := by decide
  have hdescent : baseEnd_2612725 < baseStart_2612725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612731 : List Nat := [1, 1, 1, 1, 1, 3, 2, 7, 2, 2, 2]
def baseStart_2612731 : Nat := 118140960795 + 2612731 * 2 ^ 59
def prefixEnd_2612731 : Nat := 4983230072969 + 3 ^ 40 * 2612731 * 2
def baseEnd_2612731 : Nat := 1341586823902322411646775

theorem tailTrace_2612731 : CollatzResearch.WordTrace tailWord_2612731 prefixEnd_2612731 1341586823902322411646775 := by
  unfold tailWord_2612731
  simp only [CollatzResearch.WordTrace]
  refine ⟨95294128297529280774606047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63529418865019520516404031 95294128297529280774606047)
  ·
    refine ⟨142941192446293921161909071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95294128297529280774606047 142941192446293921161909071)
    ·
      refine ⟨214411788669440881742863607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142941192446293921161909071 214411788669440881742863607)
      ·
        refine ⟨321617683004161322614295411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214411788669440881742863607 321617683004161322614295411)
        ·
          refine ⟨482426524506241983921443117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321617683004161322614295411 482426524506241983921443117)
          ·
            refine ⟨180909946689840743970541169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 482426524506241983921443117 180909946689840743970541169)
            ·
              refine ⟨135682460017380557977905877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180909946689840743970541169 135682460017380557977905877)
              ·
                refine ⟨3180057656657356827607169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 135682460017380557977905877 3180057656657356827607169)
                ·
                  refine ⟨2385043242493017620705377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3180057656657356827607169 2385043242493017620705377)
                  ·
                    refine ⟨1788782431869763215529033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2385043242493017620705377 1788782431869763215529033)
                    ·
                      refine ⟨1341586823902322411646775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1788782431869763215529033 1341586823902322411646775)
                      ·
                        rfl

theorem cell23_2612731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 2, 2, 2].length) (baseStart_2612731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612731 prefixEnd_2612731 := by exact prefixLift 2612731
  have htrace : WordTrace (prefixWord ++ tailWord_2612731) baseStart_2612731 baseEnd_2612731 := by
    simpa [prefixWord, tailWord_2612731, baseEnd_2612731] using wordTrace_append hprefix tailTrace_2612731
  have hstable : (prefixWord ++ tailWord_2612731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612731).length < 2 ^ (prefixWord ++ tailWord_2612731).sum := by decide
  have hdescent : baseEnd_2612731 < baseStart_2612731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612764 : List Nat := [2, 2, 3, 1, 2, 1, 2, 2, 2, 3, 3]
def baseStart_2612764 : Nat := 118140960795 + 2612764 * 2 ^ 59
def prefixEnd_2612764 : Nat := 4983230072969 + 3 ^ 40 * 2612764 * 2
def baseEnd_2612764 : Nat := 1341603768763920782534123

theorem tailTrace_2612764 : CollatzResearch.WordTrace tailWord_2612764 prefixEnd_2612764 1341603768763920782534123 := by
  unfold tailWord_2612764
  simp only [CollatzResearch.WordTrace]
  refine ⟨47647665953204863705278673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63530221270939818273704897 47647665953204863705278673)
  ·
    refine ⟨35735749464903647778959005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47647665953204863705278673 35735749464903647778959005)
    ·
      refine ⟨13400906049338867917109627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35735749464903647778959005 13400906049338867917109627)
      ·
        refine ⟨20101359074008301875664441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13400906049338867917109627 20101359074008301875664441)
        ·
          refine ⟨15076019305506226406748331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20101359074008301875664441 15076019305506226406748331)
          ·
            refine ⟨22614028958259339610122497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15076019305506226406748331 22614028958259339610122497)
            ·
              refine ⟨16960521718694504707591873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22614028958259339610122497 16960521718694504707591873)
              ·
                refine ⟨12720391289020878530693905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16960521718694504707591873 12720391289020878530693905)
                ·
                  refine ⟨9540293466765658898020429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12720391289020878530693905 9540293466765658898020429)
                  ·
                    refine ⟨3577610050037122086757661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9540293466765658898020429 3577610050037122086757661)
                    ·
                      refine ⟨1341603768763920782534123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3577610050037122086757661 1341603768763920782534123)
                      ·
                        rfl

theorem cell23_2612764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_2612764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612764 prefixEnd_2612764 := by exact prefixLift 2612764
  have htrace : WordTrace (prefixWord ++ tailWord_2612764) baseStart_2612764 baseEnd_2612764 := by
    simpa [prefixWord, tailWord_2612764, baseEnd_2612764] using wordTrace_append hprefix tailTrace_2612764
  have hstable : (prefixWord ++ tailWord_2612764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612764).length < 2 ^ (prefixWord ++ tailWord_2612764).sum := by decide
  have hdescent : baseEnd_2612764 < baseStart_2612764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612771 : List Nat := [1, 1, 1, 4, 5, 1, 1, 4, 5]
def baseStart_2612771 : Nat := 118140960795 + 2612771 * 2 ^ 59
def prefixEnd_2612771 : Nat := 4983230072969 + 3 ^ 40 * 2612771 * 2
def baseEnd_2612771 : Nat := 149067484792055806127399

theorem tailTrace_2612771 : CollatzResearch.WordTrace tailWord_2612771 prefixEnd_2612771 149067484792055806127399 := by
  unfold tailWord_2612771
  simp only [CollatzResearch.WordTrace]
  refine ⟨95295587217384367606062167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63530391478256245070708111 95295587217384367606062167)
  ·
    refine ⟨142943380826076551409093251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95295587217384367606062167 142943380826076551409093251)
    ·
      refine ⟨214415071239114827113639877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142943380826076551409093251 214415071239114827113639877)
      ·
        refine ⟨40202825857334030083807477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 214415071239114827113639877 40202825857334030083807477)
        ·
          refine ⟨3769014924125065320356951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40202825857334030083807477 3769014924125065320356951)
          ·
            refine ⟨5653522386187597980535427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3769014924125065320356951 5653522386187597980535427)
            ·
              refine ⟨8480283579281396970803141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5653522386187597980535427 8480283579281396970803141)
              ·
                refine ⟨1590053171115261932025589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8480283579281396970803141 1590053171115261932025589)
                ·
                  refine ⟨149067484792055806127399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1590053171115261932025589 149067484792055806127399)
                  ·
                    rfl

theorem cell23_2612771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 4, 5].length) (baseStart_2612771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612771 prefixEnd_2612771 := by exact prefixLift 2612771
  have htrace : WordTrace (prefixWord ++ tailWord_2612771) baseStart_2612771 baseEnd_2612771 := by
    simpa [prefixWord, tailWord_2612771, baseEnd_2612771] using wordTrace_append hprefix tailTrace_2612771
  have hstable : (prefixWord ++ tailWord_2612771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612771).length < 2 ^ (prefixWord ++ tailWord_2612771).sum := by decide
  have hdescent : baseEnd_2612771 < baseStart_2612771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612814 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 7, 4]
def baseStart_2612814 : Nat := 118140960795 + 2612814 * 2 ^ 59
def prefixEnd_2612814 : Nat := 4983230072969 + 3 ^ 40 * 2612814 * 2
def baseEnd_2612814 : Nat := 447209814265548528969631

theorem tailTrace_2612814 : CollatzResearch.WordTrace tailWord_2612814 prefixEnd_2612814 447209814265548528969631 := by
  unfold tailWord_2612814
  simp only [CollatzResearch.WordTrace]
  refine ⟨11912144444528573243734687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63531437037485723966584997 11912144444528573243734687)
  ·
    refine ⟨17868216666792859865602031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11912144444528573243734687 17868216666792859865602031)
    ·
      refine ⟨26802325000189289798403047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17868216666792859865602031 26802325000189289798403047)
      ·
        refine ⟨40203487500283934697604571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26802325000189289798403047 40203487500283934697604571)
        ·
          refine ⟨60305231250425902046406857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40203487500283934697604571 60305231250425902046406857)
          ·
            refine ⟨45228923437819426534805143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60305231250425902046406857 45228923437819426534805143)
            ·
              refine ⟨67843385156729139802207715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45228923437819426534805143 67843385156729139802207715)
              ·
                refine ⟨101765077735093709703311573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67843385156729139802207715 101765077735093709703311573)
                ·
                  refine ⟨2385119009416258821171365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 101765077735093709703311573 2385119009416258821171365)
                  ·
                    refine ⟨447209814265548528969631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2385119009416258821171365 447209814265548528969631)
                    ·
                      rfl

theorem cell23_2612814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_2612814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612814 prefixEnd_2612814 := by exact prefixLift 2612814
  have htrace : WordTrace (prefixWord ++ tailWord_2612814) baseStart_2612814 baseEnd_2612814 := by
    simpa [prefixWord, tailWord_2612814, baseEnd_2612814] using wordTrace_append hprefix tailTrace_2612814
  have hstable : (prefixWord ++ tailWord_2612814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612814).length < 2 ^ (prefixWord ++ tailWord_2612814).sum := by decide
  have hdescent : baseEnd_2612814 < baseStart_2612814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612817 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 1, 3, 6]
def baseStart_2612817 : Nat := 118140960795 + 2612817 * 2 ^ 59
def prefixEnd_2612817 : Nat := 4983230072969 + 3 ^ 40 * 2612817 * 2
def baseEnd_2612817 : Nat := 1341630983238609075171379

theorem tailTrace_2612817 : CollatzResearch.WordTrace tailWord_2612817 prefixEnd_2612817 1341630983238609075171379 := by
  unfold tailWord_2612817
  simp only [CollatzResearch.WordTrace]
  refine ⟨95297264975217717462236705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63531509983478478308157803 95297264975217717462236705)
  ·
    refine ⟨71472948731413288096677529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95297264975217717462236705 71472948731413288096677529)
    ·
      refine ⟨53604711548559966072508147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71472948731413288096677529 53604711548559966072508147)
      ·
        refine ⟨80407067322839949108762221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53604711548559966072508147 80407067322839949108762221)
        ·
          refine ⟨30152650246064980915785833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80407067322839949108762221 30152650246064980915785833)
          ·
            refine ⟨22614487684548735686839375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30152650246064980915785833 22614487684548735686839375)
            ·
              refine ⟨33921731526823103530259063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22614487684548735686839375 33921731526823103530259063)
              ·
                refine ⟨50882597290234655295388595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33921731526823103530259063 50882597290234655295388595)
                ·
                  refine ⟨76323895935351982943082893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50882597290234655295388595 76323895935351982943082893)
                  ·
                    refine ⟨28621460975756993603656085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 76323895935351982943082893 28621460975756993603656085)
                    ·
                      refine ⟨1341630983238609075171379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 28621460975756993603656085 1341630983238609075171379)
                      ·
                        rfl

theorem cell23_2612817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_2612817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2612817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2612817 prefixEnd_2612817 := by exact prefixLift 2612817
  have htrace : WordTrace (prefixWord ++ tailWord_2612817) baseStart_2612817 baseEnd_2612817 := by
    simpa [prefixWord, tailWord_2612817, baseEnd_2612817] using wordTrace_append hprefix tailTrace_2612817
  have hstable : (prefixWord ++ tailWord_2612817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612817).length < 2 ^ (prefixWord ++ tailWord_2612817).sum := by decide
  have hdescent : baseEnd_2612817 < baseStart_2612817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
