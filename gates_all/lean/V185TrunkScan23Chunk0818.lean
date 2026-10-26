import V185TrunkScan23Chunk0817

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4839813 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 5, 2, 3]
def baseStart_4839813 : Nat := 118140960795 + 4839813 * 2 ^ 59
def prefixEnd_4839813 : Nat := 4983230072969 + 3 ^ 40 * 4839813 * 2
def baseEnd_4839813 : Nat := 2485150346878777943079611

theorem tailTrace_4839813 : CollatzResearch.WordTrace tailWord_4839813 prefixEnd_4839813 2485150346878777943079611 := by
  unfold tailWord_4839813
  simp only [CollatzResearch.WordTrace]
  refine ⟨176522482015191550098572093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117681654676794366732381395 176522482015191550098572093)
  ·
    refine ⟨66195930755696831286964535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176522482015191550098572093 66195930755696831286964535)
    ·
      refine ⟨99293896133545246930446803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66195930755696831286964535 99293896133545246930446803)
      ·
        refine ⟨148940844200317870395670205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99293896133545246930446803 148940844200317870395670205)
        ·
          refine ⟨55852816575119201398376327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148940844200317870395670205 55852816575119201398376327)
          ·
            refine ⟨83779224862678802097564491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55852816575119201398376327 83779224862678802097564491)
            ·
              refine ⟨125668837294018203146346737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83779224862678802097564491 125668837294018203146346737)
              ·
                refine ⟨94251627970513652359760053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125668837294018203146346737 94251627970513652359760053)
                ·
                  refine ⟨8836090122235654908727505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 94251627970513652359760053 8836090122235654908727505)
                  ·
                    refine ⟨6627067591676741181545629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8836090122235654908727505 6627067591676741181545629)
                    ·
                      refine ⟨2485150346878777943079611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6627067591676741181545629 2485150346878777943079611)
                      ·
                        rfl

theorem cell23_4839813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 2, 3].length) (baseStart_4839813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839813 prefixEnd_4839813 := by exact prefixLift 4839813
  have htrace : WordTrace (prefixWord ++ tailWord_4839813) baseStart_4839813 baseEnd_4839813 := by
    simpa [prefixWord, tailWord_4839813, baseEnd_4839813] using wordTrace_append hprefix tailTrace_4839813
  have hstable : (prefixWord ++ tailWord_4839813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839813).length < 2 ^ (prefixWord ++ tailWord_4839813).sum := by decide
  have hdescent : baseEnd_4839813 < baseStart_4839813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839837 : List Nat := [1, 4, 2, 1, 4, 1, 1, 3, 2, 4]
def baseStart_4839837 : Nat := 118140960795 + 4839837 * 2 ^ 59
def prefixEnd_4839837 : Nat := 4983230072969 + 3 ^ 40 * 4839837 * 2
def baseEnd_4839837 : Nat := 828387556804828616393167

theorem tailTrace_4839837 : CollatzResearch.WordTrace tailWord_4839837 prefixEnd_4839837 828387556804828616393167 := by
  unfold tailWord_4839837
  simp only [CollatzResearch.WordTrace]
  refine ⟨176523357367104602197445765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117682238244736401464963843 176523357367104602197445765)
  ·
    refine ⟨33098129506332112912021081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176523357367104602197445765 33098129506332112912021081)
    ·
      refine ⟨24823597129749084684015811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33098129506332112912021081 24823597129749084684015811)
      ·
        refine ⟨37235395694623627026023717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24823597129749084684015811 37235395694623627026023717)
        ·
          refine ⟨6981636692741930067379447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37235395694623627026023717 6981636692741930067379447)
          ·
            refine ⟨10472455039112895101069171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6981636692741930067379447 10472455039112895101069171)
            ·
              refine ⟨15708682558669342651603757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10472455039112895101069171 15708682558669342651603757)
              ·
                refine ⟨5890755959501003494351409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15708682558669342651603757 5890755959501003494351409)
                ·
                  refine ⟨4418066969625752620763557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5890755959501003494351409 4418066969625752620763557)
                  ·
                    refine ⟨828387556804828616393167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4418066969625752620763557 828387556804828616393167)
                    ·
                      rfl

theorem cell23_4839837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_4839837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839837 prefixEnd_4839837 := by exact prefixLift 4839837
  have htrace : WordTrace (prefixWord ++ tailWord_4839837) baseStart_4839837 baseEnd_4839837 := by
    simpa [prefixWord, tailWord_4839837, baseEnd_4839837] using wordTrace_append hprefix tailTrace_4839837
  have hstable : (prefixWord ++ tailWord_4839837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839837).length < 2 ^ (prefixWord ++ tailWord_4839837).sum := by decide
  have hdescent : baseEnd_4839837 < baseStart_4839837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839847 : List Nat := [1, 1, 6, 1, 1, 2, 3, 2, 1, 2, 3]
def baseStart_4839847 : Nat := 118140960795 + 4839847 * 2 ^ 59
def prefixEnd_4839847 : Nat := 4983230072969 + 3 ^ 40 * 4839847 * 2
def baseEnd_4839847 : Nat := 2485167805221030810054455

theorem tailTrace_4839847 : CollatzResearch.WordTrace tailWord_4839847 prefixEnd_4839847 2485167805221030810054455 := by
  unfold tailWord_4839847
  simp only [CollatzResearch.WordTrace]
  refine ⟨176523722097068373905309795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117682481398045582603539863 176523722097068373905309795)
  ·
    refine ⟨264785583145602560857964693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176523722097068373905309795 264785583145602560857964693)
    ·
      refine ⟨12411824209950120040217095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 264785583145602560857964693 12411824209950120040217095)
      ·
        refine ⟨18617736314925180060325643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12411824209950120040217095 18617736314925180060325643)
        ·
          refine ⟨27926604472387770090488465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18617736314925180060325643 27926604472387770090488465)
          ·
            refine ⟨20944953354290827567866349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27926604472387770090488465 20944953354290827567866349)
            ·
              refine ⟨7854357507859060337949881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20944953354290827567866349 7854357507859060337949881)
              ·
                refine ⟨5890768130894295253462411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7854357507859060337949881 5890768130894295253462411)
                ·
                  refine ⟨8836152196341442880193617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5890768130894295253462411 8836152196341442880193617)
                  ·
                    refine ⟨6627114147256082160145213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8836152196341442880193617 6627114147256082160145213)
                    ·
                      refine ⟨2485167805221030810054455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6627114147256082160145213 2485167805221030810054455)
                      ·
                        rfl

theorem cell23_4839847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_4839847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839847 prefixEnd_4839847 := by exact prefixLift 4839847
  have htrace : WordTrace (prefixWord ++ tailWord_4839847) baseStart_4839847 baseEnd_4839847 := by
    simpa [prefixWord, tailWord_4839847, baseEnd_4839847] using wordTrace_append hprefix tailTrace_4839847
  have hstable : (prefixWord ++ tailWord_4839847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839847).length < 2 ^ (prefixWord ++ tailWord_4839847).sum := by decide
  have hdescent : baseEnd_4839847 < baseStart_4839847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839856 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 7]
def baseStart_4839856 : Nat := 118140960795 + 4839856 * 2 ^ 59
def prefixEnd_4839856 : Nat := 4983230072969 + 3 ^ 40 * 4839856 * 2
def baseEnd_4839856 : Nat := 2485172426546921274841913

theorem tailTrace_4839856 : CollatzResearch.WordTrace tailWord_4839856 prefixEnd_4839856 2485172426546921274841913 := by
  unfold tailWord_4839856
  simp only [CollatzResearch.WordTrace]
  refine ⟨88262025177017884221193711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117682700236023845628258281 88262025177017884221193711)
  ·
    refine ⟨132393037765526826331790567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88262025177017884221193711 132393037765526826331790567)
    ·
      refine ⟨198589556648290239497685851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132393037765526826331790567 198589556648290239497685851)
      ·
        refine ⟨297884334972435359246528777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198589556648290239497685851 297884334972435359246528777)
        ·
          refine ⟨223413251229326519434896583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297884334972435359246528777 223413251229326519434896583)
          ·
            refine ⟨335119876843989779152344875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223413251229326519434896583 335119876843989779152344875)
            ·
              refine ⟨502679815265984668728517313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335119876843989779152344875 502679815265984668728517313)
              ·
                refine ⟨377009861449488501546387985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 502679815265984668728517313 377009861449488501546387985)
                ·
                  refine ⟨282757396087116376159790989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 377009861449488501546387985 282757396087116376159790989)
                  ·
                    refine ⟨106034023532668641059921621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 282757396087116376159790989 106034023532668641059921621)
                    ·
                      refine ⟨2485172426546921274841913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 106034023532668641059921621 2485172426546921274841913)
                      ·
                        rfl

theorem cell23_4839856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 7].length) (baseStart_4839856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839856 prefixEnd_4839856 := by exact prefixLift 4839856
  have htrace : WordTrace (prefixWord ++ tailWord_4839856) baseStart_4839856 baseEnd_4839856 := by
    simpa [prefixWord, tailWord_4839856, baseEnd_4839856] using wordTrace_append hprefix tailTrace_4839856
  have hstable : (prefixWord ++ tailWord_4839856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839856).length < 2 ^ (prefixWord ++ tailWord_4839856).sum := by decide
  have hdescent : baseEnd_4839856 < baseStart_4839856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839893 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 1, 8]
def baseStart_4839893 : Nat := 118140960795 + 4839893 * 2 ^ 59
def prefixEnd_4839893 : Nat := 4983230072969 + 3 ^ 40 * 4839893 * 2
def baseEnd_4839893 : Nat := 828397141777045876693081

theorem tailTrace_4839893 : CollatzResearch.WordTrace tailWord_4839893 prefixEnd_4839893 828397141777045876693081 := by
  unfold tailWord_4839893
  simp only [CollatzResearch.WordTrace]
  refine ⟨176525399854901723761484333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117683599903267815840989555 176525399854901723761484333)
  ·
    refine ⟨66197024945588146410556625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176525399854901723761484333 66197024945588146410556625)
    ·
      refine ⟨49647768709191109807917469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66197024945588146410556625 49647768709191109807917469)
      ·
        refine ⟨18617913265946666177969051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49647768709191109807917469 18617913265946666177969051)
        ·
          refine ⟨27926869898919999266953577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18617913265946666177969051 27926869898919999266953577)
          ·
            refine ⟨20945152424189999450215183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27926869898919999266953577 20945152424189999450215183)
            ·
              refine ⟨31417728636284999175322775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20945152424189999450215183 31417728636284999175322775)
              ·
                refine ⟨47126592954427498762984163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31417728636284999175322775 47126592954427498762984163)
                ·
                  refine ⟨70689889431641248144476245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47126592954427498762984163 70689889431641248144476245)
                  ·
                    refine ⟨828397141777045876693081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70689889431641248144476245 828397141777045876693081)
                    ·
                      rfl

theorem cell23_4839893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_4839893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839893 prefixEnd_4839893 := by exact prefixLift 4839893
  have htrace : WordTrace (prefixWord ++ tailWord_4839893) baseStart_4839893 baseEnd_4839893 := by
    simpa [prefixWord, tailWord_4839893, baseEnd_4839893] using wordTrace_append hprefix tailTrace_4839893
  have hstable : (prefixWord ++ tailWord_4839893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839893).length < 2 ^ (prefixWord ++ tailWord_4839893).sum := by decide
  have hdescent : baseEnd_4839893 < baseStart_4839893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839894 : List Nat := [5, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3]
def baseStart_4839894 : Nat := 118140960795 + 4839894 * 2 ^ 59
def prefixEnd_4839894 : Nat := 4983230072969 + 3 ^ 40 * 4839894 * 2
def baseEnd_4839894 : Nat := 2485191938811792126166739

theorem tailTrace_4839894 : CollatzResearch.WordTrace tailWord_4839894 prefixEnd_4839894 2485191938811792126166739 := by
  unfold tailWord_4839894
  simp only [CollatzResearch.WordTrace]
  refine ⟨11032839770493631308266921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117683624218598733954847157 11032839770493631308266921)
  ·
    refine ⟨8274629827870223481200191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11032839770493631308266921 8274629827870223481200191)
    ·
      refine ⟨12411944741805335221800287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8274629827870223481200191 12411944741805335221800287)
      ·
        refine ⟨18617917112708002832700431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12411944741805335221800287 18617917112708002832700431)
        ·
          refine ⟨27926875669062004249050647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18617917112708002832700431 27926875669062004249050647)
          ·
            refine ⟨41890313503593006373575971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27926875669062004249050647 41890313503593006373575971)
            ·
              refine ⟨62835470255389509560363957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41890313503593006373575971 62835470255389509560363957)
              ·
                refine ⟨5890825336442766521284121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62835470255389509560363957 5890825336442766521284121)
                ·
                  refine ⟨4418119002332074890963091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5890825336442766521284121 4418119002332074890963091)
                  ·
                    refine ⟨6627178503498112336444637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4418119002332074890963091 6627178503498112336444637)
                    ·
                      refine ⟨2485191938811792126166739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6627178503498112336444637 2485191938811792126166739)
                      ·
                        rfl

theorem cell23_4839894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_4839894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839894 prefixEnd_4839894 := by exact prefixLift 4839894
  have htrace : WordTrace (prefixWord ++ tailWord_4839894) baseStart_4839894 baseEnd_4839894 := by
    simpa [prefixWord, tailWord_4839894, baseEnd_4839894] using wordTrace_append hprefix tailTrace_4839894
  have hstable : (prefixWord ++ tailWord_4839894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839894).length < 2 ^ (prefixWord ++ tailWord_4839894).sum := by decide
  have hdescent : baseEnd_4839894 < baseStart_4839894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839940 : List Nat := [2, 3, 2, 3, 1, 1, 1, 3, 7]
def baseStart_4839940 : Nat := 118140960795 + 4839940 * 2 ^ 59
def prefixEnd_4839940 : Nat := 4983230072969 + 3 ^ 40 * 4839940 * 2
def baseEnd_4839940 : Nat := 276135062102433216243503

theorem tailTrace_4839940 : CollatzResearch.WordTrace tailWord_4839940 prefixEnd_4839940 276135062102433216243503 := by
  unfold tailWord_4839940
  simp only [CollatzResearch.WordTrace]
  refine ⟨88263557042865725394222637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117684742723820967192296849 88263557042865725394222637)
  ·
    refine ⟨33098833891074647022833489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88263557042865725394222637 33098833891074647022833489)
    ·
      refine ⟨24824125418305985267125117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33098833891074647022833489 24824125418305985267125117)
      ·
        refine ⟨9309047031864744475171919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24824125418305985267125117 9309047031864744475171919)
        ·
          refine ⟨13963570547797116712757879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9309047031864744475171919 13963570547797116712757879)
          ·
            refine ⟨20945355821695675069136819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13963570547797116712757879 20945355821695675069136819)
            ·
              refine ⟨31418033732543512603705229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20945355821695675069136819 31418033732543512603705229)
              ·
                refine ⟨11781762649703817226389461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31418033732543512603705229 11781762649703817226389461)
                ·
                  refine ⟨276135062102433216243503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11781762649703817226389461 276135062102433216243503)
                  ·
                    rfl

theorem cell23_4839940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 7].length) (baseStart_4839940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839940 prefixEnd_4839940 := by exact prefixLift 4839940
  have htrace : WordTrace (prefixWord ++ tailWord_4839940) baseStart_4839940 baseEnd_4839940 := by
    simpa [prefixWord, tailWord_4839940, baseEnd_4839940] using wordTrace_append hprefix tailTrace_4839940
  have hstable : (prefixWord ++ tailWord_4839940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839940).length < 2 ^ (prefixWord ++ tailWord_4839940).sum := by decide
  have hdescent : baseEnd_4839940 < baseStart_4839940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839953 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 6, 5]
def baseStart_4839953 : Nat := 118140960795 + 4839953 * 2 ^ 59
def prefixEnd_4839953 : Nat := 4983230072969 + 3 ^ 40 * 4839953 * 2
def baseEnd_4839953 : Nat := 828407411390135798442989

theorem tailTrace_4839953 : CollatzResearch.WordTrace tailWord_4839953 prefixEnd_4839953 828407411390135798442989 := by
  unfold tailWord_4839953
  simp only [CollatzResearch.WordTrace]
  refine ⟨176527588234684354008668513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117685058823122902672445675 176527588234684354008668513)
  ·
    refine ⟨132395691176013265506501385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176527588234684354008668513 132395691176013265506501385)
    ·
      refine ⟨99296768382009949129876039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132395691176013265506501385 99296768382009949129876039)
      ·
        refine ⟨148945152573014923694814059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99296768382009949129876039 148945152573014923694814059)
        ·
          refine ⟨223417728859522385542221089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148945152573014923694814059 223417728859522385542221089)
          ·
            refine ⟨167563296644641789156665817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223417728859522385542221089 167563296644641789156665817)
            ·
              refine ⟨125672472483481341867499363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167563296644641789156665817 125672472483481341867499363)
              ·
                refine ⟨188508708725222012801249045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125672472483481341867499363 188508708725222012801249045)
                ·
                  refine ⟨8836345721494781850058549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 188508708725222012801249045 8836345721494781850058549)
                  ·
                    refine ⟨828407411390135798442989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8836345721494781850058549 828407411390135798442989)
                    ·
                      rfl

theorem cell23_4839953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 5].length) (baseStart_4839953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839953 prefixEnd_4839953 := by exact prefixLift 4839953
  have htrace : WordTrace (prefixWord ++ tailWord_4839953) baseStart_4839953 baseEnd_4839953 := by
    simpa [prefixWord, tailWord_4839953, baseEnd_4839953] using wordTrace_append hprefix tailTrace_4839953
  have hstable : (prefixWord ++ tailWord_4839953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839953).length < 2 ^ (prefixWord ++ tailWord_4839953).sum := by decide
  have hdescent : baseEnd_4839953 < baseStart_4839953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4839970 : List Nat := [3, 3, 1, 1, 1, 1, 1, 5, 2, 5]
def baseStart_4839970 : Nat := 118140960795 + 4839970 * 2 ^ 59
def prefixEnd_4839970 : Nat := 4983230072969 + 3 ^ 40 * 4839970 * 2
def baseEnd_4839970 : Nat := 828410321113844609605463

theorem tailTrace_4839970 : CollatzResearch.WordTrace tailWord_4839970 prefixEnd_4839970 828410321113844609605463 := by
  unfold tailWord_4839970
  simp only [CollatzResearch.WordTrace]
  refine ⟨44132052068905691478009341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117685472183748510608024909 44132052068905691478009341)
  ·
    refine ⟨16549519525839634304253503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44132052068905691478009341 16549519525839634304253503)
    ·
      refine ⟨24824279288759451456380255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16549519525839634304253503 24824279288759451456380255)
      ·
        refine ⟨37236418933139177184570383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24824279288759451456380255 37236418933139177184570383)
        ·
          refine ⟨55854628399708765776855575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37236418933139177184570383 55854628399708765776855575)
          ·
            refine ⟨83781942599563148665283363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55854628399708765776855575 83781942599563148665283363)
            ·
              refine ⟨125672913899344722997925045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83781942599563148665283363 125672913899344722997925045)
              ·
                refine ⟨11781835678063567781055473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 125672913899344722997925045 11781835678063567781055473)
                ·
                  refine ⟨8836376758547675835791605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11781835678063567781055473 8836376758547675835791605)
                  ·
                    refine ⟨828410321113844609605463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8836376758547675835791605 828410321113844609605463)
                    ·
                      rfl

theorem cell23_4839970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_4839970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4839970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4839970 prefixEnd_4839970 := by exact prefixLift 4839970
  have htrace : WordTrace (prefixWord ++ tailWord_4839970) baseStart_4839970 baseEnd_4839970 := by
    simpa [prefixWord, tailWord_4839970, baseEnd_4839970] using wordTrace_append hprefix tailTrace_4839970
  have hstable : (prefixWord ++ tailWord_4839970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4839970).length < 2 ^ (prefixWord ++ tailWord_4839970).sum := by decide
  have hdescent : baseEnd_4839970 < baseStart_4839970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4839970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840003 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 6]
def baseStart_4840003 : Nat := 118140960795 + 4840003 * 2 ^ 59
def prefixEnd_4840003 : Nat := 4983230072969 + 3 ^ 40 * 4840003 * 2
def baseEnd_4840003 : Nat := 2485247908203132199703737

theorem tailTrace_4840003 : CollatzResearch.WordTrace tailWord_4840003 prefixEnd_4840003 2485247908203132199703737 := by
  unfold tailWord_4840003
  simp only [CollatzResearch.WordTrace]
  refine ⟨176529411884503212547988663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117686274589668808365325775 176529411884503212547988663)
  ·
    refine ⟨264794117826754818821982995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176529411884503212547988663 264794117826754818821982995)
    ·
      refine ⟨397191176740132228232974493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264794117826754818821982995 397191176740132228232974493)
      ·
        refine ⟨148946691277549585587365435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 397191176740132228232974493 148946691277549585587365435)
        ·
          refine ⟨223420036916324378381048153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148946691277549585587365435 223420036916324378381048153)
          ·
            refine ⟨167565027687243283785786115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223420036916324378381048153 167565027687243283785786115)
            ·
              refine ⟨251347541530864925678679173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167565027687243283785786115 251347541530864925678679173)
              ·
                refine ⟨47127664037037173564752345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 251347541530864925678679173 47127664037037173564752345)
                ·
                  refine ⟨35345748027777880173564259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47127664037037173564752345 35345748027777880173564259)
                  ·
                    refine ⟨53018622041666820260346389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35345748027777880173564259 53018622041666820260346389)
                    ·
                      refine ⟨2485247908203132199703737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53018622041666820260346389 2485247908203132199703737)
                      ·
                        rfl

theorem cell23_4840003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_4840003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840003 prefixEnd_4840003 := by exact prefixLift 4840003
  have htrace : WordTrace (prefixWord ++ tailWord_4840003) baseStart_4840003 baseEnd_4840003 := by
    simpa [prefixWord, tailWord_4840003, baseEnd_4840003] using wordTrace_append hprefix tailTrace_4840003
  have hstable : (prefixWord ++ tailWord_4840003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840003).length < 2 ^ (prefixWord ++ tailWord_4840003).sum := by decide
  have hdescent : baseEnd_4840003 < baseStart_4840003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840060 : List Nat := [2, 2, 2, 1, 1, 2, 3, 2, 3, 5]
def baseStart_4840060 : Nat := 118140960795 + 4840060 * 2 ^ 59
def prefixEnd_4840060 : Nat := 4983230072969 + 3 ^ 40 * 4840060 * 2
def baseEnd_4840060 : Nat := 828425725533479492230325

theorem tailTrace_4840060 : CollatzResearch.WordTrace tailWord_4840060 prefixEnd_4840060 828425725533479492230325 := by
  unfold tailWord_4840060
  simp only [CollatzResearch.WordTrace]
  refine ⟨88265745422648355641406817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117687660563531140855209089 88265745422648355641406817)
  ·
    refine ⟨66199309066986266731055113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88265745422648355641406817 66199309066986266731055113)
    ·
      refine ⟨49649481800239700048291335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66199309066986266731055113 49649481800239700048291335)
      ·
        refine ⟨74474222700359550072437003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49649481800239700048291335 74474222700359550072437003)
        ·
          refine ⟨111711334050539325108655505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74474222700359550072437003 111711334050539325108655505)
          ·
            refine ⟨83783500537904493831491629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111711334050539325108655505 83783500537904493831491629)
            ·
              refine ⟨31418812701714185186809361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83783500537904493831491629 31418812701714185186809361)
              ·
                refine ⟨23564109526285638890107021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31418812701714185186809361 23564109526285638890107021)
                ·
                  refine ⟨8836541072357114583790133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23564109526285638890107021 8836541072357114583790133)
                  ·
                    refine ⟨828425725533479492230325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8836541072357114583790133 828425725533479492230325)
                    ·
                      rfl

theorem cell23_4840060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_4840060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840060 prefixEnd_4840060 := by exact prefixLift 4840060
  have htrace : WordTrace (prefixWord ++ tailWord_4840060) baseStart_4840060 baseEnd_4840060 := by
    simpa [prefixWord, tailWord_4840060, baseEnd_4840060] using wordTrace_append hprefix tailTrace_4840060
  have hstable : (prefixWord ++ tailWord_4840060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840060).length < 2 ^ (prefixWord ++ tailWord_4840060).sum := by decide
  have hdescent : baseEnd_4840060 < baseStart_4840060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840067 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 4, 3, 2]
def baseStart_4840067 : Nat := 118140960795 + 4840067 * 2 ^ 59
def prefixEnd_4840067 : Nat := 4983230072969 + 3 ^ 40 * 4840067 * 2
def baseEnd_4840067 : Nat := 2485280770965019949303443

theorem tailTrace_4840067 : CollatzResearch.WordTrace tailWord_4840067 prefixEnd_4840067 2485280770965019949303443 := by
  unfold tailWord_4840067
  simp only [CollatzResearch.WordTrace]
  refine ⟨176531746156271351478318455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117687830770847567652212303 176531746156271351478318455)
  ·
    refine ⟨264797619234407027217477683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176531746156271351478318455 264797619234407027217477683)
    ·
      refine ⟨397196428851610540826216525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264797619234407027217477683 397196428851610540826216525)
      ·
        refine ⟨148948660819353952809831197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 397196428851610540826216525 148948660819353952809831197)
        ·
          refine ⟨55855747807257732303686699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148948660819353952809831197 55855747807257732303686699)
          ·
            refine ⟨83783621710886598455530049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55855747807257732303686699 83783621710886598455530049)
            ·
              refine ⟨62837716283164948841647537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83783621710886598455530049 62837716283164948841647537)
              ·
                refine ⟨47128287212373711631235653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62837716283164948841647537 47128287212373711631235653)
                ·
                  refine ⟨8836553852320070930856685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47128287212373711631235653 8836553852320070930856685)
                  ·
                    refine ⟨3313707694620026599071257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8836553852320070930856685 3313707694620026599071257)
                    ·
                      refine ⟨2485280770965019949303443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3313707694620026599071257 2485280770965019949303443)
                      ·
                        rfl

theorem cell23_4840067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 3, 2].length) (baseStart_4840067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840067 prefixEnd_4840067 := by exact prefixLift 4840067
  have htrace : WordTrace (prefixWord ++ tailWord_4840067) baseStart_4840067 baseEnd_4840067 := by
    simpa [prefixWord, tailWord_4840067, baseEnd_4840067] using wordTrace_append hprefix tailTrace_4840067
  have hstable : (prefixWord ++ tailWord_4840067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840067).length < 2 ^ (prefixWord ++ tailWord_4840067).sum := by decide
  have hdescent : baseEnd_4840067 < baseStart_4840067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840094 : List Nat := [4, 3, 1, 1, 1, 1, 3, 3, 1, 5]
def baseStart_4840094 : Nat := 118140960795 + 4840094 * 2 ^ 59
def prefixEnd_4840094 : Nat := 4983230072969 + 3 ^ 40 * 4840094 * 2
def baseEnd_4840094 : Nat := 828431544980897114555273

theorem tailTrace_4840094 : CollatzResearch.WordTrace tailWord_4840094 prefixEnd_4840094 828431544980897114555273 := by
  unfold tailWord_4840094
  simp only [CollatzResearch.WordTrace]
  refine ⟨22066591365896691886193917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117688487284782356726367557 22066591365896691886193917)
  ·
    refine ⟨8274971762211259457322719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22066591365896691886193917 8274971762211259457322719)
    ·
      refine ⟨12412457643316889185984079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8274971762211259457322719 12412457643316889185984079)
      ·
        refine ⟨18618686464975333778976119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12412457643316889185984079 18618686464975333778976119)
        ·
          refine ⟨27928029697463000668464179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18618686464975333778976119 27928029697463000668464179)
          ·
            refine ⟨41892044546194501002696269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27928029697463000668464179 41892044546194501002696269)
            ·
              refine ⟨15709516704822937876011101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41892044546194501002696269 15709516704822937876011101)
              ·
                refine ⟨5891068764308601703504163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15709516704822937876011101 5891068764308601703504163)
                ·
                  refine ⟨8836603146462902555256245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5891068764308601703504163 8836603146462902555256245)
                  ·
                    refine ⟨828431544980897114555273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8836603146462902555256245 828431544980897114555273)
                    ·
                      rfl

theorem cell23_4840094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_4840094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840094 prefixEnd_4840094 := by exact prefixLift 4840094
  have htrace : WordTrace (prefixWord ++ tailWord_4840094) baseStart_4840094 baseEnd_4840094 := by
    simpa [prefixWord, tailWord_4840094, baseEnd_4840094] using wordTrace_append hprefix tailTrace_4840094
  have hstable : (prefixWord ++ tailWord_4840094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840094).length < 2 ^ (prefixWord ++ tailWord_4840094).sum := by decide
  have hdescent : baseEnd_4840094 < baseStart_4840094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840117 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 3, 1, 5]
def baseStart_4840117 : Nat := 118140960795 + 4840117 * 2 ^ 59
def prefixEnd_4840117 : Nat := 4983230072969 + 3 ^ 40 * 4840117 * 2
def baseEnd_4840117 : Nat := 2485306444997744753678213

theorem tailTrace_4840117 : CollatzResearch.WordTrace tailWord_4840117 prefixEnd_4840117 2485306444997744753678213 := by
  unfold tailWord_4840117
  simp only [CollatzResearch.WordTrace]
  refine ⟨176533569806090210017638605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117689046537393473345092403 176533569806090210017638605)
  ·
    refine ⟨66200088677283828756614477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176533569806090210017638605 66200088677283828756614477)
    ·
      refine ⟨24825033253981435783730429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66200088677283828756614477 24825033253981435783730429)
      ·
        refine ⟨9309387470243038418898911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24825033253981435783730429 9309387470243038418898911)
        ·
          refine ⟨13964081205364557628348367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9309387470243038418898911 13964081205364557628348367)
          ·
            refine ⟨20946121808046836442522551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13964081205364557628348367 20946121808046836442522551)
            ·
              refine ⟨31419182712070254663783827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20946121808046836442522551 31419182712070254663783827)
              ·
                refine ⟨47128774068105381995675741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31419182712070254663783827 47128774068105381995675741)
                ·
                  refine ⟨17673290275539518248378403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47128774068105381995675741 17673290275539518248378403)
                  ·
                    refine ⟨26509935413309277372567605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17673290275539518248378403 26509935413309277372567605)
                    ·
                      refine ⟨2485306444997744753678213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26509935413309277372567605 2485306444997744753678213)
                      ·
                        rfl

theorem cell23_4840117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_4840117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840117 prefixEnd_4840117 := by exact prefixLift 4840117
  have htrace : WordTrace (prefixWord ++ tailWord_4840117) baseStart_4840117 baseEnd_4840117 := by
    simpa [prefixWord, tailWord_4840117, baseEnd_4840117] using wordTrace_append hprefix tailTrace_4840117
  have hstable : (prefixWord ++ tailWord_4840117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840117).length < 2 ^ (prefixWord ++ tailWord_4840117).sum := by decide
  have hdescent : baseEnd_4840117 < baseStart_4840117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840127 : List Nat := [1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 4]
def baseStart_4840127 : Nat := 118140960795 + 4840127 * 2 ^ 59
def prefixEnd_4840127 : Nat := 4983230072969 + 3 ^ 40 * 4840127 * 2
def baseEnd_4840127 : Nat := 2485311579804289714553167

theorem tailTrace_4840127 : CollatzResearch.WordTrace tailWord_4840127 prefixEnd_4840127 2485311579804289714553167 := by
  unfold tailWord_4840127
  simp only [CollatzResearch.WordTrace]
  refine ⟨176533934536053981725502635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117689289690702654483668423 176533934536053981725502635)
  ·
    refine ⟨264800901804080972588253953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176533934536053981725502635 264800901804080972588253953)
    ·
      refine ⟨198600676353060729441190465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264800901804080972588253953 198600676353060729441190465)
      ·
        refine ⟨148950507264795547080892849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198600676353060729441190465 148950507264795547080892849)
        ·
          refine ⟨111712880448596660310669637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148950507264795547080892849 111712880448596660310669637)
          ·
            refine ⟨20946165084111873808250557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111712880448596660310669637 20946165084111873808250557)
            ·
              refine ⟨7854811906541952678093959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20946165084111873808250557 7854811906541952678093959)
              ·
                refine ⟨11782217859812929017140939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7854811906541952678093959 11782217859812929017140939)
                ·
                  refine ⟨17673326789719393525711409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11782217859812929017140939 17673326789719393525711409)
                  ·
                    refine ⟨13254995092289545144283557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17673326789719393525711409 13254995092289545144283557)
                    ·
                      refine ⟨2485311579804289714553167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13254995092289545144283557 2485311579804289714553167)
                      ·
                        rfl

theorem cell23_4840127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 2, 4].length) (baseStart_4840127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840127 prefixEnd_4840127 := by exact prefixLift 4840127
  have htrace : WordTrace (prefixWord ++ tailWord_4840127) baseStart_4840127 baseEnd_4840127 := by
    simpa [prefixWord, tailWord_4840127, baseEnd_4840127] using wordTrace_append hprefix tailTrace_4840127
  have hstable : (prefixWord ++ tailWord_4840127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840127).length < 2 ^ (prefixWord ++ tailWord_4840127).sum := by decide
  have hdescent : baseEnd_4840127 < baseStart_4840127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840160 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 5]
def baseStart_4840160 : Nat := 118140960795 + 4840160 * 2 ^ 59
def prefixEnd_4840160 : Nat := 4983230072969 + 3 ^ 40 * 4840160 * 2
def baseEnd_4840160 : Nat := 2485328524665888085440515

theorem tailTrace_4840160 : CollatzResearch.WordTrace tailWord_4840160 prefixEnd_4840160 2485328524665888085440515 := by
  unfold tailWord_4840160
  simp only [CollatzResearch.WordTrace]
  refine ⟨88267569072467214180726967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117690092096622952240969289 88267569072467214180726967)
  ·
    refine ⟨132401353608700821271090451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88267569072467214180726967 132401353608700821271090451)
    ·
      refine ⟨198602030413051231906635677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132401353608700821271090451 198602030413051231906635677)
      ·
        refine ⟨74475761404894211964988379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198602030413051231906635677 74475761404894211964988379)
        ·
          refine ⟨111713642107341317947482569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74475761404894211964988379 111713642107341317947482569)
          ·
            refine ⟨83785231580505988460611927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111713642107341317947482569 83785231580505988460611927)
            ·
              refine ⟨125677847370758982690917891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83785231580505988460611927 125677847370758982690917891)
              ·
                refine ⟨188516771056138474036376837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125677847370758982690917891 188516771056138474036376837)
                ·
                  refine ⟨35346894573025963881820657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 188516771056138474036376837 35346894573025963881820657)
                  ·
                    refine ⟨26510170929769472911365493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35346894573025963881820657 26510170929769472911365493)
                    ·
                      refine ⟨2485328524665888085440515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26510170929769472911365493 2485328524665888085440515)
                      ·
                        rfl

theorem cell23_4840160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_4840160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840160 prefixEnd_4840160 := by exact prefixLift 4840160
  have htrace : WordTrace (prefixWord ++ tailWord_4840160) baseStart_4840160 baseEnd_4840160 := by
    simpa [prefixWord, tailWord_4840160, baseEnd_4840160] using wordTrace_append hprefix tailTrace_4840160
  have hstable : (prefixWord ++ tailWord_4840160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840160).length < 2 ^ (prefixWord ++ tailWord_4840160).sum := by decide
  have hdescent : baseEnd_4840160 < baseStart_4840160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840164 : List Nat := [2, 3, 1, 1, 1, 4, 2, 1, 4, 1, 3]
def baseStart_4840164 : Nat := 118140960795 + 4840164 * 2 ^ 59
def prefixEnd_4840164 : Nat := 4983230072969 + 3 ^ 40 * 4840164 * 2
def baseEnd_4840164 : Nat := 2485330578588506069790497

theorem tailTrace_4840164 : CollatzResearch.WordTrace tailWord_4840164 prefixEnd_4840164 2485330578588506069790497 := by
  unfold tailWord_4840164
  simp only [CollatzResearch.WordTrace]
  refine ⟨88267642018459968522299773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117690189357946624696399697 88267642018459968522299773)
  ·
    refine ⟨33100365756922488195862415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88267642018459968522299773 33100365756922488195862415)
    ·
      refine ⟨49650548635383732293793623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33100365756922488195862415 49650548635383732293793623)
      ·
        refine ⟨74475822953075598440690435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49650548635383732293793623 74475822953075598440690435)
        ·
          refine ⟨111713734429613397661035653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74475822953075598440690435 111713734429613397661035653)
          ·
            refine ⟨20946325205552512061444185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111713734429613397661035653 20946325205552512061444185)
            ·
              refine ⟨15709743904164384046083139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20946325205552512061444185 15709743904164384046083139)
              ·
                refine ⟨23564615856246576069124709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15709743904164384046083139 23564615856246576069124709)
                ·
                  refine ⟨4418365473046233012960883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23564615856246576069124709 4418365473046233012960883)
                  ·
                    refine ⟨6627548209569349519441325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4418365473046233012960883 6627548209569349519441325)
                    ·
                      refine ⟨2485330578588506069790497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6627548209569349519441325 2485330578588506069790497)
                      ·
                        rfl

theorem cell23_4840164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 4, 1, 3].length) (baseStart_4840164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840164 prefixEnd_4840164 := by exact prefixLift 4840164
  have htrace : WordTrace (prefixWord ++ tailWord_4840164) baseStart_4840164 baseEnd_4840164 := by
    simpa [prefixWord, tailWord_4840164, baseEnd_4840164] using wordTrace_append hprefix tailTrace_4840164
  have hstable : (prefixWord ++ tailWord_4840164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840164).length < 2 ^ (prefixWord ++ tailWord_4840164).sum := by decide
  have hdescent : baseEnd_4840164 < baseStart_4840164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840165 : List Nat := [1, 3, 1, 4, 1, 3, 3, 2, 1, 2, 2]
def baseStart_4840165 : Nat := 118140960795 + 4840165 * 2 ^ 59
def prefixEnd_4840165 : Nat := 4983230072969 + 3 ^ 40 * 4840165 * 2
def baseEnd_4840165 : Nat := 2485331092069160565877993

theorem tailTrace_4840165 : CollatzResearch.WordTrace tailWord_4840165 prefixEnd_4840165 2485331092069160565877993 := by
  unfold tailWord_4840165
  simp only [CollatzResearch.WordTrace]
  refine ⟨176535320509916314215385949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117690213673277542810257299 176535320509916314215385949)
  ·
    refine ⟨66200745191218617830769731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176535320509916314215385949 66200745191218617830769731)
    ·
      refine ⟨99301117786827926746154597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66200745191218617830769731 99301117786827926746154597)
      ·
        refine ⟨18618959585030236264903987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99301117786827926746154597 18618959585030236264903987)
        ·
          refine ⟨27928439377545354397355981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18618959585030236264903987 27928439377545354397355981)
          ·
            refine ⟨10473164766579507899008493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27928439377545354397355981 10473164766579507899008493)
            ·
              refine ⟨3927436787467315462128185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10473164766579507899008493 3927436787467315462128185)
              ·
                refine ⟨2945577590600486596596139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3927436787467315462128185 2945577590600486596596139)
                ·
                  refine ⟨4418366385900729894894209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2945577590600486596596139 4418366385900729894894209)
                  ·
                    refine ⟨3313774789425547421170657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4418366385900729894894209 3313774789425547421170657)
                    ·
                      refine ⟨2485331092069160565877993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3313774789425547421170657 2485331092069160565877993)
                      ·
                        rfl

theorem cell23_4840165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_4840165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840165 prefixEnd_4840165 := by exact prefixLift 4840165
  have htrace : WordTrace (prefixWord ++ tailWord_4840165) baseStart_4840165 baseEnd_4840165 := by
    simpa [prefixWord, tailWord_4840165, baseEnd_4840165] using wordTrace_append hprefix tailTrace_4840165
  have hstable : (prefixWord ++ tailWord_4840165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840165).length < 2 ^ (prefixWord ++ tailWord_4840165).sum := by decide
  have hdescent : baseEnd_4840165 < baseStart_4840165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840238 : List Nat := [4, 1, 3, 2, 1, 2, 2, 1, 1, 4, 2]
def baseStart_4840238 : Nat := 118140960795 + 4840238 * 2 ^ 59
def prefixEnd_4840238 : Nat := 4983230072969 + 3 ^ 40 * 4840238 * 2
def baseEnd_4840238 : Nat := 2485368576156938780265157

theorem tailTrace_4840238 : CollatzResearch.WordTrace tailWord_4840238 prefixEnd_4840238 2485368576156938780265157 := by
  unfold tailWord_4840238
  simp only [CollatzResearch.WordTrace]
  refine ⟨22067247879831480960349171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117691988692434565121862245 22067247879831480960349171)
  ·
    refine ⟨33100871819747221440523757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22067247879831480960349171 33100871819747221440523757)
    ·
      refine ⟨12412826932405208040196409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33100871819747221440523757 12412826932405208040196409)
      ·
        refine ⟨9309620199303906030147307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12412826932405208040196409 9309620199303906030147307)
        ·
          refine ⟨13964430298955859045220961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9309620199303906030147307 13964430298955859045220961)
          ·
            refine ⟨10473322724216894283915721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13964430298955859045220961 10473322724216894283915721)
            ·
              refine ⟨7854992043162670712936791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10473322724216894283915721 7854992043162670712936791)
              ·
                refine ⟨11782488064744006069405187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7854992043162670712936791 11782488064744006069405187)
                ·
                  refine ⟨17673732097116009104107781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11782488064744006069405187 17673732097116009104107781)
                  ·
                    refine ⟨3313824768209251707020209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17673732097116009104107781 3313824768209251707020209)
                    ·
                      refine ⟨2485368576156938780265157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3313824768209251707020209 2485368576156938780265157)
                      ·
                        rfl

theorem cell23_4840238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_4840238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840238 prefixEnd_4840238 := by exact prefixLift 4840238
  have htrace : WordTrace (prefixWord ++ tailWord_4840238) baseStart_4840238 baseEnd_4840238 := by
    simpa [prefixWord, tailWord_4840238, baseEnd_4840238] using wordTrace_append hprefix tailTrace_4840238
  have hstable : (prefixWord ++ tailWord_4840238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840238).length < 2 ^ (prefixWord ++ tailWord_4840238).sum := by decide
  have hdescent : baseEnd_4840238 < baseStart_4840238 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840304 : List Nat := [2, 1, 1, 1, 4, 1, 4, 2, 3, 4]
def baseStart_4840304 : Nat := 118140960795 + 4840304 * 2 ^ 59
def prefixEnd_4840304 : Nat := 4983230072969 + 3 ^ 40 * 4840304 * 2
def baseEnd_4840304 : Nat := 828467488626711840679951

theorem tailTrace_4840304 : CollatzResearch.WordTrace tailWord_4840304 prefixEnd_4840304 828467488626711840679951 := by
  unfold tailWord_4840304
  simp only [CollatzResearch.WordTrace]
  refine ⟨88270195128206370477347983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117693593504275160636463977 88270195128206370477347983)
  ·
    refine ⟨132405292692309555716021975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88270195128206370477347983 132405292692309555716021975)
    ·
      refine ⟨198607939038464333574032963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132405292692309555716021975 198607939038464333574032963)
      ·
        refine ⟨297911908557696500361049445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198607939038464333574032963 297911908557696500361049445)
        ·
          refine ⟨55858482854568093817696771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 297911908557696500361049445 55858482854568093817696771)
          ·
            refine ⟨83787724281852140726545157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55858482854568093817696771 83787724281852140726545157)
            ·
              refine ⟨15710198302847276386227217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83787724281852140726545157 15710198302847276386227217)
              ·
                refine ⟨11782648727135457289670413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15710198302847276386227217 11782648727135457289670413)
                ·
                  refine ⟨4418493272675796483626405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11782648727135457289670413 4418493272675796483626405)
                  ·
                    refine ⟨828467488626711840679951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4418493272675796483626405 828467488626711840679951)
                    ·
                      rfl

theorem cell23_4840304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 3, 4].length) (baseStart_4840304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840304 prefixEnd_4840304 := by exact prefixLift 4840304
  have htrace : WordTrace (prefixWord ++ tailWord_4840304) baseStart_4840304 baseEnd_4840304 := by
    simpa [prefixWord, tailWord_4840304, baseEnd_4840304] using wordTrace_append hprefix tailTrace_4840304
  have hstable : (prefixWord ++ tailWord_4840304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840304).length < 2 ^ (prefixWord ++ tailWord_4840304).sum := by decide
  have hdescent : baseEnd_4840304 < baseStart_4840304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840314 : List Nat := [3, 1, 1, 1, 1, 1, 3, 5, 2, 2, 3]
def baseStart_4840314 : Nat := 118140960795 + 4840314 * 2 ^ 59
def prefixEnd_4840314 : Nat := 4983230072969 + 3 ^ 40 * 4840314 * 2
def baseEnd_4840314 : Nat := 2485407600686680482914807

theorem tailTrace_4840314 : CollatzResearch.WordTrace tailWord_4840314 prefixEnd_4840314 2485407600686680482914807 := by
  unfold tailWord_4840314
  simp only [CollatzResearch.WordTrace]
  refine ⟨44135188746594128165639999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117693836657584341775039997 44135188746594128165639999)
  ·
    refine ⟨66202783119891192248459999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44135188746594128165639999 66202783119891192248459999)
    ·
      refine ⟨99304174679836788372689999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66202783119891192248459999 99304174679836788372689999)
      ·
        refine ⟨148956262019755182559034999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99304174679836788372689999 148956262019755182559034999)
        ·
          refine ⟨223434393029632773838552499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148956262019755182559034999 223434393029632773838552499)
          ·
            refine ⟨335151589544449160757828749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223434393029632773838552499 335151589544449160757828749)
            ·
              refine ⟨125681846079168435284185781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 335151589544449160757828749 125681846079168435284185781)
              ·
                refine ⟨11782673069922040807892417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 125681846079168435284185781 11782673069922040807892417)
                ·
                  refine ⟨8837004802441530605919313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11782673069922040807892417 8837004802441530605919313)
                  ·
                    refine ⟨6627753601831147954439485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8837004802441530605919313 6627753601831147954439485)
                    ·
                      refine ⟨2485407600686680482914807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6627753601831147954439485 2485407600686680482914807)
                      ·
                        rfl

theorem cell23_4840314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 2, 2, 3].length) (baseStart_4840314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840314 prefixEnd_4840314 := by exact prefixLift 4840314
  have htrace : WordTrace (prefixWord ++ tailWord_4840314) baseStart_4840314 baseEnd_4840314 := by
    simpa [prefixWord, tailWord_4840314, baseEnd_4840314] using wordTrace_append hprefix tailTrace_4840314
  have hstable : (prefixWord ++ tailWord_4840314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840314).length < 2 ^ (prefixWord ++ tailWord_4840314).sum := by decide
  have hdescent : baseEnd_4840314 < baseStart_4840314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840317 : List Nat := [1, 4, 1, 1, 2, 1, 3, 2, 8]
def baseStart_4840317 : Nat := 118140960795 + 4840317 * 2 ^ 59
def prefixEnd_4840317 : Nat := 4983230072969 + 3 ^ 40 * 4840317 * 2
def baseEnd_4840317 : Nat := 276156571236515996797477

theorem tailTrace_4840317 : CollatzResearch.WordTrace tailWord_4840317 prefixEnd_4840317 276156571236515996797477 := by
  unfold tailWord_4840317
  simp only [CollatzResearch.WordTrace]
  refine ⟨176540864405365644174919205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117693909603577096116612803 176540864405365644174919205)
  ·
    refine ⟨33101412076006058282797351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176540864405365644174919205 33101412076006058282797351)
    ·
      refine ⟨49652118114009087424196027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33101412076006058282797351 49652118114009087424196027)
      ·
        refine ⟨74478177171013631136294041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49652118114009087424196027 74478177171013631136294041)
        ·
          refine ⟨55858632878260223352220531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74478177171013631136294041 55858632878260223352220531)
          ·
            refine ⟨83787949317390335028330797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55858632878260223352220531 83787949317390335028330797)
            ·
              refine ⟨31420480994021375635624049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83787949317390335028330797 31420480994021375635624049)
              ·
                refine ⟨23565360745516031726718037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31420480994021375635624049 23565360745516031726718037)
                ·
                  refine ⟨276156571236515996797477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23565360745516031726718037 276156571236515996797477)
                  ·
                    rfl

theorem cell23_4840317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 8].length) (baseStart_4840317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840317 prefixEnd_4840317 := by exact prefixLift 4840317
  have htrace : WordTrace (prefixWord ++ tailWord_4840317) baseStart_4840317 baseEnd_4840317 := by
    simpa [prefixWord, tailWord_4840317, baseEnd_4840317] using wordTrace_append hprefix tailTrace_4840317
  have hstable : (prefixWord ++ tailWord_4840317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840317).length < 2 ^ (prefixWord ++ tailWord_4840317).sum := by decide
  have hdescent : baseEnd_4840317 < baseStart_4840317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840351 : List Nat := [1, 1, 2, 5, 2, 1, 4, 1, 6]
def baseStart_4840351 : Nat := 118140960795 + 4840351 * 2 ^ 59
def prefixEnd_4840351 : Nat := 4983230072969 + 3 ^ 40 * 4840351 * 2
def baseEnd_4840351 : Nat := 276158511052321870905793

theorem tailTrace_4840351 : CollatzResearch.WordTrace tailWord_4840351 prefixEnd_4840351 276158511052321870905793 := by
  unfold tailWord_4840351
  simp only [CollatzResearch.WordTrace]
  refine ⟨176542104487242467981656907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117694736324828311987771271 176542104487242467981656907)
  ·
    refine ⟨264813156730863701972485361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176542104487242467981656907 264813156730863701972485361)
    ·
      refine ⟨198609867548147776479364021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264813156730863701972485361 198609867548147776479364021)
      ·
        refine ⟨18619675082638854044940377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 198609867548147776479364021 18619675082638854044940377)
        ·
          refine ⟨13964756311979140533705283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18619675082638854044940377 13964756311979140533705283)
          ·
            refine ⟨20947134467968710800557925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13964756311979140533705283 20947134467968710800557925)
            ·
              refine ⟨3927587712744133275104611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20947134467968710800557925 3927587712744133275104611)
              ·
                refine ⟨5891381569116199912656917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3927587712744133275104611 5891381569116199912656917)
                ·
                  refine ⟨276158511052321870905793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5891381569116199912656917 276158511052321870905793)
                  ·
                    rfl

theorem cell23_4840351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 6].length) (baseStart_4840351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840351 prefixEnd_4840351 := by exact prefixLift 4840351
  have htrace : WordTrace (prefixWord ++ tailWord_4840351) baseStart_4840351 baseEnd_4840351 := by
    simpa [prefixWord, tailWord_4840351, baseEnd_4840351] using wordTrace_append hprefix tailTrace_4840351
  have hstable : (prefixWord ++ tailWord_4840351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840351).length < 2 ^ (prefixWord ++ tailWord_4840351).sum := by decide
  have hdescent : baseEnd_4840351 < baseStart_4840351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840365 : List Nat := [1, 5, 2, 3, 1, 1, 2, 1, 2, 2, 3]
def baseStart_4840365 : Nat := 118140960795 + 4840365 * 2 ^ 59
def prefixEnd_4840365 : Nat := 4983230072969 + 3 ^ 40 * 4840365 * 2
def baseEnd_4840365 : Nat := 2485433788200059783377073

theorem tailTrace_4840365 : CollatzResearch.WordTrace tailWord_4840365 prefixEnd_4840365 2485433788200059783377073 := by
  unfold tailWord_4840365
  simp only [CollatzResearch.WordTrace]
  refine ⟨176542615109191748372666549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117695076739461165581777699 176542615109191748372666549)
  ·
    refine ⟨16550870166486726409937489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 176542615109191748372666549 16550870166486726409937489)
    ·
      refine ⟨12413152624865044807453117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16550870166486726409937489 12413152624865044807453117)
      ·
        refine ⟨4654932234324391802794919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12413152624865044807453117 4654932234324391802794919)
        ·
          refine ⟨6982398351486587704192379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4654932234324391802794919 6982398351486587704192379)
          ·
            refine ⟨10473597527229881556288569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6982398351486587704192379 10473597527229881556288569)
            ·
              refine ⟨7855198145422411167216427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10473597527229881556288569 7855198145422411167216427)
              ·
                refine ⟨11782797218133616750824641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7855198145422411167216427 11782797218133616750824641)
                ·
                  refine ⟨8837097913600212563118481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11782797218133616750824641 8837097913600212563118481)
                  ·
                    refine ⟨6627823435200159422338861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8837097913600212563118481 6627823435200159422338861)
                    ·
                      refine ⟨2485433788200059783377073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6627823435200159422338861 2485433788200059783377073)
                      ·
                        rfl

theorem cell23_4840365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_4840365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840365 prefixEnd_4840365 := by exact prefixLift 4840365
  have htrace : WordTrace (prefixWord ++ tailWord_4840365) baseStart_4840365 baseEnd_4840365 := by
    simpa [prefixWord, tailWord_4840365, baseEnd_4840365] using wordTrace_append hprefix tailTrace_4840365
  have hstable : (prefixWord ++ tailWord_4840365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840365).length < 2 ^ (prefixWord ++ tailWord_4840365).sum := by decide
  have hdescent : baseEnd_4840365 < baseStart_4840365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840378 : List Nat := [3, 1, 1, 1, 2, 1, 4, 5, 1, 1, 3]
def baseStart_4840378 : Nat := 118140960795 + 4840378 * 2 ^ 59
def prefixEnd_4840378 : Nat := 4983230072969 + 3 ^ 40 * 4840378 * 2
def baseEnd_4840378 : Nat := 2485440463448568232514513

theorem tailTrace_4840378 : CollatzResearch.WordTrace tailWord_4840378 prefixEnd_4840378 2485440463448568232514513 := by
  unfold tailWord_4840378
  simp only [CollatzResearch.WordTrace]
  refine ⟨44135772314536162898222447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117695392838763101061926525 44135772314536162898222447)
  ·
    refine ⟨66203658471804244347333671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44135772314536162898222447 66203658471804244347333671)
    ·
      refine ⟨99305487707706366521000507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66203658471804244347333671 99305487707706366521000507)
      ·
        refine ⟨148958231561559549781500761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99305487707706366521000507 148958231561559549781500761)
        ·
          refine ⟨111718673671169662336125571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148958231561559549781500761 111718673671169662336125571)
          ·
            refine ⟨167578010506754493504188357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111718673671169662336125571 167578010506754493504188357)
            ·
              refine ⟨31420876970016467532035317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 167578010506754493504188357 31420876970016467532035317)
              ·
                refine ⟨2945707215939043831128311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31420876970016467532035317 2945707215939043831128311)
                ·
                  refine ⟨4418560823908565746692467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2945707215939043831128311 4418560823908565746692467)
                  ·
                    refine ⟨6627841235862848620038701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4418560823908565746692467 6627841235862848620038701)
                    ·
                      refine ⟨2485440463448568232514513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6627841235862848620038701 2485440463448568232514513)
                      ·
                        rfl

theorem cell23_4840378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 5, 1, 1, 3].length) (baseStart_4840378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840378 prefixEnd_4840378 := by exact prefixLift 4840378
  have htrace : WordTrace (prefixWord ++ tailWord_4840378) baseStart_4840378 baseEnd_4840378 := by
    simpa [prefixWord, tailWord_4840378, baseEnd_4840378] using wordTrace_append hprefix tailTrace_4840378
  have hstable : (prefixWord ++ tailWord_4840378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840378).length < 2 ^ (prefixWord ++ tailWord_4840378).sum := by decide
  have hdescent : baseEnd_4840378 < baseStart_4840378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840395 : List Nat := [1, 1, 1, 1, 3, 5, 4, 2, 1, 1, 3]
def baseStart_4840395 : Nat := 118140960795 + 4840395 * 2 ^ 59
def prefixEnd_4840395 : Nat := 4983230072969 + 3 ^ 40 * 4840395 * 2
def baseEnd_4840395 : Nat := 2485449192619694666001935

theorem tailTrace_4840395 : CollatzResearch.WordTrace tailWord_4840395 prefixEnd_4840395 2485449192619694666001935 := by
  unfold tailWord_4840395
  simp only [CollatzResearch.WordTrace]
  refine ⟨176543709299083063496258639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117695806199388708997505759 176543709299083063496258639)
  ·
    refine ⟨264815563948624595244387959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176543709299083063496258639 264815563948624595244387959)
    ·
      refine ⟨397223345922936892866581939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264815563948624595244387959 397223345922936892866581939)
      ·
        refine ⟨595835018884405339299872909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397223345922936892866581939 595835018884405339299872909)
        ·
          refine ⟨223438132081652002237452341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 595835018884405339299872909 223438132081652002237452341)
          ·
            refine ⟨20947324882654875209761157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 223438132081652002237452341 20947324882654875209761157)
            ·
              refine ⟨3927623415497789101830217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20947324882654875209761157 3927623415497789101830217)
              ·
                refine ⟨2945717561623341826372663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3927623415497789101830217 2945717561623341826372663)
                ·
                  refine ⟨4418576342435012739558995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2945717561623341826372663 4418576342435012739558995)
                  ·
                    refine ⟨6627864513652519109338493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4418576342435012739558995 6627864513652519109338493)
                    ·
                      refine ⟨2485449192619694666001935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6627864513652519109338493 2485449192619694666001935)
                      ·
                        rfl

theorem cell23_4840395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 2, 1, 1, 3].length) (baseStart_4840395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840395 prefixEnd_4840395 := by exact prefixLift 4840395
  have htrace : WordTrace (prefixWord ++ tailWord_4840395) baseStart_4840395 baseEnd_4840395 := by
    simpa [prefixWord, tailWord_4840395, baseEnd_4840395] using wordTrace_append hprefix tailTrace_4840395
  have hstable : (prefixWord ++ tailWord_4840395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840395).length < 2 ^ (prefixWord ++ tailWord_4840395).sum := by decide
  have hdescent : baseEnd_4840395 < baseStart_4840395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840407 : List Nat := [1, 1, 3, 2, 1, 1, 2, 12]
def baseStart_4840407 : Nat := 118140960795 + 4840407 * 2 ^ 59
def prefixEnd_4840407 : Nat := 4983230072969 + 3 ^ 40 * 4840407 * 2
def baseEnd_4840407 : Nat := 92053902014353652557477

theorem tailTrace_4840407 : CollatzResearch.WordTrace tailWord_4840407 prefixEnd_4840407 92053902014353652557477 := by
  unfold tailWord_4840407
  simp only [CollatzResearch.WordTrace]
  refine ⟨176544146975039589545695475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117696097983359726363796983 176544146975039589545695475)
  ·
    refine ⟨264816220462559384318543213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176544146975039589545695475 264816220462559384318543213)
    ·
      refine ⟨99306082673459769119453705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 264816220462559384318543213 99306082673459769119453705)
      ·
        refine ⟨74479562005094826839590279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99306082673459769119453705 74479562005094826839590279)
        ·
          refine ⟨111719343007642240259385419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74479562005094826839590279 111719343007642240259385419)
          ·
            refine ⟨167579014511463360389078129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111719343007642240259385419 167579014511463360389078129)
            ·
              refine ⟨125684260883597520291808597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167579014511463360389078129 125684260883597520291808597)
              ·
                refine ⟨92053902014353652557477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 125684260883597520291808597 92053902014353652557477)
                ·
                  rfl

theorem cell23_4840407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 12].length) (baseStart_4840407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840407 prefixEnd_4840407 := by exact prefixLift 4840407
  have htrace : WordTrace (prefixWord ++ tailWord_4840407) baseStart_4840407 baseEnd_4840407 := by
    simpa [prefixWord, tailWord_4840407, baseEnd_4840407] using wordTrace_append hprefix tailTrace_4840407
  have hstable : (prefixWord ++ tailWord_4840407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840407).length < 2 ^ (prefixWord ++ tailWord_4840407).sum := by decide
  have hdescent : baseEnd_4840407 < baseStart_4840407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840418 : List Nat := [3, 3, 3, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_4840418 : Nat := 118140960795 + 4840418 * 2 ^ 59
def prefixEnd_4840418 : Nat := 4983230072969 + 3 ^ 40 * 4840418 * 2
def baseEnd_4840418 : Nat := 2485461002674748076014329

theorem tailTrace_4840418 : CollatzResearch.WordTrace tailWord_4840418 prefixEnd_4840418 2485461002674748076014329 := by
  unfold tailWord_4840418
  simp only [CollatzResearch.WordTrace]
  refine ⟨44136137044499934606086477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117696365451999825616230605 44136137044499934606086477)
  ·
    refine ⟨16551051391687475477282429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44136137044499934606086477 16551051391687475477282429)
    ·
      refine ⟨6206644271882803303980911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16551051391687475477282429 6206644271882803303980911)
      ·
        refine ⟨9309966407824204955971367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6206644271882803303980911 9309966407824204955971367)
        ·
          refine ⟨13964949611736307433957051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9309966407824204955971367 13964949611736307433957051)
          ·
            refine ⟨20947424417604461150935577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13964949611736307433957051 20947424417604461150935577)
            ·
              refine ⟨15710568313203345863201683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20947424417604461150935577 15710568313203345863201683)
              ·
                refine ⟨23565852469805018794802525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15710568313203345863201683 23565852469805018794802525)
                ·
                  refine ⟨8837194676176882048050947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23565852469805018794802525 8837194676176882048050947)
                  ·
                    refine ⟨13255792014265323072076421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8837194676176882048050947 13255792014265323072076421)
                    ·
                      refine ⟨2485461002674748076014329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13255792014265323072076421 2485461002674748076014329)
                      ·
                        rfl

theorem cell23_4840418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_4840418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840418 prefixEnd_4840418 := by exact prefixLift 4840418
  have htrace : WordTrace (prefixWord ++ tailWord_4840418) baseStart_4840418 baseEnd_4840418 := by
    simpa [prefixWord, tailWord_4840418, baseEnd_4840418] using wordTrace_append hprefix tailTrace_4840418
  have hstable : (prefixWord ++ tailWord_4840418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840418).length < 2 ^ (prefixWord ++ tailWord_4840418).sum := by decide
  have hdescent : baseEnd_4840418 < baseStart_4840418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840491 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 3, 4, 2]
def baseStart_4840491 : Nat := 118140960795 + 4840491 * 2 ^ 59
def prefixEnd_4840491 : Nat := 4983230072969 + 3 ^ 40 * 4840491 * 2
def baseEnd_4840491 : Nat := 2485498486762526290401493

theorem tailTrace_4840491 : CollatzResearch.WordTrace tailWord_4840491 prefixEnd_4840491 2485498486762526290401493 := by
  unfold tailWord_4840491
  simp only [CollatzResearch.WordTrace]
  refine ⟨176547210706735271891753327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117698140471156847927835551 176547210706735271891753327)
  ·
    refine ⟨264820816060102907837629991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176547210706735271891753327 264820816060102907837629991)
    ·
      refine ⟨397231224090154361756444987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264820816060102907837629991 397231224090154361756444987)
      ·
        refine ⟨595846836135231542634667481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397231224090154361756444987 595846836135231542634667481)
        ·
          refine ⟨446885127101423656976000611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 595846836135231542634667481 446885127101423656976000611)
          ·
            refine ⟨670327690652135485464000917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446885127101423656976000611 670327690652135485464000917)
            ·
              refine ⟨31421610499318850881125043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 670327690652135485464000917 31421610499318850881125043)
              ·
                refine ⟨47132415748978276321687565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31421610499318850881125043 47132415748978276321687565)
                ·
                  refine ⟨17674655905866853620632837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47132415748978276321687565 17674655905866853620632837)
                  ·
                    refine ⟨3313997982350035053868657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17674655905866853620632837 3313997982350035053868657)
                    ·
                      refine ⟨2485498486762526290401493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3313997982350035053868657 2485498486762526290401493)
                      ·
                        rfl

theorem cell23_4840491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 4, 2].length) (baseStart_4840491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840491 prefixEnd_4840491 := by exact prefixLift 4840491
  have htrace : WordTrace (prefixWord ++ tailWord_4840491) baseStart_4840491 baseEnd_4840491 := by
    simpa [prefixWord, tailWord_4840491, baseEnd_4840491] using wordTrace_append hprefix tailTrace_4840491
  have hstable : (prefixWord ++ tailWord_4840491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840491).length < 2 ^ (prefixWord ++ tailWord_4840491).sum := by decide
  have hdescent : baseEnd_4840491 < baseStart_4840491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840542 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 3, 4, 2]
def baseStart_4840542 : Nat := 118140960795 + 4840542 * 2 ^ 59
def prefixEnd_4840542 : Nat := 4983230072969 + 3 ^ 40 * 4840542 * 2
def baseEnd_4840542 : Nat := 2485524674275905590863759

theorem tailTrace_4840542 : CollatzResearch.WordTrace tailWord_4840542 prefixEnd_4840542 2485524674275905590863759 := by
  unfold tailWord_4840542
  simp only [CollatzResearch.WordTrace]
  refine ⟨22068633853693813450232485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117699380553033671734573253 22068633853693813450232485)
  ·
    refine ⟨4137868847567590021918591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22068633853693813450232485 4137868847567590021918591)
    ·
      refine ⟨6206803271351385032877887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4137868847567590021918591 6206803271351385032877887)
      ·
        refine ⟨9310204907027077549316831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6206803271351385032877887 9310204907027077549316831)
        ·
          refine ⟨13965307360540616323975247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9310204907027077549316831 13965307360540616323975247)
          ·
            refine ⟨20947961040810924485962871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13965307360540616323975247 20947961040810924485962871)
            ·
              refine ⟨31421941561216386728944307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20947961040810924485962871 31421941561216386728944307)
              ·
                refine ⟨47132912341824580093416461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31421941561216386728944307 47132912341824580093416461)
                ·
                  refine ⟨17674842128184217535031173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47132912341824580093416461 17674842128184217535031173)
                  ·
                    refine ⟨3314032899034540787818345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17674842128184217535031173 3314032899034540787818345)
                    ·
                      refine ⟨2485524674275905590863759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3314032899034540787818345 2485524674275905590863759)
                      ·
                        rfl

theorem cell23_4840542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_4840542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840542 prefixEnd_4840542 := by exact prefixLift 4840542
  have htrace : WordTrace (prefixWord ++ tailWord_4840542) baseStart_4840542 baseEnd_4840542 := by
    simpa [prefixWord, tailWord_4840542, baseEnd_4840542] using wordTrace_append hprefix tailTrace_4840542
  have hstable : (prefixWord ++ tailWord_4840542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840542).length < 2 ^ (prefixWord ++ tailWord_4840542).sum := by decide
  have hdescent : baseEnd_4840542 < baseStart_4840542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840615 : List Nat := [1, 1, 6, 2, 1, 1, 1, 2, 2, 4, 2]
def baseStart_4840615 : Nat := 118140960795 + 4840615 * 2 ^ 59
def prefixEnd_4840615 : Nat := 4983230072969 + 3 ^ 40 * 4840615 * 2
def baseEnd_4840615 : Nat := 2485562158363683805250923

theorem tailTrace_4840615 : CollatzResearch.WordTrace tailWord_4840615 prefixEnd_4840615 2485562158363683805250923 := by
  unfold tailWord_4840615
  simp only [CollatzResearch.WordTrace]
  refine ⟨176551733358286041069267299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117701155572190694046178199 176551733358286041069267299)
  ·
    refine ⟨264827600037429061603900949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176551733358286041069267299 264827600037429061603900949)
    ·
      refine ⟨12413793751754487262682857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 264827600037429061603900949 12413793751754487262682857)
      ·
        refine ⟨9310345313815865447012143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12413793751754487262682857 9310345313815865447012143)
        ·
          refine ⟨13965517970723798170518215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9310345313815865447012143 13965517970723798170518215)
          ·
            refine ⟨20948276956085697255777323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13965517970723798170518215 20948276956085697255777323)
            ·
              refine ⟨31422415434128545883665985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20948276956085697255777323 31422415434128545883665985)
              ·
                refine ⟨23566811575596409412749489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31422415434128545883665985 23566811575596409412749489)
                ·
                  refine ⟨17675108681697307059562117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23566811575596409412749489 17675108681697307059562117)
                  ·
                    refine ⟨3314082877818245073667897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17675108681697307059562117 3314082877818245073667897)
                    ·
                      refine ⟨2485562158363683805250923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3314082877818245073667897 2485562158363683805250923)
                      ·
                        rfl

theorem cell23_4840615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_4840615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840615 prefixEnd_4840615 := by exact prefixLift 4840615
  have htrace : WordTrace (prefixWord ++ tailWord_4840615) baseStart_4840615 baseEnd_4840615 := by
    simpa [prefixWord, tailWord_4840615, baseEnd_4840615] using wordTrace_append hprefix tailTrace_4840615
  have hstable : (prefixWord ++ tailWord_4840615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840615).length < 2 ^ (prefixWord ++ tailWord_4840615).sum := by decide
  have hdescent : baseEnd_4840615 < baseStart_4840615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840625 : List Nat := [1, 2, 2, 5, 1, 2, 2, 1, 3, 4]
def baseStart_4840625 : Nat := 118140960795 + 4840625 * 2 ^ 59
def prefixEnd_4840625 : Nat := 4983230072969 + 3 ^ 40 * 4840625 * 2
def baseEnd_4840625 : Nat := 828522431056742922041959

theorem tailTrace_4840625 : CollatzResearch.WordTrace tailWord_4840625 prefixEnd_4840625 828522431056742922041959 := by
  unfold tailWord_4840625
  simp only [CollatzResearch.WordTrace]
  refine ⟨176552098088249812777131329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117701398725499875184754219 176552098088249812777131329)
  ·
    refine ⟨132414073566187359582848497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176552098088249812777131329 132414073566187359582848497)
    ·
      refine ⟨99310555174640519687136373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132414073566187359582848497 99310555174640519687136373)
      ·
        refine ⟨9310364547622548720669035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99310555174640519687136373 9310364547622548720669035)
        ·
          refine ⟨13965546821433823081003553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9310364547622548720669035 13965546821433823081003553)
          ·
            refine ⟨10474160116075367310752665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13965546821433823081003553 10474160116075367310752665)
            ·
              refine ⟨7855620087056525483064499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10474160116075367310752665 7855620087056525483064499)
              ·
                refine ⟨11783430130584788224596749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7855620087056525483064499 11783430130584788224596749)
                ·
                  refine ⟨4418786298969295584223781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11783430130584788224596749 4418786298969295584223781)
                  ·
                    refine ⟨828522431056742922041959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4418786298969295584223781 828522431056742922041959)
                    ·
                      rfl

theorem cell23_4840625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 3, 4].length) (baseStart_4840625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840625 prefixEnd_4840625 := by exact prefixLift 4840625
  have htrace : WordTrace (prefixWord ++ tailWord_4840625) baseStart_4840625 baseEnd_4840625 := by
    simpa [prefixWord, tailWord_4840625, baseEnd_4840625] using wordTrace_append hprefix tailTrace_4840625
  have hstable : (prefixWord ++ tailWord_4840625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840625).length < 2 ^ (prefixWord ++ tailWord_4840625).sum := by decide
  have hdescent : baseEnd_4840625 < baseStart_4840625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840682 : List Nat := [3, 1, 3, 1, 1, 5, 1, 1, 3, 1, 3]
def baseStart_4840682 : Nat := 118140960795 + 4840682 * 2 ^ 59
def prefixEnd_4840682 : Nat := 4983230072969 + 3 ^ 40 * 4840682 * 2
def baseEnd_4840682 : Nat := 2485596561567535043113115

theorem tailTrace_4840682 : CollatzResearch.WordTrace tailWord_4840682 prefixEnd_4840682 2485596561567535043113115 := by
  unfold tailWord_4840682
  simp only [CollatzResearch.WordTrace]
  refine ⟨44138544262260827877989075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117702784699362207674637533 44138544262260827877989075)
  ·
    refine ⟨66207816393391241816983613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44138544262260827877989075 66207816393391241816983613)
    ·
      refine ⟨24827931147521715681368855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66207816393391241816983613 24827931147521715681368855)
      ·
        refine ⟨37241896721282573522053283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24827931147521715681368855 37241896721282573522053283)
        ·
          refine ⟨55862845081923860283079925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37241896721282573522053283 55862845081923860283079925)
          ·
            refine ⟨5237141726430361901538743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55862845081923860283079925 5237141726430361901538743)
            ·
              refine ⟨7855712589645542852308115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5237141726430361901538743 7855712589645542852308115)
              ·
                refine ⟨11783568884468314278462173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7855712589645542852308115 11783568884468314278462173)
                ·
                  refine ⟨4418838331675617854423315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11783568884468314278462173 4418838331675617854423315)
                  ·
                    refine ⟨6628257497513426781634973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4418838331675617854423315 6628257497513426781634973)
                    ·
                      refine ⟨2485596561567535043113115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6628257497513426781634973 2485596561567535043113115)
                      ·
                        rfl

theorem cell23_4840682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_4840682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840682 prefixEnd_4840682 := by exact prefixLift 4840682
  have htrace : WordTrace (prefixWord ++ tailWord_4840682) baseStart_4840682 baseEnd_4840682 := by
    simpa [prefixWord, tailWord_4840682, baseEnd_4840682] using wordTrace_append hprefix tailTrace_4840682
  have hstable : (prefixWord ++ tailWord_4840682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840682).length < 2 ^ (prefixWord ++ tailWord_4840682).sum := by decide
  have hdescent : baseEnd_4840682 < baseStart_4840682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840702 : List Nat := [4, 2, 2, 1, 1, 4, 1, 2, 1, 5]
def baseStart_4840702 : Nat := 118140960795 + 4840702 * 2 ^ 59
def prefixEnd_4840702 : Nat := 4983230072969 + 3 ^ 40 * 4840702 * 2
def baseEnd_4840702 : Nat := 828535610393541654954341

theorem tailTrace_4840702 : CollatzResearch.WordTrace tailWord_4840702 prefixEnd_4840702 828535610393541654954341 := by
  unfold tailWord_4840702
  simp only [CollatzResearch.WordTrace]
  refine ⟨22069363313621356865960545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117703271005980569951789573 22069363313621356865960545)
  ·
    refine ⟨16552022485216017649470409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22069363313621356865960545 16552022485216017649470409)
    ·
      refine ⟨12414016863912013237102807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16552022485216017649470409 12414016863912013237102807)
      ·
        refine ⟨18621025295868019855654211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12414016863912013237102807 18621025295868019855654211)
        ·
          refine ⟨27931537943802029783481317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18621025295868019855654211 27931537943802029783481317)
          ·
            refine ⟨5237163364462880584402747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27931537943802029783481317 5237163364462880584402747)
            ·
              refine ⟨7855745046694320876604121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5237163364462880584402747 7855745046694320876604121)
              ·
                refine ⟨5891808785020740657453091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7855745046694320876604121 5891808785020740657453091)
                ·
                  refine ⟨8837713177531110986179637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5891808785020740657453091 8837713177531110986179637)
                  ·
                    refine ⟨828535610393541654954341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8837713177531110986179637 828535610393541654954341)
                    ·
                      rfl

theorem cell23_4840702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_4840702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840702 prefixEnd_4840702 := by exact prefixLift 4840702
  have htrace : WordTrace (prefixWord ++ tailWord_4840702) baseStart_4840702 baseEnd_4840702 := by
    simpa [prefixWord, tailWord_4840702, baseEnd_4840702] using wordTrace_append hprefix tailTrace_4840702
  have hstable : (prefixWord ++ tailWord_4840702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840702).length < 2 ^ (prefixWord ++ tailWord_4840702).sum := by decide
  have hdescent : baseEnd_4840702 < baseStart_4840702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840705 : List Nat := [1, 2, 4, 1, 1, 3, 3, 2, 1, 1, 4]
def baseStart_4840705 : Nat := 118140960795 + 4840705 * 2 ^ 59
def prefixEnd_4840705 : Nat := 4983230072969 + 3 ^ 40 * 4840705 * 2
def baseEnd_4840705 : Nat := 2485608371622588453125509

theorem tailTrace_4840705 : CollatzResearch.WordTrace tailWord_4840705 prefixEnd_4840705 2485608371622588453125509 := by
  unfold tailWord_4840705
  simp only [CollatzResearch.WordTrace]
  refine ⟨176555015927959986440043569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117703343951973324293362379 176555015927959986440043569)
  ·
    refine ⟨132416261945969989830032677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176555015927959986440043569 132416261945969989830032677)
    ·
      refine ⟨24828049114869373093131127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132416261945969989830032677 24828049114869373093131127)
      ·
        refine ⟨37242073672304059639696691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24828049114869373093131127 37242073672304059639696691)
        ·
          refine ⟨55863110508456089459545037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37242073672304059639696691 55863110508456089459545037)
          ·
            refine ⟨20948666440671033547329389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55863110508456089459545037 20948666440671033547329389)
            ·
              refine ⟨7855749915251637580248521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20948666440671033547329389 7855749915251637580248521)
              ·
                refine ⟨5891812436438728185186391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7855749915251637580248521 5891812436438728185186391)
                ·
                  refine ⟨8837718654658092277779587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5891812436438728185186391 8837718654658092277779587)
                  ·
                    refine ⟨13256577981987138416669381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8837718654658092277779587 13256577981987138416669381)
                    ·
                      refine ⟨2485608371622588453125509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13256577981987138416669381 2485608371622588453125509)
                      ·
                        rfl

theorem cell23_4840705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_4840705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840705 prefixEnd_4840705 := by exact prefixLift 4840705
  have htrace : WordTrace (prefixWord ++ tailWord_4840705) baseStart_4840705 baseEnd_4840705 := by
    simpa [prefixWord, tailWord_4840705, baseEnd_4840705] using wordTrace_append hprefix tailTrace_4840705
  have hstable : (prefixWord ++ tailWord_4840705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840705).length < 2 ^ (prefixWord ++ tailWord_4840705).sum := by decide
  have hdescent : baseEnd_4840705 < baseStart_4840705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840718 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4]
def baseStart_4840718 : Nat := 118140960795 + 4840718 * 2 ^ 59
def prefixEnd_4840718 : Nat := 4983230072969 + 3 ^ 40 * 4840718 * 2
def baseEnd_4840718 : Nat := 2485615046871096902262949

theorem tailTrace_4840718 : CollatzResearch.WordTrace tailWord_4840718 prefixEnd_4840718 2485615046871096902262949 := by
  unfold tailWord_4840718
  simp only [CollatzResearch.WordTrace]
  refine ⟨22069436259614111207533351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117703660051275259773511205 22069436259614111207533351)
  ·
    refine ⟨33104154389421166811300027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22069436259614111207533351 33104154389421166811300027)
    ·
      refine ⟨49656231584131750216950041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33104154389421166811300027 49656231584131750216950041)
      ·
        refine ⟨37242173688098812662712531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49656231584131750216950041 37242173688098812662712531)
        ·
          refine ⟨55863260532148218994068797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37242173688098812662712531 55863260532148218994068797)
          ·
            refine ⟨20948722699555582122775799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55863260532148218994068797 20948722699555582122775799)
            ·
              refine ⟨31423084049333373184163699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20948722699555582122775799 31423084049333373184163699)
              ·
                refine ⟨47134626074000059776245549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31423084049333373184163699 47134626074000059776245549)
                ·
                  refine ⟨17675484777750022416092081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47134626074000059776245549 17675484777750022416092081)
                  ·
                    refine ⟨13256613583312516812069061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17675484777750022416092081 13256613583312516812069061)
                    ·
                      refine ⟨2485615046871096902262949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13256613583312516812069061 2485615046871096902262949)
                      ·
                        rfl

theorem cell23_4840718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_4840718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840718 prefixEnd_4840718 := by exact prefixLift 4840718
  have htrace : WordTrace (prefixWord ++ tailWord_4840718) baseStart_4840718 baseEnd_4840718 := by
    simpa [prefixWord, tailWord_4840718, baseEnd_4840718] using wordTrace_append hprefix tailTrace_4840718
  have hstable : (prefixWord ++ tailWord_4840718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840718).length < 2 ^ (prefixWord ++ tailWord_4840718).sum := by decide
  have hdescent : baseEnd_4840718 < baseStart_4840718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840739 : List Nat := [1, 1, 1, 4, 2, 4, 1, 4, 1, 2, 2]
def baseStart_4840739 : Nat := 118140960795 + 4840739 * 2 ^ 59
def prefixEnd_4840739 : Nat := 4983230072969 + 3 ^ 40 * 4840739 * 2
def baseEnd_4840739 : Nat := 2485625829964841320100353

theorem tailTrace_4840739 : CollatzResearch.WordTrace tailWord_4840739 prefixEnd_4840739 2485625829964841320100353 := by
  unfold tailWord_4840739
  simp only [CollatzResearch.WordTrace]
  refine ⟨176556256009836810246781271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117704170673224540164520847 176556256009836810246781271)
  ·
    refine ⟨264834384014755215370171907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176556256009836810246781271 264834384014755215370171907)
    ·
      refine ⟨397251576022132823055257861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264834384014755215370171907 397251576022132823055257861)
      ·
        refine ⟨74484670504149904322860849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 397251576022132823055257861 74484670504149904322860849)
        ·
          refine ⟨55863502878112428242145637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74484670504149904322860849 55863502878112428242145637)
          ·
            refine ⟨10474406789646080295402307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55863502878112428242145637 10474406789646080295402307)
            ·
              refine ⟨15711610184469120443103461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10474406789646080295402307 15711610184469120443103461)
              ·
                refine ⟨2945926909587960083081899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15711610184469120443103461 2945926909587960083081899)
                ·
                  refine ⟨4418890364381940124622849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2945926909587960083081899 4418890364381940124622849)
                  ·
                    refine ⟨3314167773286455093467137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4418890364381940124622849 3314167773286455093467137)
                    ·
                      refine ⟨2485625829964841320100353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3314167773286455093467137 2485625829964841320100353)
                      ·
                        rfl

theorem cell23_4840739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 4, 1, 2, 2].length) (baseStart_4840739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840739 prefixEnd_4840739 := by exact prefixLift 4840739
  have htrace : WordTrace (prefixWord ++ tailWord_4840739) baseStart_4840739 baseEnd_4840739 := by
    simpa [prefixWord, tailWord_4840739, baseEnd_4840739] using wordTrace_append hprefix tailTrace_4840739
  have hstable : (prefixWord ++ tailWord_4840739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840739).length < 2 ^ (prefixWord ++ tailWord_4840739).sum := by decide
  have hdescent : baseEnd_4840739 < baseStart_4840739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840751 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 5]
def baseStart_4840751 : Nat := 118140960795 + 4840751 * 2 ^ 59
def prefixEnd_4840751 : Nat := 4983230072969 + 3 ^ 40 * 4840751 * 2
def baseEnd_4840751 : Nat := 2485631991732695273150297

theorem tailTrace_4840751 : CollatzResearch.WordTrace tailWord_4840751 prefixEnd_4840751 2485631991732695273150297 := by
  unfold tailWord_4840751
  simp only [CollatzResearch.WordTrace]
  refine ⟨176556693685793336296218107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117704462457195557530812071 176556693685793336296218107)
  ·
    refine ⟨264835040528690004444327161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176556693685793336296218107 264835040528690004444327161)
    ·
      refine ⟨198626280396517503333245371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264835040528690004444327161 198626280396517503333245371)
      ·
        refine ⟨297939420594776254999868057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198626280396517503333245371 297939420594776254999868057)
        ·
          refine ⟨223454565446082191249901043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297939420594776254999868057 223454565446082191249901043)
          ·
            refine ⟨335181848169123286874851565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223454565446082191249901043 335181848169123286874851565)
            ·
              refine ⟨125693193063421232578069337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 335181848169123286874851565 125693193063421232578069337)
              ·
                refine ⟨94269894797565924433552003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125693193063421232578069337 94269894797565924433552003)
                ·
                  refine ⟨141404842196348886650328005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94269894797565924433552003 141404842196348886650328005)
                  ·
                    refine ⟨26513407911815416246936501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 141404842196348886650328005 26513407911815416246936501)
                    ·
                      refine ⟨2485631991732695273150297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26513407911815416246936501 2485631991732695273150297)
                      ·
                        rfl

theorem cell23_4840751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 5].length) (baseStart_4840751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840751 prefixEnd_4840751 := by exact prefixLift 4840751
  have htrace : WordTrace (prefixWord ++ tailWord_4840751) baseStart_4840751 baseEnd_4840751 := by
    simpa [prefixWord, tailWord_4840751, baseEnd_4840751] using wordTrace_append hprefix tailTrace_4840751
  have hstable : (prefixWord ++ tailWord_4840751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840751).length < 2 ^ (prefixWord ++ tailWord_4840751).sum := by decide
  have hdescent : baseEnd_4840751 < baseStart_4840751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840755 : List Nat := [1, 1, 1, 2, 5, 3, 2, 1, 1, 3, 3]
def baseStart_4840755 : Nat := 118140960795 + 4840755 * 2 ^ 59
def prefixEnd_4840755 : Nat := 4983230072969 + 3 ^ 40 * 4840755 * 2
def baseEnd_4840755 : Nat := 2485634045655313257500279

theorem tailTrace_4840755 : CollatzResearch.WordTrace tailWord_4840755 prefixEnd_4840755 2485634045655313257500279 := by
  unfold tailWord_4840755
  simp only [CollatzResearch.WordTrace]
  refine ⟨176556839577778844979363719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117704559718519229986242479 176556839577778844979363719)
  ·
    refine ⟨264835259366668267469045579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176556839577778844979363719 264835259366668267469045579)
    ·
      refine ⟨397252889050002401203568369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264835259366668267469045579 397252889050002401203568369)
      ·
        refine ⟨297939666787501800902676277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 397252889050002401203568369 297939666787501800902676277)
        ·
          refine ⟨27931843761328293834625901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 297939666787501800902676277 27931843761328293834625901)
          ·
            refine ⟨10474441410498110187984713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27931843761328293834625901 10474441410498110187984713)
            ·
              refine ⟨7855831057873582640988535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10474441410498110187984713 7855831057873582640988535)
              ·
                refine ⟨11783746586810373961482803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7855831057873582640988535 11783746586810373961482803)
                ·
                  refine ⟨17675619880215560942224205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11783746586810373961482803 17675619880215560942224205)
                  ·
                    refine ⟨6628357455080835353334077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17675619880215560942224205 6628357455080835353334077)
                    ·
                      refine ⟨2485634045655313257500279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6628357455080835353334077 2485634045655313257500279)
                      ·
                        rfl

theorem cell23_4840755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 3, 3].length) (baseStart_4840755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840755 prefixEnd_4840755 := by exact prefixLift 4840755
  have htrace : WordTrace (prefixWord ++ tailWord_4840755) baseStart_4840755 baseEnd_4840755 := by
    simpa [prefixWord, tailWord_4840755, baseEnd_4840755] using wordTrace_append hprefix tailTrace_4840755
  have hstable : (prefixWord ++ tailWord_4840755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840755).length < 2 ^ (prefixWord ++ tailWord_4840755).sum := by decide
  have hdescent : baseEnd_4840755 < baseStart_4840755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840771 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 3, 8]
def baseStart_4840771 : Nat := 118140960795 + 4840771 * 2 ^ 59
def prefixEnd_4840771 : Nat := 4983230072969 + 3 ^ 40 * 4840771 * 2
def baseEnd_4840771 : Nat := 828547420448595064966735

theorem tailTrace_4840771 : CollatzResearch.WordTrace tailWord_4840771 prefixEnd_4840771 828547420448595064966735 := by
  unfold tailWord_4840771
  simp only [CollatzResearch.WordTrace]
  refine ⟨176557423145720879711946167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117704948763813919807964111 176557423145720879711946167)
  ·
    refine ⟨264836134718581319567919251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176557423145720879711946167 264836134718581319567919251)
    ·
      refine ⟨397254202077871979351878877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264836134718581319567919251 397254202077871979351878877)
      ·
        refine ⟨148970325779201992256954579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 397254202077871979351878877 148970325779201992256954579)
        ·
          refine ⟨223455488668802988385431869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148970325779201992256954579 223455488668802988385431869)
          ·
            refine ⟨83795808250801120644536951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 223455488668802988385431869 83795808250801120644536951)
            ·
              refine ⟨125693712376201680966805427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83795808250801120644536951 125693712376201680966805427)
              ·
                refine ⟨188540568564302521450208141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125693712376201680966805427 188540568564302521450208141)
                ·
                  refine ⟨70702713211613445543828053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 188540568564302521450208141 70702713211613445543828053)
                  ·
                    refine ⟨828547420448595064966735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70702713211613445543828053 828547420448595064966735)
                    ·
                      rfl

theorem cell23_4840771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 8].length) (baseStart_4840771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840771 prefixEnd_4840771 := by exact prefixLift 4840771
  have htrace : WordTrace (prefixWord ++ tailWord_4840771) baseStart_4840771 baseEnd_4840771 := by
    simpa [prefixWord, tailWord_4840771, baseEnd_4840771] using wordTrace_append hprefix tailTrace_4840771
  have hstable : (prefixWord ++ tailWord_4840771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840771).length < 2 ^ (prefixWord ++ tailWord_4840771).sum := by decide
  have hdescent : baseEnd_4840771 < baseStart_4840771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840772 : List Nat := [2, 3, 4, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_4840772 : Nat := 118140960795 + 4840772 * 2 ^ 59
def prefixEnd_4840772 : Nat := 4983230072969 + 3 ^ 40 * 4840772 * 2
def baseEnd_4840772 : Nat := 2485642774826439690987701

theorem tailTrace_4840772 : CollatzResearch.WordTrace tailWord_4840772 prefixEnd_4840772 2485642774826439690987701 := by
  unfold tailWord_4840772
  simp only [CollatzResearch.WordTrace]
  refine ⟨88278729809358628441366285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117704973079144837921821713 88278729809358628441366285)
  ·
    refine ⟨33104523678509485665512357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88278729809358628441366285 33104523678509485665512357)
    ·
      refine ⟨6207098189720528562283567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33104523678509485665512357 6207098189720528562283567)
      ·
        refine ⟨9310647284580792843425351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6207098189720528562283567 9310647284580792843425351)
        ·
          refine ⟨13965970926871189265138027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9310647284580792843425351 13965970926871189265138027)
          ·
            refine ⟨20948956390306783897707041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13965970926871189265138027 20948956390306783897707041)
            ·
              refine ⟨15711717292730087923280281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20948956390306783897707041 15711717292730087923280281)
              ·
                refine ⟨11783787969547565942460211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15711717292730087923280281 11783787969547565942460211)
                ·
                  refine ⟨17675681954321348913690317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11783787969547565942460211 17675681954321348913690317)
                  ·
                    refine ⟨6628380732870505842633869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17675681954321348913690317 6628380732870505842633869)
                    ·
                      refine ⟨2485642774826439690987701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6628380732870505842633869 2485642774826439690987701)
                      ·
                        rfl

theorem cell23_4840772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_4840772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840772 prefixEnd_4840772 := by exact prefixLift 4840772
  have htrace : WordTrace (prefixWord ++ tailWord_4840772) baseStart_4840772 baseEnd_4840772 := by
    simpa [prefixWord, tailWord_4840772, baseEnd_4840772] using wordTrace_append hprefix tailTrace_4840772
  have hstable : (prefixWord ++ tailWord_4840772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840772).length < 2 ^ (prefixWord ++ tailWord_4840772).sum := by decide
  have hdescent : baseEnd_4840772 < baseStart_4840772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840782 : List Nat := [4, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2]
def baseStart_4840782 : Nat := 118140960795 + 4840782 * 2 ^ 59
def prefixEnd_4840782 : Nat := 4983230072969 + 3 ^ 40 * 4840782 * 2
def baseEnd_4840782 : Nat := 2485647909632984651862655

theorem tailTrace_4840782 : CollatzResearch.WordTrace tailWord_4840782 prefixEnd_4840782 2485647909632984651862655 := by
  unfold tailWord_4840782
  simp only [CollatzResearch.WordTrace]
  refine ⟨22069728043585128573824575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117705216232454019060397733 22069728043585128573824575)
  ·
    refine ⟨33104592065377692860736863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22069728043585128573824575 33104592065377692860736863)
    ·
      refine ⟨49656888098066539291105295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33104592065377692860736863 49656888098066539291105295)
      ·
        refine ⟨74485332147099808936657943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49656888098066539291105295 74485332147099808936657943)
        ·
          refine ⟨111727998220649713404986915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74485332147099808936657943 111727998220649713404986915)
          ·
            refine ⟨167591997330974570107480373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111727998220649713404986915 167591997330974570107480373)
            ·
              refine ⟨15711749749778865947576285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 167591997330974570107480373 15711749749778865947576285)
              ·
                refine ⟨5891906156167074730341107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15711749749778865947576285 5891906156167074730341107)
                ·
                  refine ⟨8837859234250612095511661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5891906156167074730341107 8837859234250612095511661)
                  ·
                    refine ⟨3314197212843979535816873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8837859234250612095511661 3314197212843979535816873)
                    ·
                      refine ⟨2485647909632984651862655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3314197212843979535816873 2485647909632984651862655)
                      ·
                        rfl

theorem cell23_4840782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2].length) (baseStart_4840782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840782 prefixEnd_4840782 := by exact prefixLift 4840782
  have htrace : WordTrace (prefixWord ++ tailWord_4840782) baseStart_4840782 baseEnd_4840782 := by
    simpa [prefixWord, tailWord_4840782, baseEnd_4840782] using wordTrace_append hprefix tailTrace_4840782
  have hstable : (prefixWord ++ tailWord_4840782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840782).length < 2 ^ (prefixWord ++ tailWord_4840782).sum := by decide
  have hdescent : baseEnd_4840782 < baseStart_4840782 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840788 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 4, 6]
def baseStart_4840788 : Nat := 118140960795 + 4840788 * 2 ^ 59
def prefixEnd_4840788 : Nat := 4983230072969 + 3 ^ 40 * 4840788 * 2
def baseEnd_4840788 : Nat := 828550330172303876129209

theorem tailTrace_4840788 : CollatzResearch.WordTrace tailWord_4840788 prefixEnd_4840788 828550330172303876129209 := by
  unfold tailWord_4840788
  simp only [CollatzResearch.WordTrace]
  refine ⟨88279021593329645807657509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117705362124439527743543345 88279021593329645807657509)
  ·
    refine ⟨16552316548749308588935783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88279021593329645807657509 16552316548749308588935783)
    ·
      refine ⟨24828474823123962883403675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16552316548749308588935783 24828474823123962883403675)
      ·
        refine ⟨37242712234685944325105513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24828474823123962883403675 37242712234685944325105513)
        ·
          refine ⟨27932034176014458243829135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37242712234685944325105513 27932034176014458243829135)
          ·
            refine ⟨41898051264021687365743703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27932034176014458243829135 41898051264021687365743703)
            ·
              refine ⟨62847076896032531048615555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41898051264021687365743703 62847076896032531048615555)
              ·
                refine ⟨94270615344048796572923333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62847076896032531048615555 94270615344048796572923333)
                ·
                  refine ⟨17675740377009149357423125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94270615344048796572923333 17675740377009149357423125)
                  ·
                    refine ⟨828550330172303876129209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17675740377009149357423125 828550330172303876129209)
                    ·
                      rfl

theorem cell23_4840788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_4840788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840788 prefixEnd_4840788 := by exact prefixLift 4840788
  have htrace : WordTrace (prefixWord ++ tailWord_4840788) baseStart_4840788 baseEnd_4840788 := by
    simpa [prefixWord, tailWord_4840788, baseEnd_4840788] using wordTrace_append hprefix tailTrace_4840788
  have hstable : (prefixWord ++ tailWord_4840788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840788).length < 2 ^ (prefixWord ++ tailWord_4840788).sum := by decide
  have hdescent : baseEnd_4840788 < baseStart_4840788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840789 : List Nat := [1, 3, 2, 2, 3, 3, 1, 2, 2, 1, 3]
def baseStart_4840789 : Nat := 118140960795 + 4840789 * 2 ^ 59
def prefixEnd_4840789 : Nat := 4983230072969 + 3 ^ 40 * 4840789 * 2
def baseEnd_4840789 : Nat := 2485651503997566124475123

theorem tailTrace_4840789 : CollatzResearch.WordTrace tailWord_4840789 prefixEnd_4840789 2485651503997566124475123 := by
  unfold tailWord_4840789
  simp only [CollatzResearch.WordTrace]
  refine ⟨176558079659655668786101421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117705386439770445857400947 176558079659655668786101421)
  ·
    refine ⟨66209279872370875794788033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176558079659655668786101421 66209279872370875794788033)
    ·
      refine ⟨49656959904278156846091025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66209279872370875794788033 49656959904278156846091025)
      ·
        refine ⟨37242719928208617634568269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49656959904278156846091025 37242719928208617634568269)
        ·
          refine ⟨13966019973078231612963101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37242719928208617634568269 13966019973078231612963101)
          ·
            refine ⟨5237257489904336854861163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13966019973078231612963101 5237257489904336854861163)
            ·
              refine ⟨7855886234856505282291745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5237257489904336854861163 7855886234856505282291745)
              ·
                refine ⟨5891914676142378961718809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7855886234856505282291745 5891914676142378961718809)
                ·
                  refine ⟨4418936007106784221289107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5891914676142378961718809 4418936007106784221289107)
                  ·
                    refine ⟨6628404010660176331933661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4418936007106784221289107 6628404010660176331933661)
                    ·
                      refine ⟨2485651503997566124475123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6628404010660176331933661 2485651503997566124475123)
                      ·
                        rfl

theorem cell23_4840789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_4840789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840789 prefixEnd_4840789 := by exact prefixLift 4840789
  have htrace : WordTrace (prefixWord ++ tailWord_4840789) baseStart_4840789 baseEnd_4840789 := by
    simpa [prefixWord, tailWord_4840789, baseEnd_4840789] using wordTrace_append hprefix tailTrace_4840789
  have hstable : (prefixWord ++ tailWord_4840789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840789).length < 2 ^ (prefixWord ++ tailWord_4840789).sum := by decide
  have hdescent : baseEnd_4840789 < baseStart_4840789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840790 : List Nat := [5, 2, 3, 1, 1, 1, 2, 1, 3, 2, 2]
def baseStart_4840790 : Nat := 118140960795 + 4840790 * 2 ^ 59
def prefixEnd_4840790 : Nat := 4983230072969 + 3 ^ 40 * 4840790 * 2
def baseEnd_4840790 : Nat := 2485652017478220620562619

theorem tailTrace_4840790 : CollatzResearch.WordTrace tailWord_4840790 prefixEnd_4840790 2485652017478220620562619 := by
  unfold tailWord_4840790
  simp only [CollatzResearch.WordTrace]
  refine ⟨11034882258290752872305489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117705410755101363971258549 11034882258290752872305489)
  ·
    refine ⟨8276161693718064654229117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11034882258290752872305489 8276161693718064654229117)
    ·
      refine ⟨3103560635144274245335919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8276161693718064654229117 3103560635144274245335919)
      ·
        refine ⟨4655340952716411368003879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3103560635144274245335919 4655340952716411368003879)
        ·
          refine ⟨6983011429074617052005819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4655340952716411368003879 6983011429074617052005819)
          ·
            refine ⟨10474517143611925578008729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6983011429074617052005819 10474517143611925578008729)
            ·
              refine ⟨7855887857708944183506547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10474517143611925578008729 7855887857708944183506547)
              ·
                refine ⟨11783831786563416275259821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7855887857708944183506547 11783831786563416275259821)
                ·
                  refine ⟨4418936919961281103222433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11783831786563416275259821 4418936919961281103222433)
                  ·
                    refine ⟨3314202689970960827416825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4418936919961281103222433 3314202689970960827416825)
                    ·
                      refine ⟨2485652017478220620562619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3314202689970960827416825 2485652017478220620562619)
                      ·
                        rfl

theorem cell23_4840790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_4840790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840790 prefixEnd_4840790 := by exact prefixLift 4840790
  have htrace : WordTrace (prefixWord ++ tailWord_4840790) baseStart_4840790 baseEnd_4840790 := by
    simpa [prefixWord, tailWord_4840790, baseEnd_4840790] using wordTrace_append hprefix tailTrace_4840790
  have hstable : (prefixWord ++ tailWord_4840790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840790).length < 2 ^ (prefixWord ++ tailWord_4840790).sum := by decide
  have hdescent : baseEnd_4840790 < baseStart_4840790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840812 : List Nat := [2, 2, 1, 1, 5, 1, 3, 1, 1, 4, 2]
def baseStart_4840812 : Nat := 118140960795 + 4840812 * 2 ^ 59
def prefixEnd_4840812 : Nat := 4983230072969 + 3 ^ 40 * 4840812 * 2
def baseEnd_4840812 : Nat := 2485663314052619534487517

theorem tailTrace_4840812 : CollatzResearch.WordTrace tailWord_4840812 prefixEnd_4840812 2485663314052619534487517 := by
  unfold tailWord_4840812
  simp only [CollatzResearch.WordTrace]
  refine ⟨88279459269286171857094345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117705945692381562476125793 88279459269286171857094345)
  ·
    refine ⟨66209594451964628892820759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88279459269286171857094345 66209594451964628892820759)
    ·
      refine ⟨99314391677946943339231139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66209594451964628892820759 99314391677946943339231139)
      ·
        refine ⟨148971587516920415008846709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99314391677946943339231139 148971587516920415008846709)
        ·
          refine ⟨13966086329711288907079379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 148971587516920415008846709 13966086329711288907079379)
          ·
            refine ⟨20949129494566933360619069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13966086329711288907079379 20949129494566933360619069)
            ·
              refine ⟨7855923560462600010232151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20949129494566933360619069 7855923560462600010232151)
              ·
                refine ⟨11783885340693900015348227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7855923560462600010232151 11783885340693900015348227)
                ·
                  refine ⟨17675828011040850023022341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11783885340693900015348227 17675828011040850023022341)
                  ·
                    refine ⟨3314217752070159379316689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17675828011040850023022341 3314217752070159379316689)
                    ·
                      refine ⟨2485663314052619534487517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3314217752070159379316689 2485663314052619534487517)
                      ·
                        rfl

theorem cell23_4840812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 4, 2].length) (baseStart_4840812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840812 prefixEnd_4840812 := by exact prefixLift 4840812
  have htrace : WordTrace (prefixWord ++ tailWord_4840812) baseStart_4840812 baseEnd_4840812 := by
    simpa [prefixWord, tailWord_4840812, baseEnd_4840812] using wordTrace_append hprefix tailTrace_4840812
  have hstable : (prefixWord ++ tailWord_4840812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840812).length < 2 ^ (prefixWord ++ tailWord_4840812).sum := by decide
  have hdescent : baseEnd_4840812 < baseStart_4840812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840818 : List Nat := [3, 2, 1, 2, 1, 2, 1, 4, 7]
def baseStart_4840818 : Nat := 118140960795 + 4840818 * 2 ^ 59
def prefixEnd_4840818 : Nat := 4983230072969 + 3 ^ 40 * 4840818 * 2
def baseEnd_4840818 : Nat := 276185154992949612334721

theorem tailTrace_4840818 : CollatzResearch.WordTrace tailWord_4840818 prefixEnd_4840818 276185154992949612334721 := by
  unfold tailWord_4840818
  simp only [CollatzResearch.WordTrace]
  refine ⟨44139784344137651684726777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117706091584367071159271405 44139784344137651684726777)
  ·
    refine ⟨33104838258103238763545083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44139784344137651684726777 33104838258103238763545083)
    ·
      refine ⟨49657257387154858145317625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33104838258103238763545083 49657257387154858145317625)
      ·
        refine ⟨37242943040366143608988219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49657257387154858145317625 37242943040366143608988219)
        ·
          refine ⟨55864414560549215413482329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37242943040366143608988219 55864414560549215413482329)
          ·
            refine ⟨41898310920411911560111747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55864414560549215413482329 41898310920411911560111747)
            ·
              refine ⟨62847466380617867340167621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41898310920411911560111747 62847466380617867340167621)
              ·
                refine ⟨11783899946365850126281429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62847466380617867340167621 11783899946365850126281429)
                ·
                  refine ⟨276185154992949612334721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11783899946365850126281429 276185154992949612334721)
                  ·
                    rfl

theorem cell23_4840818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 7].length) (baseStart_4840818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840818 prefixEnd_4840818 := by exact prefixLift 4840818
  have htrace : WordTrace (prefixWord ++ tailWord_4840818) baseStart_4840818 baseEnd_4840818 := by
    simpa [prefixWord, tailWord_4840818, baseEnd_4840818] using wordTrace_append hprefix tailTrace_4840818
  have hstable : (prefixWord ++ tailWord_4840818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840818).length < 2 ^ (prefixWord ++ tailWord_4840818).sum := by decide
  have hdescent : baseEnd_4840818 < baseStart_4840818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840852 : List Nat := [2, 4, 2, 1, 2, 3, 1, 1, 7]
def baseStart_4840852 : Nat := 118140960795 + 4840852 * 2 ^ 59
def prefixEnd_4840852 : Nat := 4983230072969 + 3 ^ 40 * 4840852 * 2
def baseEnd_4840852 : Nat := 276187094808755486443037

theorem tailTrace_4840852 : CollatzResearch.WordTrace tailWord_4840852 prefixEnd_4840852 276187094808755486443037 := by
  unfold tailWord_4840852
  simp only [CollatzResearch.WordTrace]
  refine ⟨88280188729213715272822405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117706918305618287030429873 88280188729213715272822405)
  ·
    refine ⟨16552535386727571613654201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88280188729213715272822405 16552535386727571613654201)
    ·
      refine ⟨12414401540045678710240651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16552535386727571613654201 12414401540045678710240651)
      ·
        refine ⟨18621602310068518065360977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12414401540045678710240651 18621602310068518065360977)
        ·
          refine ⟨13966201732551388549020733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18621602310068518065360977 13966201732551388549020733)
          ·
            refine ⟨5237325649706770705882775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13966201732551388549020733 5237325649706770705882775)
            ·
              refine ⟨7855988474560156058824163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5237325649706770705882775 7855988474560156058824163)
              ·
                refine ⟨11783982711840234088236245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7855988474560156058824163 11783982711840234088236245)
                ·
                  refine ⟨276187094808755486443037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11783982711840234088236245 276187094808755486443037)
                  ·
                    rfl

theorem cell23_4840852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_4840852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840852 prefixEnd_4840852 := by exact prefixLift 4840852
  have htrace : WordTrace (prefixWord ++ tailWord_4840852) baseStart_4840852 baseEnd_4840852 := by
    simpa [prefixWord, tailWord_4840852, baseEnd_4840852] using wordTrace_append hprefix tailTrace_4840852
  have hstable : (prefixWord ++ tailWord_4840852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840852).length < 2 ^ (prefixWord ++ tailWord_4840852).sum := by decide
  have hdescent : baseEnd_4840852 < baseStart_4840852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840855 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 2, 5, 2]
def baseStart_4840855 : Nat := 118140960795 + 4840855 * 2 ^ 59
def prefixEnd_4840855 : Nat := 4983230072969 + 3 ^ 40 * 4840855 * 2
def baseEnd_4840855 : Nat := 2485685393720762866249819

theorem tailTrace_4840855 : CollatzResearch.WordTrace tailWord_4840855 prefixEnd_4840855 2485685393720762866249819 := by
  unfold tailWord_4840855
  simp only [CollatzResearch.WordTrace]
  refine ⟨176560486877416562058004019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117706991251611041372002679 176560486877416562058004019)
  ·
    refine ⟨264840730316124843087006029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176560486877416562058004019 264840730316124843087006029)
    ·
      refine ⟨99315273868546816157627261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 264840730316124843087006029 99315273868546816157627261)
      ·
        refine ⟨37243227700705056059110223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99315273868546816157627261 37243227700705056059110223)
        ·
          refine ⟨55864841551057584088665335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37243227700705056059110223 55864841551057584088665335)
          ·
            refine ⟨83797262326586376132998003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55864841551057584088665335 83797262326586376132998003)
            ·
              refine ⟨125695893489879564199497005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83797262326586376132998003 125695893489879564199497005)
              ·
                refine ⟨47135960058704836574811377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125695893489879564199497005 47135960058704836574811377)
                ·
                  refine ⟨35351970044028627431108533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47135960058704836574811377 35351970044028627431108533)
                  ·
                    refine ⟨3314247191627683821666425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35351970044028627431108533 3314247191627683821666425)
                    ·
                      refine ⟨2485685393720762866249819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3314247191627683821666425 2485685393720762866249819)
                      ·
                        rfl

theorem cell23_4840855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_4840855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840855 prefixEnd_4840855 := by exact prefixLift 4840855
  have htrace : WordTrace (prefixWord ++ tailWord_4840855) baseStart_4840855 baseEnd_4840855 := by
    simpa [prefixWord, tailWord_4840855, baseEnd_4840855] using wordTrace_append hprefix tailTrace_4840855
  have hstable : (prefixWord ++ tailWord_4840855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840855).length < 2 ^ (prefixWord ++ tailWord_4840855).sum := by decide
  have hdescent : baseEnd_4840855 < baseStart_4840855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840912 : List Nat := [2, 1, 1, 1, 1, 2, 2, 8, 1, 4]
def baseStart_4840912 : Nat := 118140960795 + 4840912 * 2 ^ 59
def prefixEnd_4840912 : Nat := 4983230072969 + 3 ^ 40 * 4840912 * 2
def baseEnd_4840912 : Nat := 828571554039356381079019

theorem tailTrace_4840912 : CollatzResearch.WordTrace tailWord_4840912 prefixEnd_4840912 828571554039356381079019 := by
  unfold tailWord_4840912
  simp only [CollatzResearch.WordTrace]
  refine ⟨88281282919105030396414495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117708377225473373861885993 88281282919105030396414495)
  ·
    refine ⟨132421924378657545594621743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88281282919105030396414495 132421924378657545594621743)
    ·
      refine ⟨198632886567986318391932615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132421924378657545594621743 198632886567986318391932615)
      ·
        refine ⟨297949329851979477587898923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198632886567986318391932615 297949329851979477587898923)
        ·
          refine ⟨446923994777969216381848385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297949329851979477587898923 446923994777969216381848385)
          ·
            refine ⟨335192996083476912286386289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 446923994777969216381848385 335192996083476912286386289)
            ·
              refine ⟨251394747062607684214789717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335192996083476912286386289 251394747062607684214789717)
              ·
                refine ⟨2946032192139933799392067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 251394747062607684214789717 2946032192139933799392067)
                ·
                  refine ⟨4419048288209900699088101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2946032192139933799392067 4419048288209900699088101)
                  ·
                    refine ⟨828571554039356381079019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4419048288209900699088101 828571554039356381079019)
                    ·
                      rfl

theorem cell23_4840912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 8, 1, 4].length) (baseStart_4840912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840912 prefixEnd_4840912 := by exact prefixLift 4840912
  have htrace : WordTrace (prefixWord ++ tailWord_4840912) baseStart_4840912 baseEnd_4840912 := by
    simpa [prefixWord, tailWord_4840912, baseEnd_4840912] using wordTrace_append hprefix tailTrace_4840912
  have hstable : (prefixWord ++ tailWord_4840912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840912).length < 2 ^ (prefixWord ++ tailWord_4840912).sum := by decide
  have hdescent : baseEnd_4840912 < baseStart_4840912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840928 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 6]
def baseStart_4840928 : Nat := 118140960795 + 4840928 * 2 ^ 59
def prefixEnd_4840928 : Nat := 4983230072969 + 3 ^ 40 * 4840928 * 2
def baseEnd_4840928 : Nat := 2485722877808541080636983

theorem tailTrace_4840928 : CollatzResearch.WordTrace tailWord_4840928 prefixEnd_4840928 2485722877808541080636983 := by
  unfold tailWord_4840928
  simp only [CollatzResearch.WordTrace]
  refine ⟨88281574703076047762705719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117708766270768063683607625 88281574703076047762705719)
  ·
    refine ⟨132422362054614071644058579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88281574703076047762705719 132422362054614071644058579)
    ·
      refine ⟨198633543081921107466087869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132422362054614071644058579 198633543081921107466087869)
      ·
        refine ⟨74487578655720415299782951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198633543081921107466087869 74487578655720415299782951)
        ·
          refine ⟨111731367983580622949674427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74487578655720415299782951 111731367983580622949674427)
          ·
            refine ⟨167597051975370934424511641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111731367983580622949674427 167597051975370934424511641)
            ·
              refine ⟨125697788981528200818383731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167597051975370934424511641 125697788981528200818383731)
              ·
                refine ⟨188546683472292301227575597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125697788981528200818383731 188546683472292301227575597)
                ·
                  refine ⟨70705006302109612960340849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 188546683472292301227575597 70705006302109612960340849)
                  ·
                    refine ⟨53028754726582209720255637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 70705006302109612960340849 53028754726582209720255637)
                    ·
                      refine ⟨2485722877808541080636983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53028754726582209720255637 2485722877808541080636983)
                      ·
                        rfl

theorem cell23_4840928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_4840928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840928 prefixEnd_4840928 := by exact prefixLift 4840928
  have htrace : WordTrace (prefixWord ++ tailWord_4840928) baseStart_4840928 baseEnd_4840928 := by
    simpa [prefixWord, tailWord_4840928, baseEnd_4840928] using wordTrace_append hprefix tailTrace_4840928
  have hstable : (prefixWord ++ tailWord_4840928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840928).length < 2 ^ (prefixWord ++ tailWord_4840928).sum := by decide
  have hdescent : baseEnd_4840928 < baseStart_4840928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840946 : List Nat := [3, 2, 1, 4, 1, 2, 2, 3, 1, 4]
def baseStart_4840946 : Nat := 118140960795 + 4840946 * 2 ^ 59
def prefixEnd_4840946 : Nat := 4983230072969 + 3 ^ 40 * 4840946 * 2
def baseEnd_4840946 : Nat := 828577373486774003403967

theorem tailTrace_4840946 : CollatzResearch.WordTrace tailWord_4840946 prefixEnd_4840946 828577373486774003403967 := by
  unfold tailWord_4840946
  simp only [CollatzResearch.WordTrace]
  refine ⟨44140951480021721149891673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117709203946724589733044461 44140951480021721149891673)
  ·
    refine ⟨33105713610016290862418755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44140951480021721149891673 33105713610016290862418755)
    ·
      refine ⟨49658570415024436293628133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33105713610016290862418755 49658570415024436293628133)
      ·
        refine ⟨9310981952817081805055275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49658570415024436293628133 9310981952817081805055275)
        ·
          refine ⟨13966472929225622707582913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9310981952817081805055275 13966472929225622707582913)
          ·
            refine ⟨10474854696919217030687185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13966472929225622707582913 10474854696919217030687185)
            ·
              refine ⟨7856141022689412773015389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10474854696919217030687185 7856141022689412773015389)
              ·
                refine ⟨2946052883508529789880771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7856141022689412773015389 2946052883508529789880771)
                ·
                  refine ⟨4419079325262794684821157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2946052883508529789880771 4419079325262794684821157)
                  ·
                    refine ⟨828577373486774003403967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4419079325262794684821157 828577373486774003403967)
                    ·
                      rfl

theorem cell23_4840946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 3, 1, 4].length) (baseStart_4840946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840946 prefixEnd_4840946 := by exact prefixLift 4840946
  have htrace : WordTrace (prefixWord ++ tailWord_4840946) baseStart_4840946 baseEnd_4840946 := by
    simpa [prefixWord, tailWord_4840946, baseEnd_4840946] using wordTrace_append hprefix tailTrace_4840946
  have hstable : (prefixWord ++ tailWord_4840946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840946).length < 2 ^ (prefixWord ++ tailWord_4840946).sum := by decide
  have hdescent : baseEnd_4840946 < baseStart_4840946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840955 : List Nat := [1, 1, 1, 1, 1, 3, 2, 7, 1, 5]
def baseStart_4840955 : Nat := 118140960795 + 4840955 * 2 ^ 59
def prefixEnd_4840955 : Nat := 4983230072969 + 3 ^ 40 * 4840955 * 2
def baseEnd_4840955 : Nat := 828578913928737491666453

theorem tailTrace_4840955 : CollatzResearch.WordTrace tailWord_4840955 prefixEnd_4840955 828578913928737491666453 := by
  unfold tailWord_4840955
  simp only [CollatzResearch.WordTrace]
  refine ⟨176564134177054279136644319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117709422784702852757762879 176564134177054279136644319)
  ·
    refine ⟨264846201265581418704966479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176564134177054279136644319 264846201265581418704966479)
    ·
      refine ⟨397269301898372128057449719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264846201265581418704966479 397269301898372128057449719)
      ·
        refine ⟨595903952847558192086174579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397269301898372128057449719 595903952847558192086174579)
        ·
          refine ⟨893855929271337288129261869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 595903952847558192086174579 893855929271337288129261869)
          ·
            refine ⟨335195973476751483048473201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 893855929271337288129261869 335195973476751483048473201)
            ·
              refine ⟨251396980107563612286354901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335195973476751483048473201 251396980107563612286354901)
              ·
                refine ⟨5892116721271022162961443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 251396980107563612286354901 5892116721271022162961443)
                ·
                  refine ⟨8838175081906533244442165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5892116721271022162961443 8838175081906533244442165)
                  ·
                    refine ⟨828578913928737491666453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8838175081906533244442165 828578913928737491666453)
                    ·
                      rfl

theorem cell23_4840955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 5].length) (baseStart_4840955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840955 prefixEnd_4840955 := by exact prefixLift 4840955
  have htrace : WordTrace (prefixWord ++ tailWord_4840955) baseStart_4840955 baseEnd_4840955 := by
    simpa [prefixWord, tailWord_4840955, baseEnd_4840955] using wordTrace_append hprefix tailTrace_4840955
  have hstable : (prefixWord ++ tailWord_4840955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840955).length < 2 ^ (prefixWord ++ tailWord_4840955).sum := by decide
  have hdescent : baseEnd_4840955 < baseStart_4840955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840962 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_4840962 : Nat := 118140960795 + 4840962 * 2 ^ 59
def prefixEnd_4840962 : Nat := 4983230072969 + 3 ^ 40 * 4840962 * 2
def baseEnd_4840962 : Nat := 2485740336150793947611827

theorem tailTrace_4840962 : CollatzResearch.WordTrace tailWord_4840962 prefixEnd_4840962 2485740336150793947611827 := by
  unfold tailWord_4840962
  simp only [CollatzResearch.WordTrace]
  refine ⟨44141097372007229833037285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117709592992019279554766093 44141097372007229833037285)
  ·
    refine ⟨8276455757251355593694491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44141097372007229833037285 8276455757251355593694491)
    ·
      refine ⟨12414683635877033390541737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8276455757251355593694491 12414683635877033390541737)
      ·
        refine ⟨9311012726907775042906303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12414683635877033390541737 9311012726907775042906303)
        ·
          refine ⟨13966519090361662564359455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9311012726907775042906303 13966519090361662564359455)
          ·
            refine ⟨20949778635542493846539183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13966519090361662564359455 20949778635542493846539183)
            ·
              refine ⟨31424667953313740769808775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20949778635542493846539183 31424667953313740769808775)
              ·
                refine ⟨47137001929970611154713163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31424667953313740769808775 47137001929970611154713163)
                ·
                  refine ⟨70705502894955916732069745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47137001929970611154713163 70705502894955916732069745)
                  ·
                    refine ⟨53029127171216937549052309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 70705502894955916732069745 53029127171216937549052309)
                    ·
                      refine ⟨2485740336150793947611827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53029127171216937549052309 2485740336150793947611827)
                      ·
                        rfl

theorem cell23_4840962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_4840962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840962 prefixEnd_4840962 := by exact prefixLift 4840962
  have htrace : WordTrace (prefixWord ++ tailWord_4840962) baseStart_4840962 baseEnd_4840962 := by
    simpa [prefixWord, tailWord_4840962, baseEnd_4840962] using wordTrace_append hprefix tailTrace_4840962
  have hstable : (prefixWord ++ tailWord_4840962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840962).length < 2 ^ (prefixWord ++ tailWord_4840962).sum := by decide
  have hdescent : baseEnd_4840962 < baseStart_4840962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840969 : List Nat := [1, 2, 1, 1, 3, 1, 3, 6, 1, 1, 3]
def baseStart_4840969 : Nat := 118140960795 + 4840969 * 2 ^ 59
def prefixEnd_4840969 : Nat := 4983230072969 + 3 ^ 40 * 4840969 * 2
def baseEnd_4840969 : Nat := 2485743930515375420224295

theorem tailTrace_4840969 : CollatzResearch.WordTrace tailWord_4840969 prefixEnd_4840969 2485743930515375420224295 := by
  unfold tailWord_4840969
  simp only [CollatzResearch.WordTrace]
  refine ⟨176564644799003559527653961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117709763199335706351769307 176564644799003559527653961)
  ·
    refine ⟨132423483599252669645740471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176564644799003559527653961 132423483599252669645740471)
    ·
      refine ⟨198635225398879004468610707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132423483599252669645740471 198635225398879004468610707)
      ·
        refine ⟨297952838098318506702916061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198635225398879004468610707 297952838098318506702916061)
        ·
          refine ⟨111732314286869440013593523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 297952838098318506702916061 111732314286869440013593523)
          ·
            refine ⟨167598471430304160020390285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111732314286869440013593523 167598471430304160020390285)
            ·
              refine ⟨62849426786364060007646357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167598471430304160020390285 62849426786364060007646357)
              ·
                refine ⟨2946066880610815312858423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62849426786364060007646357 2946066880610815312858423)
                ·
                  refine ⟨4419100320916222969287635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2946066880610815312858423 4419100320916222969287635)
                  ·
                    refine ⟨6628650481374334453931453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4419100320916222969287635 6628650481374334453931453)
                    ·
                      refine ⟨2485743930515375420224295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6628650481374334453931453 2485743930515375420224295)
                      ·
                        rfl

theorem cell23_4840969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 6, 1, 1, 3].length) (baseStart_4840969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840969 prefixEnd_4840969 := by exact prefixLift 4840969
  have htrace : WordTrace (prefixWord ++ tailWord_4840969) baseStart_4840969 baseEnd_4840969 := by
    simpa [prefixWord, tailWord_4840969, baseEnd_4840969] using wordTrace_append hprefix tailTrace_4840969
  have hstable : (prefixWord ++ tailWord_4840969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840969).length < 2 ^ (prefixWord ++ tailWord_4840969).sum := by decide
  have hdescent : baseEnd_4840969 < baseStart_4840969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4840985 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 8, 4]
def baseStart_4840985 : Nat := 118140960795 + 4840985 * 2 ^ 59
def prefixEnd_4840985 : Nat := 4983230072969 + 3 ^ 40 * 4840985 * 2
def baseEnd_4840985 : Nat := 828584048735282452541407

theorem tailTrace_4840985 : CollatzResearch.WordTrace tailWord_4840985 prefixEnd_4840985 828584048735282452541407 := by
  unfold tailWord_4840985
  simp only [CollatzResearch.WordTrace]
  refine ⟨176565228366945594260236409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117710152244630396173490939 176565228366945594260236409)
  ·
    refine ⟨132423921275209195695177307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176565228366945594260236409 132423921275209195695177307)
    ·
      refine ⟨198635881912813793542765961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132423921275209195695177307 198635881912813793542765961)
      ·
        refine ⟨148976911434610345157074471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198635881912813793542765961 148976911434610345157074471)
        ·
          refine ⟨223465367151915517735611707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148976911434610345157074471 223465367151915517735611707)
          ·
            refine ⟨335198050727873276603417561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223465367151915517735611707 335198050727873276603417561)
            ·
              refine ⟨251398538045904957452563171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335198050727873276603417561 251398538045904957452563171)
              ·
                refine ⟨377097807068857436178844757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251398538045904957452563171 377097807068857436178844757)
                ·
                  refine ⟨4419114926588173080220837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 377097807068857436178844757 4419114926588173080220837)
                  ·
                    refine ⟨828584048735282452541407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4419114926588173080220837 828584048735282452541407)
                    ·
                      rfl

theorem cell23_4840985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 8, 4].length) (baseStart_4840985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4840985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4840985 prefixEnd_4840985 := by exact prefixLift 4840985
  have htrace : WordTrace (prefixWord ++ tailWord_4840985) baseStart_4840985 baseEnd_4840985 := by
    simpa [prefixWord, tailWord_4840985, baseEnd_4840985] using wordTrace_append hprefix tailTrace_4840985
  have hstable : (prefixWord ++ tailWord_4840985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4840985).length < 2 ^ (prefixWord ++ tailWord_4840985).sum := by decide
  have hdescent : baseEnd_4840985 < baseStart_4840985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4840985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841002 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 6, 4]
def baseStart_4841002 : Nat := 118140960795 + 4841002 * 2 ^ 59
def prefixEnd_4841002 : Nat := 4983230072969 + 3 ^ 40 * 4841002 * 2
def baseEnd_4841002 : Nat := 828586958458991263703881

theorem tailTrace_4841002 : CollatzResearch.WordTrace tailWord_4841002 prefixEnd_4841002 828586958458991263703881 := by
  unfold tailWord_4841002
  simp only [CollatzResearch.WordTrace]
  refine ⟨44141462101971001540901315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117710565605256004109070173 44141462101971001540901315)
  ·
    refine ⟨66212193152956502311351973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44141462101971001540901315 66212193152956502311351973)
    ·
      refine ⟨12414786216179344183378495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66212193152956502311351973 12414786216179344183378495)
      ·
        refine ⟨18622179324269016275067743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12414786216179344183378495 18622179324269016275067743)
        ·
          refine ⟨27933268986403524412601615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18622179324269016275067743 27933268986403524412601615)
          ·
            refine ⟨41899903479605286618902423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27933268986403524412601615 41899903479605286618902423)
            ·
              refine ⟨62849855219407929928353635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41899903479605286618902423 62849855219407929928353635)
              ·
                refine ⟨94274782829111894892530453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62849855219407929928353635 94274782829111894892530453)
                ·
                  refine ⟨4419130445114620073087365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 94274782829111894892530453 4419130445114620073087365)
                  ·
                    refine ⟨828586958458991263703881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4419130445114620073087365 828586958458991263703881)
                    ·
                      rfl

theorem cell23_4841002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_4841002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841002 prefixEnd_4841002 := by exact prefixLift 4841002
  have htrace : WordTrace (prefixWord ++ tailWord_4841002) baseStart_4841002 baseEnd_4841002 := by
    simpa [prefixWord, tailWord_4841002, baseEnd_4841002] using wordTrace_append hprefix tailTrace_4841002
  have hstable : (prefixWord ++ tailWord_4841002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841002).length < 2 ^ (prefixWord ++ tailWord_4841002).sum := by decide
  have hdescent : baseEnd_4841002 < baseStart_4841002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841015 : List Nat := [1, 1, 3, 1, 2, 6, 9]
def baseStart_4841015 : Nat := 118140960795 + 4841015 * 2 ^ 59
def prefixEnd_4841015 : Nat := 4983230072969 + 3 ^ 40 * 4841015 * 2
def baseEnd_4841015 : Nat := 30688488279326941237643

theorem tailTrace_4841015 : CollatzResearch.WordTrace tailWord_4841015 prefixEnd_4841015 30688488279326941237643 := by
  unfold tailWord_4841015
  simp only [CollatzResearch.WordTrace]
  refine ⟨176566322556836909383828499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117710881704557939589218999 176566322556836909383828499)
  ·
    refine ⟨264849483835255364075742749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176566322556836909383828499 264849483835255364075742749)
    ·
      refine ⟨99318556438220761528403531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 264849483835255364075742749 99318556438220761528403531)
      ·
        refine ⟨148977834657331142292605297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99318556438220761528403531 148977834657331142292605297)
        ·
          refine ⟨111733375992998356719453973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148977834657331142292605297 111733375992998356719453973)
          ·
            refine ⟨5237501999671797971224405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 111733375992998356719453973 5237501999671797971224405)
            ·
              refine ⟨30688488279326941237643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5237501999671797971224405 30688488279326941237643)
              ·
                rfl

theorem cell23_4841015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 9].length) (baseStart_4841015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841015 prefixEnd_4841015 := by exact prefixLift 4841015
  have htrace : WordTrace (prefixWord ++ tailWord_4841015) baseStart_4841015 baseEnd_4841015 := by
    simpa [prefixWord, tailWord_4841015, baseEnd_4841015] using wordTrace_append hprefix tailTrace_4841015
  have hstable : (prefixWord ++ tailWord_4841015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841015).length < 2 ^ (prefixWord ++ tailWord_4841015).sum := by decide
  have hdescent : baseEnd_4841015 < baseStart_4841015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841036 : List Nat := [2, 2, 1, 3, 1, 5, 2, 1, 2, 4]
def baseStart_4841036 : Nat := 118140960795 + 4841036 * 2 ^ 59
def prefixEnd_4841036 : Nat := 4983230072969 + 3 ^ 40 * 4841036 * 2
def baseEnd_4841036 : Nat := 828592777906408886028829

theorem tailTrace_4841036 : CollatzResearch.WordTrace tailWord_4841036 prefixEnd_4841036 828592777906408886028829 := by
  unfold tailWord_4841036
  simp only [CollatzResearch.WordTrace]
  refine ⟨88283544244880414985171481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117711392326507219980228641 88283544244880414985171481)
  ·
    refine ⟨66212658183660311238878611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88283544244880414985171481 66212658183660311238878611)
    ·
      refine ⟨99318987275490466858317917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66212658183660311238878611 99318987275490466858317917)
      ·
        refine ⟨37244620228308925071869219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99318987275490466858317917 37244620228308925071869219)
        ·
          refine ⟨55866930342463387607803829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37244620228308925071869219 55866930342463387607803829)
          ·
            refine ⟨5237524719605942588231609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55866930342463387607803829 5237524719605942588231609)
            ·
              refine ⟨3928143539704456941173707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5237524719605942588231609 3928143539704456941173707)
              ·
                refine ⟨5892215309556685411760561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3928143539704456941173707 5892215309556685411760561)
                ·
                  refine ⟨4419161482167514058820421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5892215309556685411760561 4419161482167514058820421)
                  ·
                    refine ⟨828592777906408886028829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4419161482167514058820421 828592777906408886028829)
                    ·
                      rfl

theorem cell23_4841036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 2, 4].length) (baseStart_4841036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841036 prefixEnd_4841036 := by exact prefixLift 4841036
  have htrace : WordTrace (prefixWord ++ tailWord_4841036) baseStart_4841036 baseEnd_4841036 := by
    simpa [prefixWord, tailWord_4841036, baseEnd_4841036] using wordTrace_append hprefix tailTrace_4841036
  have hstable : (prefixWord ++ tailWord_4841036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841036).length < 2 ^ (prefixWord ++ tailWord_4841036).sum := by decide
  have hdescent : baseEnd_4841036 < baseStart_4841036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841077 : List Nat := [1, 3, 4, 2, 1, 3, 2, 2, 1, 2, 2]
def baseStart_4841077 : Nat := 118140960795 + 4841077 * 2 ^ 59
def prefixEnd_4841077 : Nat := 4983230072969 + 3 ^ 40 * 4841077 * 2
def baseEnd_4841077 : Nat := 2485799386426060997673799

theorem tailTrace_4841077 : CollatzResearch.WordTrace tailWord_4841077 prefixEnd_4841077 2485799386426060997673799 := by
  unfold tailWord_4841077
  simp only [CollatzResearch.WordTrace]
  refine ⟨176568583882612293972585485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117712389255074862648390323 176568583882612293972585485)
  ·
    refine ⟨66213218955979610239719557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176568583882612293972585485 66213218955979610239719557)
    ·
      refine ⟨12414978554246176919947417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66213218955979610239719557 12414978554246176919947417)
      ·
        refine ⟨9311233915684632689960563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12414978554246176919947417 9311233915684632689960563)
        ·
          refine ⟨13966850873526949034940845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9311233915684632689960563 13966850873526949034940845)
          ·
            refine ⟨5237569077572605888102817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13966850873526949034940845 5237569077572605888102817)
            ·
              refine ⟨3928176808179454416077113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5237569077572605888102817 3928176808179454416077113)
              ·
                refine ⟨2946132606134590812057835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3928176808179454416077113 2946132606134590812057835)
                ·
                  refine ⟨4419198909201886218086753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2946132606134590812057835 4419198909201886218086753)
                  ·
                    refine ⟨3314399181901414663565065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4419198909201886218086753 3314399181901414663565065)
                    ·
                      refine ⟨2485799386426060997673799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3314399181901414663565065 2485799386426060997673799)
                      ·
                        rfl

theorem cell23_4841077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_4841077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841077 prefixEnd_4841077 := by exact prefixLift 4841077
  have htrace : WordTrace (prefixWord ++ tailWord_4841077) baseStart_4841077 baseEnd_4841077 := by
    simpa [prefixWord, tailWord_4841077, baseEnd_4841077] using wordTrace_append hprefix tailTrace_4841077
  have hstable : (prefixWord ++ tailWord_4841077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841077).length < 2 ^ (prefixWord ++ tailWord_4841077).sum := by decide
  have hdescent : baseEnd_4841077 < baseStart_4841077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841099 : List Nat := [1, 1, 1, 1, 4, 1, 6, 1, 1, 4, 2]
def baseStart_4841099 : Nat := 118140960795 + 4841099 * 2 ^ 59
def prefixEnd_4841099 : Nat := 4983230072969 + 3 ^ 40 * 4841099 * 2
def baseEnd_4841099 : Nat := 2485810683000459911598697

theorem tailTrace_4841099 : CollatzResearch.WordTrace tailWord_4841099 prefixEnd_4841099 2485810683000459911598697 := by
  unfold tailWord_4841099
  simp only [CollatzResearch.WordTrace]
  refine ⟨176569386288532591729886351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117712924192355061153257567 176569386288532591729886351)
  ·
    refine ⟨264854079432798887594829527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176569386288532591729886351 264854079432798887594829527)
    ·
      refine ⟨397281119149198331392244291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264854079432798887594829527 397281119149198331392244291)
      ·
        refine ⟨595921678723797497088366437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397281119149198331392244291 595921678723797497088366437)
        ·
          refine ⟨111735314760712030704068707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 595921678723797497088366437 111735314760712030704068707)
          ·
            refine ⟨167602972141068046056103061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111735314760712030704068707 167602972141068046056103061)
            ·
              refine ⟨7856389319112564658879831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 167602972141068046056103061 7856389319112564658879831)
              ·
                refine ⟨11784583978668846988319747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7856389319112564658879831 11784583978668846988319747)
                ·
                  refine ⟨17676875968003270482479621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11784583978668846988319747 17676875968003270482479621)
                  ·
                    refine ⟨3314414244000613215464929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17676875968003270482479621 3314414244000613215464929)
                    ·
                      refine ⟨2485810683000459911598697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3314414244000613215464929 2485810683000459911598697)
                      ·
                        rfl

theorem cell23_4841099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 4, 2].length) (baseStart_4841099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841099 prefixEnd_4841099 := by exact prefixLift 4841099
  have htrace : WordTrace (prefixWord ++ tailWord_4841099) baseStart_4841099 baseEnd_4841099 := by
    simpa [prefixWord, tailWord_4841099, baseEnd_4841099] using wordTrace_append hprefix tailTrace_4841099
  have hstable : (prefixWord ++ tailWord_4841099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841099).length < 2 ^ (prefixWord ++ tailWord_4841099).sum := by decide
  have hdescent : baseEnd_4841099 < baseStart_4841099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841150 : List Nat := [4, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2]
def baseStart_4841150 : Nat := 118140960795 + 4841150 * 2 ^ 59
def prefixEnd_4841150 : Nat := 4983230072969 + 3 ^ 40 * 4841150 * 2
def baseEnd_4841150 : Nat := 2485836870513839212060963

theorem tailTrace_4841150 : CollatzResearch.WordTrace tailWord_4841150 prefixEnd_4841150 2485836870513839212060963 := by
  unfold tailWord_4841150
  simp only [CollatzResearch.WordTrace]
  refine ⟨22071405801418478429999113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117714164274231884959995269 22071405801418478429999113)
  ·
    refine ⟨16553554351063858822499335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22071405801418478429999113 16553554351063858822499335)
    ·
      refine ⟨24830331526595788233749003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16553554351063858822499335 24830331526595788233749003)
      ·
        refine ⟨37245497289893682350623505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24830331526595788233749003 37245497289893682350623505)
        ·
          refine ⟨27934122967420261762967629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37245497289893682350623505 27934122967420261762967629)
          ·
            refine ⟨10475296112782598161112861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27934122967420261762967629 10475296112782598161112861)
            ·
              refine ⟨3928236042293474310417323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10475296112782598161112861 3928236042293474310417323)
              ·
                refine ⟨5892354063440211465625985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3928236042293474310417323 5892354063440211465625985)
                ·
                  refine ⟨4419265547580158599219489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5892354063440211465625985 4419265547580158599219489)
                  ·
                    refine ⟨3314449160685118949414617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4419265547580158599219489 3314449160685118949414617)
                    ·
                      refine ⟨2485836870513839212060963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3314449160685118949414617 2485836870513839212060963)
                      ·
                        rfl

theorem cell23_4841150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_4841150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841150 prefixEnd_4841150 := by exact prefixLift 4841150
  have htrace : WordTrace (prefixWord ++ tailWord_4841150) baseStart_4841150 baseEnd_4841150 := by
    simpa [prefixWord, tailWord_4841150, baseEnd_4841150] using wordTrace_append hprefix tailTrace_4841150
  have hstable : (prefixWord ++ tailWord_4841150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841150).length < 2 ^ (prefixWord ++ tailWord_4841150).sum := by decide
  have hdescent : baseEnd_4841150 < baseStart_4841150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841189 : List Nat := [1, 3, 1, 4, 1, 1, 3, 2, 2, 1, 4]
def baseStart_4841189 : Nat := 118140960795 + 4841189 * 2 ^ 59
def prefixEnd_4841189 : Nat := 4983230072969 + 3 ^ 40 * 4841189 * 2
def baseEnd_4841189 : Nat := 2485856896259364559473283

theorem tailTrace_4841189 : CollatzResearch.WordTrace tailWord_4841189 prefixEnd_4841189 2485856896259364559473283 := by
  unfold tailWord_4841189
  simp only [CollatzResearch.WordTrace]
  refine ⟨176572668858206537100662621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117715112572137691400441747 176572668858206537100662621)
  ·
    refine ⟨66214750821827451412748483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176572668858206537100662621 66214750821827451412748483)
    ·
      refine ⟨99322126232741177119122725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66214750821827451412748483 99322126232741177119122725)
      ·
        refine ⟨18622898668638970709835511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99322126232741177119122725 18622898668638970709835511)
        ·
          refine ⟨27934348002958456064753267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18622898668638970709835511 27934348002958456064753267)
          ·
            refine ⟨41901522004437684097129901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27934348002958456064753267 41901522004437684097129901)
            ·
              refine ⟨15713070751664131536423713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41901522004437684097129901 15713070751664131536423713)
              ·
                refine ⟨11784803063748098652317785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15713070751664131536423713 11784803063748098652317785)
                ·
                  refine ⟨8838602297811073989238339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11784803063748098652317785 8838602297811073989238339)
                  ·
                    refine ⟨13257903446716610983857509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8838602297811073989238339 13257903446716610983857509)
                    ·
                      refine ⟨2485856896259364559473283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13257903446716610983857509 2485856896259364559473283)
                      ·
                        rfl

theorem cell23_4841189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_4841189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841189 prefixEnd_4841189 := by exact prefixLift 4841189
  have htrace : WordTrace (prefixWord ++ tailWord_4841189) baseStart_4841189 baseEnd_4841189 := by
    simpa [prefixWord, tailWord_4841189, baseEnd_4841189] using wordTrace_append hprefix tailTrace_4841189
  have hstable : (prefixWord ++ tailWord_4841189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841189).length < 2 ^ (prefixWord ++ tailWord_4841189).sum := by decide
  have hdescent : baseEnd_4841189 < baseStart_4841189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841226 : List Nat := [3, 1, 2, 2, 1, 4, 2, 1, 2, 2, 3]
def baseStart_4841226 : Nat := 118140960795 + 4841226 * 2 ^ 59
def prefixEnd_4841226 : Nat := 4983230072969 + 3 ^ 40 * 4841226 * 2
def baseEnd_4841226 : Nat := 2485875895043580914710613

theorem tailTrace_4841226 : CollatzResearch.WordTrace tailWord_4841226 prefixEnd_4841226 2485875895043580914710613 := by
  unfold tailWord_4841226
  simp only [CollatzResearch.WordTrace]
  refine ⟨44143504589768123104939883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117716012239381661613173021 44143504589768123104939883)
  ·
    refine ⟨66215256884652184657409825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44143504589768123104939883 66215256884652184657409825)
    ·
      refine ⟨49661442663489138493057369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66215256884652184657409825 49661442663489138493057369)
      ·
        refine ⟨37246081997616853869793027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49661442663489138493057369 37246081997616853869793027)
        ·
          refine ⟨55869122996425280804689541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37246081997616853869793027 55869122996425280804689541)
          ·
            refine ⟨10475460561829740150879289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55869122996425280804689541 10475460561829740150879289)
            ·
              refine ⟨7856595421372305113159467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10475460561829740150879289 7856595421372305113159467)
              ·
                refine ⟨11784893132058457669739201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7856595421372305113159467 11784893132058457669739201)
                ·
                  refine ⟨8838669849043843252304401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11784893132058457669739201 8838669849043843252304401)
                  ·
                    refine ⟨6629002386782882439228301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8838669849043843252304401 6629002386782882439228301)
                    ·
                      refine ⟨2485875895043580914710613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6629002386782882439228301 2485875895043580914710613)
                      ·
                        rfl

theorem cell23_4841226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_4841226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841226 prefixEnd_4841226 := by exact prefixLift 4841226
  have htrace : WordTrace (prefixWord ++ tailWord_4841226) baseStart_4841226 baseEnd_4841226 := by
    simpa [prefixWord, tailWord_4841226, baseEnd_4841226] using wordTrace_append hprefix tailTrace_4841226
  have hstable : (prefixWord ++ tailWord_4841226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841226).length < 2 ^ (prefixWord ++ tailWord_4841226).sum := by decide
  have hdescent : baseEnd_4841226 < baseStart_4841226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841283 : List Nat := [1, 1, 1, 3, 1, 7, 1, 1, 2, 3, 2]
def baseStart_4841283 : Nat := 118140960795 + 4841283 * 2 ^ 59
def prefixEnd_4841283 : Nat := 4983230072969 + 3 ^ 40 * 4841283 * 2
def baseEnd_4841283 : Nat := 2485905163440887191697851

theorem tailTrace_4841283 : CollatzResearch.WordTrace tailWord_4841283 prefixEnd_4841283 2485905163440887191697851 := by
  unfold tailWord_4841283
  simp only [CollatzResearch.WordTrace]
  refine ⟨176576097319865991154584503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117717398213243994103056335 176576097319865991154584503)
  ·
    refine ⟨264864145979798986731876755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176576097319865991154584503 264864145979798986731876755)
    ·
      refine ⟨397296218969698480097815133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264864145979798986731876755 397296218969698480097815133)
      ·
        refine ⟨148986082113636930036680675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 397296218969698480097815133 148986082113636930036680675)
        ·
          refine ⟨223479123170455395055021013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148986082113636930036680675 223479123170455395055021013)
          ·
            refine ⟨5237791949307548321602055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 223479123170455395055021013 5237791949307548321602055)
            ·
              refine ⟨7856687923961322482403083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5237791949307548321602055 7856687923961322482403083)
              ·
                refine ⟨11785031885941983723604625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7856687923961322482403083 11785031885941983723604625)
                ·
                  refine ⟨8838773914456487792703469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11785031885941983723604625 8838773914456487792703469)
                  ·
                    refine ⟨3314540217921182922263801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8838773914456487792703469 3314540217921182922263801)
                    ·
                      refine ⟨2485905163440887191697851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3314540217921182922263801 2485905163440887191697851)
                      ·
                        rfl

theorem cell23_4841283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 3, 2].length) (baseStart_4841283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841283 prefixEnd_4841283 := by exact prefixLift 4841283
  have htrace : WordTrace (prefixWord ++ tailWord_4841283) baseStart_4841283 baseEnd_4841283 := by
    simpa [prefixWord, tailWord_4841283, baseEnd_4841283] using wordTrace_append hprefix tailTrace_4841283
  have hstable : (prefixWord ++ tailWord_4841283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841283).length < 2 ^ (prefixWord ++ tailWord_4841283).sum := by decide
  have hdescent : baseEnd_4841283 < baseStart_4841283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841289 : List Nat := [1, 2, 1, 1, 2, 4, 2, 2, 4, 4]
def baseStart_4841289 : Nat := 118140960795 + 4841289 * 2 ^ 59
def prefixEnd_4841289 : Nat := 4983230072969 + 3 ^ 40 * 4841289 * 2
def baseEnd_4841289 : Nat := 828636081441604722740941

theorem tailTrace_4841289 : CollatzResearch.WordTrace tailWord_4841289 prefixEnd_4841289 828636081441604722740941 := by
  unfold tailWord_4841289
  simp only [CollatzResearch.WordTrace]
  refine ⟨176576316157844254179302921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117717544105229502786201947 176576316157844254179302921)
  ·
    refine ⟨132432237118383190634477191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176576316157844254179302921 132432237118383190634477191)
    ·
      refine ⟨198648355677574785951715787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132432237118383190634477191 198648355677574785951715787)
      ·
        refine ⟨297972533516362178927573681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198648355677574785951715787 297972533516362178927573681)
        ·
          refine ⟨223479400137271634195680261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297972533516362178927573681 223479400137271634195680261)
          ·
            refine ⟨41902387525738431411690049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 223479400137271634195680261 41902387525738431411690049)
            ·
              refine ⟨31426790644303823558767537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41902387525738431411690049 31426790644303823558767537)
              ·
                refine ⟨23570092983227867669075653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31426790644303823558767537 23570092983227867669075653)
                ·
                  refine ⟨4419392434355225187951685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23570092983227867669075653 4419392434355225187951685)
                  ·
                    refine ⟨828636081441604722740941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4419392434355225187951685 828636081441604722740941)
                    ·
                      rfl

theorem cell23_4841289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 4, 4].length) (baseStart_4841289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841289 prefixEnd_4841289 := by exact prefixLift 4841289
  have htrace : WordTrace (prefixWord ++ tailWord_4841289) baseStart_4841289 baseEnd_4841289 := by
    simpa [prefixWord, tailWord_4841289, baseEnd_4841289] using wordTrace_append hprefix tailTrace_4841289
  have hstable : (prefixWord ++ tailWord_4841289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841289).length < 2 ^ (prefixWord ++ tailWord_4841289).sum := by decide
  have hdescent : baseEnd_4841289 < baseStart_4841289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841293 : List Nat := [1, 6, 1, 2, 1, 2, 1, 3, 1, 5]
def baseStart_4841293 : Nat := 118140960795 + 4841293 * 2 ^ 59
def prefixEnd_4841293 : Nat := 4983230072969 + 3 ^ 40 * 4841293 * 2
def baseEnd_4841293 : Nat := 828636766082477384190935

theorem tailTrace_4841293 : CollatzResearch.WordTrace tailWord_4841293 prefixEnd_4841293 828636766082477384190935 := by
  unfold tailWord_4841293
  simp only [CollatzResearch.WordTrace]
  refine ⟨176576462049829762862448533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117717641366553175241632355 176576462049829762862448533)
  ·
    refine ⟨8277021658585770134177275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 176576462049829762862448533 8277021658585770134177275)
    ·
      refine ⟨12415532487878655201265913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8277021658585770134177275 12415532487878655201265913)
      ·
        refine ⟨9311649365908991400949435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12415532487878655201265913 9311649365908991400949435)
        ·
          refine ⟨13967474048863487101424153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9311649365908991400949435 13967474048863487101424153)
          ·
            refine ⟨10475605536647615326068115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13967474048863487101424153 10475605536647615326068115)
            ·
              refine ⟨15713408304971422989102173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10475605536647615326068115 15713408304971422989102173)
              ·
                refine ⟨5892528114364283620913315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15713408304971422989102173 5892528114364283620913315)
                ·
                  refine ⟨8838792171546425431369973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5892528114364283620913315 8838792171546425431369973)
                  ·
                    refine ⟨828636766082477384190935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8838792171546425431369973 828636766082477384190935)
                    ·
                      rfl

theorem cell23_4841293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_4841293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841293 prefixEnd_4841293 := by exact prefixLift 4841293
  have htrace : WordTrace (prefixWord ++ tailWord_4841293) baseStart_4841293 baseEnd_4841293 := by
    simpa [prefixWord, tailWord_4841293, baseEnd_4841293] using wordTrace_append hprefix tailTrace_4841293
  have hstable : (prefixWord ++ tailWord_4841293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841293).length < 2 ^ (prefixWord ++ tailWord_4841293).sum := by decide
  have hdescent : baseEnd_4841293 < baseStart_4841293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841296 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 7, 2, 2]
def baseStart_4841296 : Nat := 118140960795 + 4841296 * 2 ^ 59
def prefixEnd_4841296 : Nat := 4983230072969 + 3 ^ 40 * 4841296 * 2
def baseEnd_4841296 : Nat := 2485911838689395640835291

theorem tailTrace_4841296 : CollatzResearch.WordTrace tailWord_4841296 prefixEnd_4841296 2485911838689395640835291 := by
  unfold tailWord_4841296
  simp only [CollatzResearch.WordTrace]
  refine ⟨88288285734409447187403871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117717714312545929583205161 88288285734409447187403871)
  ·
    refine ⟨132432428601614170781105807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88288285734409447187403871 132432428601614170781105807)
    ·
      refine ⟨198648642902421256171658711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132432428601614170781105807 198648642902421256171658711)
      ·
        refine ⟨297972964353631884257488067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198648642902421256171658711 297972964353631884257488067)
        ·
          refine ⟨446959446530447826386232101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297972964353631884257488067 446959446530447826386232101)
          ·
            refine ⟨83804896224458967447418519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 446959446530447826386232101 83804896224458967447418519)
            ·
              refine ⟨125707344336688451171127779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83804896224458967447418519 125707344336688451171127779)
              ·
                refine ⟨188561016505032676756691669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125707344336688451171127779 188561016505032676756691669)
                ·
                  refine ⟨4419398824336703361484961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 188561016505032676756691669 4419398824336703361484961)
                  ·
                    refine ⟨3314549118252527521113721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4419398824336703361484961 3314549118252527521113721)
                    ·
                      refine ⟨2485911838689395640835291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3314549118252527521113721 2485911838689395640835291)
                      ·
                        rfl

theorem cell23_4841296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 7, 2, 2].length) (baseStart_4841296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841296 prefixEnd_4841296 := by exact prefixLift 4841296
  have htrace : WordTrace (prefixWord ++ tailWord_4841296) baseStart_4841296 baseEnd_4841296 := by
    simpa [prefixWord, tailWord_4841296, baseEnd_4841296] using wordTrace_append hprefix tailTrace_4841296
  have hstable : (prefixWord ++ tailWord_4841296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841296).length < 2 ^ (prefixWord ++ tailWord_4841296).sum := by decide
  have hdescent : baseEnd_4841296 < baseStart_4841296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841313 : List Nat := [1, 2, 3, 1, 1, 1, 6, 1, 3, 2, 2]
def baseStart_4841313 : Nat := 118140960795 + 4841313 * 2 ^ 59
def prefixEnd_4841313 : Nat := 4983230072969 + 3 ^ 40 * 4841313 * 2
def baseEnd_4841313 : Nat := 2485920567860522074322713

theorem tailTrace_4841313 : CollatzResearch.WordTrace tailWord_4841313 prefixEnd_4841313 2485920567860522074322713 := by
  unfold tailWord_4841313
  simp only [CollatzResearch.WordTrace]
  refine ⟨176577191509757306278176593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117718127673171537518784395 176577191509757306278176593)
  ·
    refine ⟨132432893632317979708632445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176577191509757306278176593 132432893632317979708632445)
    ·
      refine ⟨49662335112119242390737167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132432893632317979708632445 49662335112119242390737167)
      ·
        refine ⟨74493502668178863586105751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49662335112119242390737167 74493502668178863586105751)
        ·
          refine ⟨111740254002268295379158627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74493502668178863586105751 111740254002268295379158627)
          ·
            refine ⟨167610381003402443068737941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111740254002268295379158627 167610381003402443068737941)
            ·
              refine ⟨7856736609534489518847091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 167610381003402443068737941 7856736609534489518847091)
              ·
                refine ⟨11785104914301734278270637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7856736609534489518847091 11785104914301734278270637)
                ·
                  refine ⟨4419414342863150354351489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11785104914301734278270637 4419414342863150354351489)
                  ·
                    refine ⟨3314560757147362765763617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4419414342863150354351489 3314560757147362765763617)
                    ·
                      refine ⟨2485920567860522074322713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3314560757147362765763617 2485920567860522074322713)
                      ·
                        rfl

theorem cell23_4841313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 3, 2, 2].length) (baseStart_4841313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841313 prefixEnd_4841313 := by exact prefixLift 4841313
  have htrace : WordTrace (prefixWord ++ tailWord_4841313) baseStart_4841313 baseEnd_4841313 := by
    simpa [prefixWord, tailWord_4841313, baseEnd_4841313] using wordTrace_append hprefix tailTrace_4841313
  have hstable : (prefixWord ++ tailWord_4841313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841313).length < 2 ^ (prefixWord ++ tailWord_4841313).sum := by decide
  have hdescent : baseEnd_4841313 < baseStart_4841313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841316 : List Nat := [2, 3, 1, 1, 5, 1, 1, 2, 1, 1, 5]
def baseStart_4841316 : Nat := 118140960795 + 4841316 * 2 ^ 59
def prefixEnd_4841316 : Nat := 4983230072969 + 3 ^ 40 * 4841316 * 2
def baseEnd_4841316 : Nat := 2485922108302485562585199

theorem tailTrace_4841316 : CollatzResearch.WordTrace tailWord_4841316 prefixEnd_4841316 2485922108302485562585199 := by
  unfold tailWord_4841316
  simp only [CollatzResearch.WordTrace]
  refine ⟨88288650464373218895267901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117718200619164291860357201 88288650464373218895267901)
  ·
    refine ⟨33108243924139957085725463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88288650464373218895267901 33108243924139957085725463)
    ·
      refine ⟨49662365886209935628588195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33108243924139957085725463 49662365886209935628588195)
      ·
        refine ⟨74493548829314903442882293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49662365886209935628588195 74493548829314903442882293)
        ·
          refine ⟨6983770202748272197770215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74493548829314903442882293 6983770202748272197770215)
          ·
            refine ⟨10475655304122408296655323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6983770202748272197770215 10475655304122408296655323)
            ·
              refine ⟨15713482956183612444982985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10475655304122408296655323 15713482956183612444982985)
              ·
                refine ⟨11785112217137709333737239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15713482956183612444982985 11785112217137709333737239)
                ·
                  refine ⟨17677668325706564000605859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11785112217137709333737239 17677668325706564000605859)
                  ·
                    refine ⟨26516502488559846000908789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17677668325706564000605859 26516502488559846000908789)
                    ·
                      refine ⟨2485922108302485562585199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26516502488559846000908789 2485922108302485562585199)
                      ·
                        rfl

theorem cell23_4841316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_4841316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841316 prefixEnd_4841316 := by exact prefixLift 4841316
  have htrace : WordTrace (prefixWord ++ tailWord_4841316) baseStart_4841316 baseEnd_4841316 := by
    simpa [prefixWord, tailWord_4841316, baseEnd_4841316] using wordTrace_append hprefix tailTrace_4841316
  have hstable : (prefixWord ++ tailWord_4841316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841316).length < 2 ^ (prefixWord ++ tailWord_4841316).sum := by decide
  have hdescent : baseEnd_4841316 < baseStart_4841316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841326 : List Nat := [4, 1, 2, 3, 1, 2, 1, 1, 1, 1, 6]
def baseStart_4841326 : Nat := 118140960795 + 4841326 * 2 ^ 59
def prefixEnd_4841326 : Nat := 4983230072969 + 3 ^ 40 * 4841326 * 2
def baseEnd_4841326 : Nat := 2485927243109030523460153

theorem tailTrace_4841326 : CollatzResearch.WordTrace tailWord_4841326 prefixEnd_4841326 2485927243109030523460153 := by
  unfold tailWord_4841326
  simp only [CollatzResearch.WordTrace]
  refine ⟨22072208207338776187299979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117718443772473472998933221 22072208207338776187299979)
  ·
    refine ⟨33108312311008164280949969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22072208207338776187299979 33108312311008164280949969)
    ·
      refine ⟨24831234233256123210712477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33108312311008164280949969 24831234233256123210712477)
      ·
        refine ⟨9311712837471046204017179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24831234233256123210712477 9311712837471046204017179)
        ·
          refine ⟨13967569256206569306025769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9311712837471046204017179 13967569256206569306025769)
          ·
            refine ⟨10475676942154926979519327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13967569256206569306025769 10475676942154926979519327)
            ·
              refine ⟨15713515413232390469278991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10475676942154926979519327 15713515413232390469278991)
              ·
                refine ⟨23570273119848585703918487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15713515413232390469278991 23570273119848585703918487)
                ·
                  refine ⟨35355409679772878555877731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23570273119848585703918487 35355409679772878555877731)
                  ·
                    refine ⟨53033114519659317833816597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35355409679772878555877731 53033114519659317833816597)
                    ·
                      refine ⟨2485927243109030523460153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53033114519659317833816597 2485927243109030523460153)
                      ·
                        rfl

theorem cell23_4841326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_4841326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841326 prefixEnd_4841326 := by exact prefixLift 4841326
  have htrace : WordTrace (prefixWord ++ tailWord_4841326) baseStart_4841326 baseEnd_4841326 := by
    simpa [prefixWord, tailWord_4841326, baseEnd_4841326] using wordTrace_append hprefix tailTrace_4841326
  have hstable : (prefixWord ++ tailWord_4841326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841326).length < 2 ^ (prefixWord ++ tailWord_4841326).sum := by decide
  have hdescent : baseEnd_4841326 < baseStart_4841326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841333 : List Nat := [1, 3, 4, 1, 1, 1, 4, 2, 1, 2, 3]
def baseStart_4841333 : Nat := 118140960795 + 4841333 * 2 ^ 59
def prefixEnd_4841333 : Nat := 4983230072969 + 3 ^ 40 * 4841333 * 2
def baseEnd_4841333 : Nat := 2485930837473611996072621

theorem tailTrace_4841333 : CollatzResearch.WordTrace tailWord_4841333 prefixEnd_4841333 2485930837473611996072621 := by
  unfold tailWord_4841333
  simp only [CollatzResearch.WordTrace]
  refine ⟨176577920969684849693904653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117718613979789899795936435 176577920969684849693904653)
  ·
    refine ⟨66216720363631818635214245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176577920969684849693904653 66216720363631818635214245)
    ·
      refine ⟨12415635068180965994102671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66216720363631818635214245 12415635068180965994102671)
      ·
        refine ⟨18623452602271448991154007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12415635068180965994102671 18623452602271448991154007)
        ·
          refine ⟨27935178903407173486731011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18623452602271448991154007 27935178903407173486731011)
          ·
            refine ⟨41902768355110760230096517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27935178903407173486731011 41902768355110760230096517)
            ·
              refine ⟨7856769066583267543143097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41902768355110760230096517 7856769066583267543143097)
              ·
                refine ⟨5892576799937450657357323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7856769066583267543143097 5892576799937450657357323)
                ·
                  refine ⟨8838865199906175986035985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5892576799937450657357323 8838865199906175986035985)
                  ·
                    refine ⟨6629148899929631989526989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8838865199906175986035985 6629148899929631989526989)
                    ·
                      refine ⟨2485930837473611996072621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6629148899929631989526989 2485930837473611996072621)
                      ·
                        rfl

theorem cell23_4841333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_4841333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841333 prefixEnd_4841333 := by exact prefixLift 4841333
  have htrace : WordTrace (prefixWord ++ tailWord_4841333) baseStart_4841333 baseEnd_4841333 := by
    simpa [prefixWord, tailWord_4841333, baseEnd_4841333] using wordTrace_append hprefix tailTrace_4841333
  have hstable : (prefixWord ++ tailWord_4841333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841333).length < 2 ^ (prefixWord ++ tailWord_4841333).sum := by decide
  have hdescent : baseEnd_4841333 < baseStart_4841333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841347 : List Nat := [1, 1, 1, 3, 4, 4, 1, 3, 1, 2, 2]
def baseStart_4841347 : Nat := 118140960795 + 4841347 * 2 ^ 59
def prefixEnd_4841347 : Nat := 4983230072969 + 3 ^ 40 * 4841347 * 2
def baseEnd_4841347 : Nat := 2485938026202774941297557

theorem tailTrace_4841347 : CollatzResearch.WordTrace tailWord_4841347 prefixEnd_4841347 2485938026202774941297557 := by
  unfold tailWord_4841347
  simp only [CollatzResearch.WordTrace]
  refine ⟨176578431591634130084914295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117718954394422753389942863 176578431591634130084914295)
  ·
    refine ⟨264867647387451195127371443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176578431591634130084914295 264867647387451195127371443)
    ·
      refine ⟨397301471081176792691057165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264867647387451195127371443 397301471081176792691057165)
      ·
        refine ⟨148988051655441297259146437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 397301471081176792691057165 148988051655441297259146437)
        ·
          refine ⟨27935259685395243236089957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 148988051655441297259146437 27935259685395243236089957)
          ·
            refine ⟨5237861191011608106766867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27935259685395243236089957 5237861191011608106766867)
            ·
              refine ⟨7856791786517412160150301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5237861191011608106766867 7856791786517412160150301)
              ·
                refine ⟨2946296919944029560056363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7856791786517412160150301 2946296919944029560056363)
                ·
                  refine ⟨4419445379916044340084545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2946296919944029560056363 4419445379916044340084545)
                  ·
                    refine ⟨3314584034937033255063409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4419445379916044340084545 3314584034937033255063409)
                    ·
                      refine ⟨2485938026202774941297557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3314584034937033255063409 2485938026202774941297557)
                      ·
                        rfl

theorem cell23_4841347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 3, 1, 2, 2].length) (baseStart_4841347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841347 prefixEnd_4841347 := by exact prefixLift 4841347
  have htrace : WordTrace (prefixWord ++ tailWord_4841347) baseStart_4841347 baseEnd_4841347 := by
    simpa [prefixWord, tailWord_4841347, baseEnd_4841347] using wordTrace_append hprefix tailTrace_4841347
  have hstable : (prefixWord ++ tailWord_4841347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841347).length < 2 ^ (prefixWord ++ tailWord_4841347).sum := by decide
  have hdescent : baseEnd_4841347 < baseStart_4841347 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841356 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 5, 3, 2]
def baseStart_4841356 : Nat := 118140960795 + 4841356 * 2 ^ 59
def prefixEnd_4841356 : Nat := 4983230072969 + 3 ^ 40 * 4841356 * 2
def baseEnd_4841356 : Nat := 2485942647528665406085015

theorem tailTrace_4841356 : CollatzResearch.WordTrace tailWord_4841356 prefixEnd_4841356 2485942647528665406085015 := by
  unfold tailWord_4841356
  simp only [CollatzResearch.WordTrace]
  refine ⟨88289379924300762310995961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117719173232401016414661281 88289379924300762310995961)
  ·
    refine ⟨66217034943225571733246971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88289379924300762310995961 66217034943225571733246971)
    ·
      refine ⟨99325552414838357599870457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66217034943225571733246971 99325552414838357599870457)
      ·
        refine ⟨74494164311128768199902843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99325552414838357599870457 74494164311128768199902843)
        ·
          refine ⟨111741246466693152299854265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74494164311128768199902843 111741246466693152299854265)
          ·
            refine ⟨83805934850019864224890699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111741246466693152299854265 83805934850019864224890699)
            ·
              refine ⟨125708902275029796337336049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83805934850019864224890699 125708902275029796337336049)
              ·
                refine ⟨94281676706272347253002037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125708902275029796337336049 94281676706272347253002037)
                ·
                  refine ⟨8838907191213032554968941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 94281676706272347253002037 8838907191213032554968941)
                  ·
                    refine ⟨3314590196704887208113353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8838907191213032554968941 3314590196704887208113353)
                    ·
                      refine ⟨2485942647528665406085015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3314590196704887208113353 2485942647528665406085015)
                      ·
                        rfl

theorem cell23_4841356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 5, 3, 2].length) (baseStart_4841356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841356 prefixEnd_4841356 := by exact prefixLift 4841356
  have htrace : WordTrace (prefixWord ++ tailWord_4841356) baseStart_4841356 baseEnd_4841356 := by
    simpa [prefixWord, tailWord_4841356, baseEnd_4841356] using wordTrace_append hprefix tailTrace_4841356
  have hstable : (prefixWord ++ tailWord_4841356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841356).length < 2 ^ (prefixWord ++ tailWord_4841356).sum := by decide
  have hdescent : baseEnd_4841356 < baseStart_4841356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841364 : List Nat := [2, 4, 2, 1, 1, 3, 3, 2, 1, 2, 2]
def baseStart_4841364 : Nat := 118140960795 + 4841364 * 2 ^ 59
def prefixEnd_4841364 : Nat := 4983230072969 + 3 ^ 40 * 4841364 * 2
def baseEnd_4841364 : Nat := 2485946755373901374784979

theorem tailTrace_4841364 : CollatzResearch.WordTrace tailWord_4841364 prefixEnd_4841364 2485946755373901374784979 := by
  unfold tailWord_4841364
  simp only [CollatzResearch.WordTrace]
  refine ⟨88289525816286270994141573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117719367755048361325522097 88289525816286270994141573)
  ·
    refine ⟨16554286090553675811401545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88289525816286270994141573 16554286090553675811401545)
    ·
      refine ⟨12415714567915256858551159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16554286090553675811401545 12415714567915256858551159)
      ·
        refine ⟨18623571851872885287826739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12415714567915256858551159 18623571851872885287826739)
        ·
          refine ⟨27935357777809327931740109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18623571851872885287826739 27935357777809327931740109)
          ·
            refine ⟨10475759166678497974402541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27935357777809327931740109 10475759166678497974402541)
            ·
              refine ⟨3928409687504436740400953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10475759166678497974402541 3928409687504436740400953)
              ·
                refine ⟨2946307265628327555300715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3928409687504436740400953 2946307265628327555300715)
                ·
                  refine ⟨4419460898442491332951073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2946307265628327555300715 4419460898442491332951073)
                  ·
                    refine ⟨3314595673831868499713305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4419460898442491332951073 3314595673831868499713305)
                    ·
                      refine ⟨2485946755373901374784979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3314595673831868499713305 2485946755373901374784979)
                      ·
                        rfl

theorem cell23_4841364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_4841364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841364 prefixEnd_4841364 := by exact prefixLift 4841364
  have htrace : WordTrace (prefixWord ++ tailWord_4841364) baseStart_4841364 baseEnd_4841364 := by
    simpa [prefixWord, tailWord_4841364, baseEnd_4841364] using wordTrace_append hprefix tailTrace_4841364
  have hstable : (prefixWord ++ tailWord_4841364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841364).length < 2 ^ (prefixWord ++ tailWord_4841364).sum := by decide
  have hdescent : baseEnd_4841364 < baseStart_4841364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841374 : List Nat := [4, 3, 1, 3, 1, 2, 2, 1, 2, 4]
def baseStart_4841374 : Nat := 118140960795 + 4841374 * 2 ^ 59
def prefixEnd_4841374 : Nat := 4983230072969 + 3 ^ 40 * 4841374 * 2
def baseEnd_4841374 : Nat := 828650630060148778553311

theorem tailTrace_4841374 : CollatzResearch.WordTrace tailWord_4841374 prefixEnd_4841374 828650630060148778553311 := by
  unfold tailWord_4841374
  simp only [CollatzResearch.WordTrace]
  refine ⟨22072427045317039212018397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117719610908357542464098117 22072427045317039212018397)
  ·
    refine ⟨8277160141993889704506899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22072427045317039212018397 8277160141993889704506899)
    ·
      refine ⟨12415740212990834556760349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8277160141993889704506899 12415740212990834556760349)
      ·
        refine ⟨4655902579871562958785131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12415740212990834556760349 4655902579871562958785131)
        ·
          refine ⟨6983853869807344438177697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4655902579871562958785131 6983853869807344438177697)
          ·
            refine ⟨5237890402355508328633273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6983853869807344438177697 5237890402355508328633273)
            ·
              refine ⟨3928417801766631246474955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5237890402355508328633273 3928417801766631246474955)
              ·
                refine ⟨5892626702649946869712433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3928417801766631246474955 5892626702649946869712433)
                ·
                  refine ⟨4419470026987460152284325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5892626702649946869712433 4419470026987460152284325)
                  ·
                    refine ⟨828650630060148778553311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4419470026987460152284325 828650630060148778553311)
                    ·
                      rfl

theorem cell23_4841374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_4841374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841374 prefixEnd_4841374 := by exact prefixLift 4841374
  have htrace : WordTrace (prefixWord ++ tailWord_4841374) baseStart_4841374 baseEnd_4841374 := by
    simpa [prefixWord, tailWord_4841374, baseEnd_4841374] using wordTrace_append hprefix tailTrace_4841374
  have hstable : (prefixWord ++ tailWord_4841374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841374).length < 2 ^ (prefixWord ++ tailWord_4841374).sum := by decide
  have hdescent : baseEnd_4841374 < baseStart_4841374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841380 : List Nat := [2, 3, 1, 2, 1, 3, 4, 1, 2, 1, 3]
def baseStart_4841380 : Nat := 118140960795 + 4841380 * 2 ^ 59
def prefixEnd_4841380 : Nat := 4983230072969 + 3 ^ 40 * 4841380 * 2
def baseEnd_4841380 : Nat := 2485954971064373312184905

theorem tailTrace_4841380 : CollatzResearch.WordTrace tailWord_4841380 prefixEnd_4841380 2485954971064373312184905 := by
  unfold tailWord_4841380
  simp only [CollatzResearch.WordTrace]
  refine ⟨88289817600257288360432797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117719756800343051147243729 88289817600257288360432797)
  ·
    refine ⟨33108681600096483135162299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88289817600257288360432797 33108681600096483135162299)
    ·
      refine ⟨49663022400144724702743449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33108681600096483135162299 49663022400144724702743449)
      ·
        refine ⟨37247266800108543527057587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49663022400144724702743449 37247266800108543527057587)
        ·
          refine ⟨55870900200162815290586381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37247266800108543527057587 55870900200162815290586381)
          ·
            refine ⟨20951587575061055733969893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55870900200162815290586381 20951587575061055733969893)
            ·
              refine ⟨3928422670323947950119355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20951587575061055733969893 3928422670323947950119355)
              ·
                refine ⟨5892634005485921925179033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3928422670323947950119355 5892634005485921925179033)
                ·
                  refine ⟨4419475504114441443884275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5892634005485921925179033 4419475504114441443884275)
                  ·
                    refine ⟨6629213256171662165826413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4419475504114441443884275 6629213256171662165826413)
                    ·
                      refine ⟨2485954971064373312184905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6629213256171662165826413 2485954971064373312184905)
                      ·
                        rfl

theorem cell23_4841380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_4841380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841380 prefixEnd_4841380 := by exact prefixLift 4841380
  have htrace : WordTrace (prefixWord ++ tailWord_4841380) baseStart_4841380 baseEnd_4841380 := by
    simpa [prefixWord, tailWord_4841380, baseEnd_4841380] using wordTrace_append hprefix tailTrace_4841380
  have hstable : (prefixWord ++ tailWord_4841380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841380).length < 2 ^ (prefixWord ++ tailWord_4841380).sum := by decide
  have hdescent : baseEnd_4841380 < baseStart_4841380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841384 : List Nat := [2, 1, 6, 2, 2, 1, 1, 2, 1, 2, 3]
def baseStart_4841384 : Nat := 118140960795 + 4841384 * 2 ^ 59
def prefixEnd_4841384 : Nat := 4983230072969 + 3 ^ 40 * 4841384 * 2
def baseEnd_4841384 : Nat := 2485957024986991296534887

theorem tailTrace_4841384 : CollatzResearch.WordTrace tailWord_4841384 prefixEnd_4841384 2485957024986991296534887 := by
  unfold tailWord_4841384
  simp only [CollatzResearch.WordTrace]
  refine ⟨88289890546250042702005603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117719854061666723602674137 88289890546250042702005603)
  ·
    refine ⟨132434835819375064053008405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88289890546250042702005603 132434835819375064053008405)
    ·
      refine ⟨6207882929033206127484769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 132434835819375064053008405 6207882929033206127484769)
      ·
        refine ⟨4655912196774904595613577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6207882929033206127484769 4655912196774904595613577)
        ·
          refine ⟨3491934147581178446710183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4655912196774904595613577 3491934147581178446710183)
          ·
            refine ⟨5237901221371767670065275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3491934147581178446710183 5237901221371767670065275)
            ·
              refine ⟨7856851832057651505097913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5237901221371767670065275 7856851832057651505097913)
              ·
                refine ⟨5892638874043238628823435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7856851832057651505097913 5892638874043238628823435)
                ·
                  refine ⟨8838958311064857943235153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5892638874043238628823435 8838958311064857943235153)
                  ·
                    refine ⟨6629218733298643457426365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8838958311064857943235153 6629218733298643457426365)
                    ·
                      refine ⟨2485957024986991296534887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6629218733298643457426365 2485957024986991296534887)
                      ·
                        rfl

theorem cell23_4841384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_4841384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841384 prefixEnd_4841384 := by exact prefixLift 4841384
  have htrace : WordTrace (prefixWord ++ tailWord_4841384) baseStart_4841384 baseEnd_4841384 := by
    simpa [prefixWord, tailWord_4841384, baseEnd_4841384] using wordTrace_append hprefix tailTrace_4841384
  have hstable : (prefixWord ++ tailWord_4841384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841384).length < 2 ^ (prefixWord ++ tailWord_4841384).sum := by decide
  have hdescent : baseEnd_4841384 < baseStart_4841384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841399 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 4]
def baseStart_4841399 : Nat := 118140960795 + 4841399 * 2 ^ 59
def prefixEnd_4841399 : Nat := 4983230072969 + 3 ^ 40 * 4841399 * 2
def baseEnd_4841399 : Nat := 2485964727196808737847317

theorem tailTrace_4841399 : CollatzResearch.WordTrace tailWord_4841399 prefixEnd_4841399 2485964727196808737847317 := by
  unfold tailWord_4841399
  simp only [CollatzResearch.WordTrace]
  refine ⟨176580328187445742965807251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117720218791630495310538167 176580328187445742965807251)
  ·
    refine ⟨264870492281168614448710877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176580328187445742965807251 264870492281168614448710877)
    ·
      refine ⟨99326434605438230418266579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 264870492281168614448710877 99326434605438230418266579)
      ·
        refine ⟨148989651908157345627399869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99326434605438230418266579 148989651908157345627399869)
        ·
          refine ⟨55871119465559004610274951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148989651908157345627399869 55871119465559004610274951)
          ·
            refine ⟨83806679198338506915412427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55871119465559004610274951 83806679198338506915412427)
            ·
              refine ⟨125710018797507760373118641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83806679198338506915412427 125710018797507760373118641)
              ·
                refine ⟨94282514098130820279838981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125710018797507760373118641 94282514098130820279838981)
                ·
                  refine ⟨17677971393399528802469809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94282514098130820279838981 17677971393399528802469809)
                  ·
                    refine ⟨13258478545049646601852357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17677971393399528802469809 13258478545049646601852357)
                    ·
                      refine ⟨2485964727196808737847317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13258478545049646601852357 2485964727196808737847317)
                      ·
                        rfl

theorem cell23_4841399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_4841399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841399 prefixEnd_4841399 := by exact prefixLift 4841399
  have htrace : WordTrace (prefixWord ++ tailWord_4841399) baseStart_4841399 baseEnd_4841399 := by
    simpa [prefixWord, tailWord_4841399, baseEnd_4841399] using wordTrace_append hprefix tailTrace_4841399
  have hstable : (prefixWord ++ tailWord_4841399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841399).length < 2 ^ (prefixWord ++ tailWord_4841399).sum := by decide
  have hdescent : baseEnd_4841399 < baseStart_4841399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841406 : List Nat := [4, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5]
def baseStart_4841406 : Nat := 118140960795 + 4841406 * 2 ^ 59
def prefixEnd_4841406 : Nat := 4983230072969 + 3 ^ 40 * 4841406 * 2
def baseEnd_4841406 : Nat := 2485968321561390210459785

theorem tailTrace_4841406 : CollatzResearch.WordTrace tailWord_4841406 prefixEnd_4841406 2485968321561390210459785 := by
  unfold tailWord_4841406
  simp only [CollatzResearch.WordTrace]
  refine ⟨22072572937302547895164009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117720388998946922107541381 22072572937302547895164009)
  ·
    refine ⟨16554429702976910921373007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22072572937302547895164009 16554429702976910921373007)
    ·
      refine ⟨24831644554465366382059511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16554429702976910921373007 24831644554465366382059511)
      ·
        refine ⟨37247466831698049573089267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24831644554465366382059511 37247466831698049573089267)
        ·
          refine ⟨55871200247547074359633901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37247466831698049573089267 55871200247547074359633901)
          ·
            refine ⟨20951700092830152884862713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55871200247547074359633901 20951700092830152884862713)
            ·
              refine ⟨15713775069622614663647035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20951700092830152884862713 15713775069622614663647035)
              ·
                refine ⟨23570662604433921995470553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15713775069622614663647035 23570662604433921995470553)
                ·
                  refine ⟨17677996953325441496602915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23570662604433921995470553 17677996953325441496602915)
                  ·
                    refine ⟨26516995429988162244904373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17677996953325441496602915 26516995429988162244904373)
                    ·
                      refine ⟨2485968321561390210459785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26516995429988162244904373 2485968321561390210459785)
                      ·
                        rfl

theorem cell23_4841406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_4841406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841406 prefixEnd_4841406 := by exact prefixLift 4841406
  have htrace : WordTrace (prefixWord ++ tailWord_4841406) baseStart_4841406 baseEnd_4841406 := by
    simpa [prefixWord, tailWord_4841406, baseEnd_4841406] using wordTrace_append hprefix tailTrace_4841406
  have hstable : (prefixWord ++ tailWord_4841406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841406).length < 2 ^ (prefixWord ++ tailWord_4841406).sum := by decide
  have hdescent : baseEnd_4841406 < baseStart_4841406 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841420 : List Nat := [2, 2, 1, 4, 1, 2, 1, 4, 2, 2, 2]
def baseStart_4841420 : Nat := 118140960795 + 4841420 * 2 ^ 59
def prefixEnd_4841420 : Nat := 4983230072969 + 3 ^ 40 * 4841420 * 2
def baseEnd_4841420 : Nat := 2485975510290553155684721

theorem tailTrace_4841420 : CollatzResearch.WordTrace tailWord_4841420 prefixEnd_4841420 2485975510290553155684721 := by
  unfold tailWord_4841420
  simp only [CollatzResearch.WordTrace]
  refine ⟨88290547060184831776160857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117720729413579775701547809 88290547060184831776160857)
  ·
    refine ⟨66217910295138623832120643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88290547060184831776160857 66217910295138623832120643)
    ·
      refine ⟨99326865442707935748180965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66217910295138623832120643 99326865442707935748180965)
      ·
        refine ⟨18623787270507737952783931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99326865442707935748180965 18623787270507737952783931)
        ·
          refine ⟨27935680905761606929175897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18623787270507737952783931 27935680905761606929175897)
          ·
            refine ⟨20951760679321205196881923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27935680905761606929175897 20951760679321205196881923)
            ·
              refine ⟨31427641018981807795322885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20951760679321205196881923 31427641018981807795322885)
              ·
                refine ⟨5892682691059088961623041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31427641018981807795322885 5892682691059088961623041)
                ·
                  refine ⟨4419512018294316721217281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5892682691059088961623041 4419512018294316721217281)
                  ·
                    refine ⟨3314634013720737540912961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4419512018294316721217281 3314634013720737540912961)
                    ·
                      refine ⟨2485975510290553155684721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3314634013720737540912961 2485975510290553155684721)
                      ·
                        rfl

theorem cell23_4841420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_4841420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841420 prefixEnd_4841420 := by exact prefixLift 4841420
  have htrace : WordTrace (prefixWord ++ tailWord_4841420) baseStart_4841420 baseEnd_4841420 := by
    simpa [prefixWord, tailWord_4841420, baseEnd_4841420] using wordTrace_append hprefix tailTrace_4841420
  have hstable : (prefixWord ++ tailWord_4841420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841420).length < 2 ^ (prefixWord ++ tailWord_4841420).sum := by decide
  have hdescent : baseEnd_4841420 < baseStart_4841420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841456 : List Nat := [2, 1, 1, 1, 3, 2, 5, 1, 2, 5]
def baseStart_4841456 : Nat := 118140960795 + 4841456 * 2 ^ 59
def prefixEnd_4841456 : Nat := 4983230072969 + 3 ^ 40 * 4841456 * 2
def baseEnd_4841456 : Nat := 828664665198038338278185

theorem tailTrace_4841456 : CollatzResearch.WordTrace tailWord_4841456 prefixEnd_4841456 828664665198038338278185 := by
  unfold tailWord_4841456
  simp only [CollatzResearch.WordTrace]
  refine ⟨88291203574119620850316111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117721604765492827800421481 88291203574119620850316111)
  ·
    refine ⟨132436805361179431275474167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88291203574119620850316111 132436805361179431275474167)
    ·
      refine ⟨198655208041769146913211251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132436805361179431275474167 198655208041769146913211251)
      ·
        refine ⟨297982812062653720369816877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198655208041769146913211251 297982812062653720369816877)
        ·
          refine ⟨111743554523495145138681329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 297982812062653720369816877 111743554523495145138681329)
          ·
            refine ⟨83807665892621358854010997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111743554523495145138681329 83807665892621358854010997)
            ·
              refine ⟨7856968677433252392563531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83807665892621358854010997 7856968677433252392563531)
              ·
                refine ⟨11785453016149878588845297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7856968677433252392563531 11785453016149878588845297)
                ·
                  refine ⟨8839089762112408941633973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11785453016149878588845297 8839089762112408941633973)
                  ·
                    refine ⟨828664665198038338278185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8839089762112408941633973 828664665198038338278185)
                    ·
                      rfl

theorem cell23_4841456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 2, 5].length) (baseStart_4841456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841456 prefixEnd_4841456 := by exact prefixLift 4841456
  have htrace : WordTrace (prefixWord ++ tailWord_4841456) baseStart_4841456 baseEnd_4841456 := by
    simpa [prefixWord, tailWord_4841456, baseEnd_4841456] using wordTrace_append hprefix tailTrace_4841456
  have hstable : (prefixWord ++ tailWord_4841456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841456).length < 2 ^ (prefixWord ++ tailWord_4841456).sum := by decide
  have hdescent : baseEnd_4841456 < baseStart_4841456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841496 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 3, 4, 3]
def baseStart_4841496 : Nat := 118140960795 + 4841496 * 2 ^ 59
def prefixEnd_4841496 : Nat := 4983230072969 + 3 ^ 40 * 4841496 * 2
def baseEnd_4841496 : Nat := 2486014534820294858334371

theorem tailTrace_4841496 : CollatzResearch.WordTrace tailWord_4841496 prefixEnd_4841496 2486014534820294858334371 := by
  unfold tailWord_4841496
  simp only [CollatzResearch.WordTrace]
  refine ⟨88291933034047164266044171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117722577378729552354725561 88291933034047164266044171)
  ·
    refine ⟨132437899551070746399066257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88291933034047164266044171 132437899551070746399066257)
    ·
      refine ⟨99328424663303059799299693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132437899551070746399066257 99328424663303059799299693)
      ·
        refine ⟨37248159248738647424737385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99328424663303059799299693 37248159248738647424737385)
        ·
          refine ⟨27936119436553985568553039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37248159248738647424737385 27936119436553985568553039)
          ·
            refine ⟨41904179154830978352829559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27936119436553985568553039 41904179154830978352829559)
            ·
              refine ⟨62856268732246467529244339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41904179154830978352829559 62856268732246467529244339)
              ·
                refine ⟨94284403098369701293866509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62856268732246467529244339 94284403098369701293866509)
                ·
                  refine ⟨35356651161888637985199941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94284403098369701293866509 35356651161888637985199941)
                  ·
                    refine ⟨6629372092854119622224989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35356651161888637985199941 6629372092854119622224989)
                    ·
                      refine ⟨2486014534820294858334371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6629372092854119622224989 2486014534820294858334371)
                      ·
                        rfl

theorem cell23_4841496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_4841496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841496 prefixEnd_4841496 := by exact prefixLift 4841496
  have htrace : WordTrace (prefixWord ++ tailWord_4841496) baseStart_4841496 baseEnd_4841496 := by
    simpa [prefixWord, tailWord_4841496, baseEnd_4841496] using wordTrace_append hprefix tailTrace_4841496
  have hstable : (prefixWord ++ tailWord_4841496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841496).length < 2 ^ (prefixWord ++ tailWord_4841496).sum := by decide
  have hdescent : baseEnd_4841496 < baseStart_4841496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841506 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 2, 4, 4]
def baseStart_4841506 : Nat := 118140960795 + 4841506 * 2 ^ 59
def prefixEnd_4841506 : Nat := 4983230072969 + 3 ^ 40 * 4841506 * 2
def baseEnd_4841506 : Nat := 2486019669626839819209325

theorem tailTrace_4841506 : CollatzResearch.WordTrace tailWord_4841506 prefixEnd_4841506 2486019669626839819209325 := by
  unfold tailWord_4841506
  simp only [CollatzResearch.WordTrace]
  refine ⟨44146057699514525059988093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117722820532038733493301581 44146057699514525059988093)
  ·
    refine ⟨16554771637317946897495535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44146057699514525059988093 16554771637317946897495535)
    ·
      refine ⟨24832157455976920346243303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16554771637317946897495535 24832157455976920346243303)
      ·
        refine ⟨37248236183965380519364955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24832157455976920346243303 37248236183965380519364955)
        ·
          refine ⟨55872354275948070779047433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37248236183965380519364955 55872354275948070779047433)
          ·
            refine ⟨41904265706961053084285575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55872354275948070779047433 41904265706961053084285575)
            ·
              refine ⟨62856398560441579626428363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41904265706961053084285575 62856398560441579626428363)
              ·
                refine ⟨94284597840662369439642545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62856398560441579626428363 94284597840662369439642545)
                ·
                  refine ⟨70713448380496777079731909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94284597840662369439642545 70713448380496777079731909)
                  ·
                    refine ⟨13258771571343145702449733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70713448380496777079731909 13258771571343145702449733)
                    ·
                      refine ⟨2486019669626839819209325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13258771571343145702449733 2486019669626839819209325)
                      ·
                        rfl

theorem cell23_4841506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_4841506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841506 prefixEnd_4841506 := by exact prefixLift 4841506
  have htrace : WordTrace (prefixWord ++ tailWord_4841506) baseStart_4841506 baseEnd_4841506 := by
    simpa [prefixWord, tailWord_4841506, baseEnd_4841506] using wordTrace_append hprefix tailTrace_4841506
  have hstable : (prefixWord ++ tailWord_4841506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841506).length < 2 ^ (prefixWord ++ tailWord_4841506).sum := by decide
  have hdescent : baseEnd_4841506 < baseStart_4841506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841519 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 8]
def baseStart_4841519 : Nat := 118140960795 + 4841519 * 2 ^ 59
def prefixEnd_4841519 : Nat := 4983230072969 + 3 ^ 40 * 4841519 * 2
def baseEnd_4841519 : Nat := 2486026344875348268346765

theorem tailTrace_4841519 : CollatzResearch.WordTrace tailWord_4841519 prefixEnd_4841519 2486026344875348268346765 := by
  unfold tailWord_4841519
  simp only [CollatzResearch.WordTrace]
  refine ⟨176584704947011003460175611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117723136631340668973450407 176584704947011003460175611)
  ·
    refine ⟨264877057420516505190263417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176584704947011003460175611 264877057420516505190263417)
    ·
      refine ⟨198657793065387378892697563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264877057420516505190263417 198657793065387378892697563)
      ·
        refine ⟨297986689598081068339046345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198657793065387378892697563 297986689598081068339046345)
        ·
          refine ⟨223490017198560801254284759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297986689598081068339046345 223490017198560801254284759)
          ·
            refine ⟨335235025797841201881427139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223490017198560801254284759 335235025797841201881427139)
            ·
              refine ⟨502852538696761802822140709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335235025797841201881427139 502852538696761802822140709)
              ·
                refine ⟨94284851005642838029151383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 502852538696761802822140709 94284851005642838029151383)
                ·
                  refine ⟨141427276508464257043727075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94284851005642838029151383 141427276508464257043727075)
                  ·
                    refine ⟨212140914762696385565590613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 141427276508464257043727075 212140914762696385565590613)
                    ·
                      refine ⟨2486026344875348268346765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 212140914762696385565590613 2486026344875348268346765)
                      ·
                        rfl

theorem cell23_4841519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 8].length) (baseStart_4841519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841519 prefixEnd_4841519 := by exact prefixLift 4841519
  have htrace : WordTrace (prefixWord ++ tailWord_4841519) baseStart_4841519 baseEnd_4841519 := by
    simpa [prefixWord, tailWord_4841519, baseEnd_4841519] using wordTrace_append hprefix tailTrace_4841519
  have hstable : (prefixWord ++ tailWord_4841519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841519).length < 2 ^ (prefixWord ++ tailWord_4841519).sum := by decide
  have hdescent : baseEnd_4841519 < baseStart_4841519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841520 : List Nat := [2, 1, 1, 1, 2, 5, 3, 3, 1, 4]
def baseStart_4841520 : Nat := 118140960795 + 4841520 * 2 ^ 59
def prefixEnd_4841520 : Nat := 4983230072969 + 3 ^ 40 * 4841520 * 2
def baseEnd_4841520 : Nat := 828675619452000921478087

theorem tailTrace_4841520 : CollatzResearch.WordTrace tailWord_4841520 prefixEnd_4841520 828675619452000921478087 := by
  unfold tailWord_4841520
  simp only [CollatzResearch.WordTrace]
  refine ⟨88292370710003690315481007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117723160946671587087308009 88292370710003690315481007)
  ·
    refine ⟨132438556065005535473221511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88292370710003690315481007 132438556065005535473221511)
    ·
      refine ⟨198657834097508303209832267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132438556065005535473221511 198657834097508303209832267)
      ·
        refine ⟨297986751146262454814748401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198657834097508303209832267 297986751146262454814748401)
        ·
          refine ⟨223490063359696841111061301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297986751146262454814748401 223490063359696841111061301)
          ·
            refine ⟨20952193439971578854161997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 223490063359696841111061301 20952193439971578854161997)
            ·
              refine ⟨7857072539989342070310749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20952193439971578854161997 7857072539989342070310749)
              ·
                refine ⟨2946402202496003276366531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7857072539989342070310749 2946402202496003276366531)
                ·
                  refine ⟨4419603303744004914549797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2946402202496003276366531 4419603303744004914549797)
                  ·
                    refine ⟨828675619452000921478087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4419603303744004914549797 828675619452000921478087)
                    ·
                      rfl

theorem cell23_4841520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 3, 1, 4].length) (baseStart_4841520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841520 prefixEnd_4841520 := by exact prefixLift 4841520
  have htrace : WordTrace (prefixWord ++ tailWord_4841520) baseStart_4841520 baseEnd_4841520 := by
    simpa [prefixWord, tailWord_4841520, baseEnd_4841520] using wordTrace_append hprefix tailTrace_4841520
  have hstable : (prefixWord ++ tailWord_4841520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841520).length < 2 ^ (prefixWord ++ tailWord_4841520).sum := by decide
  have hdescent : baseEnd_4841520 < baseStart_4841520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841546 : List Nat := [3, 1, 2, 1, 1, 2, 1, 4, 3, 5]
def baseStart_4841546 : Nat := 118140960795 + 4841546 * 2 ^ 59
def prefixEnd_4841546 : Nat := 4983230072969 + 3 ^ 40 * 4841546 * 2
def baseEnd_4841546 : Nat := 828680069617673220903047

theorem tailTrace_4841546 : CollatzResearch.WordTrace tailWord_4841546 prefixEnd_4841546 828680069617673220903047 := by
  unfold tailWord_4841546
  simp only [CollatzResearch.WordTrace]
  refine ⟨44146422429478296767852123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117723793145275458047605661 44146422429478296767852123)
  ·
    refine ⟨66219633644217445151778185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44146422429478296767852123 66219633644217445151778185)
    ·
      refine ⟨49664725233163083863833639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66219633644217445151778185 49664725233163083863833639)
      ·
        refine ⟨74497087849744625795750459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49664725233163083863833639 74497087849744625795750459)
        ·
          refine ⟨111745631774616938693625689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74497087849744625795750459 111745631774616938693625689)
          ·
            refine ⟨83809223830962704020219267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111745631774616938693625689 83809223830962704020219267)
            ·
              refine ⟨125713835746444056030328901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83809223830962704020219267 125713835746444056030328901)
              ·
                refine ⟨23571344202458260505686669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125713835746444056030328901 23571344202458260505686669)
                ·
                  refine ⟨8839254075921847689632501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23571344202458260505686669 8839254075921847689632501)
                  ·
                    refine ⟨828680069617673220903047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8839254075921847689632501 828680069617673220903047)
                    ·
                      rfl

theorem cell23_4841546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_4841546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841546 prefixEnd_4841546 := by exact prefixLift 4841546
  have htrace : WordTrace (prefixWord ++ tailWord_4841546) baseStart_4841546 baseEnd_4841546 := by
    simpa [prefixWord, tailWord_4841546, baseEnd_4841546] using wordTrace_append hprefix tailTrace_4841546
  have hstable : (prefixWord ++ tailWord_4841546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841546).length < 2 ^ (prefixWord ++ tailWord_4841546).sum := by decide
  have hdescent : baseEnd_4841546 < baseStart_4841546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841550 : List Nat := [4, 1, 1, 1, 1, 6, 2, 1, 6]
def baseStart_4841550 : Nat := 118140960795 + 4841550 * 2 ^ 59
def prefixEnd_4841550 : Nat := 4983230072969 + 3 ^ 40 * 4841550 * 2
def baseEnd_4841550 : Nat := 276226918086181960784347

theorem tailTrace_4841550 : CollatzResearch.WordTrace tailWord_4841550 prefixEnd_4841550 276226918086181960784347 := by
  unfold tailWord_4841550
  simp only [CollatzResearch.WordTrace]
  refine ⟨22073229451237336969319263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117723890406599130503036069 22073229451237336969319263)
  ·
    refine ⟨33109844176856005453978895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22073229451237336969319263 33109844176856005453978895)
    ·
      refine ⟨49664766265284008180968343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33109844176856005453978895 49664766265284008180968343)
      ·
        refine ⟨74497149397926012271452515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49664766265284008180968343 74497149397926012271452515)
        ·
          refine ⟨111745724096889018407178773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74497149397926012271452515 111745724096889018407178773)
          ·
            refine ⟨5238080817041672737836505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 111745724096889018407178773 5238080817041672737836505)
            ·
              refine ⟨3928560612781254553377379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5238080817041672737836505 3928560612781254553377379)
              ·
                refine ⟨5892840919171881830066069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3928560612781254553377379 5892840919171881830066069)
                ·
                  refine ⟨276226918086181960784347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5892840919171881830066069 276226918086181960784347)
                  ·
                    rfl

theorem cell23_4841550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 6].length) (baseStart_4841550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841550 prefixEnd_4841550 := by exact prefixLift 4841550
  have htrace : WordTrace (prefixWord ++ tailWord_4841550) baseStart_4841550 baseEnd_4841550 := by
    simpa [prefixWord, tailWord_4841550, baseEnd_4841550] using wordTrace_append hprefix tailTrace_4841550
  have hstable : (prefixWord ++ tailWord_4841550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841550).length < 2 ^ (prefixWord ++ tailWord_4841550).sum := by decide
  have hdescent : baseEnd_4841550 < baseStart_4841550 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841553 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 6, 3, 2]
def baseStart_4841553 : Nat := 118140960795 + 4841553 * 2 ^ 59
def prefixEnd_4841553 : Nat := 4983230072969 + 3 ^ 40 * 4841553 * 2
def baseEnd_4841553 : Nat := 2486043803217601135321609

theorem tailTrace_4841553 : CollatzResearch.WordTrace tailWord_4841553 prefixEnd_4841553 2486043803217601135321609 := by
  unfold tailWord_4841553
  simp only [CollatzResearch.WordTrace]
  refine ⟨176585945028887827266913313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117723963352591884844608875 176585945028887827266913313)
  ·
    refine ⟨132439458771665870450184985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176585945028887827266913313 132439458771665870450184985)
    ·
      refine ⟨99329594078749402837638739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132439458771665870450184985 99329594078749402837638739)
      ·
        refine ⟨148994391118124104256458109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99329594078749402837638739 148994391118124104256458109)
        ·
          refine ⟨55872896669296539096171791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148994391118124104256458109 55872896669296539096171791)
          ·
            refine ⟨83809345003944808644257687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55872896669296539096171791 83809345003944808644257687)
            ·
              refine ⟨125714017505917212966386531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83809345003944808644257687 125714017505917212966386531)
              ·
                refine ⟨188571026258875819449579797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125714017505917212966386531 188571026258875819449579797)
                ·
                  refine ⟨8839266855884804036699053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 188571026258875819449579797 8839266855884804036699053)
                  ·
                    refine ⟨3314725070956801513762145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8839266855884804036699053 3314725070956801513762145)
                    ·
                      refine ⟨2486043803217601135321609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3314725070956801513762145 2486043803217601135321609)
                      ·
                        rfl

theorem cell23_4841553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 3, 2].length) (baseStart_4841553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841553 prefixEnd_4841553 := by exact prefixLift 4841553
  have htrace : WordTrace (prefixWord ++ tailWord_4841553) baseStart_4841553 baseEnd_4841553 := by
    simpa [prefixWord, tailWord_4841553, baseEnd_4841553] using wordTrace_append hprefix tailTrace_4841553
  have hstable : (prefixWord ++ tailWord_4841553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841553).length < 2 ^ (prefixWord ++ tailWord_4841553).sum := by decide
  have hdescent : baseEnd_4841553 < baseStart_4841553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841580 : List Nat := [2, 2, 1, 1, 3, 4, 3, 1, 1, 5]
def baseStart_4841580 : Nat := 118140960795 + 4841580 * 2 ^ 59
def prefixEnd_4841580 : Nat := 4983230072969 + 3 ^ 40 * 4841580 * 2
def baseEnd_4841580 : Nat := 828685889065090843227995

theorem tailTrace_4841580 : CollatzResearch.WordTrace tailWord_4841580 prefixEnd_4841580 828685889065090843227995 := by
  unfold tailWord_4841580
  simp only [CollatzResearch.WordTrace]
  refine ⟨88293464899895005439073097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117724619866526673918764129 88293464899895005439073097)
  ·
    refine ⟨66220098674921254079304823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88293464899895005439073097 66220098674921254079304823)
    ·
      refine ⟨99330148012381881118957235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66220098674921254079304823 99330148012381881118957235)
      ·
        refine ⟨148995222018572821678435853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99330148012381881118957235 148995222018572821678435853)
        ·
          refine ⟨55873208256964808129413445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148995222018572821678435853 55873208256964808129413445)
          ·
            refine ⟨10476226548180901524265021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55873208256964808129413445 10476226548180901524265021)
            ·
              refine ⟨3928584955567838071599383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10476226548180901524265021 3928584955567838071599383)
              ·
                refine ⟨5892877433351757107399075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3928584955567838071599383 5892877433351757107399075)
                ·
                  refine ⟨8839316150027635661098613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5892877433351757107399075 8839316150027635661098613)
                  ·
                    refine ⟨828685889065090843227995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8839316150027635661098613 828685889065090843227995)
                    ·
                      rfl

theorem cell23_4841580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 5].length) (baseStart_4841580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841580 prefixEnd_4841580 := by exact prefixLift 4841580
  have htrace : WordTrace (prefixWord ++ tailWord_4841580) baseStart_4841580 baseEnd_4841580 := by
    simpa [prefixWord, tailWord_4841580, baseEnd_4841580] using wordTrace_append hprefix tailTrace_4841580
  have hstable : (prefixWord ++ tailWord_4841580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841580).length < 2 ^ (prefixWord ++ tailWord_4841580).sum := by decide
  have hdescent : baseEnd_4841580 < baseStart_4841580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841600 : List Nat := [2, 1, 1, 2, 1, 3, 1, 5, 3, 2, 2]
def baseStart_4841600 : Nat := 118140960795 + 4841600 * 2 ^ 59
def prefixEnd_4841600 : Nat := 4983230072969 + 3 ^ 40 * 4841600 * 2
def baseEnd_4841600 : Nat := 2486067936808362451433893

theorem tailTrace_4841600 : CollatzResearch.WordTrace tailWord_4841600 prefixEnd_4841600 2486067936808362451433893 := by
  unfold tailWord_4841600
  simp only [CollatzResearch.WordTrace]
  refine ⟨88293829629858777146937127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117725106173145036195916169 88293829629858777146937127)
  ·
    refine ⟨132440744444788165720405691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88293829629858777146937127 132440744444788165720405691)
    ·
      refine ⟨198661116667182248580608537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132440744444788165720405691 198661116667182248580608537)
      ·
        refine ⟨148995837500386686435456403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198661116667182248580608537 148995837500386686435456403)
        ·
          refine ⟨223493756250580029653184605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148995837500386686435456403 223493756250580029653184605)
          ·
            refine ⟨83810158593967511119944227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 223493756250580029653184605 83810158593967511119944227)
            ·
              refine ⟨125715237890951266679916341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83810158593967511119944227 125715237890951266679916341)
              ·
                refine ⟨11785803552276681251242157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 125715237890951266679916341 11785803552276681251242157)
                ·
                  refine ⟨4419676332103755469215809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11785803552276681251242157 4419676332103755469215809)
                  ·
                    refine ⟨3314757249077816601911857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4419676332103755469215809 3314757249077816601911857)
                    ·
                      refine ⟨2486067936808362451433893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3314757249077816601911857 2486067936808362451433893)
                      ·
                        rfl

theorem cell23_4841600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 3, 2, 2].length) (baseStart_4841600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841600 prefixEnd_4841600 := by exact prefixLift 4841600
  have htrace : WordTrace (prefixWord ++ tailWord_4841600) baseStart_4841600 baseEnd_4841600 := by
    simpa [prefixWord, tailWord_4841600, baseEnd_4841600] using wordTrace_append hprefix tailTrace_4841600
  have hstable : (prefixWord ++ tailWord_4841600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841600).length < 2 ^ (prefixWord ++ tailWord_4841600).sum := by decide
  have hdescent : baseEnd_4841600 < baseStart_4841600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841603 : List Nat := [1, 1, 1, 3, 3, 3, 1, 2, 3, 2, 3]
def baseStart_4841603 : Nat := 118140960795 + 4841603 * 2 ^ 59
def prefixEnd_4841603 : Nat := 4983230072969 + 3 ^ 40 * 4841603 * 2
def baseEnd_4841603 : Nat := 2486069477250325939696379

theorem tailTrace_4841603 : CollatzResearch.WordTrace tailWord_4841603 prefixEnd_4841603 2486069477250325939696379 := by
  unfold tailWord_4841603
  simp only [CollatzResearch.WordTrace]
  refine ⟨176587768678706685806233463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117725179119137790537488975 176587768678706685806233463)
  ·
    refine ⟨264881653018060028709350195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176587768678706685806233463 264881653018060028709350195)
    ·
      refine ⟨397322479527090043064025293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264881653018060028709350195 397322479527090043064025293)
      ·
        refine ⟨148995929822658766149009485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 397322479527090043064025293 148995929822658766149009485)
        ·
          refine ⟨55873473683497037305878557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148995929822658766149009485 55873473683497037305878557)
          ·
            refine ⟨20952552631311388989704459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55873473683497037305878557 20952552631311388989704459)
            ·
              refine ⟨31428828946967083484556689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20952552631311388989704459 31428828946967083484556689)
              ·
                refine ⟨23571621710225312613417517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31428828946967083484556689 23571621710225312613417517)
                ·
                  refine ⟨8839358141334492230031569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23571621710225312613417517 8839358141334492230031569)
                  ·
                    refine ⟨6629518606000869172523677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8839358141334492230031569 6629518606000869172523677)
                    ·
                      refine ⟨2486069477250325939696379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6629518606000869172523677 2486069477250325939696379)
                      ·
                        rfl

theorem cell23_4841603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 2, 3].length) (baseStart_4841603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841603 prefixEnd_4841603 := by exact prefixLift 4841603
  have htrace : WordTrace (prefixWord ++ tailWord_4841603) baseStart_4841603 baseEnd_4841603 := by
    simpa [prefixWord, tailWord_4841603, baseEnd_4841603] using wordTrace_append hprefix tailTrace_4841603
  have hstable : (prefixWord ++ tailWord_4841603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841603).length < 2 ^ (prefixWord ++ tailWord_4841603).sum := by decide
  have hdescent : baseEnd_4841603 < baseStart_4841603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841610 : List Nat := [3, 1, 2, 3, 1, 2, 2, 3, 2, 4]
def baseStart_4841610 : Nat := 118140960795 + 4841610 * 2 ^ 59
def prefixEnd_4841610 : Nat := 4983230072969 + 3 ^ 40 * 4841610 * 2
def baseEnd_4841610 : Nat := 828691023871635804102949

theorem tailTrace_4841610 : CollatzResearch.WordTrace tailWord_4841610 prefixEnd_4841610 828691023871635804102949 := by
  unfold tailWord_4841610
  simp only [CollatzResearch.WordTrace]
  refine ⟨44147005997420331500434571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117725349326454217334492189 44147005997420331500434571)
  ·
    refine ⟨66220508996130497250651857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44147005997420331500434571 66220508996130497250651857)
    ·
      refine ⟨49665381747097872937988893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66220508996130497250651857 49665381747097872937988893)
      ·
        refine ⟨18624518155161702351745835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49665381747097872937988893 18624518155161702351745835)
        ·
          refine ⟨27936777232742553527618753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18624518155161702351745835 27936777232742553527618753)
          ·
            refine ⟨20952582924556915145714065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27936777232742553527618753 20952582924556915145714065)
            ·
              refine ⟨15714437193417686359285549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20952582924556915145714065 15714437193417686359285549)
              ·
                refine ⟨5892913947531632384732081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15714437193417686359285549 5892913947531632384732081)
                ·
                  refine ⟨4419685460648724288549061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5892913947531632384732081 4419685460648724288549061)
                  ·
                    refine ⟨828691023871635804102949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4419685460648724288549061 828691023871635804102949)
                    ·
                      rfl

theorem cell23_4841610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_4841610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841610 prefixEnd_4841610 := by exact prefixLift 4841610
  have htrace : WordTrace (prefixWord ++ tailWord_4841610) baseStart_4841610 baseEnd_4841610 := by
    simpa [prefixWord, tailWord_4841610, baseEnd_4841610] using wordTrace_append hprefix tailTrace_4841610
  have hstable : (prefixWord ++ tailWord_4841610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841610).length < 2 ^ (prefixWord ++ tailWord_4841610).sum := by decide
  have hdescent : baseEnd_4841610 < baseStart_4841610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841634 : List Nat := [3, 3, 1, 3, 1, 3, 2, 1, 1, 1, 4]
def baseStart_4841634 : Nat := 118140960795 + 4841634 * 2 ^ 59
def prefixEnd_4841634 : Nat := 4983230072969 + 3 ^ 40 * 4841634 * 2
def baseEnd_4841634 : Nat := 2486085395150615318408737

theorem tailTrace_4841634 : CollatzResearch.WordTrace tailWord_4841634 prefixEnd_4841634 2486085395150615318408737 := by
  unfold tailWord_4841634
  simp only [CollatzResearch.WordTrace]
  refine ⟨44147224835398594525152989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117725932894396252067074637 44147224835398594525152989)
  ·
    refine ⟨16555209313274472946932371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44147224835398594525152989 16555209313274472946932371)
    ·
      refine ⟨24832813969911709420398557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16555209313274472946932371 24832813969911709420398557)
      ·
        refine ⟨9312305238716891032649459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24832813969911709420398557 9312305238716891032649459)
        ·
          refine ⟨13968457858075336548974189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9312305238716891032649459 13968457858075336548974189)
          ·
            refine ⟨5238171696778251205865321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13968457858075336548974189 5238171696778251205865321)
            ·
              refine ⟨3928628772583688404398991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5238171696778251205865321 3928628772583688404398991)
              ·
                refine ⟨5892943158875532606598487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3928628772583688404398991 5892943158875532606598487)
                ·
                  refine ⟨8839414738313298909897731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5892943158875532606598487 8839414738313298909897731)
                  ·
                    refine ⟨13259122107469948364846597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8839414738313298909897731 13259122107469948364846597)
                    ·
                      refine ⟨2486085395150615318408737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13259122107469948364846597 2486085395150615318408737)
                      ·
                        rfl

theorem cell23_4841634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_4841634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841634 prefixEnd_4841634 := by exact prefixLift 4841634
  have htrace : WordTrace (prefixWord ++ tailWord_4841634) baseStart_4841634 baseEnd_4841634 := by
    simpa [prefixWord, tailWord_4841634, baseEnd_4841634] using wordTrace_append hprefix tailTrace_4841634
  have hstable : (prefixWord ++ tailWord_4841634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841634).length < 2 ^ (prefixWord ++ tailWord_4841634).sum := by decide
  have hdescent : baseEnd_4841634 < baseStart_4841634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841650 : List Nat := [3, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3]
def baseStart_4841650 : Nat := 118140960795 + 4841650 * 2 ^ 59
def prefixEnd_4841650 : Nat := 4983230072969 + 3 ^ 40 * 4841650 * 2
def baseEnd_4841650 : Nat := 2486093610841087255808663

theorem tailTrace_4841650 : CollatzResearch.WordTrace tailWord_4841650 prefixEnd_4841650 2486093610841087255808663 := by
  unfold tailWord_4841650
  simp only [CollatzResearch.WordTrace]
  refine ⟨44147370727384103208298601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117726321939690941888796269 44147370727384103208298601)
  ·
    refine ⟨33110528045538077406223951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44147370727384103208298601 33110528045538077406223951)
    ·
      refine ⟨49665792068307116109335927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33110528045538077406223951 49665792068307116109335927)
      ·
        refine ⟨74498688102460674164003891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49665792068307116109335927 74498688102460674164003891)
        ·
          refine ⟨111748032153691011246005837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74498688102460674164003891 111748032153691011246005837)
          ·
            refine ⟨41905512057634129217252189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111748032153691011246005837 41905512057634129217252189)
            ·
              refine ⟨15714567021612798456469571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41905512057634129217252189 15714567021612798456469571)
              ·
                refine ⟨23571850532419197684704357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15714567021612798456469571 23571850532419197684704357)
                ·
                  refine ⟨4419721974828599565882067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23571850532419197684704357 4419721974828599565882067)
                  ·
                    refine ⟨6629582962242899348823101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4419721974828599565882067 6629582962242899348823101)
                    ·
                      refine ⟨2486093610841087255808663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6629582962242899348823101 2486093610841087255808663)
                      ·
                        rfl

theorem cell23_4841650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3].length) (baseStart_4841650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841650 prefixEnd_4841650 := by exact prefixLift 4841650
  have htrace : WordTrace (prefixWord ++ tailWord_4841650) baseStart_4841650 baseEnd_4841650 := by
    simpa [prefixWord, tailWord_4841650, baseEnd_4841650] using wordTrace_append hprefix tailTrace_4841650
  have hstable : (prefixWord ++ tailWord_4841650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841650).length < 2 ^ (prefixWord ++ tailWord_4841650).sum := by decide
  have hdescent : baseEnd_4841650 < baseStart_4841650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841690 : List Nat := [3, 1, 1, 2, 2, 1, 2, 4, 1, 4, 2]
def baseStart_4841690 : Nat := 118140960795 + 4841690 * 2 ^ 59
def prefixEnd_4841690 : Nat := 4983230072969 + 3 ^ 40 * 4841690 * 2
def baseEnd_4841690 : Nat := 2486114150067267099308479

theorem tailTrace_4841690 : CollatzResearch.WordTrace tailWord_4841690 prefixEnd_4841690 2486114150067267099308479 := by
  unfold tailWord_4841690
  simp only [CollatzResearch.WordTrace]
  refine ⟨44147735457347874916162631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117727294552927666443100349 44147735457347874916162631)
  ·
    refine ⟨66221603186021812374243947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44147735457347874916162631 66221603186021812374243947)
    ·
      refine ⟨99332404779032718561365921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66221603186021812374243947 99332404779032718561365921)
      ·
        refine ⟨74499303584274538921024441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99332404779032718561365921 74499303584274538921024441)
        ·
          refine ⟨55874477688205904190768331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74499303584274538921024441 55874477688205904190768331)
          ·
            refine ⟨83811716532308856286152497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55874477688205904190768331 83811716532308856286152497)
            ·
              refine ⟨62858787399231642214614373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83811716532308856286152497 62858787399231642214614373)
              ·
                refine ⟨11786022637355932915240195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62858787399231642214614373 11786022637355932915240195)
                ·
                  refine ⟨17679033956033899372860293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11786022637355932915240195 17679033956033899372860293)
                  ·
                    refine ⟨3314818866756356132411305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17679033956033899372860293 3314818866756356132411305)
                    ·
                      refine ⟨2486114150067267099308479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3314818866756356132411305 2486114150067267099308479)
                      ·
                        rfl

theorem cell23_4841690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 1, 4, 2].length) (baseStart_4841690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841690 prefixEnd_4841690 := by exact prefixLift 4841690
  have htrace : WordTrace (prefixWord ++ tailWord_4841690) baseStart_4841690 baseEnd_4841690 := by
    simpa [prefixWord, tailWord_4841690, baseEnd_4841690] using wordTrace_append hprefix tailTrace_4841690
  have hstable : (prefixWord ++ tailWord_4841690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841690).length < 2 ^ (prefixWord ++ tailWord_4841690).sum := by decide
  have hdescent : baseEnd_4841690 < baseStart_4841690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841707 : List Nat := [1, 1, 1, 1, 2, 5, 2, 4, 2, 2, 2]
def baseStart_4841707 : Nat := 118140960795 + 4841707 * 2 ^ 59
def prefixEnd_4841707 : Nat := 4983230072969 + 3 ^ 40 * 4841707 * 2
def baseEnd_4841707 : Nat := 2486122879238393532795901

theorem tailTrace_4841707 : CollatzResearch.WordTrace tailWord_4841707 prefixEnd_4841707 2486122879238393532795901 := by
  unfold tailWord_4841707
  simp only [CollatzResearch.WordTrace]
  refine ⟨176591561870329911568019375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117727707913553274378679583 176591561870329911568019375)
  ·
    refine ⟨264887342805494867352029063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176591561870329911568019375 264887342805494867352029063)
    ·
      refine ⟨397331014208242301028043595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264887342805494867352029063 397331014208242301028043595)
      ·
        refine ⟨595996521312363451542065393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397331014208242301028043595 595996521312363451542065393)
        ·
          refine ⟨446997390984272588656549045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 595996521312363451542065393 446997390984272588656549045)
          ·
            refine ⟨41906005404775555186551473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 446997390984272588656549045 41906005404775555186551473)
            ·
              refine ⟨31429504053581666389913605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41906005404775555186551473 31429504053581666389913605)
              ·
                refine ⟨5893032010046562448108801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31429504053581666389913605 5893032010046562448108801)
                ·
                  refine ⟨4419774007534921836081601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5893032010046562448108801 4419774007534921836081601)
                  ·
                    refine ⟨3314830505651191377061201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4419774007534921836081601 3314830505651191377061201)
                    ·
                      refine ⟨2486122879238393532795901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3314830505651191377061201 2486122879238393532795901)
                      ·
                        rfl

theorem cell23_4841707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 4, 2, 2, 2].length) (baseStart_4841707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841707 prefixEnd_4841707 := by exact prefixLift 4841707
  have htrace : WordTrace (prefixWord ++ tailWord_4841707) baseStart_4841707 baseEnd_4841707 := by
    simpa [prefixWord, tailWord_4841707, baseEnd_4841707] using wordTrace_append hprefix tailTrace_4841707
  have hstable : (prefixWord ++ tailWord_4841707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841707).length < 2 ^ (prefixWord ++ tailWord_4841707).sum := by decide
  have hdescent : baseEnd_4841707 < baseStart_4841707 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841713 : List Nat := [1, 2, 2, 2, 2, 1, 5, 1, 7]
def baseStart_4841713 : Nat := 118140960795 + 4841713 * 2 ^ 59
def prefixEnd_4841713 : Nat := 4983230072969 + 3 ^ 40 * 4841713 * 2
def baseEnd_4841713 : Nat := 276236217791368945480097

theorem tailTrace_4841713 : CollatzResearch.WordTrace tailWord_4841713 prefixEnd_4841713 276236217791368945480097 := by
  unfold tailWord_4841713
  simp only [CollatzResearch.WordTrace]
  refine ⟨176591780708308174592737793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117727853805538783061825195 176591780708308174592737793)
  ·
    refine ⟨132443835531231130944553345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176591780708308174592737793 132443835531231130944553345)
    ·
      refine ⟨99332876648423348208415009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132443835531231130944553345 99332876648423348208415009)
      ·
        refine ⟨74499657486317511156311257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99332876648423348208415009 74499657486317511156311257)
        ·
          refine ⟨55874743114738133367233443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74499657486317511156311257 55874743114738133367233443)
          ·
            refine ⟨83812114672107200050850165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55874743114738133367233443 83812114672107200050850165)
            ·
              refine ⟨7857385750510050004767203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83812114672107200050850165 7857385750510050004767203)
              ·
                refine ⟨11786078625765075007150805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7857385750510050004767203 11786078625765075007150805)
                ·
                  refine ⟨276236217791368945480097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11786078625765075007150805 276236217791368945480097)
                  ·
                    rfl

theorem cell23_4841713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 7].length) (baseStart_4841713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841713 prefixEnd_4841713 := by exact prefixLift 4841713
  have htrace : WordTrace (prefixWord ++ tailWord_4841713) baseStart_4841713 baseEnd_4841713 := by
    simpa [prefixWord, tailWord_4841713, baseEnd_4841713] using wordTrace_append hprefix tailTrace_4841713
  have hstable : (prefixWord ++ tailWord_4841713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841713).length < 2 ^ (prefixWord ++ tailWord_4841713).sum := by decide
  have hdescent : baseEnd_4841713 < baseStart_4841713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841724 : List Nat := [2, 2, 2, 1, 4, 2, 1, 3, 2, 2, 2]
def baseStart_4841724 : Nat := 118140960795 + 4841724 * 2 ^ 59
def prefixEnd_4841724 : Nat := 4983230072969 + 3 ^ 40 * 4841724 * 2
def baseEnd_4841724 : Nat := 2486131608409519966283323

theorem tailTrace_4841724 : CollatzResearch.WordTrace tailWord_4841724 prefixEnd_4841724 2486131608409519966283323 := by
  unfold tailWord_4841724
  simp only [CollatzResearch.WordTrace]
  refine ⟨88296090955634161735694113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117728121274178882314258817 88296090955634161735694113)
  ·
    refine ⟨66222068216725621301770585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88296090955634161735694113 66222068216725621301770585)
    ·
      refine ⟨49666551162544215976327939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66222068216725621301770585 49666551162544215976327939)
      ·
        refine ⟨74499826743816323964491909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49666551162544215976327939 74499826743816323964491909)
        ·
          refine ⟨13968717514465560743342233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74499826743816323964491909 13968717514465560743342233)
          ·
            refine ⟨10476538135849170557506675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13968717514465560743342233 10476538135849170557506675)
            ·
              refine ⟨15714807203773755836260013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10476538135849170557506675 15714807203773755836260013)
              ·
                refine ⟨5893052701415158438597505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15714807203773755836260013 5893052701415158438597505)
                ·
                  refine ⟨4419789526061368828948129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5893052701415158438597505 4419789526061368828948129)
                  ·
                    refine ⟨3314842144546026621711097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4419789526061368828948129 3314842144546026621711097)
                    ·
                      refine ⟨2486131608409519966283323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3314842144546026621711097 2486131608409519966283323)
                      ·
                        rfl

theorem cell23_4841724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 3, 2, 2, 2].length) (baseStart_4841724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841724 prefixEnd_4841724 := by exact prefixLift 4841724
  have htrace : WordTrace (prefixWord ++ tailWord_4841724) baseStart_4841724 baseEnd_4841724 := by
    simpa [prefixWord, tailWord_4841724, baseEnd_4841724] using wordTrace_append hprefix tailTrace_4841724
  have hstable : (prefixWord ++ tailWord_4841724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841724).length < 2 ^ (prefixWord ++ tailWord_4841724).sum := by decide
  have hdescent : baseEnd_4841724 < baseStart_4841724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841758 : List Nat := [4, 3, 2, 1, 1, 2, 2, 2, 2, 2, 2]
def baseStart_4841758 : Nat := 118140960795 + 4841758 * 2 ^ 59
def prefixEnd_4841758 : Nat := 4983230072969 + 3 ^ 40 * 4841758 * 2
def baseEnd_4841758 : Nat := 2486149066751772833258167

theorem tailTrace_4841758 : CollatzResearch.WordTrace tailWord_4841758 prefixEnd_4841758 2486149066751772833258167 := by
  unfold tailWord_4841758
  simp only [CollatzResearch.WordTrace]
  refine ⟨22074177749143143409765741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117728947995430098185417285 22074177749143143409765741)
  ·
    refine ⟨8277816655928678778662153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22074177749143143409765741 8277816655928678778662153)
    ·
      refine ⟨6208362491946509083996615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8277816655928678778662153 6208362491946509083996615)
      ·
        refine ⟨9312543737919763625994923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6208362491946509083996615 9312543737919763625994923)
        ·
          refine ⟨13968815606879645438992385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9312543737919763625994923 13968815606879645438992385)
          ·
            refine ⟨10476611705159734079244289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13968815606879645438992385 10476611705159734079244289)
            ·
              refine ⟨7857458778869800559433217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10476611705159734079244289 7857458778869800559433217)
              ·
                refine ⟨5893094084152350419574913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7857458778869800559433217 5893094084152350419574913)
                ·
                  refine ⟨4419820563114262814681185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5893094084152350419574913 4419820563114262814681185)
                  ·
                    refine ⟨3314865422335697111010889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4419820563114262814681185 3314865422335697111010889)
                    ·
                      refine ⟨2486149066751772833258167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3314865422335697111010889 2486149066751772833258167)
                      ·
                        rfl

theorem cell23_4841758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_4841758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841758 prefixEnd_4841758 := by exact prefixLift 4841758
  have htrace : WordTrace (prefixWord ++ tailWord_4841758) baseStart_4841758 baseEnd_4841758 := by
    simpa [prefixWord, tailWord_4841758, baseEnd_4841758] using wordTrace_append hprefix tailTrace_4841758
  have hstable : (prefixWord ++ tailWord_4841758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841758).length < 2 ^ (prefixWord ++ tailWord_4841758).sum := by decide
  have hdescent : baseEnd_4841758 < baseStart_4841758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841760 : List Nat := [2, 1, 1, 5, 2, 1, 2, 2, 2, 5]
def baseStart_4841760 : Nat := 118140960795 + 4841760 * 2 ^ 59
def prefixEnd_4841760 : Nat := 4983230072969 + 3 ^ 40 * 4841760 * 2
def baseEnd_4841760 : Nat := 828716697904360608477719

theorem tailTrace_4841760 : CollatzResearch.WordTrace tailWord_4841760 prefixEnd_4841760 828716697904360608477719 := by
  unfold tailWord_4841760
  simp only [CollatzResearch.WordTrace]
  refine ⟨88296747469568950809849367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117728996626091934413132489 88296747469568950809849367)
  ·
    refine ⟨132445121204353426214774051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88296747469568950809849367 132445121204353426214774051)
    ·
      refine ⟨198667681806530139322161077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132445121204353426214774051 198667681806530139322161077)
      ·
        refine ⟨18625095169362200561452601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 198667681806530139322161077 18625095169362200561452601)
        ·
          refine ⟨13968821377021650421089451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18625095169362200561452601 13968821377021650421089451)
          ·
            refine ⟨20953232065532475631634177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13968821377021650421089451 20953232065532475631634177)
            ·
              refine ⟨15714924049149356723725633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20953232065532475631634177 15714924049149356723725633)
              ·
                refine ⟨11786193036862017542794225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15714924049149356723725633 11786193036862017542794225)
                ·
                  refine ⟨8839644777646513157095669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11786193036862017542794225 8839644777646513157095669)
                  ·
                    refine ⟨828716697904360608477719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8839644777646513157095669 828716697904360608477719)
                    ·
                      rfl

theorem cell23_4841760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 2, 5].length) (baseStart_4841760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841760 prefixEnd_4841760 := by exact prefixLift 4841760
  have htrace : WordTrace (prefixWord ++ tailWord_4841760) baseStart_4841760 baseEnd_4841760 := by
    simpa [prefixWord, tailWord_4841760, baseEnd_4841760] using wordTrace_append hprefix tailTrace_4841760
  have hstable : (prefixWord ++ tailWord_4841760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841760).length < 2 ^ (prefixWord ++ tailWord_4841760).sum := by decide
  have hdescent : baseEnd_4841760 < baseStart_4841760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841764 : List Nat := [2, 3, 1, 3, 1, 4, 2, 2, 5]
def baseStart_4841764 : Nat := 118140960795 + 4841764 * 2 ^ 59
def prefixEnd_4841764 : Nat := 4983230072969 + 3 ^ 40 * 4841764 * 2
def baseEnd_4841764 : Nat := 276239127515077756642571

theorem tailTrace_4841764 : CollatzResearch.WordTrace tailWord_4841764 prefixEnd_4841764 276239127515077756642571 := by
  unfold tailWord_4841764
  simp only [CollatzResearch.WordTrace]
  refine ⟨88296820415561705151422173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117729093887415606868562897 88296820415561705151422173)
  ·
    refine ⟨33111307655835639431783315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88296820415561705151422173 33111307655835639431783315)
    ·
      refine ⟨49666961483753459147674973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33111307655835639431783315 49666961483753459147674973)
      ·
        refine ⟨18625110556407547180378115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49666961483753459147674973 18625110556407547180378115)
        ·
          refine ⟨27937665834611320770567173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18625110556407547180378115 27937665834611320770567173)
          ·
            refine ⟨5238312343989622644481345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27937665834611320770567173 5238312343989622644481345)
            ·
              refine ⟨3928734257992216983361009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5238312343989622644481345 3928734257992216983361009)
              ·
                refine ⟨2946550693494162737520757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3928734257992216983361009 2946550693494162737520757)
                ·
                  refine ⟨276239127515077756642571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2946550693494162737520757 276239127515077756642571)
                  ·
                    rfl

theorem cell23_4841764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 2, 5].length) (baseStart_4841764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841764 prefixEnd_4841764 := by exact prefixLift 4841764
  have htrace : WordTrace (prefixWord ++ tailWord_4841764) baseStart_4841764 baseEnd_4841764 := by
    simpa [prefixWord, tailWord_4841764, baseEnd_4841764] using wordTrace_append hprefix tailTrace_4841764
  have hstable : (prefixWord ++ tailWord_4841764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841764).length < 2 ^ (prefixWord ++ tailWord_4841764).sum := by decide
  have hdescent : baseEnd_4841764 < baseStart_4841764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841774 : List Nat := [4, 1, 3, 3, 1, 1, 1, 1, 2, 3, 3]
def baseStart_4841774 : Nat := 118140960795 + 4841774 * 2 ^ 59
def prefixEnd_4841774 : Nat := 4983230072969 + 3 ^ 40 * 4841774 * 2
def baseEnd_4841774 : Nat := 2486157282442244770658093

theorem tailTrace_4841774 : CollatzResearch.WordTrace tailWord_4841774 prefixEnd_4841774 2486157282442244770658093 := by
  unfold tailWord_4841774
  simp only [CollatzResearch.WordTrace]
  refine ⟨22074250695135897751338547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117729337040724788007138917 22074250695135897751338547)
  ·
    refine ⟨33111376042703846627007821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22074250695135897751338547 33111376042703846627007821)
    ·
      refine ⟨12416766016013942485127933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33111376042703846627007821 12416766016013942485127933)
      ·
        refine ⟨4656287256005228431922975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12416766016013942485127933 4656287256005228431922975)
        ·
          refine ⟨6984430884007842647884463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4656287256005228431922975 6984430884007842647884463)
          ·
            refine ⟨10476646326011763971826695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6984430884007842647884463 10476646326011763971826695)
            ·
              refine ⟨15714969489017645957740043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10476646326011763971826695 15714969489017645957740043)
              ·
                refine ⟨23572454233526468936610065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15714969489017645957740043 23572454233526468936610065)
                ·
                  refine ⟨17679340675144851702457549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23572454233526468936610065 17679340675144851702457549)
                  ·
                    refine ⟨6629752753179319388421581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17679340675144851702457549 6629752753179319388421581)
                    ·
                      refine ⟨2486157282442244770658093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6629752753179319388421581 2486157282442244770658093)
                      ·
                        rfl

theorem cell23_4841774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_4841774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841774 prefixEnd_4841774 := by exact prefixLift 4841774
  have htrace : WordTrace (prefixWord ++ tailWord_4841774) baseStart_4841774 baseEnd_4841774 := by
    simpa [prefixWord, tailWord_4841774, baseEnd_4841774] using wordTrace_append hprefix tailTrace_4841774
  have hstable : (prefixWord ++ tailWord_4841774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841774).length < 2 ^ (prefixWord ++ tailWord_4841774).sum := by decide
  have hdescent : baseEnd_4841774 < baseStart_4841774 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841823 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 6]
def baseStart_4841823 : Nat := 118140960795 + 4841823 * 2 ^ 59
def prefixEnd_4841823 : Nat := 4983230072969 + 3 ^ 40 * 4841823 * 2
def baseEnd_4841823 : Nat := 2486182442994315078945367

theorem tailTrace_4841823 : CollatzResearch.WordTrace tailWord_4841823 prefixEnd_4841823 2486182442994315078945367 := by
  unfold tailWord_4841823
  simp only [CollatzResearch.WordTrace]
  refine ⟨176595792737909663379242123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117730528491939775586161415 176595792737909663379242123)
  ·
    refine ⟨264893689106864495068863185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176595792737909663379242123 264893689106864495068863185)
    ·
      refine ⟨198670266830148371301647389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264893689106864495068863185 198670266830148371301647389)
      ·
        refine ⟨74501350061305639238117771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198670266830148371301647389 74501350061305639238117771)
        ·
          refine ⟨111752025091958458857176657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74501350061305639238117771 111752025091958458857176657)
          ·
            refine ⟨83814018818968844142882493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111752025091958458857176657 83814018818968844142882493)
            ·
              refine ⟨31430257057113316553580935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83814018818968844142882493 31430257057113316553580935)
              ·
                refine ⟨47145385585669974830371403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31430257057113316553580935 47145385585669974830371403)
                ·
                  refine ⟨70718078378504962245557105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47145385585669974830371403 70718078378504962245557105)
                  ·
                    refine ⟨53038558783878721684167829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 70718078378504962245557105 53038558783878721684167829)
                    ·
                      refine ⟨2486182442994315078945367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53038558783878721684167829 2486182442994315078945367)
                      ·
                        rfl

theorem cell23_4841823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_4841823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841823 prefixEnd_4841823 := by exact prefixLift 4841823
  have htrace : WordTrace (prefixWord ++ tailWord_4841823) baseStart_4841823 baseEnd_4841823 := by
    simpa [prefixWord, tailWord_4841823, baseEnd_4841823] using wordTrace_append hprefix tailTrace_4841823
  have hstable : (prefixWord ++ tailWord_4841823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841823).length < 2 ^ (prefixWord ++ tailWord_4841823).sum := by decide
  have hdescent : baseEnd_4841823 < baseStart_4841823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841837 : List Nat := [1, 5, 1, 1, 1, 2, 5, 1, 6]
def baseStart_4841837 : Nat := 118140960795 + 4841837 * 2 ^ 59
def prefixEnd_4841837 : Nat := 4983230072969 + 3 ^ 40 * 4841837 * 2
def baseEnd_4841837 : Nat := 276243292413719780463367

theorem tailTrace_4841837 : CollatzResearch.WordTrace tailWord_4841837 prefixEnd_4841837 276243292413719780463367 := by
  unfold tailWord_4841837
  simp only [CollatzResearch.WordTrace]
  refine ⟨176596303359858943770251765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117730868906572629180167843 176596303359858943770251765)
  ·
    refine ⟨16555903439986775978461103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 176596303359858943770251765 16555903439986775978461103)
    ·
      refine ⟨24833855159980163967691655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16555903439986775978461103 24833855159980163967691655)
      ·
        refine ⟨37250782739970245951537483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24833855159980163967691655 37250782739970245951537483)
        ·
          refine ⟨55876174109955368927306225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37250782739970245951537483 55876174109955368927306225)
          ·
            refine ⟨41907130582466526695479669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55876174109955368927306225 41907130582466526695479669)
            ·
              refine ⟨3928793492106236877701219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41907130582466526695479669 3928793492106236877701219)
              ·
                refine ⟨5893190238159355316551829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3928793492106236877701219 5893190238159355316551829)
                ·
                  refine ⟨276243292413719780463367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5893190238159355316551829 276243292413719780463367)
                  ·
                    rfl

theorem cell23_4841837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_4841837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841837 prefixEnd_4841837 := by exact prefixLift 4841837
  have htrace : WordTrace (prefixWord ++ tailWord_4841837) baseStart_4841837 baseEnd_4841837 := by
    simpa [prefixWord, tailWord_4841837, baseEnd_4841837] using wordTrace_append hprefix tailTrace_4841837
  have hstable : (prefixWord ++ tailWord_4841837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841837).length < 2 ^ (prefixWord ++ tailWord_4841837).sum := by decide
  have hdescent : baseEnd_4841837 < baseStart_4841837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841881 : List Nat := [1, 2, 1, 2, 1, 4, 5, 2, 1, 1, 3]
def baseStart_4841881 : Nat := 118140960795 + 4841881 * 2 ^ 59
def prefixEnd_4841881 : Nat := 4983230072969 + 3 ^ 40 * 4841881 * 2
def baseEnd_4841881 : Nat := 2486212224872275852020101

theorem tailTrace_4841881 : CollatzResearch.WordTrace tailWord_4841881 prefixEnd_4841881 2486212224872275852020101 := by
  unfold tailWord_4841881
  simp only [CollatzResearch.WordTrace]
  refine ⟨176597908171699539284853497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117731938781133026189902331 176597908171699539284853497)
  ·
    refine ⟨132448431128774654463640123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176597908171699539284853497 132448431128774654463640123)
    ·
      refine ⟨198672646693161981695460185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132448431128774654463640123 198672646693161981695460185)
      ·
        refine ⟨149004485019871486271595139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198672646693161981695460185 149004485019871486271595139)
        ·
          refine ⟨223506727529807229407392709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149004485019871486271595139 223506727529807229407392709)
          ·
            refine ⟨41907511411838855513886133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 223506727529807229407392709 41907511411838855513886133)
            ·
              refine ⟨3928829194859892704426825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41907511411838855513886133 3928829194859892704426825)
              ·
                refine ⟨2946621896144919528320119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3928829194859892704426825 2946621896144919528320119)
                ·
                  refine ⟨4419932844217379292480179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2946621896144919528320119 4419932844217379292480179)
                  ·
                    refine ⟨6629899266326068938720269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4419932844217379292480179 6629899266326068938720269)
                    ·
                      refine ⟨2486212224872275852020101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6629899266326068938720269 2486212224872275852020101)
                      ·
                        rfl

theorem cell23_4841881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 2, 1, 1, 3].length) (baseStart_4841881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841881 prefixEnd_4841881 := by exact prefixLift 4841881
  have htrace : WordTrace (prefixWord ++ tailWord_4841881) baseStart_4841881 baseEnd_4841881 := by
    simpa [prefixWord, tailWord_4841881, baseEnd_4841881] using wordTrace_append hprefix tailTrace_4841881
  have hstable : (prefixWord ++ tailWord_4841881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841881).length < 2 ^ (prefixWord ++ tailWord_4841881).sum := by decide
  have hdescent : baseEnd_4841881 < baseStart_4841881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841900 : List Nat := [2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 4]
def baseStart_4841900 : Nat := 118140960795 + 4841900 * 2 ^ 59
def prefixEnd_4841900 : Nat := 4983230072969 + 3 ^ 40 * 4841900 * 2
def baseEnd_4841900 : Nat := 2486221981004711277682513

theorem tailTrace_4841900 : CollatzResearch.WordTrace tailWord_4841900 prefixEnd_4841900 2486221981004711277682513 := by
  unfold tailWord_4841900
  simp only [CollatzResearch.WordTrace]
  refine ⟨88299300579315352764897577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117732400772420470353196769 88299300579315352764897577)
  ·
    refine ⟨66224475434486514573673183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88299300579315352764897577 66224475434486514573673183)
    ·
      refine ⟨99336713151729771860509775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66224475434486514573673183 99336713151729771860509775)
      ·
        refine ⟨149005069727594657790764663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99336713151729771860509775 149005069727594657790764663)
        ·
          refine ⟨223507604591391986686146995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149005069727594657790764663 223507604591391986686146995)
          ·
            refine ⟨335261406887087980029220493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223507604591391986686146995 335261406887087980029220493)
            ·
              refine ⟨125723027582657992510957685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 335261406887087980029220493 125723027582657992510957685)
              ·
                refine ⟨11786533835874186797902283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 125723027582657992510957685 11786533835874186797902283)
                ·
                  refine ⟨17679800753811280196853425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11786533835874186797902283 17679800753811280196853425)
                  ·
                    refine ⟨13259850565358460147640069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17679800753811280196853425 13259850565358460147640069)
                    ·
                      refine ⟨2486221981004711277682513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13259850565358460147640069 2486221981004711277682513)
                      ·
                        rfl

theorem cell23_4841900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 4].length) (baseStart_4841900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841900 prefixEnd_4841900 := by exact prefixLift 4841900
  have htrace : WordTrace (prefixWord ++ tailWord_4841900) baseStart_4841900 baseEnd_4841900 := by
    simpa [prefixWord, tailWord_4841900, baseEnd_4841900] using wordTrace_append hprefix tailTrace_4841900
  have hstable : (prefixWord ++ tailWord_4841900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841900).length < 2 ^ (prefixWord ++ tailWord_4841900).sum := by decide
  have hdescent : baseEnd_4841900 < baseStart_4841900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841901 : List Nat := [1, 5, 2, 2, 2, 2, 1, 2, 1, 5]
def baseStart_4841901 : Nat := 118140960795 + 4841901 * 2 ^ 59
def prefixEnd_4841901 : Nat := 4983230072969 + 3 ^ 40 * 4841901 * 2
def baseEnd_4841901 : Nat := 828740831495121924590003

theorem tailTrace_4841901 : CollatzResearch.WordTrace tailWord_4841901 prefixEnd_4841901 828740831495121924590003 := by
  unfold tailWord_4841901
  simp only [CollatzResearch.WordTrace]
  refine ⟨176598637631627082700581557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117732425087751388467054371 176598637631627082700581557)
  ·
    refine ⟨16556122277965039003179521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 176598637631627082700581557 16556122277965039003179521)
    ·
      refine ⟨12417091708473779252384641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16556122277965039003179521 12417091708473779252384641)
      ·
        refine ⟨9312818781355334439288481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12417091708473779252384641 9312818781355334439288481)
        ·
          refine ⟨6984614086016500829466361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9312818781355334439288481 6984614086016500829466361)
          ·
            refine ⟨5238460564512375622099771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6984614086016500829466361 5238460564512375622099771)
            ·
              refine ⟨7857690846768563433149657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5238460564512375622099771 7857690846768563433149657)
              ·
                refine ⟨5893268135076422574862243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7857690846768563433149657 5893268135076422574862243)
                ·
                  refine ⟨8839902202614633862293365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5893268135076422574862243 8839902202614633862293365)
                  ·
                    refine ⟨828740831495121924590003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8839902202614633862293365 828740831495121924590003)
                    ·
                      rfl

theorem cell23_4841901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_4841901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841901 prefixEnd_4841901 := by exact prefixLift 4841901
  have htrace : WordTrace (prefixWord ++ tailWord_4841901) baseStart_4841901 baseEnd_4841901 := by
    simpa [prefixWord, tailWord_4841901, baseEnd_4841901] using wordTrace_append hprefix tailTrace_4841901
  have hstable : (prefixWord ++ tailWord_4841901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841901).length < 2 ^ (prefixWord ++ tailWord_4841901).sum := by decide
  have hdescent : baseEnd_4841901 < baseStart_4841901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841917 : List Nat := [1, 4, 1, 2, 2, 3, 1, 2, 1, 2, 4]
def baseStart_4841917 : Nat := 118140960795 + 4841917 * 2 ^ 59
def prefixEnd_4841917 : Nat := 4983230072969 + 3 ^ 40 * 4841917 * 2
def baseEnd_4841917 : Nat := 2486230710175837711169935

theorem tailTrace_4841917 : CollatzResearch.WordTrace tailWord_4841917 prefixEnd_4841917 2486230710175837711169935 := by
  unfold tailWord_4841917
  simp only [CollatzResearch.WordTrace]
  refine ⟨176599221199569117433164005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117732814133046078288776003 176599221199569117433164005)
  ·
    refine ⟨33112353974919209518718251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176599221199569117433164005 33112353974919209518718251)
    ·
      refine ⟨49668530962378814278077377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33112353974919209518718251 49668530962378814278077377)
      ·
        refine ⟨37251398221784110708558033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49668530962378814278077377 37251398221784110708558033)
        ·
          refine ⟨27938548666338083031418525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37251398221784110708558033 27938548666338083031418525)
          ·
            refine ⟨10476955749876781136781947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27938548666338083031418525 10476955749876781136781947)
            ·
              refine ⟨15715433624815171705172921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10476955749876781136781947 15715433624815171705172921)
              ·
                refine ⟨11786575218611378778879691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15715433624815171705172921 11786575218611378778879691)
                ·
                  refine ⟨17679862827917068168319537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11786575218611378778879691 17679862827917068168319537)
                  ·
                    refine ⟨13259897120937801126239653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17679862827917068168319537 13259897120937801126239653)
                    ·
                      refine ⟨2486230710175837711169935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13259897120937801126239653 2486230710175837711169935)
                      ·
                        rfl

theorem cell23_4841917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_4841917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841917 prefixEnd_4841917 := by exact prefixLift 4841917
  have htrace : WordTrace (prefixWord ++ tailWord_4841917) baseStart_4841917 baseEnd_4841917 := by
    simpa [prefixWord, tailWord_4841917, baseEnd_4841917] using wordTrace_append hprefix tailTrace_4841917
  have hstable : (prefixWord ++ tailWord_4841917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841917).length < 2 ^ (prefixWord ++ tailWord_4841917).sum := by decide
  have hdescent : baseEnd_4841917 < baseStart_4841917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841937 : List Nat := [1, 2, 2, 1, 2, 1, 1, 5, 4, 1, 3]
def baseStart_4841937 : Nat := 118140960795 + 4841937 * 2 ^ 59
def prefixEnd_4841937 : Nat := 4983230072969 + 3 ^ 40 * 4841937 * 2
def baseEnd_4841937 : Nat := 2486240979788927632919843

theorem tailTrace_4841937 : CollatzResearch.WordTrace tailWord_4841937 prefixEnd_4841937 2486240979788927632919843 := by
  unfold tailWord_4841937
  simp only [CollatzResearch.WordTrace]
  refine ⟨176599950659496660848892065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117733300439664440565928043 176599950659496660848892065)
  ·
    refine ⟨132449962994622495636669049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176599950659496660848892065 132449962994622495636669049)
    ·
      refine ⟨99337472245966871727501787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132449962994622495636669049 99337472245966871727501787)
      ·
        refine ⟨149006208368950307591252681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99337472245966871727501787 149006208368950307591252681)
        ·
          refine ⟨111754656276712730693439511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149006208368950307591252681 111754656276712730693439511)
          ·
            refine ⟨167631984415069096040159267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111754656276712730693439511 167631984415069096040159267)
            ·
              refine ⟨251447976622603644060238901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167631984415069096040159267 251447976622603644060238901)
              ·
                refine ⟨23573247808369091630647397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 251447976622603644060238901 23573247808369091630647397)
                ·
                  refine ⟨4419983964069204680746387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23573247808369091630647397 4419983964069204680746387)
                  ·
                    refine ⟨6629975946103807021119581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4419983964069204680746387 6629975946103807021119581)
                    ·
                      refine ⟨2486240979788927632919843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6629975946103807021119581 2486240979788927632919843)
                      ·
                        rfl

theorem cell23_4841937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 4, 1, 3].length) (baseStart_4841937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841937 prefixEnd_4841937 := by exact prefixLift 4841937
  have htrace : WordTrace (prefixWord ++ tailWord_4841937) baseStart_4841937 baseEnd_4841937 := by
    simpa [prefixWord, tailWord_4841937, baseEnd_4841937] using wordTrace_append hprefix tailTrace_4841937
  have hstable : (prefixWord ++ tailWord_4841937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841937).length < 2 ^ (prefixWord ++ tailWord_4841937).sum := by decide
  have hdescent : baseEnd_4841937 < baseStart_4841937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841964 : List Nat := [2, 2, 1, 1, 2, 1, 4, 4, 1, 3, 2]
def baseStart_4841964 : Nat := 118140960795 + 4841964 * 2 ^ 59
def prefixEnd_4841964 : Nat := 4983230072969 + 3 ^ 40 * 4841964 * 2
def baseEnd_4841964 : Nat := 2486254843766599027282219

theorem tailTrace_4841964 : CollatzResearch.WordTrace tailWord_4841964 prefixEnd_4841964 2486254843766599027282219 := by
  unfold tailWord_4841964
  simp only [CollatzResearch.WordTrace]
  refine ⟨88300467715199422230062473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117733956953599229640083297 88300467715199422230062473)
  ·
    refine ⟨66225350786399566672546855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88300467715199422230062473 66225350786399566672546855)
    ·
      refine ⟨99338026179599350008820283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66225350786399566672546855 99338026179599350008820283)
      ·
        refine ⟨149007039269399025013230425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99338026179599350008820283 149007039269399025013230425)
        ·
          refine ⟨111755279452049268759922819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149007039269399025013230425 111755279452049268759922819)
          ·
            refine ⟨167632919178073903139884229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111755279452049268759922819 167632919178073903139884229)
            ·
              refine ⟨31431172345888856838728293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 167632919178073903139884229 31431172345888856838728293)
              ·
                refine ⟨5893344814854160657261555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31431172345888856838728293 5893344814854160657261555)
                ·
                  refine ⟨8840017222281240985892333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5893344814854160657261555 8840017222281240985892333)
                  ·
                    refine ⟨3315006458355465369709625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8840017222281240985892333 3315006458355465369709625)
                    ·
                      refine ⟨2486254843766599027282219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3315006458355465369709625 2486254843766599027282219)
                      ·
                        rfl

theorem cell23_4841964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 3, 2].length) (baseStart_4841964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841964 prefixEnd_4841964 := by exact prefixLift 4841964
  have htrace : WordTrace (prefixWord ++ tailWord_4841964) baseStart_4841964 baseEnd_4841964 := by
    simpa [prefixWord, tailWord_4841964, baseEnd_4841964] using wordTrace_append hprefix tailTrace_4841964
  have hstable : (prefixWord ++ tailWord_4841964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841964).length < 2 ^ (prefixWord ++ tailWord_4841964).sum := by decide
  have hdescent : baseEnd_4841964 < baseStart_4841964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841980 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 1, 3, 5]
def baseStart_4841980 : Nat := 118140960795 + 4841980 * 2 ^ 59
def prefixEnd_4841980 : Nat := 4983230072969 + 3 ^ 40 * 4841980 * 2
def baseEnd_4841980 : Nat := 2486263059457070964682145

theorem tailTrace_4841980 : CollatzResearch.WordTrace tailWord_4841980 prefixEnd_4841980 2486263059457070964682145 := by
  unfold tailWord_4841980
  simp only [CollatzResearch.WordTrace]
  refine ⟨88300759499170439596353697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117734345998893919461804929 88300759499170439596353697)
  ·
    refine ⟨66225569624377829697265273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88300759499170439596353697 66225569624377829697265273)
    ·
      refine ⟨49669177218283372272948955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66225569624377829697265273 49669177218283372272948955)
      ·
        refine ⟨74503765827425058409423433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49669177218283372272948955 74503765827425058409423433)
        ·
          refine ⟨55877824370568793807067575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74503765827425058409423433 55877824370568793807067575)
          ·
            refine ⟨83816736555853190710601363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55877824370568793807067575 83816736555853190710601363)
            ·
              refine ⟨125725104833779786065902045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83816736555853190710601363 125725104833779786065902045)
              ·
                refine ⟨47146914312667419774713267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125725104833779786065902045 47146914312667419774713267)
                ·
                  refine ⟨70720371469001129662069901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47146914312667419774713267 70720371469001129662069901)
                  ·
                    refine ⟨26520139300875423623276213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 70720371469001129662069901 26520139300875423623276213)
                    ·
                      refine ⟨2486263059457070964682145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26520139300875423623276213 2486263059457070964682145)
                      ·
                        rfl

theorem cell23_4841980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_4841980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841980 prefixEnd_4841980 := by exact prefixLift 4841980
  have htrace : WordTrace (prefixWord ++ tailWord_4841980) baseStart_4841980 baseEnd_4841980 := by
    simpa [prefixWord, tailWord_4841980, baseEnd_4841980] using wordTrace_append hprefix tailTrace_4841980
  have hstable : (prefixWord ++ tailWord_4841980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841980).length < 2 ^ (prefixWord ++ tailWord_4841980).sum := by decide
  have hdescent : baseEnd_4841980 < baseStart_4841980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4841988 : List Nat := [2, 3, 2, 3, 1, 3, 1, 2, 2, 1, 3]
def baseStart_4841988 : Nat := 118140960795 + 4841988 * 2 ^ 59
def prefixEnd_4841988 : Nat := 4983230072969 + 3 ^ 40 * 4841988 * 2
def baseEnd_4841988 : Nat := 2486267167302306933382109

theorem tailTrace_4841988 : CollatzResearch.WordTrace tailWord_4841988 prefixEnd_4841988 2486267167302306933382109 := by
  unfold tailWord_4841988
  simp only [CollatzResearch.WordTrace]
  refine ⟨88300905391155948279499309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117734540521541264372665745 88300905391155948279499309)
  ·
    refine ⟨33112839521683480604812241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88300905391155948279499309 33112839521683480604812241)
    ·
      refine ⟨24834629641262610453609181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33112839521683480604812241 24834629641262610453609181)
      ·
        refine ⟨9312986115473478920103443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24834629641262610453609181 9312986115473478920103443)
        ·
          refine ⟨13969479173210218380155165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9312986115473478920103443 13969479173210218380155165)
          ·
            refine ⟨5238554689953831892558187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13969479173210218380155165 5238554689953831892558187)
            ·
              refine ⟨7857832034930747838837281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5238554689953831892558187 7857832034930747838837281)
              ·
                refine ⟨5893374026198060879127961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7857832034930747838837281 5893374026198060879127961)
                ·
                  refine ⟨4420030519648545659345971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5893374026198060879127961 4420030519648545659345971)
                  ·
                    refine ⟨6630045779472818489018957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4420030519648545659345971 6630045779472818489018957)
                    ·
                      refine ⟨2486267167302306933382109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6630045779472818489018957 2486267167302306933382109)
                      ·
                        rfl

theorem cell23_4841988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_4841988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4841988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4841988 prefixEnd_4841988 := by exact prefixLift 4841988
  have htrace : WordTrace (prefixWord ++ tailWord_4841988) baseStart_4841988 baseEnd_4841988 := by
    simpa [prefixWord, tailWord_4841988, baseEnd_4841988] using wordTrace_append hprefix tailTrace_4841988
  have hstable : (prefixWord ++ tailWord_4841988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4841988).length < 2 ^ (prefixWord ++ tailWord_4841988).sum := by decide
  have hdescent : baseEnd_4841988 < baseStart_4841988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4841988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842004 : List Nat := [2, 4, 3, 1, 1, 1, 2, 1, 2, 6]
def baseStart_4842004 : Nat := 118140960795 + 4842004 * 2 ^ 59
def prefixEnd_4842004 : Nat := 4983230072969 + 3 ^ 40 * 4842004 * 2
def baseEnd_4842004 : Nat := 828758460997592956927345

theorem tailTrace_4842004 : CollatzResearch.WordTrace tailWord_4842004 prefixEnd_4842004 828758460997592956927345 := by
  unfold tailWord_4842004
  simp only [CollatzResearch.WordTrace]
  refine ⟨88301197175126965645790533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117734929566835954194387377 88301197175126965645790533)
  ·
    refine ⟨16556474470336306058585725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88301197175126965645790533 16556474470336306058585725)
    ·
      refine ⟨6208677926376114771969647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16556474470336306058585725 6208677926376114771969647)
      ·
        refine ⟨9313016889564172157954471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6208677926376114771969647 9313016889564172157954471)
        ·
          refine ⟨13969525334346258236931707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9313016889564172157954471 13969525334346258236931707)
          ·
            refine ⟨20954288001519387355397561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13969525334346258236931707 20954288001519387355397561)
            ·
              refine ⟨15715716001139540516548171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20954288001519387355397561 15715716001139540516548171)
              ·
                refine ⟨23573574001709310774822257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15715716001139540516548171 23573574001709310774822257)
                ·
                  refine ⟨17680180501281983081116693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23573574001709310774822257 17680180501281983081116693)
                  ·
                    refine ⟨828758460997592956927345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17680180501281983081116693 828758460997592956927345)
                    ·
                      rfl

theorem cell23_4842004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_4842004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842004 prefixEnd_4842004 := by exact prefixLift 4842004
  have htrace : WordTrace (prefixWord ++ tailWord_4842004) baseStart_4842004 baseEnd_4842004 := by
    simpa [prefixWord, tailWord_4842004, baseEnd_4842004] using wordTrace_append hprefix tailTrace_4842004
  have hstable : (prefixWord ++ tailWord_4842004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842004).length < 2 ^ (prefixWord ++ tailWord_4842004).sum := by decide
  have hdescent : baseEnd_4842004 < baseStart_4842004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842034 : List Nat := [3, 2, 1, 1, 2, 1, 5, 3, 5]
def baseStart_4842034 : Nat := 118140960795 + 4842034 * 2 ^ 59
def prefixEnd_4842034 : Nat := 4983230072969 + 3 ^ 40 * 4842034 * 2
def baseEnd_4842034 : Nat := 276254531934712639267433

theorem tailTrace_4842034 : CollatzResearch.WordTrace tailWord_4842034 prefixEnd_4842034 276254531934712639267433 := by
  unfold tailWord_4842034
  simp only [CollatzResearch.WordTrace]
  refine ⟨44150872135036311603793289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117735659026763497610115437 44150872135036311603793289)
  ·
    refine ⟨33113154101277233702844967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44150872135036311603793289 33113154101277233702844967)
    ·
      refine ⟨49669731151915850554267451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33113154101277233702844967 49669731151915850554267451)
      ·
        refine ⟨74504596727873775831401177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49669731151915850554267451 74504596727873775831401177)
        ·
          refine ⟨55878447545905331873550883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74504596727873775831401177 55878447545905331873550883)
          ·
            refine ⟨83817671318857997810326325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55878447545905331873550883 83817671318857997810326325)
            ·
              refine ⟨7857906686142937294718093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83817671318857997810326325 7857906686142937294718093)
              ·
                refine ⟨2946715007303601485519285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7857906686142937294718093 2946715007303601485519285)
                ·
                  refine ⟨276254531934712639267433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2946715007303601485519285 276254531934712639267433)
                  ·
                    rfl

theorem cell23_4842034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 3, 5].length) (baseStart_4842034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842034 prefixEnd_4842034 := by exact prefixLift 4842034
  have htrace : WordTrace (prefixWord ++ tailWord_4842034) baseStart_4842034 baseEnd_4842034 := by
    simpa [prefixWord, tailWord_4842034, baseEnd_4842034] using wordTrace_append hprefix tailTrace_4842034
  have hstable : (prefixWord ++ tailWord_4842034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842034).length < 2 ^ (prefixWord ++ tailWord_4842034).sum := by decide
  have hdescent : baseEnd_4842034 < baseStart_4842034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842047 : List Nat := [1, 1, 2, 2, 3, 2, 3, 2, 2, 5]
def baseStart_4842047 : Nat := 118140960795 + 4842047 * 2 ^ 59
def prefixEnd_4842047 : Nat := 4983230072969 + 3 ^ 40 * 4842047 * 2
def baseEnd_4842047 : Nat := 828765820886974067514779

theorem tailTrace_4842047 : CollatzResearch.WordTrace tailWord_4842047 prefixEnd_4842047 828765820886974067514779 := by
  unfold tailWord_4842047
  simp only [CollatzResearch.WordTrace]
  refine ⟨176603962689098149635396395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117735975126065433090264263 176603962689098149635396395)
  ·
    refine ⟨264905944033647224453094593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176603962689098149635396395 264905944033647224453094593)
    ·
      refine ⟨198679458025235418339820945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264905944033647224453094593 198679458025235418339820945)
      ·
        refine ⟨149009593518926563754865709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198679458025235418339820945 149009593518926563754865709)
        ·
          refine ⟨55878597569597461408074641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149009593518926563754865709 55878597569597461408074641)
          ·
            refine ⟨41908948177198096056055981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55878597569597461408074641 41908948177198096056055981)
            ·
              refine ⟨15715855566449286021020993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41908948177198096056055981 15715855566449286021020993)
              ·
                refine ⟨11786891674836964515765745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15715855566449286021020993 11786891674836964515765745)
                ·
                  refine ⟨8840168756127723386824309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11786891674836964515765745 8840168756127723386824309)
                  ·
                    refine ⟨828765820886974067514779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8840168756127723386824309 828765820886974067514779)
                    ·
                      rfl

theorem cell23_4842047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 5].length) (baseStart_4842047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842047 prefixEnd_4842047 := by exact prefixLift 4842047
  have htrace : WordTrace (prefixWord ++ tailWord_4842047) baseStart_4842047 baseEnd_4842047 := by
    simpa [prefixWord, tailWord_4842047, baseEnd_4842047] using wordTrace_append hprefix tailTrace_4842047
  have hstable : (prefixWord ++ tailWord_4842047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842047).length < 2 ^ (prefixWord ++ tailWord_4842047).sum := by decide
  have hdescent : baseEnd_4842047 < baseStart_4842047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842084 : List Nat := [2, 3, 1, 1, 2, 2, 4, 1, 2, 1, 4]
def baseStart_4842084 : Nat := 118140960795 + 4842084 * 2 ^ 59
def prefixEnd_4842084 : Nat := 4983230072969 + 3 ^ 40 * 4842084 * 2
def baseEnd_4842084 : Nat := 2486316461445138557781667

theorem tailTrace_4842084 : CollatzResearch.WordTrace tailWord_4842084 prefixEnd_4842084 2486316461445138557781667 := by
  unfold tailWord_4842084
  simp only [CollatzResearch.WordTrace]
  refine ⟨88302656094982052477246653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117736874793309403302995537 88302656094982052477246653)
  ·
    refine ⟨33113496035618269678967495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88302656094982052477246653 33113496035618269678967495)
    ·
      refine ⟨49670244053427404518451243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33113496035618269678967495 49670244053427404518451243)
      ·
        refine ⟨74505366080141106777676865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49670244053427404518451243 74505366080141106777676865)
        ·
          refine ⟨55879024560105830083257649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74505366080141106777676865 55879024560105830083257649)
          ·
            refine ⟨41909268420079372562443237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55879024560105830083257649 41909268420079372562443237)
            ·
              refine ⟨7857987828764882355458107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41909268420079372562443237 7857987828764882355458107)
              ·
                refine ⟨11786981743147323533187161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7857987828764882355458107 11786981743147323533187161)
                ·
                  refine ⟨8840236307360492649890371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11786981743147323533187161 8840236307360492649890371)
                  ·
                    refine ⟨13260354461040738974835557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8840236307360492649890371 13260354461040738974835557)
                    ·
                      refine ⟨2486316461445138557781667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13260354461040738974835557 2486316461445138557781667)
                      ·
                        rfl

theorem cell23_4842084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_4842084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842084 prefixEnd_4842084 := by exact prefixLift 4842084
  have htrace : WordTrace (prefixWord ++ tailWord_4842084) baseStart_4842084 baseEnd_4842084 := by
    simpa [prefixWord, tailWord_4842084, baseEnd_4842084] using wordTrace_append hprefix tailTrace_4842084
  have hstable : (prefixWord ++ tailWord_4842084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842084).length < 2 ^ (prefixWord ++ tailWord_4842084).sum := by decide
  have hdescent : baseEnd_4842084 < baseStart_4842084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842137 : List Nat := [1, 2, 1, 2, 1, 2, 3, 3, 3, 5]
def baseStart_4842137 : Nat := 118140960795 + 4842137 * 2 ^ 59
def prefixEnd_4842137 : Nat := 4983230072969 + 3 ^ 40 * 4842137 * 2
def baseEnd_4842137 : Nat := 828781225306608950139641

theorem tailTrace_4842137 : CollatzResearch.WordTrace tailWord_4842137 prefixEnd_4842137 828781225306608950139641 := by
  unfold tailWord_4842137
  simp only [CollatzResearch.WordTrace]
  refine ⟨176607245258772095006172665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117738163505848063337448443 176607245258772095006172665)
  ·
    refine ⟨132455433944079071254629499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176607245258772095006172665 132455433944079071254629499)
    ·
      refine ⟨198683150916118606881944249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132455433944079071254629499 198683150916118606881944249)
      ·
        refine ⟨149012363187088955161458187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198683150916118606881944249 149012363187088955161458187)
        ·
          refine ⟨223518544780633432742187281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149012363187088955161458187 223518544780633432742187281)
          ·
            refine ⟨167638908585475074556640461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223518544780633432742187281 167638908585475074556640461)
            ·
              refine ⟨62864590719553152958740173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167638908585475074556640461 62864590719553152958740173)
              ·
                refine ⟨23574221519832432359527565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62864590719553152958740173 23574221519832432359527565)
                ·
                  refine ⟨8840333069937162134822837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23574221519832432359527565 8840333069937162134822837)
                  ·
                    refine ⟨828781225306608950139641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8840333069937162134822837 828781225306608950139641)
                    ·
                      rfl

theorem cell23_4842137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 5].length) (baseStart_4842137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842137 prefixEnd_4842137 := by exact prefixLift 4842137
  have htrace : WordTrace (prefixWord ++ tailWord_4842137) baseStart_4842137 baseEnd_4842137 := by
    simpa [prefixWord, tailWord_4842137, baseEnd_4842137] using wordTrace_append hprefix tailTrace_4842137
  have hstable : (prefixWord ++ tailWord_4842137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842137).length < 2 ^ (prefixWord ++ tailWord_4842137).sum := by decide
  have hdescent : baseEnd_4842137 < baseStart_4842137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842158 : List Nat := [4, 1, 4, 1, 1, 3, 1, 2, 6]
def baseStart_4842158 : Nat := 118140960795 + 4842158 * 2 ^ 59
def prefixEnd_4842158 : Nat := 4983230072969 + 3 ^ 40 * 4842158 * 2
def baseEnd_4842158 : Nat := 276261606557063474250703

theorem tailTrace_4842158 : CollatzResearch.WordTrace tailWord_4842158 prefixEnd_4842158 276261606557063474250703 := by
  unfold tailWord_4842158
  simp only [CollatzResearch.WordTrace]
  refine ⟨22076001398962001949085891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117738674127797343728458085 22076001398962001949085891)
  ·
    refine ⟨33114002098443002923628837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22076001398962001949085891 33114002098443002923628837)
    ·
      refine ⟨6208875393458063048180407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33114002098443002923628837 6208875393458063048180407)
      ·
        refine ⟨9313313090187094572270611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6208875393458063048180407 9313313090187094572270611)
        ·
          refine ⟨13969969635280641858405917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9313313090187094572270611 13969969635280641858405917)
          ·
            refine ⟨5238738613230240696902219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13969969635280641858405917 5238738613230240696902219)
            ·
              refine ⟨7858107919845361045353329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5238738613230240696902219 7858107919845361045353329)
              ·
                refine ⟨5893580939884020784014997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7858107919845361045353329 5893580939884020784014997)
                ·
                  refine ⟨276261606557063474250703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5893580939884020784014997 276261606557063474250703)
                  ·
                    rfl

theorem cell23_4842158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 6].length) (baseStart_4842158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842158 prefixEnd_4842158 := by exact prefixLift 4842158
  have htrace : WordTrace (prefixWord ++ tailWord_4842158) baseStart_4842158 baseEnd_4842158 := by
    simpa [prefixWord, tailWord_4842158, baseEnd_4842158] using wordTrace_append hprefix tailTrace_4842158
  have hstable : (prefixWord ++ tailWord_4842158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842158).length < 2 ^ (prefixWord ++ tailWord_4842158).sum := by decide
  have hdescent : baseEnd_4842158 < baseStart_4842158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842184 : List Nat := [2, 1, 3, 1, 2, 3, 3, 1, 1, 6]
def baseStart_4842184 : Nat := 118140960795 + 4842184 * 2 ^ 59
def prefixEnd_4842184 : Nat := 4983230072969 + 3 ^ 40 * 4842184 * 2
def baseEnd_4842184 : Nat := 828789269836862722177069

theorem tailTrace_4842184 : CollatzResearch.WordTrace tailWord_4842184 prefixEnd_4842184 828789269836862722177069 := by
  unfold tailWord_4842184
  simp only [CollatzResearch.WordTrace]
  refine ⟨88304479744800911016566803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117739306326401214688755737 88304479744800911016566803)
  ·
    refine ⟨132456719617201366524850205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88304479744800911016566803 132456719617201366524850205)
    ·
      refine ⟨49671269856450512446818827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132456719617201366524850205 49671269856450512446818827)
      ·
        refine ⟨74506904784675768670228241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49671269856450512446818827 74506904784675768670228241)
        ·
          refine ⟨55880178588506826502671181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74506904784675768670228241 55880178588506826502671181)
          ·
            refine ⟨20955066970690059938501693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55880178588506826502671181 20955066970690059938501693)
            ·
              refine ⟨7858150114008772476938135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20955066970690059938501693 7858150114008772476938135)
              ·
                refine ⟨11787225171013158715407203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7858150114008772476938135 11787225171013158715407203)
                ·
                  refine ⟨17680837756519738073110805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11787225171013158715407203 17680837756519738073110805)
                  ·
                    refine ⟨828789269836862722177069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17680837756519738073110805 828789269836862722177069)
                    ·
                      rfl

theorem cell23_4842184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_4842184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842184 prefixEnd_4842184 := by exact prefixLift 4842184
  have htrace : WordTrace (prefixWord ++ tailWord_4842184) baseStart_4842184 baseEnd_4842184 := by
    simpa [prefixWord, tailWord_4842184, baseEnd_4842184] using wordTrace_append hprefix tailTrace_4842184
  have hstable : (prefixWord ++ tailWord_4842184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842184).length < 2 ^ (prefixWord ++ tailWord_4842184).sum := by decide
  have hdescent : baseEnd_4842184 < baseStart_4842184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842211 : List Nat := [1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 5]
def baseStart_4842211 : Nat := 118140960795 + 4842211 * 2 ^ 59
def prefixEnd_4842211 : Nat := 4983230072969 + 3 ^ 40 * 4842211 * 2
def baseEnd_4842211 : Nat := 2486381673488259560893583

theorem tailTrace_4842211 : CollatzResearch.WordTrace tailWord_4842211 prefixEnd_4842211 2486381673488259560893583 := by
  unfold tailWord_4842211
  simp only [CollatzResearch.WordTrace]
  refine ⟨176609944260504005644366487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117739962840336003762910991 176609944260504005644366487)
  ·
    refine ⟨264914916390756008466549731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176609944260504005644366487 264914916390756008466549731)
    ·
      refine ⟨397372374586134012699824597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264914916390756008466549731 397372374586134012699824597)
      ·
        refine ⟨9313415029362515922652139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 397372374586134012699824597 9313415029362515922652139)
        ·
          refine ⟨13970122544043773883978209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9313415029362515922652139 13970122544043773883978209)
          ·
            refine ⟨10477591908032830412983657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13970122544043773883978209 10477591908032830412983657)
            ·
              refine ⟨7858193931024622809737743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10477591908032830412983657 7858193931024622809737743)
              ·
                refine ⟨11787290896536934214606615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7858193931024622809737743 11787290896536934214606615)
                ·
                  refine ⟨17680936344805401321909923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11787290896536934214606615 17680936344805401321909923)
                  ·
                    refine ⟨26521404517208101982864885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17680936344805401321909923 26521404517208101982864885)
                    ·
                      refine ⟨2486381673488259560893583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26521404517208101982864885 2486381673488259560893583)
                      ·
                        rfl

theorem cell23_4842211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_4842211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842211 prefixEnd_4842211 := by exact prefixLift 4842211
  have htrace : WordTrace (prefixWord ++ tailWord_4842211) baseStart_4842211 baseEnd_4842211 := by
    simpa [prefixWord, tailWord_4842211, baseEnd_4842211] using wordTrace_append hprefix tailTrace_4842211
  have hstable : (prefixWord ++ tailWord_4842211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842211).length < 2 ^ (prefixWord ++ tailWord_4842211).sum := by decide
  have hdescent : baseEnd_4842211 < baseStart_4842211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842227 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 2, 7]
def baseStart_4842227 : Nat := 118140960795 + 4842227 * 2 ^ 59
def prefixEnd_4842227 : Nat := 4983230072969 + 3 ^ 40 * 4842227 * 2
def baseEnd_4842227 : Nat := 828796629726243832764503

theorem tailTrace_4842227 : CollatzResearch.WordTrace tailWord_4842227 prefixEnd_4842227 828796629726243832764503 := by
  unfold tailWord_4842227
  simp only [CollatzResearch.WordTrace]
  refine ⟨176610527828446040376948935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117740351885630693584632623 176610527828446040376948935)
  ·
    refine ⟨264915791742669060565423403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176610527828446040376948935 264915791742669060565423403)
    ·
      refine ⟨397373687614003590848135105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264915791742669060565423403 397373687614003590848135105)
      ·
        refine ⟨298030265710502693136101329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 397373687614003590848135105 298030265710502693136101329)
        ·
          refine ⟨223522699282877019852075997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298030265710502693136101329 223522699282877019852075997)
          ·
            refine ⟨83821012231078882444528499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 223522699282877019852075997 83821012231078882444528499)
            ·
              refine ⟨125731518346618323666792749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83821012231078882444528499 125731518346618323666792749)
              ·
                refine ⟨47149319379981871375047281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125731518346618323666792749 47149319379981871375047281)
                ·
                  refine ⟨35361989534986403531285461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47149319379981871375047281 35361989534986403531285461)
                  ·
                    refine ⟨828796629726243832764503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35361989534986403531285461 828796629726243832764503)
                    ·
                      rfl

theorem cell23_4842227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 7].length) (baseStart_4842227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842227 prefixEnd_4842227 := by exact prefixLift 4842227
  have htrace : WordTrace (prefixWord ++ tailWord_4842227) baseStart_4842227 baseEnd_4842227 := by
    simpa [prefixWord, tailWord_4842227, baseEnd_4842227] using wordTrace_append hprefix tailTrace_4842227
  have hstable : (prefixWord ++ tailWord_4842227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842227).length < 2 ^ (prefixWord ++ tailWord_4842227).sum := by decide
  have hdescent : baseEnd_4842227 < baseStart_4842227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842276 : List Nat := [2, 3, 1, 3, 4, 1, 2, 2, 1, 2, 2]
def baseStart_4842276 : Nat := 118140960795 + 4842276 * 2 ^ 59
def prefixEnd_4842276 : Nat := 4983230072969 + 3 ^ 40 * 4842276 * 2
def baseEnd_4842276 : Nat := 2486415049730801806580785

theorem tailTrace_4842276 : CollatzResearch.WordTrace tailWord_4842276 prefixEnd_4842276 2486415049730801806580785 := by
  unfold tailWord_4842276
  simp only [CollatzResearch.WordTrace]
  refine ⟨88306157502634260872741341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117741543336845681163655121 88306157502634260872741341)
  ·
    refine ⟨33114809063487847827278003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88306157502634260872741341 33114809063487847827278003)
    ·
      refine ⟨49672213595231771740917005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33114809063487847827278003 49672213595231771740917005)
      ·
        refine ⟨18627080098211914402843877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49672213595231771740917005 18627080098211914402843877)
        ·
          refine ⟨3492577518414733950533227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18627080098211914402843877 3492577518414733950533227)
          ·
            refine ⟨5238866277622100925799841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3492577518414733950533227 5238866277622100925799841)
            ·
              refine ⟨3929149708216575694349881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5238866277622100925799841 3929149708216575694349881)
              ·
                refine ⟨2946862281162431770762411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3929149708216575694349881 2946862281162431770762411)
                ·
                  refine ⟨4420293421743647656143617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2946862281162431770762411 4420293421743647656143617)
                  ·
                    refine ⟨3315220066307735742107713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4420293421743647656143617 3315220066307735742107713)
                    ·
                      refine ⟨2486415049730801806580785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3315220066307735742107713 2486415049730801806580785)
                      ·
                        rfl

theorem cell23_4842276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_4842276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842276 prefixEnd_4842276 := by exact prefixLift 4842276
  have htrace : WordTrace (prefixWord ++ tailWord_4842276) baseStart_4842276 baseEnd_4842276 := by
    simpa [prefixWord, tailWord_4842276, baseEnd_4842276] using wordTrace_append hprefix tailTrace_4842276
  have hstable : (prefixWord ++ tailWord_4842276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842276).length < 2 ^ (prefixWord ++ tailWord_4842276).sum := by decide
  have hdescent : baseEnd_4842276 < baseStart_4842276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842284 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 3]
def baseStart_4842284 : Nat := 118140960795 + 4842284 * 2 ^ 59
def prefixEnd_4842284 : Nat := 4983230072969 + 3 ^ 40 * 4842284 * 2
def baseEnd_4842284 : Nat := 2486419157576037775280747

theorem tailTrace_4842284 : CollatzResearch.WordTrace tailWord_4842284 prefixEnd_4842284 2486419157576037775280747 := by
  unfold tailWord_4842284
  simp only [CollatzResearch.WordTrace]
  refine ⟨88306303394619769555886953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117741737859493026074515937 88306303394619769555886953)
  ·
    refine ⟨66229727545964827166915215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88306303394619769555886953 66229727545964827166915215)
    ·
      refine ⟨99344591318947240750372823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66229727545964827166915215 99344591318947240750372823)
      ·
        refine ⟨149016886978420861125559235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99344591318947240750372823 149016886978420861125559235)
        ·
          refine ⟨223525330467631291688338853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149016886978420861125559235 223525330467631291688338853)
          ·
            refine ⟨41910999462680867191563535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 223525330467631291688338853 41910999462680867191563535)
            ·
              refine ⟨62866499194021300787345303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41910999462680867191563535 62866499194021300787345303)
              ·
                refine ⟨94299748791031951181017955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62866499194021300787345303 94299748791031951181017955)
                ·
                  refine ⟨141449623186547926771526933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94299748791031951181017955 141449623186547926771526933)
                  ·
                    refine ⟨6630451086869434067415325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 141449623186547926771526933 6630451086869434067415325)
                    ·
                      refine ⟨2486419157576037775280747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6630451086869434067415325 2486419157576037775280747)
                      ·
                        rfl

theorem cell23_4842284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 3].length) (baseStart_4842284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842284 prefixEnd_4842284 := by exact prefixLift 4842284
  have htrace : WordTrace (prefixWord ++ tailWord_4842284) baseStart_4842284 baseEnd_4842284 := by
    simpa [prefixWord, tailWord_4842284, baseEnd_4842284] using wordTrace_append hprefix tailTrace_4842284
  have hstable : (prefixWord ++ tailWord_4842284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842284).length < 2 ^ (prefixWord ++ tailWord_4842284).sum := by decide
  have hdescent : baseEnd_4842284 < baseStart_4842284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842332 : List Nat := [2, 2, 4, 2, 1, 1, 3, 2, 2, 2, 2]
def baseStart_4842332 : Nat := 118140960795 + 4842332 * 2 ^ 59
def prefixEnd_4842332 : Nat := 4983230072969 + 3 ^ 40 * 4842332 * 2
def baseEnd_4842332 : Nat := 2486443804647453587480527

theorem tailTrace_4842332 : CollatzResearch.WordTrace tailWord_4842332 prefixEnd_4842332 2486443804647453587480527 := by
  unfold tailWord_4842332
  simp only [CollatzResearch.WordTrace]
  refine ⟨88307178746532821654760625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117742904995377095539680833 88307178746532821654760625)
  ·
    refine ⟨66230384059899616241070469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88307178746532821654760625 66230384059899616241070469)
    ·
      refine ⟨12418197011231178045200713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66230384059899616241070469 12418197011231178045200713)
      ·
        refine ⟨9313647758423383533900535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12418197011231178045200713 9313647758423383533900535)
        ·
          refine ⟨13970471637635075300850803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9313647758423383533900535 13970471637635075300850803)
          ·
            refine ⟨20955707456452612951276205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13970471637635075300850803 20955707456452612951276205)
            ·
              refine ⟨7858390296169729856728577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20955707456452612951276205 7858390296169729856728577)
              ·
                refine ⟨5893792722127297392546433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7858390296169729856728577 5893792722127297392546433)
                ·
                  refine ⟨4420344541595473044409825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5893792722127297392546433 4420344541595473044409825)
                  ·
                    refine ⟨3315258406196604783307369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4420344541595473044409825 3315258406196604783307369)
                    ·
                      refine ⟨2486443804647453587480527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3315258406196604783307369 2486443804647453587480527)
                      ·
                        rfl

theorem cell23_4842332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_4842332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842332 prefixEnd_4842332 := by exact prefixLift 4842332
  have htrace : WordTrace (prefixWord ++ tailWord_4842332) baseStart_4842332 baseEnd_4842332 := by
    simpa [prefixWord, tailWord_4842332, baseEnd_4842332] using wordTrace_append hprefix tailTrace_4842332
  have hstable : (prefixWord ++ tailWord_4842332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842332).length < 2 ^ (prefixWord ++ tailWord_4842332).sum := by decide
  have hdescent : baseEnd_4842332 < baseStart_4842332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842338 : List Nat := [3, 3, 2, 1, 3, 1, 2, 1, 7]
def baseStart_4842338 : Nat := 118140960795 + 4842338 * 2 ^ 59
def prefixEnd_4842338 : Nat := 4983230072969 + 3 ^ 40 * 4842338 * 2
def baseEnd_4842338 : Nat := 276271876170153396000611

theorem tailTrace_4842338 : CollatzResearch.WordTrace tailWord_4842338 prefixEnd_4842338 276271876170153396000611 := by
  unfold tailWord_4842338
  simp only [CollatzResearch.WordTrace]
  refine ⟨44153644082760976583559917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117743050887362604222826445 44153644082760976583559917)
  ·
    refine ⟨16557616531035366218834969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44153644082760976583559917 16557616531035366218834969)
    ·
      refine ⟨12418212398276524664126227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16557616531035366218834969 12418212398276524664126227)
      ·
        refine ⟨18627318597414786996189341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12418212398276524664126227 18627318597414786996189341)
        ·
          refine ⟨6985244474030545123571003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18627318597414786996189341 6985244474030545123571003)
          ·
            refine ⟨10477866711045817685356505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6985244474030545123571003 10477866711045817685356505)
            ·
              refine ⟨7858400033284363264017379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10477866711045817685356505 7858400033284363264017379)
              ·
                refine ⟨11787600049926544896026069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7858400033284363264017379 11787600049926544896026069)
                ·
                  refine ⟨276271876170153396000611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11787600049926544896026069 276271876170153396000611)
                  ·
                    rfl

theorem cell23_4842338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_4842338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842338 prefixEnd_4842338 := by exact prefixLift 4842338
  have htrace : WordTrace (prefixWord ++ tailWord_4842338) baseStart_4842338 baseEnd_4842338 := by
    simpa [prefixWord, tailWord_4842338, baseEnd_4842338] using wordTrace_append hprefix tailTrace_4842338
  have hstable : (prefixWord ++ tailWord_4842338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842338).length < 2 ^ (prefixWord ++ tailWord_4842338).sum := by decide
  have hdescent : baseEnd_4842338 < baseStart_4842338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842341 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 1, 7, 2]
def baseStart_4842341 : Nat := 118140960795 + 4842341 * 2 ^ 59
def prefixEnd_4842341 : Nat := 4983230072969 + 3 ^ 40 * 4842341 * 2
def baseEnd_4842341 : Nat := 2486448425973344052267985

theorem tailTrace_4842341 : CollatzResearch.WordTrace tailWord_4842341 prefixEnd_4842341 2486448425973344052267985 := by
  unfold tailWord_4842341
  simp only [CollatzResearch.WordTrace]
  refine ⟨176614685750033037846598877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117743123833355358564399251 176614685750033037846598877)
  ·
    refine ⟨66230507156262389192474579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176614685750033037846598877 66230507156262389192474579)
    ·
      refine ⟨99345760734393583788711869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66230507156262389192474579 99345760734393583788711869)
      ·
        refine ⟨37254660275397593920766951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99345760734393583788711869 37254660275397593920766951)
        ·
          refine ⟨55881990413096390881150427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37254660275397593920766951 55881990413096390881150427)
          ·
            refine ⟨83822985619644586321725641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55881990413096390881150427 83822985619644586321725641)
            ·
              refine ⟨62867239214733439741294231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83822985619644586321725641 62867239214733439741294231)
              ·
                refine ⟨94300858822100159611941347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62867239214733439741294231 94300858822100159611941347)
                ·
                  refine ⟨141451288233150239417912021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94300858822100159611941347 141451288233150239417912021)
                  ·
                    refine ⟨3315264567964458736357313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 141451288233150239417912021 3315264567964458736357313)
                    ·
                      refine ⟨2486448425973344052267985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3315264567964458736357313 2486448425973344052267985)
                      ·
                        rfl

theorem cell23_4842341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_4842341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842341 prefixEnd_4842341 := by exact prefixLift 4842341
  have htrace : WordTrace (prefixWord ++ tailWord_4842341) baseStart_4842341 baseEnd_4842341 := by
    simpa [prefixWord, tailWord_4842341, baseEnd_4842341] using wordTrace_append hprefix tailTrace_4842341
  have hstable : (prefixWord ++ tailWord_4842341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842341).length < 2 ^ (prefixWord ++ tailWord_4842341).sum := by decide
  have hdescent : baseEnd_4842341 < baseStart_4842341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842371 : List Nat := [1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 4]
def baseStart_4842371 : Nat := 118140960795 + 4842371 * 2 ^ 59
def prefixEnd_4842371 : Nat := 4983230072969 + 3 ^ 40 * 4842371 * 2
def baseEnd_4842371 : Nat := 2486463830392978934892847

theorem tailTrace_4842371 : CollatzResearch.WordTrace tailWord_4842371 prefixEnd_4842371 2486463830392978934892847 := by
  unfold tailWord_4842371
  simp only [CollatzResearch.WordTrace]
  refine ⟨176615779939924352970190967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117743853293282901980127311 176615779939924352970190967)
  ·
    refine ⟨264923669909886529455286451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176615779939924352970190967 264923669909886529455286451)
    ·
      refine ⟨397385504864829794182929677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264923669909886529455286451 397385504864829794182929677)
      ·
        refine ⟨149019564324311172818598629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 397385504864829794182929677 149019564324311172818598629)
        ·
          refine ⟨27941168310808344903487243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 149019564324311172818598629 27941168310808344903487243)
          ·
            refine ⟨41911752466212517355230865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27941168310808344903487243 41911752466212517355230865)
            ·
              refine ⟨31433814349659388016423149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41911752466212517355230865 31433814349659388016423149)
              ·
                refine ⟨11787680381122270506158681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31433814349659388016423149 11787680381122270506158681)
                ·
                  refine ⟨8840760285841702879619011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11787680381122270506158681 8840760285841702879619011)
                  ·
                    refine ⟨13261140428762554319428517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8840760285841702879619011 13261140428762554319428517)
                    ·
                      refine ⟨2486463830392978934892847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13261140428762554319428517 2486463830392978934892847)
                      ·
                        rfl

theorem cell23_4842371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 4].length) (baseStart_4842371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842371 prefixEnd_4842371 := by exact prefixLift 4842371
  have htrace : WordTrace (prefixWord ++ tailWord_4842371) baseStart_4842371 baseEnd_4842371 := by
    simpa [prefixWord, tailWord_4842371, baseEnd_4842371] using wordTrace_append hprefix tailTrace_4842371
  have hstable : (prefixWord ++ tailWord_4842371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842371).length < 2 ^ (prefixWord ++ tailWord_4842371).sum := by decide
  have hdescent : baseEnd_4842371 < baseStart_4842371 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842384 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 4]
def baseStart_4842384 : Nat := 118140960795 + 4842384 * 2 ^ 59
def prefixEnd_4842384 : Nat := 4983230072969 + 3 ^ 40 * 4842384 * 2
def baseEnd_4842384 : Nat := 2486470505641487384030287

theorem tailTrace_4842384 : CollatzResearch.WordTrace tailWord_4842384 prefixEnd_4842384 2486470505641487384030287 := by
  unfold tailWord_4842384
  simp only [CollatzResearch.WordTrace]
  refine ⟨88308127044438628095207103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117744169392584837460276137 88308127044438628095207103)
  ·
    refine ⟨132462190566657942142810655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88308127044438628095207103 132462190566657942142810655)
    ·
      refine ⟨198693285849986913214215983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132462190566657942142810655 198693285849986913214215983)
      ·
        refine ⟨298039928774980369821323975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198693285849986913214215983 298039928774980369821323975)
        ·
          refine ⟨447059893162470554731985963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298039928774980369821323975 447059893162470554731985963)
          ·
            refine ⟨670589839743705832097978945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447059893162470554731985963 670589839743705832097978945)
            ·
              refine ⟨502942379807779374073484209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 670589839743705832097978945 502942379807779374073484209)
              ·
                refine ⟨377206784855834530555113157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 502942379807779374073484209 377206784855834530555113157)
                ·
                  refine ⟨70726272160468974479083717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 377206784855834530555113157 70726272160468974479083717)
                  ·
                    refine ⟨13261176030087932714828197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70726272160468974479083717 13261176030087932714828197)
                    ·
                      refine ⟨2486470505641487384030287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13261176030087932714828197 2486470505641487384030287)
                      ·
                        rfl

theorem cell23_4842384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 4].length) (baseStart_4842384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842384 prefixEnd_4842384 := by exact prefixLift 4842384
  have htrace : WordTrace (prefixWord ++ tailWord_4842384) baseStart_4842384 baseEnd_4842384 := by
    simpa [prefixWord, tailWord_4842384, baseEnd_4842384] using wordTrace_append hprefix tailTrace_4842384
  have hstable : (prefixWord ++ tailWord_4842384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842384).length < 2 ^ (prefixWord ++ tailWord_4842384).sum := by decide
  have hdescent : baseEnd_4842384 < baseStart_4842384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842388 : List Nat := [2, 4, 2, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_4842388 : Nat := 118140960795 + 4842388 * 2 ^ 59
def prefixEnd_4842388 : Nat := 4983230072969 + 3 ^ 40 * 4842388 * 2
def baseEnd_4842388 : Nat := 2486472559564105368380269

theorem tailTrace_4842388 : CollatzResearch.WordTrace tailWord_4842388 prefixEnd_4842388 2486472559564105368380269 := by
  unfold tailWord_4842388
  simp only [CollatzResearch.WordTrace]
  refine ⟨88308199990431382436779909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117744266653908509915706545 88308199990431382436779909)
  ·
    refine ⟨16557787498205884206896233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88308199990431382436779909 16557787498205884206896233)
    ·
      refine ⟨12418340623654413155172175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16557787498205884206896233 12418340623654413155172175)
      ·
        refine ⟨18627510935481619732758263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12418340623654413155172175 18627510935481619732758263)
        ·
          refine ⟨27941266403222429599137395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18627510935481619732758263 27941266403222429599137395)
          ·
            refine ⟨41911899604833644398706093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27941266403222429599137395 41911899604833644398706093)
            ·
              refine ⟨15716962351812616649514785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41911899604833644398706093 15716962351812616649514785)
              ·
                refine ⟨11787721763859462487136089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15716962351812616649514785 11787721763859462487136089)
                ·
                  refine ⟨8840791322894596865352067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11787721763859462487136089 8840791322894596865352067)
                  ·
                    refine ⟨13261186984341895298028101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8840791322894596865352067 13261186984341895298028101)
                    ·
                      refine ⟨2486472559564105368380269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13261186984341895298028101 2486472559564105368380269)
                      ·
                        rfl

theorem cell23_4842388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_4842388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842388 prefixEnd_4842388 := by exact prefixLift 4842388
  have htrace : WordTrace (prefixWord ++ tailWord_4842388) baseStart_4842388 baseEnd_4842388 := by
    simpa [prefixWord, tailWord_4842388, baseEnd_4842388] using wordTrace_append hprefix tailTrace_4842388
  have hstable : (prefixWord ++ tailWord_4842388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842388).length < 2 ^ (prefixWord ++ tailWord_4842388).sum := by decide
  have hdescent : baseEnd_4842388 < baseStart_4842388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842482 : List Nat := [3, 2, 1, 5, 1, 1, 1, 1, 1, 5, 2]
def baseStart_4842482 : Nat := 118140960795 + 4842482 * 2 ^ 59
def prefixEnd_4842482 : Nat := 4983230072969 + 3 ^ 40 * 4842482 * 2
def baseEnd_4842482 : Nat := 2486520826745628000604837

theorem tailTrace_4842482 : CollatzResearch.WordTrace tailWord_4842482 prefixEnd_4842482 2486520826745628000604837 := by
  unfold tailWord_4842482
  simp only [CollatzResearch.WordTrace]
  refine ⟨44154957110630554731870425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117746552295014812618321133 44154957110630554731870425)
  ·
    refine ⟨33116217832972916048902819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44154957110630554731870425 33116217832972916048902819)
    ·
      refine ⟨49674326749459374073354229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33116217832972916048902819 49674326749459374073354229)
      ·
        refine ⟨4656968132761816319376959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49674326749459374073354229 4656968132761816319376959)
        ·
          refine ⟨6985452199142724479065439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4656968132761816319376959 6985452199142724479065439)
          ·
            refine ⟨10478178298714086718598159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6985452199142724479065439 10478178298714086718598159)
            ·
              refine ⟨15717267448071130077897239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10478178298714086718598159 15717267448071130077897239)
              ·
                refine ⟨23575901172106695116845859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15717267448071130077897239 23575901172106695116845859)
                ·
                  refine ⟨35363851758160042675268789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23575901172106695116845859 35363851758160042675268789)
                  ·
                    refine ⟨3315361102327504000806449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35363851758160042675268789 3315361102327504000806449)
                    ·
                      refine ⟨2486520826745628000604837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3315361102327504000806449 2486520826745628000604837)
                      ·
                        rfl

theorem cell23_4842482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_4842482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842482 prefixEnd_4842482 := by exact prefixLift 4842482
  have htrace : WordTrace (prefixWord ++ tailWord_4842482) baseStart_4842482 baseEnd_4842482 := by
    simpa [prefixWord, tailWord_4842482, baseEnd_4842482] using wordTrace_append hprefix tailTrace_4842482
  have hstable : (prefixWord ++ tailWord_4842482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842482).length < 2 ^ (prefixWord ++ tailWord_4842482).sum := by decide
  have hdescent : baseEnd_4842482 < baseStart_4842482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842532 : List Nat := [2, 3, 1, 4, 1, 2, 2, 2, 1, 2, 3]
def baseStart_4842532 : Nat := 118140960795 + 4842532 * 2 ^ 59
def prefixEnd_4842532 : Nat := 4983230072969 + 3 ^ 40 * 4842532 * 2
def baseEnd_4842532 : Nat := 2486546500778352804979607

theorem tailTrace_4842532 : CollatzResearch.WordTrace tailWord_4842532 prefixEnd_4842532 2486546500778352804979607 := by
  unfold tailWord_4842532
  simp only [CollatzResearch.WordTrace]
  refine ⟨88310826046170538733400925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117747768061560718311201233 88310826046170538733400925)
  ·
    refine ⟨33116559767313952025025347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88310826046170538733400925 33116559767313952025025347)
    ·
      refine ⟨49674839650970928037538021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33116559767313952025025347 49674839650970928037538021)
      ·
        refine ⟨9314032434557049007038379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49674839650970928037538021 9314032434557049007038379)
        ·
          refine ⟨13971048651835573510557569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9314032434557049007038379 13971048651835573510557569)
          ·
            refine ⟨10478286488876680132918177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13971048651835573510557569 10478286488876680132918177)
            ·
              refine ⟨7858714866657510099688633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10478286488876680132918177 7858714866657510099688633)
              ·
                refine ⟨5894036149993132574766475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7858714866657510099688633 5894036149993132574766475)
                ·
                  refine ⟨8841054224989698862149713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5894036149993132574766475 8841054224989698862149713)
                  ·
                    refine ⟨6630790668742274146612285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8841054224989698862149713 6630790668742274146612285)
                    ·
                      refine ⟨2486546500778352804979607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6630790668742274146612285 2486546500778352804979607)
                      ·
                        rfl

theorem cell23_4842532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_4842532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842532 prefixEnd_4842532 := by exact prefixLift 4842532
  have htrace : WordTrace (prefixWord ++ tailWord_4842532) baseStart_4842532 baseEnd_4842532 := by
    simpa [prefixWord, tailWord_4842532, baseEnd_4842532] using wordTrace_append hprefix tailTrace_4842532
  have hstable : (prefixWord ++ tailWord_4842532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842532).length < 2 ^ (prefixWord ++ tailWord_4842532).sum := by decide
  have hdescent : baseEnd_4842532 < baseStart_4842532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842535 : List Nat := [1, 1, 7, 1, 1, 1, 4, 7]
def baseStart_4842535 : Nat := 118140960795 + 4842535 * 2 ^ 59
def prefixEnd_4842535 : Nat := 4983230072969 + 3 ^ 40 * 4842535 * 2
def baseEnd_4842535 : Nat := 92094371897048751601559

theorem tailTrace_4842535 : CollatzResearch.WordTrace tailWord_4842535 prefixEnd_4842535 92094371897048751601559 := by
  unfold tailWord_4842535
  simp only [CollatzResearch.WordTrace]
  refine ⟨176621761511330208979161059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117747841007553472652774039 176621761511330208979161059)
  ·
    refine ⟨264932642266995313468741589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176621761511330208979161059 264932642266995313468741589)
    ·
      refine ⟨6209358803132702659423631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 264932642266995313468741589 6209358803132702659423631)
      ·
        refine ⟨9314038204699053989135447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6209358803132702659423631 9314038204699053989135447)
        ·
          refine ⟨13971057307048580983703171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9314038204699053989135447 13971057307048580983703171)
          ·
            refine ⟨20956585960572871475554757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13971057307048580983703171 20956585960572871475554757)
            ·
              refine ⟨3929359867607413401666517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20956585960572871475554757 3929359867607413401666517)
              ·
                refine ⟨92094371897048751601559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3929359867607413401666517 92094371897048751601559)
                ·
                  rfl

theorem cell23_4842535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 7].length) (baseStart_4842535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842535 prefixEnd_4842535 := by exact prefixLift 4842535
  have htrace : WordTrace (prefixWord ++ tailWord_4842535) baseStart_4842535 baseEnd_4842535 := by
    simpa [prefixWord, tailWord_4842535, baseEnd_4842535] using wordTrace_append hprefix tailTrace_4842535
  have hstable : (prefixWord ++ tailWord_4842535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842535).length < 2 ^ (prefixWord ++ tailWord_4842535).sum := by decide
  have hdescent : baseEnd_4842535 < baseStart_4842535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842551 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 4]
def baseStart_4842551 : Nat := 118140960795 + 4842551 * 2 ^ 59
def prefixEnd_4842551 : Nat := 4983230072969 + 3 ^ 40 * 4842551 * 2
def baseEnd_4842551 : Nat := 2486556256910788230642019

theorem tailTrace_4842551 : CollatzResearch.WordTrace tailWord_4842551 prefixEnd_4842551 2486556256910788230642019 := by
  unfold tailWord_4842551
  simp only [CollatzResearch.WordTrace]
  refine ⟨176622345079272243711743507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117748230052848162474495671 176622345079272243711743507)
  ·
    refine ⟨264933517618908365567615261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176622345079272243711743507 264933517618908365567615261)
    ·
      refine ⟨99350069107090637087855723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 264933517618908365567615261 99350069107090637087855723)
      ·
        refine ⟨149025103660635955631783585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99350069107090637087855723 149025103660635955631783585)
        ·
          refine ⟨111768827745476966723837689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149025103660635955631783585 111768827745476966723837689)
          ·
            refine ⟨83826620809107725042878267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111768827745476966723837689 83826620809107725042878267)
            ·
              refine ⟨125739931213661587564317401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83826620809107725042878267 125739931213661587564317401)
              ·
                refine ⟨94304948410246190673238051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125739931213661587564317401 94304948410246190673238051)
                ·
                  refine ⟨141457422615369286009857077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94304948410246190673238051 141457422615369286009857077)
                  ·
                    refine ⟨13261633370190870563424101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 141457422615369286009857077 13261633370190870563424101)
                    ·
                      refine ⟨2486556256910788230642019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13261633370190870563424101 2486556256910788230642019)
                      ·
                        rfl

theorem cell23_4842551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_4842551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842551 prefixEnd_4842551 := by exact prefixLift 4842551
  have htrace : WordTrace (prefixWord ++ tailWord_4842551) baseStart_4842551 baseEnd_4842551 := by
    simpa [prefixWord, tailWord_4842551, baseEnd_4842551] using wordTrace_append hprefix tailTrace_4842551
  have hstable : (prefixWord ++ tailWord_4842551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842551).length < 2 ^ (prefixWord ++ tailWord_4842551).sum := by decide
  have hdescent : baseEnd_4842551 < baseStart_4842551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842571 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 5]
def baseStart_4842571 : Nat := 118140960795 + 4842571 * 2 ^ 59
def prefixEnd_4842571 : Nat := 4983230072969 + 3 ^ 40 * 4842571 * 2
def baseEnd_4842571 : Nat := 2486566526523878152391927

theorem tailTrace_4842571 : CollatzResearch.WordTrace tailWord_4842571 prefixEnd_4842571 2486566526523878152391927 := by
  unfold tailWord_4842571
  simp only [CollatzResearch.WordTrace]
  refine ⟨176623074539199787127471567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117748716359466524751647711 176623074539199787127471567)
  ·
    refine ⟨264934611808799680691207351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176623074539199787127471567 264934611808799680691207351)
    ·
      refine ⟨397401917713199521036811027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264934611808799680691207351 397401917713199521036811027)
      ·
        refine ⟨596102876569799281555216541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397401917713199521036811027 596102876569799281555216541)
        ·
          refine ⟨223538578713674730583206203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 596102876569799281555216541 223538578713674730583206203)
          ·
            refine ⟨335307868070512095874809305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223538578713674730583206203 335307868070512095874809305)
            ·
              refine ⟨251480901052884071906106979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335307868070512095874809305 251480901052884071906106979)
              ·
                refine ⟨377221351579326107859160469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251480901052884071906106979 377221351579326107859160469)
                ·
                  refine ⟨17682250855280911305898147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 377221351579326107859160469 17682250855280911305898147)
                  ·
                    refine ⟨26523376282921366958847221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17682250855280911305898147 26523376282921366958847221)
                    ·
                      refine ⟨2486566526523878152391927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26523376282921366958847221 2486566526523878152391927)
                      ·
                        rfl

theorem cell23_4842571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 5].length) (baseStart_4842571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842571 prefixEnd_4842571 := by exact prefixLift 4842571
  have htrace : WordTrace (prefixWord ++ tailWord_4842571) baseStart_4842571 baseEnd_4842571 := by
    simpa [prefixWord, tailWord_4842571, baseEnd_4842571] using wordTrace_append hprefix tailTrace_4842571
  have hstable : (prefixWord ++ tailWord_4842571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842571).length < 2 ^ (prefixWord ++ tailWord_4842571).sum := by decide
  have hdescent : baseEnd_4842571 < baseStart_4842571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842585 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 6, 2, 2]
def baseStart_4842585 : Nat := 118140960795 + 4842585 * 2 ^ 59
def prefixEnd_4842585 : Nat := 4983230072969 + 3 ^ 40 * 4842585 * 2
def baseEnd_4842585 : Nat := 2486573715253041097616863

theorem tailTrace_4842585 : CollatzResearch.WordTrace tailWord_4842585 prefixEnd_4842585 2486573715253041097616863 := by
  unfold tailWord_4842585
  simp only [CollatzResearch.WordTrace]
  refine ⟨176623585161149067518481209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117749056774099378345654139 176623585161149067518481209)
  ·
    refine ⟨132467688870861800638860907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176623585161149067518481209 132467688870861800638860907)
    ·
      refine ⟨198701533306292700958291361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132467688870861800638860907 198701533306292700958291361)
      ·
        refine ⟨149026149979719525718718521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198701533306292700958291361 149026149979719525718718521)
        ·
          refine ⟨111769612484789644289038891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149026149979719525718718521 111769612484789644289038891)
          ·
            refine ⟨167654418727184466433558337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111769612484789644289038891 167654418727184466433558337)
            ·
              refine ⟨125740814045388349825168753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167654418727184466433558337 125740814045388349825168753)
              ·
                refine ⟨94305610534041262368876565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125740814045388349825168753 94305610534041262368876565)
                ·
                  refine ⟨4420575493783184173541089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 94305610534041262368876565 4420575493783184173541089)
                  ·
                    refine ⟨3315431620337388130155817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4420575493783184173541089 3315431620337388130155817)
                    ·
                      refine ⟨2486573715253041097616863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3315431620337388130155817 2486573715253041097616863)
                      ·
                        rfl

theorem cell23_4842585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 6, 2, 2].length) (baseStart_4842585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842585 prefixEnd_4842585 := by exact prefixLift 4842585
  have htrace : WordTrace (prefixWord ++ tailWord_4842585) baseStart_4842585 baseEnd_4842585 := by
    simpa [prefixWord, tailWord_4842585, baseEnd_4842585] using wordTrace_append hprefix tailTrace_4842585
  have hstable : (prefixWord ++ tailWord_4842585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842585).length < 2 ^ (prefixWord ++ tailWord_4842585).sum := by decide
  have hdescent : baseEnd_4842585 < baseStart_4842585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842588 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_4842588 : Nat := 118140960795 + 4842588 * 2 ^ 59
def prefixEnd_4842588 : Nat := 4983230072969 + 3 ^ 40 * 4842588 * 2
def baseEnd_4842588 : Nat := 2486575255695004585879349

theorem tailTrace_4842588 : CollatzResearch.WordTrace tailWord_4842588 prefixEnd_4842588 2486575255695004585879349 := by
  unfold tailWord_4842588
  simp only [CollatzResearch.WordTrace]
  refine ⟨88311847290069099515420209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117749129720092132687226945 88311847290069099515420209)
  ·
    refine ⟨66233885467551824636565157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88311847290069099515420209 66233885467551824636565157)
    ·
      refine ⟨12418853525165967119355967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66233885467551824636565157 12418853525165967119355967)
      ·
        refine ⟨18628280287748950679033951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12418853525165967119355967 18628280287748950679033951)
        ·
          refine ⟨27942420431623426018550927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18628280287748950679033951 27942420431623426018550927)
          ·
            refine ⟨41913630647435139027826391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27942420431623426018550927 41913630647435139027826391)
            ·
              refine ⟨62870445971152708541739587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41913630647435139027826391 62870445971152708541739587)
              ·
                refine ⟨94305668956729062812609381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62870445971152708541739587 94305668956729062812609381)
                ·
                  refine ⟨17682312929386699277364259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94305668956729062812609381 17682312929386699277364259)
                  ·
                    refine ⟨26523469394080048916046389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17682312929386699277364259 26523469394080048916046389)
                    ·
                      refine ⟨2486575255695004585879349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26523469394080048916046389 2486575255695004585879349)
                      ·
                        rfl

theorem cell23_4842588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_4842588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842588 prefixEnd_4842588 := by exact prefixLift 4842588
  have htrace : WordTrace (prefixWord ++ tailWord_4842588) baseStart_4842588 baseEnd_4842588 := by
    simpa [prefixWord, tailWord_4842588, baseEnd_4842588] using wordTrace_append hprefix tailTrace_4842588
  have hstable : (prefixWord ++ tailWord_4842588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842588).length < 2 ^ (prefixWord ++ tailWord_4842588).sum := by decide
  have hdescent : baseEnd_4842588 < baseStart_4842588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842589 : List Nat := [1, 4, 4, 1, 2, 1, 1, 1, 3, 3, 2]
def baseStart_4842589 : Nat := 118140960795 + 4842589 * 2 ^ 59
def prefixEnd_4842589 : Nat := 4983230072969 + 3 ^ 40 * 4842589 * 2
def baseEnd_4842589 : Nat := 2486575769175659081966845

theorem tailTrace_4842589 : CollatzResearch.WordTrace tailWord_4842589 prefixEnd_4842589 2486575769175659081966845 := by
  unfold tailWord_4842589
  simp only [CollatzResearch.WordTrace]
  refine ⟨176623731053134576201626821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117749154035423050801084547 176623731053134576201626821)
  ·
    refine ⟨33116949572462733037805029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176623731053134576201626821 33116949572462733037805029)
    ·
      refine ⟨6209428044836762444588443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33116949572462733037805029 6209428044836762444588443)
      ·
        refine ⟨9314142067255143666882665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6209428044836762444588443 9314142067255143666882665)
        ·
          refine ⟨6985606550441357750161999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9314142067255143666882665 6985606550441357750161999)
          ·
            refine ⟨10478409825662036625242999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6985606550441357750161999 10478409825662036625242999)
            ·
              refine ⟨15717614738493054937864499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10478409825662036625242999 15717614738493054937864499)
              ·
                refine ⟨23576422107739582406796749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15717614738493054937864499 23576422107739582406796749)
                ·
                  refine ⟨8841158290402343402548781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23576422107739582406796749 8841158290402343402548781)
                  ·
                    refine ⟨3315434358900878775955793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8841158290402343402548781 3315434358900878775955793)
                    ·
                      refine ⟨2486575769175659081966845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3315434358900878775955793 2486575769175659081966845)
                      ·
                        rfl

theorem cell23_4842589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_4842589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842589 prefixEnd_4842589 := by exact prefixLift 4842589
  have htrace : WordTrace (prefixWord ++ tailWord_4842589) baseStart_4842589 baseEnd_4842589 := by
    simpa [prefixWord, tailWord_4842589, baseEnd_4842589] using wordTrace_append hprefix tailTrace_4842589
  have hstable : (prefixWord ++ tailWord_4842589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842589).length < 2 ^ (prefixWord ++ tailWord_4842589).sum := by decide
  have hdescent : baseEnd_4842589 < baseStart_4842589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842591 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 9]
def baseStart_4842591 : Nat := 118140960795 + 4842591 * 2 ^ 59
def prefixEnd_4842591 : Nat := 4983230072969 + 3 ^ 40 * 4842591 * 2
def baseEnd_4842591 : Nat := 276286310681885341571315

theorem tailTrace_4842591 : CollatzResearch.WordTrace tailWord_4842591 prefixEnd_4842591 276286310681885341571315 := by
  unfold tailWord_4842591
  simp only [CollatzResearch.WordTrace]
  refine ⟨176623803999127330543199627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117749202666084887028799751 176623803999127330543199627)
  ·
    refine ⟨264935705998690995814799441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176623803999127330543199627 264935705998690995814799441)
    ·
      refine ⟨198701779499018246861099581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264935705998690995814799441 198701779499018246861099581)
      ·
        refine ⟨74513167312131842572912343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198701779499018246861099581 74513167312131842572912343)
        ·
          refine ⟨111769750968197763859368515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74513167312131842572912343 111769750968197763859368515)
          ·
            refine ⟨167654626452296645789052773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111769750968197763859368515 167654626452296645789052773)
            ·
              refine ⟨31435242459805621085447395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 167654626452296645789052773 31435242459805621085447395)
              ·
                refine ⟨47152863689708431628171093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31435242459805621085447395 47152863689708431628171093)
                ·
                  refine ⟨276286310681885341571315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47152863689708431628171093 276286310681885341571315)
                  ·
                    rfl

theorem cell23_4842591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 9].length) (baseStart_4842591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842591 prefixEnd_4842591 := by exact prefixLift 4842591
  have htrace : WordTrace (prefixWord ++ tailWord_4842591) baseStart_4842591 baseEnd_4842591 := by
    simpa [prefixWord, tailWord_4842591, baseEnd_4842591] using wordTrace_append hprefix tailTrace_4842591
  have hstable : (prefixWord ++ tailWord_4842591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842591).length < 2 ^ (prefixWord ++ tailWord_4842591).sum := by decide
  have hdescent : baseEnd_4842591 < baseStart_4842591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842602 : List Nat := [3, 1, 3, 2, 2, 2, 1, 2, 1, 4, 2]
def baseStart_4842602 : Nat := 118140960795 + 4842602 * 2 ^ 59
def prefixEnd_4842602 : Nat := 4983230072969 + 3 ^ 40 * 4842602 * 2
def baseEnd_4842602 : Nat := 2486582444424167531104285

theorem tailTrace_4842602 : CollatzResearch.WordTrace tailWord_4842602 prefixEnd_4842602 2486582444424167531104285 := by
  unfold tailWord_4842602
  simp only [CollatzResearch.WordTrace]
  refine ⟨44156051300521869855462515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117749470134724986281233373 44156051300521869855462515)
  ·
    refine ⟨66234076950782804783193773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44156051300521869855462515 66234076950782804783193773)
    ·
      refine ⟨24837778856543551793697665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66234076950782804783193773 24837778856543551793697665)
      ·
        refine ⟨18628334142407663845273249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24837778856543551793697665 18628334142407663845273249)
        ·
          refine ⟨13971250606805747883954937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18628334142407663845273249 13971250606805747883954937)
          ·
            refine ⟨10478437955104310912966203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13971250606805747883954937 10478437955104310912966203)
            ·
              refine ⟨15717656932656466369449305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10478437955104310912966203 15717656932656466369449305)
              ·
                refine ⟨11788242699492349777086979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15717656932656466369449305 11788242699492349777086979)
                ·
                  refine ⟨17682364049238524665630469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11788242699492349777086979 17682364049238524665630469)
                  ·
                    refine ⟨3315443259232223374805713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17682364049238524665630469 3315443259232223374805713)
                    ·
                      refine ⟨2486582444424167531104285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3315443259232223374805713 2486582444424167531104285)
                      ·
                        rfl

theorem cell23_4842602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_4842602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842602 prefixEnd_4842602 := by exact prefixLift 4842602
  have htrace : WordTrace (prefixWord ++ tailWord_4842602) baseStart_4842602 baseEnd_4842602 := by
    simpa [prefixWord, tailWord_4842602, baseEnd_4842602] using wordTrace_append hprefix tailTrace_4842602
  have hstable : (prefixWord ++ tailWord_4842602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842602).length < 2 ^ (prefixWord ++ tailWord_4842602).sum := by decide
  have hdescent : baseEnd_4842602 < baseStart_4842602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842655 : List Nat := [1, 1, 2, 6, 2, 1, 1, 1, 1, 7]
def baseStart_4842655 : Nat := 118140960795 + 4842655 * 2 ^ 59
def prefixEnd_4842655 : Nat := 4983230072969 + 3 ^ 40 * 4842655 * 2
def baseEnd_4842655 : Nat := 828869886299618607913847

theorem tailTrace_4842655 : CollatzResearch.WordTrace tailWord_4842655 prefixEnd_4842655 828869886299618607913847 := by
  unfold tailWord_4842655
  simp only [CollatzResearch.WordTrace]
  refine ⟨176626138270895469473529419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117750758847263646315686279 176626138270895469473529419)
  ·
    refine ⟨264939207406343204210294129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176626138270895469473529419 264939207406343204210294129)
    ·
      refine ⟨198704405554757403157720597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264939207406343204210294129 198704405554757403157720597)
      ·
        refine ⟨9314269010379253273018153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 198704405554757403157720597 9314269010379253273018153)
        ·
          refine ⟨6985701757784439954763615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9314269010379253273018153 6985701757784439954763615)
          ·
            refine ⟨10478552636676659932145423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6985701757784439954763615 10478552636676659932145423)
            ·
              refine ⟨15717828955014989898218135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10478552636676659932145423 15717828955014989898218135)
              ·
                refine ⟨23576743432522484847327203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15717828955014989898218135 23576743432522484847327203)
                ·
                  refine ⟨35365115148783727270990805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23576743432522484847327203 35365115148783727270990805)
                  ·
                    refine ⟨828869886299618607913847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35365115148783727270990805 828869886299618607913847)
                    ·
                      rfl

theorem cell23_4842655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 7].length) (baseStart_4842655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842655 prefixEnd_4842655 := by exact prefixLift 4842655
  have htrace : WordTrace (prefixWord ++ tailWord_4842655) baseStart_4842655 baseEnd_4842655 := by
    simpa [prefixWord, tailWord_4842655, baseEnd_4842655] using wordTrace_append hprefix tailTrace_4842655
  have hstable : (prefixWord ++ tailWord_4842655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842655).length < 2 ^ (prefixWord ++ tailWord_4842655).sum := by decide
  have hdescent : baseEnd_4842655 < baseStart_4842655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842675 : List Nat := [1, 1, 1, 2, 3, 2, 3, 2, 2, 4, 2]
def baseStart_4842675 : Nat := 118140960795 + 4842675 * 2 ^ 59
def prefixEnd_4842675 : Nat := 4983230072969 + 3 ^ 40 * 4842675 * 2
def baseEnd_4842675 : Nat := 2486619928511945745491449

theorem tailTrace_4842675 : CollatzResearch.WordTrace tailWord_4842675 prefixEnd_4842675 2486619928511945745491449 := by
  unfold tailWord_4842675
  simp only [CollatzResearch.WordTrace]
  refine ⟨176626867730823012889257479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117751245153882008592838319 176626867730823012889257479)
  ·
    refine ⟨264940301596234519333886219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176626867730823012889257479 264940301596234519333886219)
    ·
      refine ⟨397410452394351779000829329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264940301596234519333886219 397410452394351779000829329)
      ·
        refine ⟨298057839295763834250621997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 397410452394351779000829329 298057839295763834250621997)
        ·
          refine ⟨111771689735911437843983249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 298057839295763834250621997 111771689735911437843983249)
          ·
            refine ⟨83828767301933578382987437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111771689735911437843983249 83828767301933578382987437)
            ·
              refine ⟨31435787738225091893620289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83828767301933578382987437 31435787738225091893620289)
              ·
                refine ⟨23576840803668818920215217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31435787738225091893620289 23576840803668818920215217)
                ·
                  refine ⟨17682630602751614190161413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23576840803668818920215217 17682630602751614190161413)
                  ·
                    refine ⟨3315493238015927660655265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17682630602751614190161413 3315493238015927660655265)
                    ·
                      refine ⟨2486619928511945745491449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3315493238015927660655265 2486619928511945745491449)
                      ·
                        rfl

theorem cell23_4842675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 4, 2].length) (baseStart_4842675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842675 prefixEnd_4842675 := by exact prefixLift 4842675
  have htrace : WordTrace (prefixWord ++ tailWord_4842675) baseStart_4842675 baseEnd_4842675 := by
    simpa [prefixWord, tailWord_4842675, baseEnd_4842675] using wordTrace_append hprefix tailTrace_4842675
  have hstable : (prefixWord ++ tailWord_4842675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842675).length < 2 ^ (prefixWord ++ tailWord_4842675).sum := by decide
  have hdescent : baseEnd_4842675 < baseStart_4842675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842685 : List Nat := [1, 4, 1, 2, 1, 1, 3, 3, 3, 4]
def baseStart_4842685 : Nat := 118140960795 + 4842685 * 2 ^ 59
def prefixEnd_4842685 : Nat := 4983230072969 + 3 ^ 40 * 4842685 * 2
def baseEnd_4842685 : Nat := 828875021106163568788801

theorem tailTrace_4842685 : CollatzResearch.WordTrace tailWord_4842685 prefixEnd_4842685 828875021106163568788801 := by
  unfold tailWord_4842685
  simp only [CollatzResearch.WordTrace]
  refine ⟨176627232460786784597121509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117751488307191189731414339 176627232460786784597121509)
  ·
    refine ⟨33117606086397522111960283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176627232460786784597121509 33117606086397522111960283)
    ·
      refine ⟨49676409129596283167940425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33117606086397522111960283 49676409129596283167940425)
      ·
        refine ⟨37257306847197212375955319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49676409129596283167940425 37257306847197212375955319)
        ·
          refine ⟨55885960270795818563932979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37257306847197212375955319 55885960270795818563932979)
          ·
            refine ⟨83828940406193727845899469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55885960270795818563932979 83828940406193727845899469)
            ·
              refine ⟨31435852652322647942212301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83828940406193727845899469 31435852652322647942212301)
              ·
                refine ⟨11788444744620992978329613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31435852652322647942212301 11788444744620992978329613)
                ·
                  refine ⟨4420666779232872366873605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11788444744620992978329613 4420666779232872366873605)
                  ·
                    refine ⟨828875021106163568788801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4420666779232872366873605 828875021106163568788801)
                    ·
                      rfl

theorem cell23_4842685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_4842685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842685 prefixEnd_4842685 := by exact prefixLift 4842685
  have htrace : WordTrace (prefixWord ++ tailWord_4842685) baseStart_4842685 baseEnd_4842685 := by
    simpa [prefixWord, tailWord_4842685, baseEnd_4842685] using wordTrace_append hprefix tailTrace_4842685
  have hstable : (prefixWord ++ tailWord_4842685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842685).length < 2 ^ (prefixWord ++ tailWord_4842685).sum := by decide
  have hdescent : baseEnd_4842685 < baseStart_4842685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842775 : List Nat := [1, 1, 3, 4, 1, 1, 3, 2, 1, 6]
def baseStart_4842775 : Nat := 118140960795 + 4842775 * 2 ^ 59
def prefixEnd_4842775 : Nat := 4983230072969 + 3 ^ 40 * 4842775 * 2
def baseEnd_4842775 : Nat := 828890425525798451413663

theorem tailTrace_4842775 : CollatzResearch.WordTrace tailWord_4842775 prefixEnd_4842775 828890425525798451413663 := by
  unfold tailWord_4842775
  simp only [CollatzResearch.WordTrace]
  refine ⟨176630515030460729967897779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117753676686973819978598519 176630515030460729967897779)
  ·
    refine ⟨264945772545691094951846669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176630515030460729967897779 264945772545691094951846669)
    ·
      refine ⟨99354664704634160606942501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 264945772545691094951846669 99354664704634160606942501)
      ·
        refine ⟨18628999632118905113801719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99354664704634160606942501 18628999632118905113801719)
        ·
          refine ⟨27943499448178357670702579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18628999632118905113801719 27943499448178357670702579)
          ·
            refine ⟨41915249172267536506053869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27943499448178357670702579 41915249172267536506053869)
            ·
              refine ⟨15718218439600326189770201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41915249172267536506053869 15718218439600326189770201)
              ·
                refine ⟨11788663829700244642327651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15718218439600326189770201 11788663829700244642327651)
                ·
                  refine ⟨17682995744550366963491477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11788663829700244642327651 17682995744550366963491477)
                  ·
                    refine ⟨828890425525798451413663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17682995744550366963491477 828890425525798451413663)
                    ·
                      rfl

theorem cell23_4842775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 6].length) (baseStart_4842775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842775 prefixEnd_4842775 := by exact prefixLift 4842775
  have htrace : WordTrace (prefixWord ++ tailWord_4842775) baseStart_4842775 baseEnd_4842775 := by
    simpa [prefixWord, tailWord_4842775, baseEnd_4842775] using wordTrace_append hprefix tailTrace_4842775
  have hstable : (prefixWord ++ tailWord_4842775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842775).length < 2 ^ (prefixWord ++ tailWord_4842775).sum := by decide
  have hdescent : baseEnd_4842775 < baseStart_4842775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842802 : List Nat := [3, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3]
def baseStart_4842802 : Nat := 118140960795 + 4842802 * 2 ^ 59
def prefixEnd_4842802 : Nat := 4983230072969 + 3 ^ 40 * 4842802 * 2
def baseEnd_4842802 : Nat := 2486685140555066748603365

theorem tailTrace_4842802 : CollatzResearch.WordTrace tailWord_4842802 prefixEnd_4842802 2486685140555066748603365 := by
  unfold tailWord_4842802
  simp only [CollatzResearch.WordTrace]
  refine ⟨44157874950340728394782665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117754333200908609052753773 44157874950340728394782665)
  ·
    refine ⟨33118406212755546296086999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44157874950340728394782665 33118406212755546296086999)
    ·
      refine ⟨49677609319133319444130499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33118406212755546296086999 49677609319133319444130499)
      ·
        refine ⟨74516413978699979166195749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49677609319133319444130499 74516413978699979166195749)
        ·
          refine ⟨13971827621006246093661703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74516413978699979166195749 13971827621006246093661703)
          ·
            refine ⟨20957741431509369140492555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13971827621006246093661703 20957741431509369140492555)
            ·
              refine ⟨31436612147264053710738833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20957741431509369140492555 31436612147264053710738833)
              ·
                refine ⟨23577459110448040283054125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31436612147264053710738833 23577459110448040283054125)
                ·
                  refine ⟨8841547166418015106145297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23577459110448040283054125 8841547166418015106145297)
                  ·
                    refine ⟨6631160374813511329608973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8841547166418015106145297 6631160374813511329608973)
                    ·
                      refine ⟨2486685140555066748603365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6631160374813511329608973 2486685140555066748603365)
                      ·
                        rfl

theorem cell23_4842802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_4842802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842802 prefixEnd_4842802 := by exact prefixLift 4842802
  have htrace : WordTrace (prefixWord ++ tailWord_4842802) baseStart_4842802 baseEnd_4842802 := by
    simpa [prefixWord, tailWord_4842802, baseEnd_4842802] using wordTrace_append hprefix tailTrace_4842802
  have hstable : (prefixWord ++ tailWord_4842802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842802).length < 2 ^ (prefixWord ++ tailWord_4842802).sum := by decide
  have hdescent : baseEnd_4842802 < baseStart_4842802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842805 : List Nat := [1, 3, 3, 1, 2, 2, 3, 8]
def baseStart_4842805 : Nat := 118140960795 + 4842805 * 2 ^ 59
def prefixEnd_4842805 : Nat := 4983230072969 + 3 ^ 40 * 4842805 * 2
def baseEnd_4842805 : Nat := 92099506703593712476513

theorem tailTrace_4842805 : CollatzResearch.WordTrace tailWord_4842805 prefixEnd_4842805 92099506703593712476513 := by
  unfold tailWord_4842805
  simp only [CollatzResearch.WordTrace]
  refine ⟨176631609220352045091489869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117754406146901363394326579 176631609220352045091489869)
  ·
    refine ⟨66236853457632016909308701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176631609220352045091489869 66236853457632016909308701)
    ·
      refine ⟨24838820046612006340990763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66236853457632016909308701 24838820046612006340990763)
      ·
        refine ⟨37258230069918009511486145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24838820046612006340990763 37258230069918009511486145)
        ·
          refine ⟨27943672552438507133614609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37258230069918009511486145 27943672552438507133614609)
          ·
            refine ⟨20957754414328880350210957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27943672552438507133614609 20957754414328880350210957)
            ·
              refine ⟨7859157905373330131329109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20957754414328880350210957 7859157905373330131329109)
              ·
                refine ⟨92099506703593712476513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7859157905373330131329109 92099506703593712476513)
                ·
                  rfl

theorem cell23_4842805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 8].length) (baseStart_4842805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842805 prefixEnd_4842805 := by exact prefixLift 4842805
  have htrace : WordTrace (prefixWord ++ tailWord_4842805) baseStart_4842805 baseEnd_4842805 := by
    simpa [prefixWord, tailWord_4842805, baseEnd_4842805] using wordTrace_append hprefix tailTrace_4842805
  have hstable : (prefixWord ++ tailWord_4842805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842805).length < 2 ^ (prefixWord ++ tailWord_4842805).sum := by decide
  have hdescent : baseEnd_4842805 < baseStart_4842805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842812 : List Nat := [2, 2, 2, 2, 1, 4, 2, 1, 1, 2, 4]
def baseStart_4842812 : Nat := 118140960795 + 4842812 * 2 ^ 59
def prefixEnd_4842812 : Nat := 4983230072969 + 3 ^ 40 * 4842812 * 2
def baseEnd_4842812 : Nat := 2486690275361611709478319

theorem tailTrace_4842812 : CollatzResearch.WordTrace tailWord_4842812 prefixEnd_4842812 2486690275361611709478319 := by
  unfold tailWord_4842812
  simp only [CollatzResearch.WordTrace]
  refine ⟨88315932265663342643497345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117754576354217790191329793 88315932265663342643497345)
  ·
    refine ⟨66236949199247506982623009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88315932265663342643497345 66236949199247506982623009)
    ·
      refine ⟨49677711899435630236967257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66236949199247506982623009 49677711899435630236967257)
      ·
        refine ⟨37258283924576722677725443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49677711899435630236967257 37258283924576722677725443)
        ·
          refine ⟨55887425886865084016588165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37258283924576722677725443 55887425886865084016588165)
          ·
            refine ⟨10478892353787203253110281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55887425886865084016588165 10478892353787203253110281)
            ·
              refine ⟨7859169265340402439832711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10478892353787203253110281 7859169265340402439832711)
              ·
                refine ⟨11788753898010603659749067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7859169265340402439832711 11788753898010603659749067)
                ·
                  refine ⟨17683130847015905489623601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11788753898010603659749067 17683130847015905489623601)
                  ·
                    refine ⟨13262348135261929117217701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17683130847015905489623601 13262348135261929117217701)
                    ·
                      refine ⟨2486690275361611709478319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13262348135261929117217701 2486690275361611709478319)
                      ·
                        rfl

theorem cell23_4842812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_4842812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842812 prefixEnd_4842812 := by exact prefixLift 4842812
  have htrace : WordTrace (prefixWord ++ tailWord_4842812) baseStart_4842812 baseEnd_4842812 := by
    simpa [prefixWord, tailWord_4842812, baseEnd_4842812] using wordTrace_append hprefix tailTrace_4842812
  have hstable : (prefixWord ++ tailWord_4842812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842812).length < 2 ^ (prefixWord ++ tailWord_4842812).sum := by decide
  have hdescent : baseEnd_4842812 < baseStart_4842812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842832 : List Nat := [2, 1, 1, 1, 1, 5, 2, 2, 4, 1, 3]
def baseStart_4842832 : Nat := 118140960795 + 4842832 * 2 ^ 59
def prefixEnd_4842832 : Nat := 4983230072969 + 3 ^ 40 * 4842832 * 2
def baseEnd_4842832 : Nat := 2486700544974701631228227

theorem tailTrace_4842832 : CollatzResearch.WordTrace tailWord_4842832 prefixEnd_4842832 2486700544974701631228227 := by
  unfold tailWord_4842832
  simp only [CollatzResearch.WordTrace]
  refine ⟨88316296995627114351361375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117755062660836152468481833 88316296995627114351361375)
  ·
    refine ⟨132474445493440671527042063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88316296995627114351361375 132474445493440671527042063)
    ·
      refine ⟨198711668240161007290563095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132474445493440671527042063 198711668240161007290563095)
      ·
        refine ⟨298067502360241510935844643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198711668240161007290563095 298067502360241510935844643)
        ·
          refine ⟨447101253540362266403766965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298067502360241510935844643 447101253540362266403766965)
          ·
            refine ⟨41915742519408962475353153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 447101253540362266403766965 41915742519408962475353153)
            ·
              refine ⟨31436806889556721856514865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41915742519408962475353153 31436806889556721856514865)
              ·
                refine ⟨23577605167167541392386149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31436806889556721856514865 23577605167167541392386149)
                ·
                  refine ⟨4420800968843914011072403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23577605167167541392386149 4420800968843914011072403)
                  ·
                    refine ⟨6631201453265871016608605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4420800968843914011072403 6631201453265871016608605)
                    ·
                      refine ⟨2486700544974701631228227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6631201453265871016608605 2486700544974701631228227)
                      ·
                        rfl

theorem cell23_4842832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 4, 1, 3].length) (baseStart_4842832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842832 prefixEnd_4842832 := by exact prefixLift 4842832
  have htrace : WordTrace (prefixWord ++ tailWord_4842832) baseStart_4842832 baseEnd_4842832 := by
    simpa [prefixWord, tailWord_4842832, baseEnd_4842832] using wordTrace_append hprefix tailTrace_4842832
  have hstable : (prefixWord ++ tailWord_4842832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842832).length < 2 ^ (prefixWord ++ tailWord_4842832).sum := by decide
  have hdescent : baseEnd_4842832 < baseStart_4842832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842865 : List Nat := [1, 2, 2, 2, 1, 2, 4, 1, 2, 6]
def baseStart_4842865 : Nat := 118140960795 + 4842865 * 2 ^ 59
def prefixEnd_4842865 : Nat := 4983230072969 + 3 ^ 40 * 4842865 * 2
def baseEnd_4842865 : Nat := 828905829945433334038525

theorem tailTrace_4842865 : CollatzResearch.WordTrace tailWord_4842865 prefixEnd_4842865 828905829945433334038525 := by
  unfold tailWord_4842865
  simp only [CollatzResearch.WordTrace]
  refine ⟨176633797600134675338674049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117755865066756450225782699 176633797600134675338674049)
  ·
    refine ⟨132475348200101006504005537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176633797600134675338674049 132475348200101006504005537)
    ·
      refine ⟨99356511150075754878004153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132475348200101006504005537 99356511150075754878004153)
      ·
        refine ⟨74517383362556816158503115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99356511150075754878004153 74517383362556816158503115)
        ·
          refine ⟨111776075043835224237754673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74517383362556816158503115 111776075043835224237754673)
          ·
            refine ⟨83832056282876418178316005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111776075043835224237754673 83832056282876418178316005)
            ·
              refine ⟨15718510553039328408434251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83832056282876418178316005 15718510553039328408434251)
              ·
                refine ⟨23577765829558992612651377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15718510553039328408434251 23577765829558992612651377)
                ·
                  refine ⟨17683324372169244459488533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23577765829558992612651377 17683324372169244459488533)
                  ·
                    refine ⟨828905829945433334038525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17683324372169244459488533 828905829945433334038525)
                    ·
                      rfl

theorem cell23_4842865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 6].length) (baseStart_4842865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842865 prefixEnd_4842865 := by exact prefixLift 4842865
  have htrace : WordTrace (prefixWord ++ tailWord_4842865) baseStart_4842865 baseEnd_4842865 := by
    simpa [prefixWord, tailWord_4842865, baseEnd_4842865] using wordTrace_append hprefix tailTrace_4842865
  have hstable : (prefixWord ++ tailWord_4842865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842865).length < 2 ^ (prefixWord ++ tailWord_4842865).sum := by decide
  have hdescent : baseEnd_4842865 < baseStart_4842865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842866 : List Nat := [3, 2, 1, 2, 1, 2, 5, 1, 2, 1, 3]
def baseStart_4842866 : Nat := 118140960795 + 4842866 * 2 ^ 59
def prefixEnd_4842866 : Nat := 4983230072969 + 3 ^ 40 * 4842866 * 2
def baseEnd_4842866 : Nat := 2486718003316954498203071

theorem tailTrace_4842866 : CollatzResearch.WordTrace tailWord_4842866 prefixEnd_4842866 2486718003316954498203071 := by
  unfold tailWord_4842866
  simp only [CollatzResearch.WordTrace]
  refine ⟨44158458518282763127365113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117755889382087368339640301 44158458518282763127365113)
  ·
    refine ⟨33118843888712072345523835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44158458518282763127365113 33118843888712072345523835)
    ·
      refine ⟨49678265833068108518285753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33118843888712072345523835 49678265833068108518285753)
      ·
        refine ⟨37258699374801081388714315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49678265833068108518285753 37258699374801081388714315)
        ·
          refine ⟨55888049062201622083071473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37258699374801081388714315 55888049062201622083071473)
          ·
            refine ⟨41916036796651216562303605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55888049062201622083071473 41916036796651216562303605)
            ·
              refine ⟨3929628449686051552715963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41916036796651216562303605 3929628449686051552715963)
              ·
                refine ⟨5894442674529077329073945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3929628449686051552715963 5894442674529077329073945)
                ·
                  refine ⟨4420832005896807996805459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5894442674529077329073945 4420832005896807996805459)
                  ·
                    refine ⟨6631248008845211995208189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4420832005896807996805459 6631248008845211995208189)
                    ·
                      refine ⟨2486718003316954498203071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6631248008845211995208189 2486718003316954498203071)
                      ·
                        rfl

theorem cell23_4842866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_4842866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842866 prefixEnd_4842866 := by exact prefixLift 4842866
  have htrace : WordTrace (prefixWord ++ tailWord_4842866) baseStart_4842866 baseEnd_4842866 := by
    simpa [prefixWord, tailWord_4842866, baseEnd_4842866] using wordTrace_append hprefix tailTrace_4842866
  have hstable : (prefixWord ++ tailWord_4842866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842866).length < 2 ^ (prefixWord ++ tailWord_4842866).sum := by decide
  have hdescent : baseEnd_4842866 < baseStart_4842866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842875 : List Nat := [1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 5]
def baseStart_4842875 : Nat := 118140960795 + 4842875 * 2 ^ 59
def prefixEnd_4842875 : Nat := 4983230072969 + 3 ^ 40 * 4842875 * 2
def baseEnd_4842875 : Nat := 2486722624642844962990529

theorem tailTrace_4842875 : CollatzResearch.WordTrace tailWord_4842875 prefixEnd_4842875 2486722624642844962990529 := by
  unfold tailWord_4842875
  simp only [CollatzResearch.WordTrace]
  refine ⟨176634162330098447046538079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117756108220065631364358719 176634162330098447046538079)
  ·
    refine ⟨264951243495147670569807119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176634162330098447046538079 264951243495147670569807119)
    ·
      refine ⟨397426865242721505854710679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264951243495147670569807119 397426865242721505854710679)
      ·
        refine ⟨596140297864082258782066019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397426865242721505854710679 596140297864082258782066019)
        ·
          refine ⟨894210446796123388173099029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 596140297864082258782066019 894210446796123388173099029)
          ·
            refine ⟨41916114693568283820614017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 894210446796123388173099029 41916114693568283820614017)
            ·
              refine ⟨31437086020176212865460513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41916114693568283820614017 31437086020176212865460513)
              ·
                refine ⟨23577814515132159649095385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31437086020176212865460513 23577814515132159649095385)
                ·
                  refine ⟨17683360886349119736821539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23577814515132159649095385 17683360886349119736821539)
                  ·
                    refine ⟨26525041329523679605232309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17683360886349119736821539 26525041329523679605232309)
                    ·
                      refine ⟨2486722624642844962990529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26525041329523679605232309 2486722624642844962990529)
                      ·
                        rfl

theorem cell23_4842875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 5].length) (baseStart_4842875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842875 prefixEnd_4842875 := by exact prefixLift 4842875
  have htrace : WordTrace (prefixWord ++ tailWord_4842875) baseStart_4842875 baseEnd_4842875 := by
    simpa [prefixWord, tailWord_4842875, baseEnd_4842875] using wordTrace_append hprefix tailTrace_4842875
  have hstable : (prefixWord ++ tailWord_4842875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842875).length < 2 ^ (prefixWord ++ tailWord_4842875).sum := by decide
  have hdescent : baseEnd_4842875 < baseStart_4842875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842885 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 1, 4, 4]
def baseStart_4842885 : Nat := 118140960795 + 4842885 * 2 ^ 59
def prefixEnd_4842885 : Nat := 4983230072969 + 3 ^ 40 * 4842885 * 2
def baseEnd_4842885 : Nat := 2486727759449389923865483

theorem tailTrace_4842885 : CollatzResearch.WordTrace tailWord_4842885 prefixEnd_4842885 2486727759449389923865483 := by
  unfold tailWord_4842885
  simp only [CollatzResearch.WordTrace]
  refine ⟨176634527060062218754402109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117756351373374812502934739 176634527060062218754402109)
  ·
    refine ⟨66237947647523332032900791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176634527060062218754402109 66237947647523332032900791)
    ·
      refine ⟨99356921471284998049351187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66237947647523332032900791 99356921471284998049351187)
      ·
        refine ⟨149035382206927497074026781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99356921471284998049351187 149035382206927497074026781)
        ·
          refine ⟨55888268327597811402760043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149035382206927497074026781 55888268327597811402760043)
          ·
            refine ⟨83832402491396717104140065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55888268327597811402760043 83832402491396717104140065)
            ·
              refine ⟨62874301868547537828105049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83832402491396717104140065 62874301868547537828105049)
              ·
                refine ⟨47155726401410653371078787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62874301868547537828105049 47155726401410653371078787)
                ·
                  refine ⟨70733589602115980056618181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47155726401410653371078787 70733589602115980056618181)
                  ·
                    refine ⟨13262548050396746260615909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 70733589602115980056618181 13262548050396746260615909)
                    ·
                      refine ⟨2486727759449389923865483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13262548050396746260615909 2486727759449389923865483)
                      ·
                        rfl

theorem cell23_4842885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_4842885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842885 prefixEnd_4842885 := by exact prefixLift 4842885
  have htrace : WordTrace (prefixWord ++ tailWord_4842885) baseStart_4842885 baseEnd_4842885 := by
    simpa [prefixWord, tailWord_4842885, baseEnd_4842885] using wordTrace_append hprefix tailTrace_4842885
  have hstable : (prefixWord ++ tailWord_4842885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842885).length < 2 ^ (prefixWord ++ tailWord_4842885).sum := by decide
  have hdescent : baseEnd_4842885 < baseStart_4842885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842906 : List Nat := [3, 1, 1, 4, 1, 1, 2, 4, 2, 2, 2]
def baseStart_4842906 : Nat := 118140960795 + 4842906 * 2 ^ 59
def prefixEnd_4842906 : Nat := 4983230072969 + 3 ^ 40 * 4842906 * 2
def baseEnd_4842906 : Nat := 2486738542543134341702887

theorem tailTrace_4842906 : CollatzResearch.WordTrace tailWord_4842906 prefixEnd_4842906 2486738542543134341702887 := by
  unfold tailWord_4842906
  simp only [CollatzResearch.WordTrace]
  refine ⟨44158823248246534835229143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117756861995324092893944381 44158823248246534835229143)
  ·
    refine ⟨66238234872369802252843715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44158823248246534835229143 66238234872369802252843715)
    ·
      refine ⟨99357352308554703379265573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66238234872369802252843715 99357352308554703379265573)
      ·
        refine ⟨18629503557854006883612295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99357352308554703379265573 18629503557854006883612295)
        ·
          refine ⟨27944255336781010325418443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18629503557854006883612295 27944255336781010325418443)
          ·
            refine ⟨41916383005171515488127665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27944255336781010325418443 41916383005171515488127665)
            ·
              refine ⟨31437287253878636616095749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41916383005171515488127665 31437287253878636616095749)
              ·
                refine ⟨5894491360102244365517953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31437287253878636616095749 5894491360102244365517953)
                ·
                  refine ⟨4420868520076683274138465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5894491360102244365517953 4420868520076683274138465)
                  ·
                    refine ⟨3315651390057512455603849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4420868520076683274138465 3315651390057512455603849)
                    ·
                      refine ⟨2486738542543134341702887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3315651390057512455603849 2486738542543134341702887)
                      ·
                        rfl

theorem cell23_4842906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_4842906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842906 prefixEnd_4842906 := by exact prefixLift 4842906
  have htrace : WordTrace (prefixWord ++ tailWord_4842906) baseStart_4842906 baseEnd_4842906 := by
    simpa [prefixWord, tailWord_4842906, baseEnd_4842906] using wordTrace_append hprefix tailTrace_4842906
  have hstable : (prefixWord ++ tailWord_4842906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842906).length < 2 ^ (prefixWord ++ tailWord_4842906).sum := by decide
  have hdescent : baseEnd_4842906 < baseStart_4842906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842935 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 7]
def baseStart_4842935 : Nat := 118140960795 + 4842935 * 2 ^ 59
def prefixEnd_4842935 : Nat := 4983230072969 + 3 ^ 40 * 4842935 * 2
def baseEnd_4842935 : Nat := 2486753433482114728240253

theorem tailTrace_4842935 : CollatzResearch.WordTrace tailWord_4842935 prefixEnd_4842935 2486753433482114728240253 := by
  unfold tailWord_4842935
  simp only [CollatzResearch.WordTrace]
  refine ⟨176636350709881077293722259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117757567139920718195814839 176636350709881077293722259)
  ·
    refine ⟨264954526064821615940583389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176636350709881077293722259 264954526064821615940583389)
    ·
      refine ⟨99357947274308105977718771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 264954526064821615940583389 99357947274308105977718771)
      ·
        refine ⟨149036920911462158966578157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99357947274308105977718771 149036920911462158966578157)
        ·
          refine ⟨55888845341798309612466809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149036920911462158966578157 55888845341798309612466809)
          ·
            refine ⟨41916634006348732209350107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55888845341798309612466809 41916634006348732209350107)
            ·
              refine ⟨62874951009523098314025161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41916634006348732209350107 62874951009523098314025161)
              ·
                refine ⟨47156213257142323735518871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62874951009523098314025161 47156213257142323735518871)
                ·
                  refine ⟨70734319885713485603278307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47156213257142323735518871 70734319885713485603278307)
                  ·
                    refine ⟨106101479828570228404917461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 70734319885713485603278307 106101479828570228404917461)
                    ·
                      refine ⟨2486753433482114728240253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 106101479828570228404917461 2486753433482114728240253)
                      ·
                        rfl

theorem cell23_4842935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_4842935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842935 prefixEnd_4842935 := by exact prefixLift 4842935
  have htrace : WordTrace (prefixWord ++ tailWord_4842935) baseStart_4842935 baseEnd_4842935 := by
    simpa [prefixWord, tailWord_4842935, baseEnd_4842935] using wordTrace_append hprefix tailTrace_4842935
  have hstable : (prefixWord ++ tailWord_4842935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842935).length < 2 ^ (prefixWord ++ tailWord_4842935).sum := by decide
  have hdescent : baseEnd_4842935 < baseStart_4842935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842966 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2]
def baseStart_4842966 : Nat := 118140960795 + 4842966 * 2 ^ 59
def prefixEnd_4842966 : Nat := 4983230072969 + 3 ^ 40 * 4842966 * 2
def baseEnd_4842966 : Nat := 2486769351382404106952611

theorem tailTrace_4842966 : CollatzResearch.WordTrace tailWord_4842966 prefixEnd_4842966 2486769351382404106952611 := by
  unfold tailWord_4842966
  simp only [CollatzResearch.WordTrace]
  refine ⟨11039842585798048099256297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117758320915179179725400501 11039842585798048099256297)
  ·
    refine ⟨8279881939348536074442223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11039842585798048099256297 8279881939348536074442223)
    ·
      refine ⟨12419822909022804111663335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8279881939348536074442223 12419822909022804111663335)
      ·
        refine ⟨18629734363534206167495003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12419822909022804111663335 18629734363534206167495003)
        ·
          refine ⟨27944601545301309251242505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18629734363534206167495003 27944601545301309251242505)
          ·
            refine ⟨20958451158975981938431879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27944601545301309251242505 20958451158975981938431879)
            ·
              refine ⟨31437676738463972907647819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20958451158975981938431879 31437676738463972907647819)
              ·
                refine ⟨47156515107695959361471729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31437676738463972907647819 47156515107695959361471729)
                ·
                  refine ⟨35367386330771969521103797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47156515107695959361471729 35367386330771969521103797)
                  ·
                    refine ⟨3315692468509872142603481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35367386330771969521103797 3315692468509872142603481)
                    ·
                      refine ⟨2486769351382404106952611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3315692468509872142603481 2486769351382404106952611)
                      ·
                        rfl

theorem cell23_4842966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_4842966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842966 prefixEnd_4842966 := by exact prefixLift 4842966
  have htrace : WordTrace (prefixWord ++ tailWord_4842966) baseStart_4842966 baseEnd_4842966 := by
    simpa [prefixWord, tailWord_4842966, baseEnd_4842966] using wordTrace_append hprefix tailTrace_4842966
  have hstable : (prefixWord ++ tailWord_4842966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842966).length < 2 ^ (prefixWord ++ tailWord_4842966).sum := by decide
  have hdescent : baseEnd_4842966 < baseStart_4842966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4842979 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 1, 6, 2]
def baseStart_4842979 : Nat := 118140960795 + 4842979 * 2 ^ 59
def prefixEnd_4842979 : Nat := 4983230072969 + 3 ^ 40 * 4842979 * 2
def baseEnd_4842979 : Nat := 2486776026630912556090051

theorem tailTrace_4842979 : CollatzResearch.WordTrace tailWord_4842979 prefixEnd_4842979 2486776026630912556090051 := by
  unfold tailWord_4842979
  simp only [CollatzResearch.WordTrace]
  refine ⟨176637955521721672808323991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117758637014481115205549327 176637955521721672808323991)
  ·
    refine ⟨264956933282582509212485987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176637955521721672808323991 264956933282582509212485987)
    ·
      refine ⟨397435399923873763818728981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264956933282582509212485987 397435399923873763818728981)
      ·
        refine ⟨18629784371431582679002921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 397435399923873763818728981 18629784371431582679002921)
        ·
          refine ⟨13972338278573687009252191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18629784371431582679002921 13972338278573687009252191)
          ·
            refine ⟨20958507417860530513878287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13972338278573687009252191 20958507417860530513878287)
            ·
              refine ⟨31437761126790795770817431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20958507417860530513878287 31437761126790795770817431)
              ·
                refine ⟨47156641690186193656226147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31437761126790795770817431 47156641690186193656226147)
                ·
                  refine ⟨70734962535279290484339221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47156641690186193656226147 70734962535279290484339221)
                  ·
                    refine ⟨3315701368841216741453401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70734962535279290484339221 3315701368841216741453401)
                    ·
                      refine ⟨2486776026630912556090051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3315701368841216741453401 2486776026630912556090051)
                      ·
                        rfl

theorem cell23_4842979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_4842979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4842979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4842979 prefixEnd_4842979 := by exact prefixLift 4842979
  have htrace : WordTrace (prefixWord ++ tailWord_4842979) baseStart_4842979 baseEnd_4842979 := by
    simpa [prefixWord, tailWord_4842979, baseEnd_4842979] using wordTrace_append hprefix tailTrace_4842979
  have hstable : (prefixWord ++ tailWord_4842979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4842979).length < 2 ^ (prefixWord ++ tailWord_4842979).sum := by decide
  have hdescent : baseEnd_4842979 < baseStart_4842979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4842979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4843039 : List Nat := [1, 1, 2, 4, 1, 1, 3, 2, 1, 5, 2]
def baseStart_4843039 : Nat := 118140960795 + 4843039 * 2 ^ 59
def prefixEnd_4843039 : Nat := 4983230072969 + 3 ^ 40 * 4843039 * 2
def baseEnd_4843039 : Nat := 2486806835470182321339775

theorem tailTrace_4843039 : CollatzResearch.WordTrace tailWord_4843039 prefixEnd_4843039 2486806835470182321339775 := by
  unfold tailWord_4843039
  simp only [CollatzResearch.WordTrace]
  refine ⟨176640143901504303055508171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117760095934336202037005447 176640143901504303055508171)
  ·
    refine ⟨264960215852256454583262257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176640143901504303055508171 264960215852256454583262257)
    ·
      refine ⟨198720161889192340937446693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264960215852256454583262257 198720161889192340937446693)
      ·
        refine ⟨37260030354223563925771255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 198720161889192340937446693 37260030354223563925771255)
        ·
          refine ⟨55890045531335345888656883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37260030354223563925771255 55890045531335345888656883)
          ·
            refine ⟨83835068297003018832985325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55890045531335345888656883 83835068297003018832985325)
            ·
              refine ⟨31438150611376132062369497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83835068297003018832985325 31438150611376132062369497)
              ·
                refine ⟨23578612958532099046777123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31438150611376132062369497 23578612958532099046777123)
                ·
                  refine ⟨35367919437798148570165685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23578612958532099046777123 35367919437798148570165685)
                  ·
                    refine ⟨3315742447293576428453033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35367919437798148570165685 3315742447293576428453033)
                    ·
                      refine ⟨2486806835470182321339775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3315742447293576428453033 2486806835470182321339775)
                      ·
                        rfl

theorem cell23_4843039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_4843039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4843039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4843039 prefixEnd_4843039 := by exact prefixLift 4843039
  have htrace : WordTrace (prefixWord ++ tailWord_4843039) baseStart_4843039 baseEnd_4843039 := by
    simpa [prefixWord, tailWord_4843039, baseEnd_4843039] using wordTrace_append hprefix tailTrace_4843039
  have hstable : (prefixWord ++ tailWord_4843039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4843039).length < 2 ^ (prefixWord ++ tailWord_4843039).sum := by decide
  have hdescent : baseEnd_4843039 < baseStart_4843039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4843039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4843042 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 2, 1, 7]
def baseStart_4843042 : Nat := 118140960795 + 4843042 * 2 ^ 59
def prefixEnd_4843042 : Nat := 4983230072969 + 3 ^ 40 * 4843042 * 2
def baseEnd_4843042 : Nat := 2486808375912145809602261

theorem tailTrace_4843042 : CollatzResearch.WordTrace tailWord_4843042 prefixEnd_4843042 2486808375912145809602261 := by
  unfold tailWord_4843042
  simp only [CollatzResearch.WordTrace]
  refine ⟨44160063330123358641966845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117760168880328956378578253 44160063330123358641966845)
  ·
    refine ⟨16560023748796259490737567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44160063330123358641966845 16560023748796259490737567)
    ·
      refine ⟨24840035623194389236106351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16560023748796259490737567 24840035623194389236106351)
      ·
        refine ⟨37260053434791583854159527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24840035623194389236106351 37260053434791583854159527)
        ·
          refine ⟨55890080152187375781239291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37260053434791583854159527 55890080152187375781239291)
          ·
            refine ⟨83835120228281063671858937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55890080152187375781239291 83835120228281063671858937)
            ·
              refine ⟨62876340171210797753894203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83835120228281063671858937 62876340171210797753894203)
              ·
                refine ⟨94314510256816196630841305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62876340171210797753894203 94314510256816196630841305)
                ·
                  refine ⟨70735882692612147473130979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94314510256816196630841305 70735882692612147473130979)
                  ·
                    refine ⟨106103824038918221209696469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 70735882692612147473130979 106103824038918221209696469)
                    ·
                      refine ⟨2486808375912145809602261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 106103824038918221209696469 2486808375912145809602261)
                      ·
                        rfl

theorem cell23_4843042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_4843042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4843042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4843042 prefixEnd_4843042 := by exact prefixLift 4843042
  have htrace : WordTrace (prefixWord ++ tailWord_4843042) baseStart_4843042 baseEnd_4843042 := by
    simpa [prefixWord, tailWord_4843042, baseEnd_4843042] using wordTrace_append hprefix tailTrace_4843042
  have hstable : (prefixWord ++ tailWord_4843042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4843042).length < 2 ^ (prefixWord ++ tailWord_4843042).sum := by decide
  have hdescent : baseEnd_4843042 < baseStart_4843042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4843042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4843063 : List Nat := [1, 1, 3, 1, 2, 4, 3, 3, 1, 1, 3]
def baseStart_4843063 : Nat := 118140960795 + 4843063 * 2 ^ 59
def prefixEnd_4843063 : Nat := 4983230072969 + 3 ^ 40 * 4843063 * 2
def baseEnd_4843063 : Nat := 2486819159005890227439665

theorem tailTrace_4843063 : CollatzResearch.WordTrace tailWord_4843063 prefixEnd_4843063 2486819159005890227439665 := by
  unfold tailWord_4843063
  simp only [CollatzResearch.WordTrace]
  refine ⟨176641019253417355154381843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117760679502278236769587895 176641019253417355154381843)
  ·
    refine ⟨264961528880126032731572765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176641019253417355154381843 264961528880126032731572765)
    ·
      refine ⟨99360573330047262274339787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 264961528880126032731572765 99360573330047262274339787)
      ·
        refine ⟨149040859995070893411509681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99360573330047262274339787 149040859995070893411509681)
        ·
          refine ⟨111780644996303170058632261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149040859995070893411509681 111780644996303170058632261)
          ·
            refine ⟨20958870936806844385993549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111780644996303170058632261 20958870936806844385993549)
            ·
              refine ⟨7859576601302566644747581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20958870936806844385993549 7859576601302566644747581)
              ·
                refine ⟨2947341225488462491780343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7859576601302566644747581 2947341225488462491780343)
                ·
                  refine ⟨4421011838232693737670515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2947341225488462491780343 4421011838232693737670515)
                  ·
                    refine ⟨6631517757349040606505773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4421011838232693737670515 6631517757349040606505773)
                    ·
                      refine ⟨2486819159005890227439665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6631517757349040606505773 2486819159005890227439665)
                      ·
                        rfl

theorem cell23_4843063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 3, 1, 1, 3].length) (baseStart_4843063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4843063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4843063 prefixEnd_4843063 := by exact prefixLift 4843063
  have htrace : WordTrace (prefixWord ++ tailWord_4843063) baseStart_4843063 baseEnd_4843063 := by
    simpa [prefixWord, tailWord_4843063, baseEnd_4843063] using wordTrace_append hprefix tailTrace_4843063
  have hstable : (prefixWord ++ tailWord_4843063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4843063).length < 2 ^ (prefixWord ++ tailWord_4843063).sum := by decide
  have hdescent : baseEnd_4843063 < baseStart_4843063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4843063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4843082 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 3, 1, 6]
def baseStart_4843082 : Nat := 118140960795 + 4843082 * 2 ^ 59
def prefixEnd_4843082 : Nat := 4983230072969 + 3 ^ 40 * 4843082 * 2
def baseEnd_4843082 : Nat := 2486828915138325653102077

theorem tailTrace_4843082 : CollatzResearch.WordTrace tailWord_4843082 prefixEnd_4843082 2486828915138325653102077 := by
  unfold tailWord_4843082
  simp only [CollatzResearch.WordTrace]
  refine ⟨44160428060087130349830875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117761141493565680932882333 44160428060087130349830875)
  ·
    refine ⟨66240642090130695524746313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44160428060087130349830875 66240642090130695524746313)
    ·
      refine ⟨49680481567598021643559735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66240642090130695524746313 49680481567598021643559735)
      ·
        refine ⟨74520722351397032465339603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49680481567598021643559735 74520722351397032465339603)
        ·
          refine ⟨111781083527095548698009405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74520722351397032465339603 111781083527095548698009405)
          ·
            refine ⟨41917906322660830761753527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111781083527095548698009405 41917906322660830761753527)
            ·
              refine ⟨62876859483991246142630291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41917906322660830761753527 62876859483991246142630291)
              ·
                refine ⟨94315289225986869213945437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62876859483991246142630291 94315289225986869213945437)
                ·
                  refine ⟨35368233459745075955229539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94315289225986869213945437 35368233459745075955229539)
                  ·
                    refine ⟨53052350189617613932844309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35368233459745075955229539 53052350189617613932844309)
                    ·
                      refine ⟨2486828915138325653102077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53052350189617613932844309 2486828915138325653102077)
                      ·
                        rfl

theorem cell23_4843082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_4843082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4843082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4843082 prefixEnd_4843082 := by exact prefixLift 4843082
  have htrace : WordTrace (prefixWord ++ tailWord_4843082) baseStart_4843082 baseEnd_4843082 := by
    simpa [prefixWord, tailWord_4843082, baseEnd_4843082] using wordTrace_append hprefix tailTrace_4843082
  have hstable : (prefixWord ++ tailWord_4843082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4843082).length < 2 ^ (prefixWord ++ tailWord_4843082).sum := by decide
  have hdescent : baseEnd_4843082 < baseStart_4843082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4843082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4843089 : List Nat := [1, 2, 2, 1, 3, 2, 2, 2, 3, 2, 3]
def baseStart_4843089 : Nat := 118140960795 + 4843089 * 2 ^ 59
def prefixEnd_4843089 : Nat := 4983230072969 + 3 ^ 40 * 4843089 * 2
def baseEnd_4843089 : Nat := 2486832509502907125714545

theorem tailTrace_4843089 : CollatzResearch.WordTrace tailWord_4843089 prefixEnd_4843089 2486832509502907125714545 := by
  unfold tailWord_4843089
  simp only [CollatzResearch.WordTrace]
  refine ⟨176641967551323161594828321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117761311700882107729885547 176641967551323161594828321)
  ·
    refine ⟨132481475663492371196121241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176641967551323161594828321 132481475663492371196121241)
    ·
      refine ⟨99361106747619278397090931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132481475663492371196121241 99361106747619278397090931)
      ·
        refine ⟨149041660121428917595636397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99361106747619278397090931 149041660121428917595636397)
        ·
          refine ⟨55890622545535844098363649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149041660121428917595636397 55890622545535844098363649)
          ·
            refine ⟨41917966909151883073772737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55890622545535844098363649 41917966909151883073772737)
            ·
              refine ⟨31438475181863912305329553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41917966909151883073772737 31438475181863912305329553)
              ·
                refine ⟨23578856386397934228997165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31438475181863912305329553 23578856386397934228997165)
                ·
                  refine ⟨8842071144899225335873937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23578856386397934228997165 8842071144899225335873937)
                  ·
                    refine ⟨6631553358674419001905453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8842071144899225335873937 6631553358674419001905453)
                    ·
                      refine ⟨2486832509502907125714545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6631553358674419001905453 2486832509502907125714545)
                      ·
                        rfl

theorem cell23_4843089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 2, 3].length) (baseStart_4843089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4843089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4843089 prefixEnd_4843089 := by exact prefixLift 4843089
  have htrace : WordTrace (prefixWord ++ tailWord_4843089) baseStart_4843089 baseEnd_4843089 := by
    simpa [prefixWord, tailWord_4843089, baseEnd_4843089] using wordTrace_append hprefix tailTrace_4843089
  have hstable : (prefixWord ++ tailWord_4843089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4843089).length < 2 ^ (prefixWord ++ tailWord_4843089).sum := by decide
  have hdescent : baseEnd_4843089 < baseStart_4843089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4843089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4843137 : List Nat := [1, 2, 4, 2, 1, 2, 4, 2, 1, 2, 2]
def baseStart_4843137 : Nat := 118140960795 + 4843137 * 2 ^ 59
def prefixEnd_4843137 : Nat := 4983230072969 + 3 ^ 40 * 4843137 * 2
def baseEnd_4843137 : Nat := 2486857156574322937914325

theorem tailTrace_4843137 : CollatzResearch.WordTrace tailWord_4843137 prefixEnd_4843137 2486857156574322937914325 := by
  unfold tailWord_4843137
  simp only [CollatzResearch.WordTrace]
  refine ⟨176643718255149265792575665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117762478836766177195050443 176643718255149265792575665)
  ·
    refine ⟨132482788691361949344431749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176643718255149265792575665 132482788691361949344431749)
    ·
      refine ⟨24840522879630365502080953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132482788691361949344431749 24840522879630365502080953)
      ·
        refine ⟨18630392159722774126560715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24840522879630365502080953 18630392159722774126560715)
        ·
          refine ⟨27945588239584161189841073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18630392159722774126560715 27945588239584161189841073)
          ·
            refine ⟨20959191179688120892380805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27945588239584161189841073 20959191179688120892380805)
            ·
              refine ⟨3929848346191522667321401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20959191179688120892380805 3929848346191522667321401)
              ·
                refine ⟨2947386259643642000491051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3929848346191522667321401 2947386259643642000491051)
                ·
                  refine ⟨4421079389465463000736577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2947386259643642000491051 4421079389465463000736577)
                  ·
                    refine ⟨3315809542099097250552433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4421079389465463000736577 3315809542099097250552433)
                    ·
                      refine ⟨2486857156574322937914325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3315809542099097250552433 2486857156574322937914325)
                      ·
                        rfl

theorem cell23_4843137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_4843137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4843137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4843137 prefixEnd_4843137 := by exact prefixLift 4843137
  have htrace : WordTrace (prefixWord ++ tailWord_4843137) baseStart_4843137 baseEnd_4843137 := by
    simpa [prefixWord, tailWord_4843137, baseEnd_4843137] using wordTrace_append hprefix tailTrace_4843137
  have hstable : (prefixWord ++ tailWord_4843137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4843137).length < 2 ^ (prefixWord ++ tailWord_4843137).sum := by decide
  have hdescent : baseEnd_4843137 < baseStart_4843137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4843137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4843199 : List Nat := [1, 1, 2, 2, 2, 3, 4, 1, 7]
def baseStart_4843199 : Nat := 118140960795 + 4843199 * 2 ^ 59
def prefixEnd_4843199 : Nat := 4983230072969 + 3 ^ 40 * 4843199 * 2
def baseEnd_4843199 : Nat := 276320999152766855037671

theorem tailTrace_4843199 : CollatzResearch.WordTrace tailWord_4843199 prefixEnd_4843199 276320999152766855037671 := by
  unfold tailWord_4843199
  simp only [CollatzResearch.WordTrace]
  refine ⟨176645979580924650381332651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117763986387283100254221767 176645979580924650381332651)
  ·
    refine ⟨264968969371386975571998977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176645979580924650381332651 264968969371386975571998977)
    ·
      refine ⟨198726727028540231678999233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264968969371386975571998977 198726727028540231678999233)
      ·
        refine ⟨149045045271405173759249425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198726727028540231678999233 149045045271405173759249425)
        ·
          refine ⟨111783783953553880319437069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149045045271405173759249425 111783783953553880319437069)
          ·
            refine ⟨41918918982582705119788901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111783783953553880319437069 41918918982582705119788901)
            ·
              refine ⟨7859797309234257209960419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41918918982582705119788901 7859797309234257209960419)
              ·
                refine ⟨11789695963851385814940629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7859797309234257209960419 11789695963851385814940629)
                ·
                  refine ⟨276320999152766855037671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11789695963851385814940629 276320999152766855037671)
                  ·
                    rfl

theorem cell23_4843199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 7].length) (baseStart_4843199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4843199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4843199 prefixEnd_4843199 := by exact prefixLift 4843199
  have htrace : WordTrace (prefixWord ++ tailWord_4843199) baseStart_4843199 baseEnd_4843199 := by
    simpa [prefixWord, tailWord_4843199, baseEnd_4843199] using wordTrace_append hprefix tailTrace_4843199
  have hstable : (prefixWord ++ tailWord_4843199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4843199).length < 2 ^ (prefixWord ++ tailWord_4843199).sum := by decide
  have hdescent : baseEnd_4843199 < baseStart_4843199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4843199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4843210 : List Nat := [3, 1, 2, 1, 5, 2, 1, 1, 1, 4, 2]
def baseStart_4843210 : Nat := 118140960795 + 4843210 * 2 ^ 59
def prefixEnd_4843210 : Nat := 4983230072969 + 3 ^ 40 * 4843210 * 2
def baseEnd_4843210 : Nat := 2486894640662101152301489

theorem tailTrace_4843210 : CollatzResearch.WordTrace tailWord_4843210 prefixEnd_4843210 2486894640662101152301489 := by
  unfold tailWord_4843210
  simp only [CollatzResearch.WordTrace]
  refine ⟨44161595195971199814995771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117764253855923199506655389 44161595195971199814995771)
  ·
    refine ⟨66242392793956799722493657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44161595195971199814995771 66242392793956799722493657)
    ·
      refine ⟨49681794595467599791870243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66242392793956799722493657 49681794595467599791870243)
      ·
        refine ⟨74522691893201399687805365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49681794595467599791870243 74522691893201399687805365)
        ·
          refine ⟨6986502364987631220731753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74522691893201399687805365 6986502364987631220731753)
          ·
            refine ⟨5239876773740723415548815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6986502364987631220731753 5239876773740723415548815)
            ·
              refine ⟨7859815160611085123323223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5239876773740723415548815 7859815160611085123323223)
              ·
                refine ⟨11789722740916627684984835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7859815160611085123323223 11789722740916627684984835)
                ·
                  refine ⟨17684584111374941527477253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11789722740916627684984835 17684584111374941527477253)
                  ·
                    refine ⟨3315859520882801536401985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17684584111374941527477253 3315859520882801536401985)
                    ·
                      refine ⟨2486894640662101152301489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3315859520882801536401985 2486894640662101152301489)
                      ·
                        rfl

theorem cell23_4843210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 1, 1, 4, 2].length) (baseStart_4843210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4843210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4843210 prefixEnd_4843210 := by exact prefixLift 4843210
  have htrace : WordTrace (prefixWord ++ tailWord_4843210) baseStart_4843210 baseEnd_4843210 := by
    simpa [prefixWord, tailWord_4843210, baseEnd_4843210] using wordTrace_append hprefix tailTrace_4843210
  have hstable : (prefixWord ++ tailWord_4843210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4843210).length < 2 ^ (prefixWord ++ tailWord_4843210).sum := by decide
  have hdescent : baseEnd_4843210 < baseStart_4843210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4843210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4843246 : List Nat := [4, 1, 2, 1, 1, 2, 3, 2, 2, 5]
def baseStart_4843246 : Nat := 118140960795 + 4843246 * 2 ^ 59
def prefixEnd_4843246 : Nat := 4983230072969 + 3 ^ 40 * 4843246 * 2
def baseEnd_4843246 : Nat := 828971041988554337150441

theorem tailTrace_4843246 : CollatzResearch.WordTrace tailWord_4843246 prefixEnd_4843246 828971041988554337150441 := by
  unfold tailWord_4843246
  simp only [CollatzResearch.WordTrace]
  refine ⟨22080961726469297176036699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117765129207836251605529061 22080961726469297176036699)
  ·
    refine ⟨33121442589703945764055049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22080961726469297176036699 33121442589703945764055049)
    ·
      refine ⟨24841081942277959323041287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33121442589703945764055049 24841081942277959323041287)
      ·
        refine ⟨37261622913416938984561931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24841081942277959323041287 37261622913416938984561931)
        ·
          refine ⟨55892434370125408476842897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37261622913416938984561931 55892434370125408476842897)
          ·
            refine ⟨41919325777594056357632173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55892434370125408476842897 41919325777594056357632173)
            ·
              refine ⟨15719747166597771134112065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41919325777594056357632173 15719747166597771134112065)
              ·
                refine ⟨11789810374948328350584049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15719747166597771134112065 11789810374948328350584049)
                ·
                  refine ⟨8842357781211246262938037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11789810374948328350584049 8842357781211246262938037)
                  ·
                    refine ⟨828971041988554337150441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8842357781211246262938037 828971041988554337150441)
                    ·
                      rfl

theorem cell23_4843246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_4843246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4843246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4843246 prefixEnd_4843246 := by exact prefixLift 4843246
  have htrace : WordTrace (prefixWord ++ tailWord_4843246) baseStart_4843246 baseEnd_4843246 := by
    simpa [prefixWord, tailWord_4843246, baseEnd_4843246] using wordTrace_append hprefix tailTrace_4843246
  have hstable : (prefixWord ++ tailWord_4843246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4843246).length < 2 ^ (prefixWord ++ tailWord_4843246).sum := by decide
  have hdescent : baseEnd_4843246 < baseStart_4843246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4843246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4843276 : List Nat := [2, 2, 1, 2, 2, 1, 2, 4, 3, 4]
def baseStart_4843276 : Nat := 118140960795 + 4843276 * 2 ^ 59
def prefixEnd_4843276 : Nat := 4983230072969 + 3 ^ 40 * 4843276 * 2
def baseEnd_4843276 : Nat := 828976176795099298025395

theorem tailTrace_4843276 : CollatzResearch.WordTrace tailWord_4843276 prefixEnd_4843276 828976176795099298025395 := by
  unfold tailWord_4843276
  simp only [CollatzResearch.WordTrace]
  refine ⟨88324394000822846265942841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117765858667763795021257121 88324394000822846265942841)
  ·
    refine ⟨66243295500617134699457131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88324394000822846265942841 66243295500617134699457131)
    ·
      refine ⟨99364943250925702049185697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66243295500617134699457131 99364943250925702049185697)
      ·
        refine ⟨74523707438194276536889273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99364943250925702049185697 74523707438194276536889273)
        ·
          refine ⟨55892780578645707402666955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74523707438194276536889273 55892780578645707402666955)
          ·
            refine ⟨83839170867968561104000433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55892780578645707402666955 83839170867968561104000433)
            ·
              refine ⟨62879378150976420828000325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83839170867968561104000433 62879378150976420828000325)
              ·
                refine ⟨11789883403308078905250061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62879378150976420828000325 11789883403308078905250061)
                ·
                  refine ⟨4421206276240529589468773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11789883403308078905250061 4421206276240529589468773)
                  ·
                    refine ⟨828976176795099298025395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4421206276240529589468773 828976176795099298025395)
                    ·
                      rfl

theorem cell23_4843276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 3, 4].length) (baseStart_4843276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4843276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4843276 prefixEnd_4843276 := by exact prefixLift 4843276
  have htrace : WordTrace (prefixWord ++ tailWord_4843276) baseStart_4843276 baseEnd_4843276 := by
    simpa [prefixWord, tailWord_4843276, baseEnd_4843276] using wordTrace_append hprefix tailTrace_4843276
  have hstable : (prefixWord ++ tailWord_4843276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4843276).length < 2 ^ (prefixWord ++ tailWord_4843276).sum := by decide
  have hdescent : baseEnd_4843276 < baseStart_4843276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4843276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4843333 : List Nat := [1, 3, 1, 1, 1, 2, 5, 2, 3, 1, 3]
def baseStart_4843333 : Nat := 118140960795 + 4843333 * 2 ^ 59
def prefixEnd_4843333 : Nat := 4983230072969 + 3 ^ 40 * 4843333 * 2
def baseEnd_4843333 : Nat := 2486957798782604171063423

theorem tailTrace_4843333 : CollatzResearch.WordTrace tailWord_4843333 prefixEnd_4843333 2486957798782604171063423 := by
  unfold tailWord_4843333
  simp only [CollatzResearch.WordTrace]
  refine ⟨176650866962439191266710653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117767244641626127511140435 176650866962439191266710653)
  ·
    refine ⟨66244075110914696725016495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176650866962439191266710653 66244075110914696725016495)
    ·
      refine ⟨99366112666372045087524743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66244075110914696725016495 99366112666372045087524743)
      ·
        refine ⟨149049168999558067631287115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99366112666372045087524743 149049168999558067631287115)
        ·
          refine ⟨223573753499337101446930673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149049168999558067631287115 223573753499337101446930673)
          ·
            refine ⟨167680315124502826085198005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223573753499337101446930673 167680315124502826085198005)
            ·
              refine ⟨15720029542922139945487313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 167680315124502826085198005 15720029542922139945487313)
              ·
                refine ⟨11790022157191604959115485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15720029542922139945487313 11790022157191604959115485)
                ·
                  refine ⟨4421258308946851859668307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11790022157191604959115485 4421258308946851859668307)
                  ·
                    refine ⟨6631887463420277789502461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4421258308946851859668307 6631887463420277789502461)
                    ·
                      refine ⟨2486957798782604171063423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6631887463420277789502461 2486957798782604171063423)
                      ·
                        rfl

theorem cell23_4843333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 3, 1, 3].length) (baseStart_4843333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4843333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4843333 prefixEnd_4843333 := by exact prefixLift 4843333
  have htrace : WordTrace (prefixWord ++ tailWord_4843333) baseStart_4843333 baseEnd_4843333 := by
    simpa [prefixWord, tailWord_4843333, baseEnd_4843333] using wordTrace_append hprefix tailTrace_4843333
  have hstable : (prefixWord ++ tailWord_4843333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4843333).length < 2 ^ (prefixWord ++ tailWord_4843333).sum := by decide
  have hdescent : baseEnd_4843333 < baseStart_4843333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4843333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4843336 : List Nat := [2, 1, 3, 1, 1, 4, 2, 1, 3, 5]
def baseStart_4843336 : Nat := 118140960795 + 4843336 * 2 ^ 59
def prefixEnd_4843336 : Nat := 4983230072969 + 3 ^ 40 * 4843336 * 2
def baseEnd_4843336 : Nat := 828986446408189219775303

theorem tailTrace_4843336 : CollatzResearch.WordTrace tailWord_4843336 prefixEnd_4843336 828986446408189219775303 := by
  unfold tailWord_4843336
  simp only [CollatzResearch.WordTrace]
  refine ⟨88325488190714161389534931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117767317587618881852713241 88325488190714161389534931)
  ·
    refine ⟨132488232286071242084302397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88325488190714161389534931 132488232286071242084302397)
    ·
      refine ⟨49683087107276715781613399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132488232286071242084302397 49683087107276715781613399)
      ·
        refine ⟨74524630660915073672420099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49683087107276715781613399 74524630660915073672420099)
        ·
          refine ⟨111786945991372610508630149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74524630660915073672420099 111786945991372610508630149)
          ·
            refine ⟨20960052373382364470368153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111786945991372610508630149 20960052373382364470368153)
            ·
              refine ⟨15720039280036773352776115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20960052373382364470368153 15720039280036773352776115)
              ·
                refine ⟨23580058920055160029164173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15720039280036773352776115 23580058920055160029164173)
                ·
                  refine ⟨8842522095020685010936565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23580058920055160029164173 8842522095020685010936565)
                  ·
                    refine ⟨828986446408189219775303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8842522095020685010936565 828986446408189219775303)
                    ·
                      rfl

theorem cell23_4843336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_4843336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4843336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4843336 prefixEnd_4843336 := by exact prefixLift 4843336
  have htrace : WordTrace (prefixWord ++ tailWord_4843336) baseStart_4843336 baseEnd_4843336 := by
    simpa [prefixWord, tailWord_4843336, baseEnd_4843336] using wordTrace_append hprefix tailTrace_4843336
  have hstable : (prefixWord ++ tailWord_4843336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4843336).length < 2 ^ (prefixWord ++ tailWord_4843336).sum := by decide
  have hdescent : baseEnd_4843336 < baseStart_4843336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4843336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4843379 : List Nat := [1, 1, 1, 2, 2, 1, 3, 12]
def baseStart_4843379 : Nat := 118140960795 + 4843379 * 2 ^ 59
def prefixEnd_4843379 : Nat := 4983230072969 + 3 ^ 40 * 4843379 * 2
def baseEnd_4843379 : Nat := 92110422921952258929193

theorem tailTrace_4843379 : CollatzResearch.WordTrace tailWord_4843379 prefixEnd_4843379 92110422921952258929193 := by
  unfold tailWord_4843379
  simp only [CollatzResearch.WordTrace]
  refine ⟨176652544720272541122885191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117768363146848360748590127 176652544720272541122885191)
  ·
    refine ⟨264978817080408811684327787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176652544720272541122885191 264978817080408811684327787)
    ·
      refine ⟨397468225620613217526491681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264978817080408811684327787 397468225620613217526491681)
      ·
        refine ⟨298101169215459913144868761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 397468225620613217526491681 298101169215459913144868761)
        ·
          refine ⟨223575876911594934858651571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298101169215459913144868761 223575876911594934858651571)
          ·
            refine ⟨335363815367392402287977357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223575876911594934858651571 335363815367392402287977357)
            ·
              refine ⟨125761430762772150857991509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 335363815367392402287977357 125761430762772150857991509)
              ·
                refine ⟨92110422921952258929193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 125761430762772150857991509 92110422921952258929193)
                ·
                  rfl

theorem cell23_4843379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 12].length) (baseStart_4843379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4843379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4843379 prefixEnd_4843379 := by exact prefixLift 4843379
  have htrace : WordTrace (prefixWord ++ tailWord_4843379) baseStart_4843379 baseEnd_4843379 := by
    simpa [prefixWord, tailWord_4843379, baseEnd_4843379] using wordTrace_append hprefix tailTrace_4843379
  have hstable : (prefixWord ++ tailWord_4843379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4843379).length < 2 ^ (prefixWord ++ tailWord_4843379).sum := by decide
  have hdescent : baseEnd_4843379 < baseStart_4843379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4843379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4843410 : List Nat := [3, 2, 3, 2, 1, 2, 2, 1, 1, 1, 5]
def baseStart_4843410 : Nat := 118140960795 + 4843410 * 2 ^ 59
def prefixEnd_4843410 : Nat := 4983230072969 + 3 ^ 40 * 4843410 * 2
def baseEnd_4843410 : Nat := 2486997336793000369800569

theorem tailTrace_4843410 : CollatzResearch.WordTrace tailWord_4843410 prefixEnd_4843410 2486997336793000369800569 := by
  unfold tailWord_4843410
  simp only [CollatzResearch.WordTrace]
  refine ⟨44163418845790058354315921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117769116922106822278175789 44163418845790058354315921)
  ·
    refine ⟨33122564134342543765736941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44163418845790058354315921 33122564134342543765736941)
    ·
      refine ⟨12420961550378453912151353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33122564134342543765736941 12420961550378453912151353)
      ·
        refine ⟨9315721162783840434113515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12420961550378453912151353 9315721162783840434113515)
        ·
          refine ⟨13973581744175760651170273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9315721162783840434113515 13973581744175760651170273)
          ·
            refine ⟨10480186308131820488377705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13973581744175760651170273 10480186308131820488377705)
            ·
              refine ⟨7860139731098865366283279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10480186308131820488377705 7860139731098865366283279)
              ·
                refine ⟨11790209596648298049424919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7860139731098865366283279 11790209596648298049424919)
                ·
                  refine ⟨17685314394972447074137379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11790209596648298049424919 17685314394972447074137379)
                  ·
                    refine ⟨26527971592458670611206069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17685314394972447074137379 26527971592458670611206069)
                    ·
                      refine ⟨2486997336793000369800569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26527971592458670611206069 2486997336793000369800569)
                      ·
                        rfl

theorem cell23_4843410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_4843410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4843410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4843410 prefixEnd_4843410 := by exact prefixLift 4843410
  have htrace : WordTrace (prefixWord ++ tailWord_4843410) baseStart_4843410 baseEnd_4843410 := by
    simpa [prefixWord, tailWord_4843410, baseEnd_4843410] using wordTrace_append hprefix tailTrace_4843410
  have hstable : (prefixWord ++ tailWord_4843410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4843410).length < 2 ^ (prefixWord ++ tailWord_4843410).sum := by decide
  have hdescent : baseEnd_4843410 < baseStart_4843410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4843410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4843450 : List Nat := [3, 1, 1, 1, 2, 1, 2, 6, 1, 3, 2]
def baseStart_4843450 : Nat := 118140960795 + 4843450 * 2 ^ 59
def prefixEnd_4843450 : Nat := 4983230072969 + 3 ^ 40 * 4843450 * 2
def baseEnd_4843450 : Nat := 2487017876019180213300385

theorem tailTrace_4843450 : CollatzResearch.WordTrace tailWord_4843450 prefixEnd_4843450 2487017876019180213300385 := by
  unfold tailWord_4843450
  simp only [CollatzResearch.WordTrace]
  refine ⟨44163783575753830062179951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117770089535343546832479869 44163783575753830062179951)
  ·
    refine ⟨66245675363630745093269927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44163783575753830062179951 66245675363630745093269927)
    ·
      refine ⟨99368513045446117639904891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66245675363630745093269927 99368513045446117639904891)
      ·
        refine ⟨149052769568169176459857337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99368513045446117639904891 149052769568169176459857337)
        ·
          refine ⟨111789577176126882344893003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149052769568169176459857337 111789577176126882344893003)
          ·
            refine ⟨167684365764190323517339505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111789577176126882344893003 167684365764190323517339505)
            ·
              refine ⟨125763274323142742638004629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167684365764190323517339505 125763274323142742638004629)
              ·
                refine ⟨5895153483897316061156467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 125763274323142742638004629 5895153483897316061156467)
                ·
                  refine ⟨8842730225845974091734701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5895153483897316061156467 8842730225845974091734701)
                  ·
                    refine ⟨3316023834692240284400513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8842730225845974091734701 3316023834692240284400513)
                    ·
                      refine ⟨2487017876019180213300385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3316023834692240284400513 2487017876019180213300385)
                      ·
                        rfl

theorem cell23_4843450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 1, 3, 2].length) (baseStart_4843450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4843450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4843450 prefixEnd_4843450 := by exact prefixLift 4843450
  have htrace : WordTrace (prefixWord ++ tailWord_4843450) baseStart_4843450 baseEnd_4843450 := by
    simpa [prefixWord, tailWord_4843450, baseEnd_4843450] using wordTrace_append hprefix tailTrace_4843450
  have hstable : (prefixWord ++ tailWord_4843450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4843450).length < 2 ^ (prefixWord ++ tailWord_4843450).sum := by decide
  have hdescent : baseEnd_4843450 < baseStart_4843450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4843450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4843467 : List Nat := [1, 1, 1, 1, 3, 4, 5, 1, 1, 3, 2]
def baseStart_4843467 : Nat := 118140960795 + 4843467 * 2 ^ 59
def prefixEnd_4843467 : Nat := 4983230072969 + 3 ^ 40 * 4843467 * 2
def baseEnd_4843467 : Nat := 2487026605190306646787807

theorem tailTrace_4843467 : CollatzResearch.WordTrace tailWord_4843467 prefixEnd_4843467 2487026605190306646787807 := by
  unfold tailWord_4843467
  simp only [CollatzResearch.WordTrace]
  refine ⟨176655754343953732152088655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117770502895969154768059103 176655754343953732152088655)
  ·
    refine ⟨264983631515930598228132983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176655754343953732152088655 264983631515930598228132983)
    ·
      refine ⟨397475447273895897342199475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264983631515930598228132983 397475447273895897342199475)
      ·
        refine ⟨596213170910843846013299213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397475447273895897342199475 596213170910843846013299213)
        ·
          refine ⟨223579939091566442254987205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 596213170910843846013299213 223579939091566442254987205)
          ·
            refine ⟨41921238579668707922810101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 223579939091566442254987205 41921238579668707922810101)
            ·
              refine ⟨3930116116843941367763447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41921238579668707922810101 3930116116843941367763447)
              ·
                refine ⟨5895174175265912051645171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3930116116843941367763447 5895174175265912051645171)
                ·
                  refine ⟨8842761262898868077467757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5895174175265912051645171 8842761262898868077467757)
                  ·
                    refine ⟨3316035473587075529050409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8842761262898868077467757 3316035473587075529050409)
                    ·
                      refine ⟨2487026605190306646787807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3316035473587075529050409 2487026605190306646787807)
                      ·
                        rfl

theorem cell23_4843467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 1, 3, 2].length) (baseStart_4843467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4843467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4843467 prefixEnd_4843467 := by exact prefixLift 4843467
  have htrace : WordTrace (prefixWord ++ tailWord_4843467) baseStart_4843467 baseEnd_4843467 := by
    simpa [prefixWord, tailWord_4843467, baseEnd_4843467] using wordTrace_append hprefix tailTrace_4843467
  have hstable : (prefixWord ++ tailWord_4843467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4843467).length < 2 ^ (prefixWord ++ tailWord_4843467).sum := by decide
  have hdescent : baseEnd_4843467 < baseStart_4843467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4843467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4843474 : List Nat := [3, 2, 2, 3, 2, 1, 2, 2, 2, 1, 3]
def baseStart_4843474 : Nat := 118140960795 + 4843474 * 2 ^ 59
def prefixEnd_4843474 : Nat := 4983230072969 + 3 ^ 40 * 4843474 * 2
def baseEnd_4843474 : Nat := 2487030199554888119400275

theorem tailTrace_4843474 : CollatzResearch.WordTrace tailWord_4843474 prefixEnd_4843474 2487030199554888119400275 := by
  unfold tailWord_4843474
  simp only [CollatzResearch.WordTrace]
  refine ⟨44164002413732093086898369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117770673103285581565062317 44164002413732093086898369)
  ·
    refine ⟨33123001810299069815173777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44164002413732093086898369 33123001810299069815173777)
    ·
      refine ⟨24842251357724302361380333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33123001810299069815173777 24842251357724302361380333)
      ·
        refine ⟨9315844259146613385517625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24842251357724302361380333 9315844259146613385517625)
        ·
          refine ⟨6986883194359960039138219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9315844259146613385517625 6986883194359960039138219)
          ·
            refine ⟨10480324791539940058707329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6986883194359960039138219 10480324791539940058707329)
            ·
              refine ⟨7860243593654955044030497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10480324791539940058707329 7860243593654955044030497)
              ·
                refine ⟨5895182695241216283022873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7860243593654955044030497 5895182695241216283022873)
                ·
                  refine ⟨4421387021430912212267155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5895182695241216283022873 4421387021430912212267155)
                  ·
                    refine ⟨6632080532146368318400733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4421387021430912212267155 6632080532146368318400733)
                    ·
                      refine ⟨2487030199554888119400275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6632080532146368318400733 2487030199554888119400275)
                      ·
                        rfl

theorem cell23_4843474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_4843474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4843474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4843474 prefixEnd_4843474 := by exact prefixLift 4843474
  have htrace : WordTrace (prefixWord ++ tailWord_4843474) baseStart_4843474 baseEnd_4843474 := by
    simpa [prefixWord, tailWord_4843474, baseEnd_4843474] using wordTrace_append hprefix tailTrace_4843474
  have hstable : (prefixWord ++ tailWord_4843474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4843474).length < 2 ^ (prefixWord ++ tailWord_4843474).sum := by decide
  have hdescent : baseEnd_4843474 < baseStart_4843474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4843474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4843563 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 5, 4]
def baseStart_4843563 : Nat := 118140960795 + 4843563 * 2 ^ 59
def prefixEnd_4843563 : Nat := 4983230072969 + 3 ^ 40 * 4843563 * 2
def baseEnd_4843563 : Nat := 829025299777712757062455

theorem tailTrace_4843563 : CollatzResearch.WordTrace tailWord_4843563 prefixEnd_4843563 829025299777712757062455 := by
  unfold tailWord_4843563
  simp only [CollatzResearch.WordTrace]
  refine ⟨176659255751605940547583343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117772837167737293698388895 176659255751605940547583343)
  ·
    refine ⟨264988883627408910821375015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176659255751605940547583343 264988883627408910821375015)
    ·
      refine ⟨397483325441113366232062523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264988883627408910821375015 397483325441113366232062523)
      ·
        refine ⟨596224988161670049348093785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397483325441113366232062523 596224988161670049348093785)
        ·
          refine ⟨447168741121252537011070339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 596224988161670049348093785 447168741121252537011070339)
          ·
            refine ⟨670753111681878805516605509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447168741121252537011070339 670753111681878805516605509)
            ·
              refine ⟨125766208440352276034363533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 670753111681878805516605509 125766208440352276034363533)
              ·
                refine ⟨47162328165132103512886325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125766208440352276034363533 47162328165132103512886325)
                ·
                  refine ⟨4421468265481134704333093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47162328165132103512886325 4421468265481134704333093)
                  ·
                    refine ⟨829025299777712757062455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4421468265481134704333093 829025299777712757062455)
                    ·
                      rfl

theorem cell23_4843563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 5, 4].length) (baseStart_4843563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4843563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4843563 prefixEnd_4843563 := by exact prefixLift 4843563
  have htrace : WordTrace (prefixWord ++ tailWord_4843563) baseStart_4843563 baseEnd_4843563 := by
    simpa [prefixWord, tailWord_4843563, baseEnd_4843563] using wordTrace_append hprefix tailTrace_4843563
  have hstable : (prefixWord ++ tailWord_4843563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4843563).length < 2 ^ (prefixWord ++ tailWord_4843563).sum := by decide
  have hdescent : baseEnd_4843563 < baseStart_4843563 := by decide
  rcases family_descends (prefixWord ++ tailWord_4843563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4843593 : List Nat := [1, 2, 1, 1, 2, 2, 4, 4, 6]
def baseStart_4843593 : Nat := 118140960795 + 4843593 * 2 ^ 59
def prefixEnd_4843593 : Nat := 4983230072969 + 3 ^ 40 * 4843593 * 2
def baseEnd_4843593 : Nat := 276343478194752572645803

theorem tailTrace_4843593 : CollatzResearch.WordTrace tailWord_4843593 prefixEnd_4843593 276343478194752572645803 := by
  unfold tailWord_4843593
  simp only [CollatzResearch.WordTrace]
  refine ⟨176660349941497255671175433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117773566627664837114116955 176660349941497255671175433)
  ·
    refine ⟨132495262456122941753381575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176660349941497255671175433 132495262456122941753381575)
    ·
      refine ⟨198742893684184412630072363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132495262456122941753381575 198742893684184412630072363)
      ·
        refine ⟨298114340526276618945108545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198742893684184412630072363 298114340526276618945108545)
        ·
          refine ⟨223585755394707464208831409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298114340526276618945108545 223585755394707464208831409)
          ·
            refine ⟨167689316546030598156623557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223585755394707464208831409 167689316546030598156623557)
            ·
              refine ⟨31441746852380737154366917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 167689316546030598156623557 31441746852380737154366917)
              ·
                refine ⟨5895327534821388216443797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31441746852380737154366917 5895327534821388216443797)
                ·
                  refine ⟨276343478194752572645803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5895327534821388216443797 276343478194752572645803)
                  ·
                    rfl

theorem cell23_4843593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 6].length) (baseStart_4843593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4843593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4843593 prefixEnd_4843593 := by exact prefixLift 4843593
  have htrace : WordTrace (prefixWord ++ tailWord_4843593) baseStart_4843593 baseEnd_4843593 := by
    simpa [prefixWord, tailWord_4843593, baseEnd_4843593] using wordTrace_append hprefix tailTrace_4843593
  have hstable : (prefixWord ++ tailWord_4843593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4843593).length < 2 ^ (prefixWord ++ tailWord_4843593).sum := by decide
  have hdescent : baseEnd_4843593 < baseStart_4843593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4843593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4843660 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 4, 6, 2]
def baseStart_4843660 : Nat := 118140960795 + 4843660 * 2 ^ 59
def prefixEnd_4843660 : Nat := 4983230072969 + 3 ^ 40 * 4843660 * 2
def baseEnd_4843660 : Nat := 2487125706956624391674419

theorem tailTrace_4843660 : CollatzResearch.WordTrace tailWord_4843660 prefixEnd_4843660 2487125706956624391674419 := by
  unfold tailWord_4843660
  simp only [CollatzResearch.WordTrace]
  refine ⟨88331396816127263056932217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117775195754836350742576289 88331396816127263056932217)
  ·
    refine ⟨66248547612095447292699163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88331396816127263056932217 66248547612095447292699163)
    ·
      refine ⟨99372821418143170939048745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66248547612095447292699163 99372821418143170939048745)
      ·
        refine ⟨74529616063607378204286559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99372821418143170939048745 74529616063607378204286559)
        ·
          refine ⟨111794424095411067306429839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74529616063607378204286559 111794424095411067306429839)
          ·
            refine ⟨167691636143116600959644759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111794424095411067306429839 167691636143116600959644759)
            ·
              refine ⟨251537454214674901439467139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167691636143116600959644759 251537454214674901439467139)
              ·
                refine ⟨377306181322012352159200709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251537454214674901439467139 377306181322012352159200709)
                ·
                  refine ⟨70744908997877316029850133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 377306181322012352159200709 70744908997877316029850133)
                  ·
                    refine ⟨3316167609275499188899225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70744908997877316029850133 3316167609275499188899225)
                    ·
                      refine ⟨2487125706956624391674419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3316167609275499188899225 2487125706956624391674419)
                      ·
                        rfl

theorem cell23_4843660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 4, 6, 2].length) (baseStart_4843660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4843660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4843660 prefixEnd_4843660 := by exact prefixLift 4843660
  have htrace : WordTrace (prefixWord ++ tailWord_4843660) baseStart_4843660 baseEnd_4843660 := by
    simpa [prefixWord, tailWord_4843660, baseEnd_4843660] using wordTrace_append hprefix tailTrace_4843660
  have hstable : (prefixWord ++ tailWord_4843660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4843660).length < 2 ^ (prefixWord ++ tailWord_4843660).sum := by decide
  have hdescent : baseEnd_4843660 < baseStart_4843660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4843660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4843673 : List Nat := [1, 2, 1, 2, 1, 2, 1, 5, 1, 1, 6]
def baseStart_4843673 : Nat := 118140960795 + 4843673 * 2 ^ 59
def prefixEnd_4843673 : Nat := 4983230072969 + 3 ^ 40 * 4843673 * 2
def baseEnd_4843673 : Nat := 2487132382205132840811859

theorem tailTrace_4843673 : CollatzResearch.WordTrace tailWord_4843673 prefixEnd_4843673 2487132382205132840811859 := by
  unfold tailWord_4843673
  simp only [CollatzResearch.WordTrace]
  refine ⟨176663267781207429334087673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117775511854138286222725115 176663267781207429334087673)
  ·
    refine ⟨132497450835905572000565755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176663267781207429334087673 132497450835905572000565755)
    ·
      refine ⟨198746176253858358000848633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132497450835905572000565755 198746176253858358000848633)
      ·
        refine ⟨149059632190393768500636475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198746176253858358000848633 149059632190393768500636475)
        ·
          refine ⟨223589448285590652750954713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149059632190393768500636475 223589448285590652750954713)
          ·
            refine ⟨167692086214192989563216035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223589448285590652750954713 167692086214192989563216035)
            ·
              refine ⟨251538129321289484344824053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167692086214192989563216035 251538129321289484344824053)
              ·
                refine ⟨23581699623870889157327255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 251538129321289484344824053 23581699623870889157327255)
                ·
                  refine ⟨35372549435806333735990883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23581699623870889157327255 35372549435806333735990883)
                  ·
                    refine ⟨53058824153709500603986325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35372549435806333735990883 53058824153709500603986325)
                    ·
                      refine ⟨2487132382205132840811859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53058824153709500603986325 2487132382205132840811859)
                      ·
                        rfl

theorem cell23_4843673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_4843673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4843673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4843673 prefixEnd_4843673 := by exact prefixLift 4843673
  have htrace : WordTrace (prefixWord ++ tailWord_4843673) baseStart_4843673 baseEnd_4843673 := by
    simpa [prefixWord, tailWord_4843673, baseEnd_4843673] using wordTrace_append hprefix tailTrace_4843673
  have hstable : (prefixWord ++ tailWord_4843673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4843673).length < 2 ^ (prefixWord ++ tailWord_4843673).sum := by decide
  have hdescent : baseEnd_4843673 < baseStart_4843673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4843673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4843714 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_4843714 : Nat := 118140960795 + 4843714 * 2 ^ 59
def prefixEnd_4843714 : Nat := 4983230072969 + 3 ^ 40 * 4843714 * 2
def baseEnd_4843714 : Nat := 2487153434911967180399171

theorem tailTrace_4843714 : CollatzResearch.WordTrace tailWord_4843714 prefixEnd_4843714 2487153434911967180399171 := by
  unfold tailWord_4843714
  simp only [CollatzResearch.WordTrace]
  refine ⟨44166190793514723334082549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117776508782705928890886797 44166190793514723334082549)
  ·
    refine ⟨4140580386892005312570239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44166190793514723334082549 4140580386892005312570239)
    ·
      refine ⟨6210870580338007968855359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4140580386892005312570239 6210870580338007968855359)
      ·
        refine ⟨9316305870507011953283039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6210870580338007968855359 9316305870507011953283039)
        ·
          refine ⟨13974458805760517929924559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9316305870507011953283039 13974458805760517929924559)
          ·
            refine ⟨20961688208640776894886839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13974458805760517929924559 20961688208640776894886839)
            ·
              refine ⟨31442532312961165342330259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20961688208640776894886839 31442532312961165342330259)
              ·
                refine ⟨47163798469441748013495389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31442532312961165342330259 47163798469441748013495389)
                ·
                  refine ⟨17686424426040655505060771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47163798469441748013495389 17686424426040655505060771)
                  ·
                    refine ⟨26529636639060983257591157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17686424426040655505060771 26529636639060983257591157)
                    ·
                      refine ⟨2487153434911967180399171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26529636639060983257591157 2487153434911967180399171)
                      ·
                        rfl

theorem cell23_4843714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_4843714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4843714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4843714 prefixEnd_4843714 := by exact prefixLift 4843714
  have htrace : WordTrace (prefixWord ++ tailWord_4843714) baseStart_4843714 baseEnd_4843714 := by
    simpa [prefixWord, tailWord_4843714, baseEnd_4843714] using wordTrace_append hprefix tailTrace_4843714
  have hstable : (prefixWord ++ tailWord_4843714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4843714).length < 2 ^ (prefixWord ++ tailWord_4843714).sum := by decide
  have hdescent : baseEnd_4843714 < baseStart_4843714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4843714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4843734 : List Nat := [5, 2, 1, 2, 1, 1, 4, 7]
def baseStart_4843734 : Nat := 118140960795 + 4843734 * 2 ^ 59
def prefixEnd_4843734 : Nat := 4983230072969 + 3 ^ 40 * 4843734 * 2
def baseEnd_4843734 : Nat := 92117174241668781561077

theorem tailTrace_4843734 : CollatzResearch.WordTrace tailWord_4843734 prefixEnd_4843734 92117174241668781561077 := by
  unfold tailWord_4843734
  simp only [CollatzResearch.WordTrace]
  refine ⟨11041593289624152297003641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117776995089324291168038837 11041593289624152297003641)
  ·
    refine ⟨8281194967218114222752731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11041593289624152297003641 8281194967218114222752731)
    ·
      refine ⟨12421792450827171334129097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8281194967218114222752731 12421792450827171334129097)
      ·
        refine ⟨9316344338120378500596823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12421792450827171334129097 9316344338120378500596823)
        ·
          refine ⟨13974516507180567750895235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9316344338120378500596823 13974516507180567750895235)
          ·
            refine ⟨20961774760770851626342853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13974516507180567750895235 20961774760770851626342853)
            ·
              refine ⟨3930332767644534679939285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20961774760770851626342853 3930332767644534679939285)
              ·
                refine ⟨92117174241668781561077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3930332767644534679939285 92117174241668781561077)
                ·
                  rfl

theorem cell23_4843734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 7].length) (baseStart_4843734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4843734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4843734 prefixEnd_4843734 := by exact prefixLift 4843734
  have htrace : WordTrace (prefixWord ++ tailWord_4843734) baseStart_4843734 baseEnd_4843734 := by
    simpa [prefixWord, tailWord_4843734, baseEnd_4843734] using wordTrace_append hprefix tailTrace_4843734
  have hstable : (prefixWord ++ tailWord_4843734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4843734).length < 2 ^ (prefixWord ++ tailWord_4843734).sum := by decide
  have hdescent : baseEnd_4843734 < baseStart_4843734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4843734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4843737 : List Nat := [1, 2, 1, 2, 3, 1, 2, 3, 3, 3, 2]
def baseStart_4843737 : Nat := 118140960795 + 4843737 * 2 ^ 59
def prefixEnd_4843737 : Nat := 4983230072969 + 3 ^ 40 * 4843737 * 2
def baseEnd_4843737 : Nat := 2487165244967020590411565

theorem tailTrace_4843737 : CollatzResearch.WordTrace tailWord_4843737 prefixEnd_4843737 2487165244967020590411565 := by
  unfold tailWord_4843737
  simp only [CollatzResearch.WordTrace]
  refine ⟨176665602052975568264417465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117777068035317045509611643 176665602052975568264417465)
  ·
    refine ⟨132499201539731676198313099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176665602052975568264417465 132499201539731676198313099)
    ·
      refine ⟨198748802309597514297469649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132499201539731676198313099 198748802309597514297469649)
      ·
        refine ⟨149061601732198135723102237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198748802309597514297469649 149061601732198135723102237)
        ·
          refine ⟨55898100649574300896163339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149061601732198135723102237 55898100649574300896163339)
          ·
            refine ⟨83847150974361451344245009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55898100649574300896163339 83847150974361451344245009)
            ·
              refine ⟨62885363230771088508183757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83847150974361451344245009 62885363230771088508183757)
              ·
                refine ⟨23582011211539158190568909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62885363230771088508183757 23582011211539158190568909)
                ·
                  refine ⟨8843254204327184321463341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23582011211539158190568909 8843254204327184321463341)
                  ·
                    refine ⟨3316220326622694120548753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8843254204327184321463341 3316220326622694120548753)
                    ·
                      refine ⟨2487165244967020590411565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3316220326622694120548753 2487165244967020590411565)
                      ·
                        rfl

theorem cell23_4843737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 3, 2].length) (baseStart_4843737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4843737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4843737 prefixEnd_4843737 := by exact prefixLift 4843737
  have htrace : WordTrace (prefixWord ++ tailWord_4843737) baseStart_4843737 baseEnd_4843737 := by
    simpa [prefixWord, tailWord_4843737, baseEnd_4843737] using wordTrace_append hprefix tailTrace_4843737
  have hstable : (prefixWord ++ tailWord_4843737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4843737).length < 2 ^ (prefixWord ++ tailWord_4843737).sum := by decide
  have hdescent : baseEnd_4843737 < baseStart_4843737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4843737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4843754 : List Nat := [3, 1, 3, 1, 1, 2, 1, 5, 1, 3, 2]
def baseStart_4843754 : Nat := 118140960795 + 4843754 * 2 ^ 59
def prefixEnd_4843754 : Nat := 4983230072969 + 3 ^ 40 * 4843754 * 2
def baseEnd_4843754 : Nat := 2487173974138147023898987

theorem tailTrace_4843754 : CollatzResearch.WordTrace tailWord_4843754 prefixEnd_4843754 2487173974138147023898987 := by
  unfold tailWord_4843754
  simp only [CollatzResearch.WordTrace]
  refine ⟨44166555523478495041946579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117777481395942653445190877 44166555523478495041946579)
  ·
    refine ⟨66249833285217742562919869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44166555523478495041946579 66249833285217742562919869)
    ·
      refine ⟨24843687481956653461094951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66249833285217742562919869 24843687481956653461094951)
      ·
        refine ⟨37265531222934980191642427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24843687481956653461094951 37265531222934980191642427)
        ·
          refine ⟨55898296834402470287463641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37265531222934980191642427 55898296834402470287463641)
          ·
            refine ⟨41923722625801852715597731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55898296834402470287463641 41923722625801852715597731)
            ·
              refine ⟨62885583938702779073396597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41923722625801852715597731 62885583938702779073396597)
              ·
                refine ⟨5895523494253385538130931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62885583938702779073396597 5895523494253385538130931)
                ·
                  refine ⟨8843285241380078307196397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5895523494253385538130931 8843285241380078307196397)
                  ·
                    refine ⟨3316231965517529365198649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8843285241380078307196397 3316231965517529365198649)
                    ·
                      refine ⟨2487173974138147023898987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3316231965517529365198649 2487173974138147023898987)
                      ·
                        rfl

theorem cell23_4843754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_4843754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4843754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4843754 prefixEnd_4843754 := by exact prefixLift 4843754
  have htrace : WordTrace (prefixWord ++ tailWord_4843754) baseStart_4843754 baseEnd_4843754 := by
    simpa [prefixWord, tailWord_4843754, baseEnd_4843754] using wordTrace_append hprefix tailTrace_4843754
  have hstable : (prefixWord ++ tailWord_4843754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4843754).length < 2 ^ (prefixWord ++ tailWord_4843754).sum := by decide
  have hdescent : baseEnd_4843754 < baseStart_4843754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4843754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4843778 : List Nat := [3, 4, 1, 1, 2, 1, 4, 1, 2, 1, 3]
def baseStart_4843778 : Nat := 118140960795 + 4843778 * 2 ^ 59
def prefixEnd_4843778 : Nat := 4983230072969 + 3 ^ 40 * 4843778 * 2
def baseEnd_4843778 : Nat := 2487186297673854929998877

theorem tailTrace_4843778 : CollatzResearch.WordTrace tailWord_4843778 prefixEnd_4843778 2487186297673854929998877 := by
  unfold tailWord_4843778
  simp only [CollatzResearch.WordTrace]
  refine ⟨44166774361456758066664997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117778064963884688177773325 44166774361456758066664997)
  ·
    refine ⟨8281270192773142137499687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44166774361456758066664997 8281270192773142137499687)
    ·
      refine ⟨12421905289159713206249531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8281270192773142137499687 12421905289159713206249531)
      ·
        refine ⟨18632857933739569809374297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12421905289159713206249531 18632857933739569809374297)
        ·
          refine ⟨13974643450304677357030723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18632857933739569809374297 13974643450304677357030723)
          ·
            refine ⟨20961965175457016035546085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13974643450304677357030723 20961965175457016035546085)
            ·
              refine ⟨3930368470398190506664891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20961965175457016035546085 3930368470398190506664891)
              ·
                refine ⟨5895552705597285759997337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3930368470398190506664891 5895552705597285759997337)
                ·
                  refine ⟨4421664529197964319998003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5895552705597285759997337 4421664529197964319998003)
                  ·
                    refine ⟨6632496793796946479997005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4421664529197964319998003 6632496793796946479997005)
                    ·
                      refine ⟨2487186297673854929998877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6632496793796946479997005 2487186297673854929998877)
                      ·
                        rfl

theorem cell23_4843778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_4843778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4843778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4843778 prefixEnd_4843778 := by exact prefixLift 4843778
  have htrace : WordTrace (prefixWord ++ tailWord_4843778) baseStart_4843778 baseEnd_4843778 := by
    simpa [prefixWord, tailWord_4843778, baseEnd_4843778] using wordTrace_append hprefix tailTrace_4843778
  have hstable : (prefixWord ++ tailWord_4843778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4843778).length < 2 ^ (prefixWord ++ tailWord_4843778).sum := by decide
  have hdescent : baseEnd_4843778 < baseStart_4843778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4843778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4843790 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 9]
def baseStart_4843790 : Nat := 118140960795 + 4843790 * 2 ^ 59
def prefixEnd_4843790 : Nat := 4983230072969 + 3 ^ 40 * 4843790 * 2
def baseEnd_4843790 : Nat := 276354717715745431449869

theorem tailTrace_4843790 : CollatzResearch.WordTrace tailWord_4843790 prefixEnd_4843790 276354717715745431449869 := by
  unfold tailWord_4843790
  simp only [CollatzResearch.WordTrace]
  refine ⟨22083441890222944789512103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117778356747855705544064549 22083441890222944789512103)
  ·
    refine ⟨33125162835334417184268155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22083441890222944789512103 33125162835334417184268155)
    ·
      refine ⟨49687744253001625776402233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33125162835334417184268155 49687744253001625776402233)
      ·
        refine ⟨37265808189751219332301675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49687744253001625776402233 37265808189751219332301675)
        ·
          refine ⟨55898712284626828998452513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37265808189751219332301675 55898712284626828998452513)
          ·
            refine ⟨41924034213470121748839385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55898712284626828998452513 41924034213470121748839385)
            ·
              refine ⟨31443025660102591311629539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41924034213470121748839385 31443025660102591311629539)
              ·
                refine ⟨47164538490153886967444309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31443025660102591311629539 47164538490153886967444309)
                ·
                  refine ⟨276354717715745431449869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47164538490153886967444309 276354717715745431449869)
                  ·
                    rfl

theorem cell23_4843790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 9].length) (baseStart_4843790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4843790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4843790 prefixEnd_4843790 := by exact prefixLift 4843790
  have htrace : WordTrace (prefixWord ++ tailWord_4843790) baseStart_4843790 baseEnd_4843790 := by
    simpa [prefixWord, tailWord_4843790, baseEnd_4843790] using wordTrace_append hprefix tailTrace_4843790
  have hstable : (prefixWord ++ tailWord_4843790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4843790).length < 2 ^ (prefixWord ++ tailWord_4843790).sum := by decide
  have hdescent : baseEnd_4843790 < baseStart_4843790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4843790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4843827 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 1, 7, 2]
def baseStart_4843827 : Nat := 118140960795 + 4843827 * 2 ^ 59
def prefixEnd_4843827 : Nat := 4983230072969 + 3 ^ 40 * 4843827 * 2
def baseEnd_4843827 : Nat := 2487211458225925238286151

theorem tailTrace_4843827 : CollatzResearch.WordTrace tailWord_4843827 prefixEnd_4843827 2487211458225925238286151 := by
  unfold tailWord_4843827
  simp only [CollatzResearch.WordTrace]
  refine ⟨176668884622649513635193735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117779256415099675756795823 176668884622649513635193735)
  ·
    refine ⟨265003326933974270452790603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176668884622649513635193735 265003326933974270452790603)
    ·
      refine ⟨397504990400961405679185905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265003326933974270452790603 397504990400961405679185905)
      ·
        refine ⟨298128742800721054259389429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 397504990400961405679185905 298128742800721054259389429)
        ·
          refine ⟨27949569637567598836817759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 298128742800721054259389429 27949569637567598836817759)
          ·
            refine ⟨41924354456351398255226639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27949569637567598836817759 41924354456351398255226639)
            ·
              refine ⟨62886531684527097382839959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41924354456351398255226639 62886531684527097382839959)
              ·
                refine ⟨94329797526790646074259939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62886531684527097382839959 94329797526790646074259939)
                ·
                  refine ⟨141494696290185969111389909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94329797526790646074259939 141494696290185969111389909)
                  ·
                    refine ⟨3316281944301233651048201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 141494696290185969111389909 3316281944301233651048201)
                    ·
                      refine ⟨2487211458225925238286151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3316281944301233651048201 2487211458225925238286151)
                      ·
                        rfl

theorem cell23_4843827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 7, 2].length) (baseStart_4843827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4843827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4843827 prefixEnd_4843827 := by exact prefixLift 4843827
  have htrace : WordTrace (prefixWord ++ tailWord_4843827) baseStart_4843827 baseEnd_4843827 := by
    simpa [prefixWord, tailWord_4843827, baseEnd_4843827] using wordTrace_append hprefix tailTrace_4843827
  have hstable : (prefixWord ++ tailWord_4843827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4843827).length < 2 ^ (prefixWord ++ tailWord_4843827).sum := by decide
  have hdescent : baseEnd_4843827 < baseStart_4843827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4843827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4843857 : List Nat := [1, 2, 2, 1, 4, 3, 1, 1, 1, 3, 4]
def baseStart_4843857 : Nat := 118140960795 + 4843857 * 2 ^ 59
def prefixEnd_4843857 : Nat := 4983230072969 + 3 ^ 40 * 4843857 * 2
def baseEnd_4843857 : Nat := 2487226862645560120911013

theorem tailTrace_4843857 : CollatzResearch.WordTrace tailWord_4843857 prefixEnd_4843857 2487226862645560120911013 := by
  unfold tailWord_4843857
  simp only [CollatzResearch.WordTrace]
  refine ⟨176669978812540828758785825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117779985875027219172523883 176669978812540828758785825)
  ·
    refine ⟨132502484109405621569089369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176669978812540828758785825 132502484109405621569089369)
    ·
      refine ⟨99376863082054216176817027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132502484109405621569089369 99376863082054216176817027)
      ·
        refine ⟨149065294623081324265225541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99376863082054216176817027 149065294623081324265225541)
        ·
          refine ⟨27949742741827748299729789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 149065294623081324265225541 27949742741827748299729789)
          ·
            refine ⟨10481153528185405612398671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27949742741827748299729789 10481153528185405612398671)
            ·
              refine ⟨15721730292278108418598007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10481153528185405612398671 15721730292278108418598007)
              ·
                refine ⟨23582595438417162627897011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15721730292278108418598007 23582595438417162627897011)
                ·
                  refine ⟨35373893157625743941845517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23582595438417162627897011 35373893157625743941845517)
                  ·
                    refine ⟨13265209934109653978192069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35373893157625743941845517 13265209934109653978192069)
                    ·
                      refine ⟨2487226862645560120911013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13265209934109653978192069 2487226862645560120911013)
                      ·
                        rfl

theorem cell23_4843857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 3, 4].length) (baseStart_4843857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4843857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4843857 prefixEnd_4843857 := by exact prefixLift 4843857
  have htrace : WordTrace (prefixWord ++ tailWord_4843857) baseStart_4843857 baseEnd_4843857 := by
    simpa [prefixWord, tailWord_4843857, baseEnd_4843857] using wordTrace_append hprefix tailTrace_4843857
  have hstable : (prefixWord ++ tailWord_4843857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4843857).length < 2 ^ (prefixWord ++ tailWord_4843857).sum := by decide
  have hdescent : baseEnd_4843857 < baseStart_4843857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4843857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4843918 : List Nat := [4, 1, 1, 4, 1, 1, 3, 3, 1, 4]
def baseStart_4843918 : Nat := 118140960795 + 4843918 * 2 ^ 59
def prefixEnd_4843918 : Nat := 4983230072969 + 3 ^ 40 * 4843918 * 2
def baseEnd_4843918 : Nat := 829086061655161460749411

theorem tailTrace_4843918 : CollatzResearch.WordTrace tailWord_4843918 prefixEnd_4843918 829086061655161460749411 := by
  unfold tailWord_4843918
  simp only [CollatzResearch.WordTrace]
  refine ⟨22084025458164979522094551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117781469110213224117837605 22084025458164979522094551)
  ·
    refine ⟨33126038187247469283141827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22084025458164979522094551 33126038187247469283141827)
    ·
      refine ⟨49689057280871203924712741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33126038187247469283141827 49689057280871203924712741)
      ·
        refine ⟨9316698240163350735883639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49689057280871203924712741 9316698240163350735883639)
        ·
          refine ⟨13975047360245026103825459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9316698240163350735883639 13975047360245026103825459)
          ·
            refine ⟨20962571040367539155738189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13975047360245026103825459 20962571040367539155738189)
            ·
              refine ⟨7860964140137827183401821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20962571040367539155738189 7860964140137827183401821)
              ·
                refine ⟨2947861552551685193775683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7860964140137827183401821 2947861552551685193775683)
                ·
                  refine ⟨4421792328827527790663525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2947861552551685193775683 4421792328827527790663525)
                  ·
                    refine ⟨829086061655161460749411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4421792328827527790663525 829086061655161460749411)
                    ·
                      rfl

theorem cell23_4843918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 3, 1, 4].length) (baseStart_4843918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4843918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4843918 prefixEnd_4843918 := by exact prefixLift 4843918
  have htrace : WordTrace (prefixWord ++ tailWord_4843918) baseStart_4843918 baseEnd_4843918 := by
    simpa [prefixWord, tailWord_4843918, baseEnd_4843918] using wordTrace_append hprefix tailTrace_4843918
  have hstable : (prefixWord ++ tailWord_4843918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4843918).length < 2 ^ (prefixWord ++ tailWord_4843918).sum := by decide
  have hdescent : baseEnd_4843918 < baseStart_4843918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4843918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4843920 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 7]
def baseStart_4843920 : Nat := 118140960795 + 4843920 * 2 ^ 59
def prefixEnd_4843920 : Nat := 4983230072969 + 3 ^ 40 * 4843920 * 2
def baseEnd_4843920 : Nat := 2487259211926793374423223

theorem tailTrace_4843920 : CollatzResearch.WordTrace tailWord_4843920 prefixEnd_4843920 2487259211926793374423223 := by
  unfold tailWord_4843920
  simp only [CollatzResearch.WordTrace]
  refine ⟨88336138305656295259164607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117781517740875060345552809 88336138305656295259164607)
  ·
    refine ⟨132504207458484442888746911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88336138305656295259164607 132504207458484442888746911)
    ·
      refine ⟨198756311187726664333120367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132504207458484442888746911 198756311187726664333120367)
      ·
        refine ⟨298134466781589996499680551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198756311187726664333120367 298134466781589996499680551)
        ·
          refine ⟨447201700172384994749520827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298134466781589996499680551 447201700172384994749520827)
          ·
            refine ⟨670802550258577492124281241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447201700172384994749520827 670802550258577492124281241)
            ·
              refine ⟨503101912693933119093210931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 670802550258577492124281241 503101912693933119093210931)
              ·
                refine ⟨754652869040899678639816397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 503101912693933119093210931 754652869040899678639816397)
                ·
                  refine ⟨282994825890337379489931149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 754652869040899678639816397 282994825890337379489931149)
                  ·
                    refine ⟨106123059708876517308724181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 282994825890337379489931149 106123059708876517308724181)
                    ·
                      refine ⟨2487259211926793374423223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 106123059708876517308724181 2487259211926793374423223)
                      ·
                        rfl

theorem cell23_4843920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 7].length) (baseStart_4843920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4843920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4843920 prefixEnd_4843920 := by exact prefixLift 4843920
  have htrace : WordTrace (prefixWord ++ tailWord_4843920) baseStart_4843920 baseEnd_4843920 := by
    simpa [prefixWord, tailWord_4843920, baseEnd_4843920] using wordTrace_append hprefix tailTrace_4843920
  have hstable : (prefixWord ++ tailWord_4843920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4843920).length < 2 ^ (prefixWord ++ tailWord_4843920).sum := by decide
  have hdescent : baseEnd_4843920 < baseStart_4843920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4843920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4843961 : List Nat := [1, 2, 1, 4, 3, 3, 1, 2, 1, 5]
def baseStart_4843961 : Nat := 118140960795 + 4843961 * 2 ^ 59
def prefixEnd_4843961 : Nat := 4983230072969 + 3 ^ 40 * 4843961 * 2
def baseEnd_4843961 : Nat := 829093421544542571336845

theorem tailTrace_4843961 : CollatzResearch.WordTrace tailWord_4843961 prefixEnd_4843961 829093421544542571336845 := by
  unfold tailWord_4843961
  simp only [CollatzResearch.WordTrace]
  refine ⟨176673772004164054520571737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117782514669442703013714491 176673772004164054520571737)
  ·
    refine ⟨132505329003123040890428803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176673772004164054520571737 132505329003123040890428803)
    ·
      refine ⟨198757993504684561335643205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132505329003123040890428803 198757993504684561335643205)
      ·
        refine ⟨37267123782128355250433101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 198757993504684561335643205 37267123782128355250433101)
        ·
          refine ⟨13975171418298133218912413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37267123782128355250433101 13975171418298133218912413)
          ·
            refine ⟨5240689281861799957092155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13975171418298133218912413 5240689281861799957092155)
            ·
              refine ⟨7861033922792699935638233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5240689281861799957092155 7861033922792699935638233)
              ·
                refine ⟨5895775442094524951728675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7861033922792699935638233 5895775442094524951728675)
                ·
                  refine ⟨8843663163141787427593013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5895775442094524951728675 8843663163141787427593013)
                  ·
                    refine ⟨829093421544542571336845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8843663163141787427593013 829093421544542571336845)
                    ·
                      rfl

theorem cell23_4843961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 5].length) (baseStart_4843961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4843961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4843961 prefixEnd_4843961 := by exact prefixLift 4843961
  have htrace : WordTrace (prefixWord ++ tailWord_4843961) baseStart_4843961 baseEnd_4843961 := by
    simpa [prefixWord, tailWord_4843961, baseEnd_4843961] using wordTrace_append hprefix tailTrace_4843961
  have hstable : (prefixWord ++ tailWord_4843961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4843961).length < 2 ^ (prefixWord ++ tailWord_4843961).sum := by decide
  have hdescent : baseEnd_4843961 < baseStart_4843961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4843961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4843977 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 3, 2, 4]
def baseStart_4843977 : Nat := 118140960795 + 4843977 * 2 ^ 59
def prefixEnd_4843977 : Nat := 4983230072969 + 3 ^ 40 * 4843977 * 2
def baseEnd_4843977 : Nat := 2487288480324099651410461

theorem tailTrace_4843977 : CollatzResearch.WordTrace tailWord_4843977 prefixEnd_4843977 2487288480324099651410461 := by
  unfold tailWord_4843977
  simp only [CollatzResearch.WordTrace]
  refine ⟨176674355572106089253154185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117782903714737392835436123 176674355572106089253154185)
  ·
    refine ⟨132505766679079566939865639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176674355572106089253154185 132505766679079566939865639)
    ·
      refine ⟨198758650018619350409798459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132505766679079566939865639 198758650018619350409798459)
      ·
        refine ⟨298137975027929025614697689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198758650018619350409798459 298137975027929025614697689)
        ·
          refine ⟨223603481270946769211023267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298137975027929025614697689 223603481270946769211023267)
          ·
            refine ⟨335405221906420153816534901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223603481270946769211023267 335405221906420153816534901)
            ·
              refine ⟨31444239553726889420300147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 335405221906420153816534901 31444239553726889420300147)
              ·
                refine ⟨47166359330590334130450221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31444239553726889420300147 47166359330590334130450221)
                ·
                  refine ⟨17687384748971375298918833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47166359330590334130450221 17687384748971375298918833)
                  ·
                    refine ⟨13265538561728531474189125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17687384748971375298918833 13265538561728531474189125)
                    ·
                      refine ⟨2487288480324099651410461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13265538561728531474189125 2487288480324099651410461)
                      ·
                        rfl

theorem cell23_4843977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 2, 4].length) (baseStart_4843977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4843977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4843977 prefixEnd_4843977 := by exact prefixLift 4843977
  have htrace : WordTrace (prefixWord ++ tailWord_4843977) baseStart_4843977 baseEnd_4843977 := by
    simpa [prefixWord, tailWord_4843977, baseEnd_4843977] using wordTrace_append hprefix tailTrace_4843977
  have hstable : (prefixWord ++ tailWord_4843977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4843977).length < 2 ^ (prefixWord ++ tailWord_4843977).sum := by decide
  have hdescent : baseEnd_4843977 < baseStart_4843977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4843977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844017 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 2, 7]
def baseStart_4844017 : Nat := 118140960795 + 4844017 * 2 ^ 59
def prefixEnd_4844017 : Nat := 4983230072969 + 3 ^ 40 * 4844017 * 2
def baseEnd_4844017 : Nat := 829103006516759831636759

theorem tailTrace_4844017 : CollatzResearch.WordTrace tailWord_4844017 prefixEnd_4844017 829103006516759831636759 := by
  unfold tailWord_4844017
  simp only [CollatzResearch.WordTrace]
  refine ⟨176675814491961176084610305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117783876327974117389740203 176675814491961176084610305)
  ·
    refine ⟨132506860868970882063457729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176675814491961176084610305 132506860868970882063457729)
    ·
      refine ⟨99380145651728161547593297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132506860868970882063457729 99380145651728161547593297)
      ·
        refine ⟨74535109238796121160694973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99380145651728161547593297 74535109238796121160694973)
        ·
          refine ⟨27950665964548545435260615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74535109238796121160694973 27950665964548545435260615)
          ·
            refine ⟨41925998946822818152890923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27950665964548545435260615 41925998946822818152890923)
            ·
              refine ⟨62888998420234227229336385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41925998946822818152890923 62888998420234227229336385)
              ·
                refine ⟨47166748815175670422002289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62888998420234227229336385 47166748815175670422002289)
                ·
                  refine ⟨35375061611381752816501717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47166748815175670422002289 35375061611381752816501717)
                  ·
                    refine ⟨829103006516759831636759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35375061611381752816501717 829103006516759831636759)
                    ·
                      rfl

theorem cell23_4844017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 7].length) (baseStart_4844017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844017 prefixEnd_4844017 := by exact prefixLift 4844017
  have htrace : WordTrace (prefixWord ++ tailWord_4844017) baseStart_4844017 baseEnd_4844017 := by
    simpa [prefixWord, tailWord_4844017, baseEnd_4844017] using wordTrace_append hprefix tailTrace_4844017
  have hstable : (prefixWord ++ tailWord_4844017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844017).length < 2 ^ (prefixWord ++ tailWord_4844017).sum := by decide
  have hdescent : baseEnd_4844017 < baseStart_4844017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844038 : List Nat := [6, 2, 1, 1, 1, 2, 10]
def baseStart_4844038 : Nat := 118140960795 + 4844038 * 2 ^ 59
def prefixEnd_4844038 : Nat := 4983230072969 + 3 ^ 40 * 4844038 * 2
def baseEnd_4844038 : Nat := 30707651884494122379601

theorem tailTrace_4844038 : CollatzResearch.WordTrace tailWord_4844038 prefixEnd_4844038 30707651884494122379601 := by
  unfold tailWord_4844038
  simp only [CollatzResearch.WordTrace]
  refine ⟨5521143138277659270972649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 117784386949923397780749845 5521143138277659270972649)
  ·
    refine ⟨4140857353708244453229487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5521143138277659270972649 4140857353708244453229487)
    ·
      refine ⟨6211286030562366679844231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4140857353708244453229487 6211286030562366679844231)
      ·
        refine ⟨9316929045843550019766347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6211286030562366679844231 9316929045843550019766347)
        ·
          refine ⟨13975393568765325029649521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9316929045843550019766347 13975393568765325029649521)
          ·
            refine ⟨10481545176573993772237141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13975393568765325029649521 10481545176573993772237141)
            ·
              refine ⟨30707651884494122379601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10481545176573993772237141 30707651884494122379601)
              ·
                rfl

theorem cell23_4844038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 10].length) (baseStart_4844038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844038 prefixEnd_4844038 := by exact prefixLift 4844038
  have htrace : WordTrace (prefixWord ++ tailWord_4844038) baseStart_4844038 baseEnd_4844038 := by
    simpa [prefixWord, tailWord_4844038, baseEnd_4844038] using wordTrace_append hprefix tailTrace_4844038
  have hstable : (prefixWord ++ tailWord_4844038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844038).length < 2 ^ (prefixWord ++ tailWord_4844038).sum := by decide
  have hdescent : baseEnd_4844038 < baseStart_4844038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844047 : List Nat := [1, 1, 2, 1, 1, 1, 2, 6, 2, 6]
def baseStart_4844047 : Nat := 118140960795 + 4844047 * 2 ^ 59
def prefixEnd_4844047 : Nat := 4983230072969 + 3 ^ 40 * 4844047 * 2
def baseEnd_4844047 : Nat := 829108141323304792511713

theorem tailTrace_4844047 : CollatzResearch.WordTrace tailWord_4844047 prefixEnd_4844047 829108141323304792511713 := by
  unfold tailWord_4844047
  simp only [CollatzResearch.WordTrace]
  refine ⟨176676908681852491208202395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117784605787901660805468263 176676908681852491208202395)
  ·
    refine ⟨265015363022778736812303593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176676908681852491208202395 265015363022778736812303593)
    ·
      refine ⟨198761522267084052609227695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265015363022778736812303593 198761522267084052609227695)
      ·
        refine ⟨298142283400626078913841543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198761522267084052609227695 298142283400626078913841543)
        ·
          refine ⟨447213425100939118370762315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298142283400626078913841543 447213425100939118370762315)
          ·
            refine ⟨670820137651408677556143473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447213425100939118370762315 670820137651408677556143473)
            ·
              refine ⟨503115103238556508167107605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 670820137651408677556143473 503115103238556508167107605)
              ·
                refine ⟨23583520464307336320333169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 503115103238556508167107605 23583520464307336320333169)
                ·
                  refine ⟨17687640348230502240249877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23583520464307336320333169 17687640348230502240249877)
                  ·
                    refine ⟨829108141323304792511713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17687640348230502240249877 829108141323304792511713)
                    ·
                      rfl

theorem cell23_4844047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 6].length) (baseStart_4844047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844047 prefixEnd_4844047 := by exact prefixLift 4844047
  have htrace : WordTrace (prefixWord ++ tailWord_4844047) baseStart_4844047 baseEnd_4844047 := by
    simpa [prefixWord, tailWord_4844047, baseEnd_4844047] using wordTrace_append hprefix tailTrace_4844047
  have hstable : (prefixWord ++ tailWord_4844047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844047).length < 2 ^ (prefixWord ++ tailWord_4844047).sum := by decide
  have hdescent : baseEnd_4844047 < baseStart_4844047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844057 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 1, 3, 5]
def baseStart_4844057 : Nat := 118140960795 + 4844057 * 2 ^ 59
def prefixEnd_4844057 : Nat := 4983230072969 + 3 ^ 40 * 4844057 * 2
def baseEnd_4844057 : Nat := 2487329558776459338410093

theorem tailTrace_4844057 : CollatzResearch.WordTrace tailWord_4844057 prefixEnd_4844057 2487329558776459338410093 := by
  unfold tailWord_4844057
  simp only [CollatzResearch.WordTrace]
  refine ⟨176677273411816262916066425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117784848941210841944044283 176677273411816262916066425)
  ·
    refine ⟨132507955058862197187049819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176677273411816262916066425 132507955058862197187049819)
    ·
      refine ⟨198761932588293295780574729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132507955058862197187049819 198761932588293295780574729)
      ·
        refine ⟨149071449441219971835431047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198761932588293295780574729 149071449441219971835431047)
        ·
          refine ⟨223607174161829957753146571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149071449441219971835431047 223607174161829957753146571)
          ·
            refine ⟨335410761242744936629719857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223607174161829957753146571 335410761242744936629719857)
            ·
              refine ⟨251558070932058702472289893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335410761242744936629719857 251558070932058702472289893)
              ·
                refine ⟨47167138299761006713554355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 251558070932058702472289893 47167138299761006713554355)
                ·
                  refine ⟨70750707449641510070331533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47167138299761006713554355 70750707449641510070331533)
                  ·
                    refine ⟨26531515293615566276374325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 70750707449641510070331533 26531515293615566276374325)
                    ·
                      refine ⟨2487329558776459338410093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26531515293615566276374325 2487329558776459338410093)
                      ·
                        rfl

theorem cell23_4844057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_4844057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844057 prefixEnd_4844057 := by exact prefixLift 4844057
  have htrace : WordTrace (prefixWord ++ tailWord_4844057) baseStart_4844057 baseEnd_4844057 := by
    simpa [prefixWord, tailWord_4844057, baseEnd_4844057] using wordTrace_append hprefix tailTrace_4844057
  have hstable : (prefixWord ++ tailWord_4844057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844057).length < 2 ^ (prefixWord ++ tailWord_4844057).sum := by decide
  have hdescent : baseEnd_4844057 < baseStart_4844057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844104 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 4, 3, 3]
def baseStart_4844104 : Nat := 118140960795 + 4844104 * 2 ^ 59
def prefixEnd_4844104 : Nat := 4983230072969 + 3 ^ 40 * 4844104 * 2
def baseEnd_4844104 : Nat := 2487353692367220654522377

theorem tailTrace_4844104 : CollatzResearch.WordTrace tailWord_4844104 prefixEnd_4844104 2487353692367220654522377 := by
  unfold tailWord_4844104
  simp only [CollatzResearch.WordTrace]
  refine ⟨88339493821322994971513683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117785991761763993295351577 88339493821322994971513683)
  ·
    refine ⟨132509240731984492457270525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88339493821322994971513683 132509240731984492457270525)
    ·
      refine ⟨49690965274494184671476447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132509240731984492457270525 49690965274494184671476447)
      ·
        refine ⟨74536447911741277007214671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49690965274494184671476447 74536447911741277007214671)
        ·
          refine ⟨111804671867611915510822007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74536447911741277007214671 111804671867611915510822007)
          ·
            refine ⟨167707007801417873266233011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111804671867611915510822007 167707007801417873266233011)
            ·
              refine ⟨251560511702126809899349517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167707007801417873266233011 251560511702126809899349517)
              ·
                refine ⟨94335191888297553712256069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 251560511702126809899349517 94335191888297553712256069)
                ·
                  refine ⟨17687848479055791321048013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94335191888297553712256069 17687848479055791321048013)
                  ·
                    refine ⟨6632943179645921745393005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17687848479055791321048013 6632943179645921745393005)
                    ·
                      refine ⟨2487353692367220654522377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6632943179645921745393005 2487353692367220654522377)
                      ·
                        rfl

theorem cell23_4844104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_4844104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844104 prefixEnd_4844104 := by exact prefixLift 4844104
  have htrace : WordTrace (prefixWord ++ tailWord_4844104) baseStart_4844104 baseEnd_4844104 := by
    simpa [prefixWord, tailWord_4844104, baseEnd_4844104] using wordTrace_append hprefix tailTrace_4844104
  have hstable : (prefixWord ++ tailWord_4844104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844104).length < 2 ^ (prefixWord ++ tailWord_4844104).sum := by decide
  have hdescent : baseEnd_4844104 < baseStart_4844104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844126 : List Nat := [4, 4, 1, 2, 1, 2, 1, 2, 1, 3, 2]
def baseStart_4844126 : Nat := 118140960795 + 4844126 * 2 ^ 59
def prefixEnd_4844126 : Nat := 4983230072969 + 3 ^ 40 * 4844126 * 2
def baseEnd_4844126 : Nat := 2487364988941619568447277

theorem tailTrace_4844126 : CollatzResearch.WordTrace tailWord_4844126 prefixEnd_4844126 2487364988941619568447277 := by
  unfold tailWord_4844126
  simp only [CollatzResearch.WordTrace]
  refine ⟨22084973756070785962541029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117786526699044191800218821 22084973756070785962541029)
  ·
    refine ⟨4140932579263272367976443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22084973756070785962541029 4140932579263272367976443)
    ·
      refine ⟨6211398868894908551964665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4140932579263272367976443 6211398868894908551964665)
      ·
        refine ⟨4658549151671181413973499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6211398868894908551964665 4658549151671181413973499)
        ·
          refine ⟨6987823727506772120960249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4658549151671181413973499 6987823727506772120960249)
          ·
            refine ⟨5240867795630079090720187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6987823727506772120960249 5240867795630079090720187)
            ·
              refine ⟨7861301693445118636080281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5240867795630079090720187 7861301693445118636080281)
              ·
                refine ⟨5895976270083838977060211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7861301693445118636080281 5895976270083838977060211)
                ·
                  refine ⟨8843964405125758465590317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5895976270083838977060211 8843964405125758465590317)
                  ·
                    refine ⟨3316486651922159424596369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8843964405125758465590317 3316486651922159424596369)
                    ·
                      refine ⟨2487364988941619568447277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3316486651922159424596369 2487364988941619568447277)
                      ·
                        rfl

theorem cell23_4844126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_4844126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844126 prefixEnd_4844126 := by exact prefixLift 4844126
  have htrace : WordTrace (prefixWord ++ tailWord_4844126) baseStart_4844126 baseEnd_4844126 := by
    simpa [prefixWord, tailWord_4844126, baseEnd_4844126] using wordTrace_append hprefix tailTrace_4844126
  have hstable : (prefixWord ++ tailWord_4844126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844126).length < 2 ^ (prefixWord ++ tailWord_4844126).sum := by decide
  have hdescent : baseEnd_4844126 < baseStart_4844126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844141 : List Nat := [1, 5, 1, 1, 3, 1, 1, 3, 2, 5]
def baseStart_4844141 : Nat := 118140960795 + 4844141 * 2 ^ 59
def prefixEnd_4844141 : Nat := 4983230072969 + 3 ^ 40 * 4844141 * 2
def baseEnd_4844141 : Nat := 829124230383812336586569

theorem tailTrace_4844141 : CollatzResearch.WordTrace tailWord_4844141 prefixEnd_4844141 829124230383812336586569 := by
  unfold tailWord_4844141
  simp only [CollatzResearch.WordTrace]
  refine ⟨176680337143511945262124277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117786891429007963508082851 176680337143511945262124277)
  ·
    refine ⟨16563781607204244868324151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 176680337143511945262124277 16563781607204244868324151)
    ·
      refine ⟨24845672410806367302486227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16563781607204244868324151 24845672410806367302486227)
      ·
        refine ⟨37268508616209550953729341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24845672410806367302486227 37268508616209550953729341)
        ·
          refine ⟨13975690731078581607648503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37268508616209550953729341 13975690731078581607648503)
          ·
            refine ⟨20963536096617872411472755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13975690731078581607648503 20963536096617872411472755)
            ·
              refine ⟨31445304144926808617209133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20963536096617872411472755 31445304144926808617209133)
              ·
                refine ⟨11791989054347553231453425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31445304144926808617209133 11791989054347553231453425)
                ·
                  refine ⟨8843991790760664923590069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11791989054347553231453425 8843991790760664923590069)
                  ·
                    refine ⟨829124230383812336586569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8843991790760664923590069 829124230383812336586569)
                    ·
                      rfl

theorem cell23_4844141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_4844141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844141 prefixEnd_4844141 := by exact prefixLift 4844141
  have htrace : WordTrace (prefixWord ++ tailWord_4844141) baseStart_4844141 baseEnd_4844141 := by
    simpa [prefixWord, tailWord_4844141, baseEnd_4844141] using wordTrace_append hprefix tailTrace_4844141
  have hstable : (prefixWord ++ tailWord_4844141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844141).length < 2 ^ (prefixWord ++ tailWord_4844141).sum := by decide
  have hdescent : baseEnd_4844141 < baseStart_4844141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844161 : List Nat := [1, 2, 4, 2, 1, 1, 1, 4, 2, 1, 4]
def baseStart_4844161 : Nat := 118140960795 + 4844161 * 2 ^ 59
def prefixEnd_4844161 : Nat := 4983230072969 + 3 ^ 40 * 4844161 * 2
def baseEnd_4844161 : Nat := 2487382960764526931509615

theorem tailTrace_4844161 : CollatzResearch.WordTrace tailWord_4844161 prefixEnd_4844161 2487382960764526931509615 := by
  unfold tailWord_4844161
  simp only [CollatzResearch.WordTrace]
  refine ⟨176681066603439488677852337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117787377735626325785234891 176681066603439488677852337)
  ·
    refine ⟨132510799952579616508389253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176681066603439488677852337 132510799952579616508389253)
    ·
      refine ⟨24845774991108678095322985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132510799952579616508389253 24845774991108678095322985)
      ·
        refine ⟨18634331243331508571492239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24845774991108678095322985 18634331243331508571492239)
        ·
          refine ⟨27951496864997262857238359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18634331243331508571492239 27951496864997262857238359)
          ·
            refine ⟨41927245297495894285857539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27951496864997262857238359 41927245297495894285857539)
            ·
              refine ⟨62890867946243841428786309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41927245297495894285857539 62890867946243841428786309)
              ·
                refine ⟨11792037739920720267897433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62890867946243841428786309 11792037739920720267897433)
                ·
                  refine ⟨8844028304940540200923075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11792037739920720267897433 8844028304940540200923075)
                  ·
                    refine ⟨13266042457410810301384613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8844028304940540200923075 13266042457410810301384613)
                    ·
                      refine ⟨2487382960764526931509615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13266042457410810301384613 2487382960764526931509615)
                      ·
                        rfl

theorem cell23_4844161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_4844161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844161 prefixEnd_4844161 := by exact prefixLift 4844161
  have htrace : WordTrace (prefixWord ++ tailWord_4844161) baseStart_4844161 baseEnd_4844161 := by
    simpa [prefixWord, tailWord_4844161, baseEnd_4844161] using wordTrace_append hprefix tailTrace_4844161
  have hstable : (prefixWord ++ tailWord_4844161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844161).length < 2 ^ (prefixWord ++ tailWord_4844161).sum := by decide
  have hdescent : baseEnd_4844161 < baseStart_4844161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844178 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 1, 6, 2]
def baseStart_4844178 : Nat := 118140960795 + 4844178 * 2 ^ 59
def prefixEnd_4844178 : Nat := 4983230072969 + 3 ^ 40 * 4844178 * 2
def baseEnd_4844178 : Nat := 2487391689935653364997037

theorem tailTrace_4844178 : CollatzResearch.WordTrace tailWord_4844178 prefixEnd_4844178 2487391689935653364997037 := by
  unfold tailWord_4844178
  simp only [CollatzResearch.WordTrace]
  refine ⟨44170421661094475145305297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117787791096251933720814125 44170421661094475145305297)
  ·
    refine ⟨33127816245820856358978973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44170421661094475145305297 33127816245820856358978973)
    ·
      refine ⟨12422931092182821134617115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33127816245820856358978973 12422931092182821134617115)
      ·
        refine ⟨18634396638274231701925673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12422931092182821134617115 18634396638274231701925673)
        ·
          refine ⟨13975797478705673776444255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18634396638274231701925673 13975797478705673776444255)
          ·
            refine ⟨20963696218058510664666383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13975797478705673776444255 20963696218058510664666383)
            ·
              refine ⟨31445544327087765996999575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20963696218058510664666383 31445544327087765996999575)
              ·
                refine ⟨47168316490631648995499363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31445544327087765996999575 47168316490631648995499363)
                ·
                  refine ⟨70752474735947473493249045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47168316490631648995499363 70752474735947473493249045)
                  ·
                    refine ⟨3316522253247537819996049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70752474735947473493249045 3316522253247537819996049)
                    ·
                      refine ⟨2487391689935653364997037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3316522253247537819996049 2487391689935653364997037)
                      ·
                        rfl

theorem cell23_4844178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_4844178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844178 prefixEnd_4844178 := by exact prefixLift 4844178
  have htrace : WordTrace (prefixWord ++ tailWord_4844178) baseStart_4844178 baseEnd_4844178 := by
    simpa [prefixWord, tailWord_4844178, baseEnd_4844178] using wordTrace_append hprefix tailTrace_4844178
  have hstable : (prefixWord ++ tailWord_4844178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844178).length < 2 ^ (prefixWord ++ tailWord_4844178).sum := by decide
  have hdescent : baseEnd_4844178 < baseStart_4844178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844188 : List Nat := [2, 2, 3, 2, 2, 2, 1, 2, 3, 4]
def baseStart_4844188 : Nat := 118140960795 + 4844188 * 2 ^ 59
def prefixEnd_4844188 : Nat := 4983230072969 + 3 ^ 40 * 4844188 * 2
def baseEnd_4844188 : Nat := 829132274914066108623997

theorem tailTrace_4844188 : CollatzResearch.WordTrace tailWord_4844188 prefixEnd_4844188 829132274914066108623997 := by
  unfold tailWord_4844188
  simp only [CollatzResearch.WordTrace]
  refine ⟨88341025687170836144542609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117788034249561114859390145 88341025687170836144542609)
  ·
    refine ⟨66255769265378127108406957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88341025687170836144542609 66255769265378127108406957)
    ·
      refine ⟨24845913474516797665652609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66255769265378127108406957 24845913474516797665652609)
      ·
        refine ⟨18634435105887598249239457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24845913474516797665652609 18634435105887598249239457)
        ·
          refine ⟨13975826329415698686929593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18634435105887598249239457 13975826329415698686929593)
          ·
            refine ⟨10481869747061774015197195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13975826329415698686929593 10481869747061774015197195)
            ·
              refine ⟨15722804620592661022795793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10481869747061774015197195 15722804620592661022795793)
              ·
                refine ⟨11792103465444495767096845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15722804620592661022795793 11792103465444495767096845)
                ·
                  refine ⟨4422038799541685912661317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11792103465444495767096845 4422038799541685912661317)
                  ·
                    refine ⟨829132274914066108623997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4422038799541685912661317 829132274914066108623997)
                    ·
                      rfl

theorem cell23_4844188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_4844188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844188 prefixEnd_4844188 := by exact prefixLift 4844188
  have htrace : WordTrace (prefixWord ++ tailWord_4844188) baseStart_4844188 baseEnd_4844188 := by
    simpa [prefixWord, tailWord_4844188, baseEnd_4844188] using wordTrace_append hprefix tailTrace_4844188
  have hstable : (prefixWord ++ tailWord_4844188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844188).length < 2 ^ (prefixWord ++ tailWord_4844188).sum := by decide
  have hdescent : baseEnd_4844188 < baseStart_4844188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844205 : List Nat := [1, 5, 2, 1, 1, 2, 1, 5, 1, 4]
def baseStart_4844205 : Nat := 118140960795 + 4844205 * 2 ^ 59
def prefixEnd_4844205 : Nat := 4983230072969 + 3 ^ 40 * 4844205 * 2
def baseEnd_4844205 : Nat := 829135184637774919786471

theorem tailTrace_4844205 : CollatzResearch.WordTrace tailWord_4844205 prefixEnd_4844205 829135184637774919786471 := by
  unfold tailWord_4844205
  simp only [CollatzResearch.WordTrace]
  refine ⟨176682671415280084192454069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117788447610186722794969379 176682671415280084192454069)
  ·
    refine ⟨16564000445182507893042569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 176682671415280084192454069 16564000445182507893042569)
    ·
      refine ⟨12423000333886880919781927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16564000445182507893042569 12423000333886880919781927)
      ·
        refine ⟨18634500500830321379672891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12423000333886880919781927 18634500500830321379672891)
        ·
          refine ⟨27951750751245482069509337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18634500500830321379672891 27951750751245482069509337)
          ·
            refine ⟨20963813063434111552132003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27951750751245482069509337 20963813063434111552132003)
            ·
              refine ⟨31445719595151167328198005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20963813063434111552132003 31445719595151167328198005)
              ·
                refine ⟨2948036212045421937018563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31445719595151167328198005 2948036212045421937018563)
                ·
                  refine ⟨4422054318068132905527845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2948036212045421937018563 4422054318068132905527845)
                  ·
                    refine ⟨829135184637774919786471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4422054318068132905527845 829135184637774919786471)
                    ·
                      rfl

theorem cell23_4844205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_4844205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844205 prefixEnd_4844205 := by exact prefixLift 4844205
  have htrace : WordTrace (prefixWord ++ tailWord_4844205) baseStart_4844205 baseEnd_4844205 := by
    simpa [prefixWord, tailWord_4844205, baseEnd_4844205] using wordTrace_append hprefix tailTrace_4844205
  have hstable : (prefixWord ++ tailWord_4844205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844205).length < 2 ^ (prefixWord ++ tailWord_4844205).sum := by decide
  have hdescent : baseEnd_4844205 < baseStart_4844205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844238 : List Nat := [4, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2]
def baseStart_4844238 : Nat := 118140960795 + 4844238 * 2 ^ 59
def prefixEnd_4844238 : Nat := 4983230072969 + 3 ^ 40 * 4844238 * 2
def baseEnd_4844238 : Nat := 2487422498774923130246761

theorem tailTrace_4844238 : CollatzResearch.WordTrace tailWord_4844238 prefixEnd_4844238 2487422498774923130246761 := by
  unfold tailWord_4844238
  simp only [CollatzResearch.WordTrace]
  refine ⟨22085484378020066353550671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117789250016107020552270245 22085484378020066353550671)
  ·
    refine ⟨33128226567030099530326007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22085484378020066353550671 33128226567030099530326007)
    ·
      refine ⟨49692339850545149295489011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33128226567030099530326007 49692339850545149295489011)
      ·
        refine ⟨74538509775817723943233517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49692339850545149295489011 74538509775817723943233517)
        ·
          refine ⟨27951941165931646478712569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74538509775817723943233517 27951941165931646478712569)
          ·
            refine ⟨20963955874448734859034427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27951941165931646478712569 20963955874448734859034427)
            ·
              refine ⟨31445933811673102288551641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20963955874448734859034427 31445933811673102288551641)
              ·
                refine ⟨23584450358754826716413731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31445933811673102288551641 23584450358754826716413731)
                ·
                  refine ⟨35376675538132240074620597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23584450358754826716413731 35376675538132240074620597)
                  ·
                    refine ⟨3316563331699897506995681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35376675538132240074620597 3316563331699897506995681)
                    ·
                      refine ⟨2487422498774923130246761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3316563331699897506995681 2487422498774923130246761)
                      ·
                        rfl

theorem cell23_4844238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2].length) (baseStart_4844238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844238 prefixEnd_4844238 := by exact prefixLift 4844238
  have htrace : WordTrace (prefixWord ++ tailWord_4844238) baseStart_4844238 baseEnd_4844238 := by
    simpa [prefixWord, tailWord_4844238, baseEnd_4844238] using wordTrace_append hprefix tailTrace_4844238
  have hstable : (prefixWord ++ tailWord_4844238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844238).length < 2 ^ (prefixWord ++ tailWord_4844238).sum := by decide
  have hdescent : baseEnd_4844238 < baseStart_4844238 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844248 : List Nat := [2, 1, 2, 2, 3, 3, 2, 2, 1, 5]
def baseStart_4844248 : Nat := 118140960795 + 4844248 * 2 ^ 59
def prefixEnd_4844248 : Nat := 4983230072969 + 3 ^ 40 * 4844248 * 2
def baseEnd_4844248 : Nat := 829142544527156030373905

theorem tailTrace_4844248 : CollatzResearch.WordTrace tailWord_4844248 prefixEnd_4844248 829142544527156030373905 := by
  unfold tailWord_4844248
  simp only [CollatzResearch.WordTrace]
  refine ⟨88342119877062151268134699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117789493169416201690846265 88342119877062151268134699)
  ·
    refine ⟨132513179815593226902202049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88342119877062151268134699 132513179815593226902202049)
    ·
      refine ⟨99384884861694920176651537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132513179815593226902202049 99384884861694920176651537)
      ·
        refine ⟨74538663646271190132488653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99384884861694920176651537 74538663646271190132488653)
        ·
          refine ⟨27951998867351696299683245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74538663646271190132488653 27951998867351696299683245)
          ·
            refine ⟨10481999575256886112381217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27951998867351696299683245 10481999575256886112381217)
            ·
              refine ⟨7861499681442664584285913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10481999575256886112381217 7861499681442664584285913)
              ·
                refine ⟨5896124761081998438214435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7861499681442664584285913 5896124761081998438214435)
                ·
                  refine ⟨8844187141622997657321653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5896124761081998438214435 8844187141622997657321653)
                  ·
                    refine ⟨829142544527156030373905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8844187141622997657321653 829142544527156030373905)
                    ·
                      rfl

theorem cell23_4844248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 2, 1, 5].length) (baseStart_4844248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844248 prefixEnd_4844248 := by exact prefixLift 4844248
  have htrace : WordTrace (prefixWord ++ tailWord_4844248) baseStart_4844248 baseEnd_4844248 := by
    simpa [prefixWord, tailWord_4844248, baseEnd_4844248] using wordTrace_append hprefix tailTrace_4844248
  have hstable : (prefixWord ++ tailWord_4844248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844248).length < 2 ^ (prefixWord ++ tailWord_4844248).sum := by decide
  have hdescent : baseEnd_4844248 < baseStart_4844248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844271 : List Nat := [1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 5]
def baseStart_4844271 : Nat := 118140960795 + 4844271 * 2 ^ 59
def prefixEnd_4844271 : Nat := 4983230072969 + 3 ^ 40 * 4844271 * 2
def baseEnd_4844271 : Nat := 2487439443636521501134109

theorem tailTrace_4844271 : CollatzResearch.WordTrace tailWord_4844271 prefixEnd_4844271 2487439443636521501134109 := by
  unfold tailWord_4844271
  simp only [CollatzResearch.WordTrace]
  refine ⟨176685078633040977464356667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117790052422027318309571111 176685078633040977464356667)
  ·
    refine ⟨265027617949561466196535001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176685078633040977464356667 265027617949561466196535001)
    ·
      refine ⟨198770713462171099647401251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265027617949561466196535001 198770713462171099647401251)
      ·
        refine ⟨298156070193256649471101877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198770713462171099647401251 298156070193256649471101877)
        ·
          refine ⟨27952131580617810887915801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 298156070193256649471101877 27952131580617810887915801)
          ·
            refine ⟨20964098685463358165936851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27952131580617810887915801 20964098685463358165936851)
            ·
              refine ⟨31446148028195037248905277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20964098685463358165936851 31446148028195037248905277)
              ·
                refine ⟨11792305510573138968339479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31446148028195037248905277 11792305510573138968339479)
                ·
                  refine ⟨17688458265859708452509219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11792305510573138968339479 17688458265859708452509219)
                  ·
                    refine ⟨26532687398789562678763829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17688458265859708452509219 26532687398789562678763829)
                    ·
                      refine ⟨2487439443636521501134109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26532687398789562678763829 2487439443636521501134109)
                      ·
                        rfl

theorem cell23_4844271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 5].length) (baseStart_4844271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844271 prefixEnd_4844271 := by exact prefixLift 4844271
  have htrace : WordTrace (prefixWord ++ tailWord_4844271) baseStart_4844271 baseEnd_4844271 := by
    simpa [prefixWord, tailWord_4844271, baseEnd_4844271] using wordTrace_append hprefix tailTrace_4844271
  have hstable : (prefixWord ++ tailWord_4844271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844271).length < 2 ^ (prefixWord ++ tailWord_4844271).sum := by decide
  have hdescent : baseEnd_4844271 < baseStart_4844271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844278 : List Nat := [5, 1, 1, 1, 1, 2, 1, 3, 4, 4]
def baseStart_4844278 : Nat := 118140960795 + 4844278 * 2 ^ 59
def prefixEnd_4844278 : Nat := 4983230072969 + 3 ^ 40 * 4844278 * 2
def baseEnd_4844278 : Nat := 829147679333700991248859

theorem tailTrace_4844278 : CollatzResearch.WordTrace tailWord_4844278 prefixEnd_4844278 829147679333700991248859 := by
  unfold tailWord_4844278
  simp only [CollatzResearch.WordTrace]
  refine ⟨11042833371500976103741343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117790222629343745106574325 11042833371500976103741343)
  ·
    refine ⟨16564250057251464155612015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11042833371500976103741343 16564250057251464155612015)
    ·
      refine ⟨24846375085877196233418023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16564250057251464155612015 24846375085877196233418023)
      ·
        refine ⟨37269562628815794350127035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24846375085877196233418023 37269562628815794350127035)
        ·
          refine ⟨55904343943223691525190553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37269562628815794350127035 55904343943223691525190553)
          ·
            refine ⟨41928257957417768643892915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55904343943223691525190553 41928257957417768643892915)
            ·
              refine ⟨62892386936126652965839373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41928257957417768643892915 62892386936126652965839373)
              ·
                refine ⟨23584645101047494862189765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62892386936126652965839373 23584645101047494862189765)
                ·
                  refine ⟨4422120956446405286660581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23584645101047494862189765 4422120956446405286660581)
                  ·
                    refine ⟨829147679333700991248859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4422120956446405286660581 829147679333700991248859)
                    ·
                      rfl

theorem cell23_4844278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_4844278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844278 prefixEnd_4844278 := by exact prefixLift 4844278
  have htrace : WordTrace (prefixWord ++ tailWord_4844278) baseStart_4844278 baseEnd_4844278 := by
    simpa [prefixWord, tailWord_4844278, baseEnd_4844278] using wordTrace_append hprefix tailTrace_4844278
  have hstable : (prefixWord ++ tailWord_4844278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844278).length < 2 ^ (prefixWord ++ tailWord_4844278).sum := by decide
  have hdescent : baseEnd_4844278 < baseStart_4844278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844295 : List Nat := [1, 1, 4, 4, 1, 2, 1, 3, 2, 4]
def baseStart_4844295 : Nat := 118140960795 + 4844295 * 2 ^ 59
def prefixEnd_4844295 : Nat := 4983230072969 + 3 ^ 40 * 4844295 * 2
def baseEnd_4844295 : Nat := 829150589057409802411333

theorem tailTrace_4844295 : CollatzResearch.WordTrace tailWord_4844295 prefixEnd_4844295 829150589057409802411333 := by
  unfold tailWord_4844295
  simp only [CollatzResearch.WordTrace]
  refine ⟨176685953984954029563230339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117790635989969353042153559 176685953984954029563230339)
  ·
    refine ⟨265028930977431044344845509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176685953984954029563230339 265028930977431044344845509)
    ·
      refine ⟨49692924558268320814658533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 265028930977431044344845509 49692924558268320814658533)
      ·
        refine ⟨9317423354675310152748475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49692924558268320814658533 9317423354675310152748475)
        ·
          refine ⟨13976135032012965229122713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9317423354675310152748475 13976135032012965229122713)
          ·
            refine ⟨10482101274009723921842035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13976135032012965229122713 10482101274009723921842035)
            ·
              refine ⟨15723151911014585882763053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10482101274009723921842035 15723151911014585882763053)
              ·
                refine ⟨5896181966630469706036145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15723151911014585882763053 5896181966630469706036145)
                ·
                  refine ⟨4422136474972852279527109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5896181966630469706036145 4422136474972852279527109)
                  ·
                    refine ⟨829150589057409802411333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4422136474972852279527109 829150589057409802411333)
                    ·
                      rfl

theorem cell23_4844295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_4844295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844295 prefixEnd_4844295 := by exact prefixLift 4844295
  have htrace : WordTrace (prefixWord ++ tailWord_4844295) baseStart_4844295 baseEnd_4844295 := by
    simpa [prefixWord, tailWord_4844295, baseEnd_4844295] using wordTrace_append hprefix tailTrace_4844295
  have hstable : (prefixWord ++ tailWord_4844295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844295).length < 2 ^ (prefixWord ++ tailWord_4844295).sum := by decide
  have hdescent : baseEnd_4844295 < baseStart_4844295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844322 : List Nat := [3, 3, 1, 1, 2, 3, 3, 1, 1, 2, 3]
def baseStart_4844322 : Nat := 118140960795 + 4844322 * 2 ^ 59
def prefixEnd_4844322 : Nat := 4983230072969 + 3 ^ 40 * 4844322 * 2
def baseEnd_4844322 : Nat := 2487465631149900801596375

theorem tailTrace_4844322 : CollatzResearch.WordTrace tailWord_4844322 prefixEnd_4844322 2487465631149900801596375 := by
  unfold tailWord_4844322
  simp only [CollatzResearch.WordTrace]
  refine ⟨44171734688964053293615805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117791292503904142116308813 44171734688964053293615805)
  ·
    refine ⟨16564400508361519985105927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44171734688964053293615805 16564400508361519985105927)
    ·
      refine ⟨24846600762542279977658891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16564400508361519985105927 24846600762542279977658891)
      ·
        refine ⟨37269901143813419966488337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24846600762542279977658891 37269901143813419966488337)
        ·
          refine ⟨27952425857860064974866253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37269901143813419966488337 27952425857860064974866253)
          ·
            refine ⟨10482159696697524365574845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27952425857860064974866253 10482159696697524365574845)
            ·
              refine ⟨3930809886261571637090567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10482159696697524365574845 3930809886261571637090567)
              ·
                refine ⟨5896214829392357455635851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3930809886261571637090567 5896214829392357455635851)
                ·
                  refine ⟨8844322244088536183453777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5896214829392357455635851 8844322244088536183453777)
                  ·
                    refine ⟨6633241683066402137590333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8844322244088536183453777 6633241683066402137590333)
                    ·
                      refine ⟨2487465631149900801596375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6633241683066402137590333 2487465631149900801596375)
                      ·
                        rfl

theorem cell23_4844322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_4844322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844322 prefixEnd_4844322 := by exact prefixLift 4844322
  have htrace : WordTrace (prefixWord ++ tailWord_4844322) baseStart_4844322 baseEnd_4844322 := by
    simpa [prefixWord, tailWord_4844322, baseEnd_4844322] using wordTrace_append hprefix tailTrace_4844322
  have hstable : (prefixWord ++ tailWord_4844322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844322).length < 2 ^ (prefixWord ++ tailWord_4844322).sum := by decide
  have hdescent : baseEnd_4844322 < baseStart_4844322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844342 : List Nat := [5, 1, 2, 2, 3, 1, 1, 8]
def baseStart_4844342 : Nat := 118140960795 + 4844342 * 2 ^ 59
def prefixEnd_4844342 : Nat := 4983230072969 + 3 ^ 40 * 4844342 * 2
def baseEnd_4844342 : Nat := 92128737065295952716529

theorem tailTrace_4844342 : CollatzResearch.WordTrace tailWord_4844342 prefixEnd_4844342 92128737065295952716529 := by
  unfold tailWord_4844342
  simp only [CollatzResearch.WordTrace]
  refine ⟨11042979263486484786886955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 117791778810522504393460853 11042979263486484786886955)
  ·
    refine ⟨16564468895229727180330433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11042979263486484786886955 16564468895229727180330433)
    ·
      refine ⟨12423351671422295385247825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16564468895229727180330433 12423351671422295385247825)
      ·
        refine ⟨9317513753566721538935869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12423351671422295385247825 9317513753566721538935869)
        ·
          refine ⟨3494067657587520577100951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9317513753566721538935869 3494067657587520577100951)
          ·
            refine ⟨5241101486381280865651427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3494067657587520577100951 5241101486381280865651427)
            ·
              refine ⟨7861652229571921298477141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5241101486381280865651427 7861652229571921298477141)
              ·
                refine ⟨92128737065295952716529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7861652229571921298477141 92128737065295952716529)
                ·
                  rfl

theorem cell23_4844342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 8].length) (baseStart_4844342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844342 prefixEnd_4844342 := by exact prefixLift 4844342
  have htrace : WordTrace (prefixWord ++ tailWord_4844342) baseStart_4844342 baseEnd_4844342 := by
    simpa [prefixWord, tailWord_4844342, baseEnd_4844342] using wordTrace_append hprefix tailTrace_4844342
  have hstable : (prefixWord ++ tailWord_4844342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844342).length < 2 ^ (prefixWord ++ tailWord_4844342).sum := by decide
  have hdescent : baseEnd_4844342 < baseStart_4844342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844351 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 1, 8]
def baseStart_4844351 : Nat := 118140960795 + 4844351 * 2 ^ 59
def prefixEnd_4844351 : Nat := 4983230072969 + 3 ^ 40 * 4844351 * 2
def baseEnd_4844351 : Nat := 829160174029627062711247

theorem tailTrace_4844351 : CollatzResearch.WordTrace tailWord_4844351 prefixEnd_4844351 829160174029627062711247 := by
  unfold tailWord_4844351
  simp only [CollatzResearch.WordTrace]
  refine ⟨176687996472751151127268907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117791997648500767418179271 176687996472751151127268907)
  ·
    refine ⟨265031994709126726690903361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176687996472751151127268907 265031994709126726690903361)
    ·
      refine ⟨198773996031845045018177521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265031994709126726690903361 198773996031845045018177521)
      ·
        refine ⟨149080497023883783763633141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198773996031845045018177521 149080497023883783763633141)
        ·
          refine ⟨13976296595989104727840607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 149080497023883783763633141 13976296595989104727840607)
          ·
            refine ⟨20964444893983657091760911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13976296595989104727840607 20964444893983657091760911)
            ·
              refine ⟨31446667340975485637641367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20964444893983657091760911 31446667340975485637641367)
              ·
                refine ⟨47170001011463228456462051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31446667340975485637641367 47170001011463228456462051)
                ·
                  refine ⟨70755001517194842684693077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47170001011463228456462051 70755001517194842684693077)
                  ·
                    refine ⟨829160174029627062711247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70755001517194842684693077 829160174029627062711247)
                    ·
                      rfl

theorem cell23_4844351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 8].length) (baseStart_4844351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844351 prefixEnd_4844351 := by exact prefixLift 4844351
  have htrace : WordTrace (prefixWord ++ tailWord_4844351) baseStart_4844351 baseEnd_4844351 := by
    simpa [prefixWord, tailWord_4844351, baseEnd_4844351] using wordTrace_append hprefix tailTrace_4844351
  have hstable : (prefixWord ++ tailWord_4844351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844351).length < 2 ^ (prefixWord ++ tailWord_4844351).sum := by decide
  have hdescent : baseEnd_4844351 < baseStart_4844351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844375 : List Nat := [1, 1, 3, 2, 4, 1, 2, 2, 1, 4, 2]
def baseStart_4844375 : Nat := 118140960795 + 4844375 * 2 ^ 59
def prefixEnd_4844375 : Nat := 4983230072969 + 3 ^ 40 * 4844375 * 2
def baseEnd_4844375 : Nat := 2487492845624589094233631

theorem tailTrace_4844375 : CollatzResearch.WordTrace tailWord_4844375 prefixEnd_4844375 2487492845624589094233631 := by
  unfold tailWord_4844375
  simp only [CollatzResearch.WordTrace]
  refine ⟨176688871824664203226142579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117792581216442802150761719 176688871824664203226142579)
  ·
    refine ⟨265033307736996304839213869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176688871824664203226142579 265033307736996304839213869)
    ·
      refine ⟨99387490401373614314705201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 265033307736996304839213869 99387490401373614314705201)
      ·
        refine ⟨74540617801030210736028901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99387490401373614314705201 74540617801030210736028901)
        ·
          refine ⟨13976365837693164513005419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74540617801030210736028901 13976365837693164513005419)
          ·
            refine ⟨20964548756539746769508129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13976365837693164513005419 20964548756539746769508129)
            ·
              refine ⟨15723411567404810077131097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20964548756539746769508129 15723411567404810077131097)
              ·
                refine ⟨11792558675553607557848323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15723411567404810077131097 11792558675553607557848323)
                ·
                  refine ⟨17688838013330411336772485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11792558675553607557848323 17688838013330411336772485)
                  ·
                    refine ⟨3316657127499452125644841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17688838013330411336772485 3316657127499452125644841)
                    ·
                      refine ⟨2487492845624589094233631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3316657127499452125644841 2487492845624589094233631)
                      ·
                        rfl

theorem cell23_4844375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 4, 2].length) (baseStart_4844375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844375 prefixEnd_4844375 := by exact prefixLift 4844375
  have htrace : WordTrace (prefixWord ++ tailWord_4844375) baseStart_4844375 baseEnd_4844375 := by
    simpa [prefixWord, tailWord_4844375, baseEnd_4844375] using wordTrace_append hprefix tailTrace_4844375
  have hstable : (prefixWord ++ tailWord_4844375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844375).length < 2 ^ (prefixWord ++ tailWord_4844375).sum := by decide
  have hdescent : baseEnd_4844375 < baseStart_4844375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844386 : List Nat := [3, 3, 2, 1, 4, 1, 1, 2, 2, 1, 3]
def baseStart_4844386 : Nat := 118140960795 + 4844386 * 2 ^ 59
def prefixEnd_4844386 : Nat := 4983230072969 + 3 ^ 40 * 4844386 * 2
def baseEnd_4844386 : Nat := 2487498493911788551196081

theorem tailTrace_4844386 : CollatzResearch.WordTrace tailWord_4844386 prefixEnd_4844386 2487498493911788551196081 := by
  unfold tailWord_4844386
  simp only [CollatzResearch.WordTrace]
  refine ⟨44172318256906088026198253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117792848685082901403195341 44172318256906088026198253)
  ·
    refine ⟨16564619346339783009824345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44172318256906088026198253 16564619346339783009824345)
    ·
      refine ⟨12423464509754837257368259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16564619346339783009824345 12423464509754837257368259)
      ·
        refine ⟨18635196764632255886052389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12423464509754837257368259 18635196764632255886052389)
        ·
          refine ⟨3494099393368547978634823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18635196764632255886052389 3494099393368547978634823)
          ·
            refine ⟨5241149090052821967952235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3494099393368547978634823 5241149090052821967952235)
            ·
              refine ⟨7861723635079232951928353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5241149090052821967952235 7861723635079232951928353)
              ·
                refine ⟨5896292726309424713946265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7861723635079232951928353 5896292726309424713946265)
                ·
                  refine ⟨4422219544732068535459699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5896292726309424713946265 4422219544732068535459699)
                  ·
                    refine ⟨6633329317098102803189549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4422219544732068535459699 6633329317098102803189549)
                    ·
                      refine ⟨2487498493911788551196081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6633329317098102803189549 2487498493911788551196081)
                      ·
                        rfl

theorem cell23_4844386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_4844386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844386 prefixEnd_4844386 := by exact prefixLift 4844386
  have htrace : WordTrace (prefixWord ++ tailWord_4844386) baseStart_4844386 baseEnd_4844386 := by
    simpa [prefixWord, tailWord_4844386, baseEnd_4844386] using wordTrace_append hprefix tailTrace_4844386
  have hstable : (prefixWord ++ tailWord_4844386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844386).length < 2 ^ (prefixWord ++ tailWord_4844386).sum := by decide
  have hdescent : baseEnd_4844386 < baseStart_4844386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844388 : List Nat := [2, 3, 1, 1, 4, 1, 1, 2, 2, 2, 4]
def baseStart_4844388 : Nat := 118140960795 + 4844388 * 2 ^ 59
def prefixEnd_4844388 : Nat := 4983230072969 + 3 ^ 40 * 4844388 * 2
def baseEnd_4844388 : Nat := 2487499520873097543371071

theorem tailTrace_4844388 : CollatzResearch.WordTrace tailWord_4844388 prefixEnd_4844388 2487499520873097543371071 := by
  unfold tailWord_4844388
  simp only [CollatzResearch.WordTrace]
  refine ⟨88344672986808553223182909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117792897315744737630910545 88344672986808553223182909)
  ·
    refine ⟨33129252370053207458693591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88344672986808553223182909 33129252370053207458693591)
    ·
      refine ⟨49693878555079811188040387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33129252370053207458693591 49693878555079811188040387)
      ·
        refine ⟨74540817832619716782060581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49693878555079811188040387 74540817832619716782060581)
        ·
          refine ⟨13976403343616196896636359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74540817832619716782060581 13976403343616196896636359)
          ·
            refine ⟨20964605015424295344954539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13976403343616196896636359 20964605015424295344954539)
            ·
              refine ⟨31446907523136443017431809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20964605015424295344954539 31446907523136443017431809)
              ·
                refine ⟨23585180642352332263073857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31446907523136443017431809 23585180642352332263073857)
                ·
                  refine ⟨17688885481764249197305393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23585180642352332263073857 17688885481764249197305393)
                  ·
                    refine ⟨13266664111323186897979045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17688885481764249197305393 13266664111323186897979045)
                    ·
                      refine ⟨2487499520873097543371071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13266664111323186897979045 2487499520873097543371071)
                      ·
                        rfl

theorem cell23_4844388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_4844388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844388 prefixEnd_4844388 := by exact prefixLift 4844388
  have htrace : WordTrace (prefixWord ++ tailWord_4844388) baseStart_4844388 baseEnd_4844388 := by
    simpa [prefixWord, tailWord_4844388, baseEnd_4844388] using wordTrace_append hprefix tailTrace_4844388
  have hstable : (prefixWord ++ tailWord_4844388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844388).length < 2 ^ (prefixWord ++ tailWord_4844388).sum := by decide
  have hdescent : baseEnd_4844388 < baseStart_4844388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844392 : List Nat := [2, 1, 4, 2, 1, 3, 1, 1, 4, 2, 2]
def baseStart_4844392 : Nat := 118140960795 + 4844392 * 2 ^ 59
def prefixEnd_4844392 : Nat := 4983230072969 + 3 ^ 40 * 4844392 * 2
def baseEnd_4844392 : Nat := 2487501574795715527721053

theorem tailTrace_4844392 : CollatzResearch.WordTrace tailWord_4844392 prefixEnd_4844392 2487501574795715527721053 := by
  unfold tailWord_4844392
  simp only [CollatzResearch.WordTrace]
  refine ⟨88344745932801307564755715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117792994577068410086340953 88344745932801307564755715)
  ·
    refine ⟨132517118899201961347133573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88344745932801307564755715 132517118899201961347133573)
    ·
      refine ⟨24846959793600367752587545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132517118899201961347133573 24846959793600367752587545)
      ·
        refine ⟨18635219845200275814440659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24846959793600367752587545 18635219845200275814440659)
        ·
          refine ⟨27952829767800413721660989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18635219845200275814440659 27952829767800413721660989)
          ·
            refine ⟨10482311162925155145622871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27952829767800413721660989 10482311162925155145622871)
            ·
              refine ⟨15723466744387732718434307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10482311162925155145622871 15723466744387732718434307)
              ·
                refine ⟨23585200116581599077651461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15723466744387732718434307 23585200116581599077651461)
                ·
                  refine ⟨4422225021859049827059649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23585200116581599077651461 4422225021859049827059649)
                  ·
                    refine ⟨3316668766394287370294737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4422225021859049827059649 3316668766394287370294737)
                    ·
                      refine ⟨2487501574795715527721053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3316668766394287370294737 2487501574795715527721053)
                      ·
                        rfl

theorem cell23_4844392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_4844392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844392 prefixEnd_4844392 := by exact prefixLift 4844392
  have htrace : WordTrace (prefixWord ++ tailWord_4844392) baseStart_4844392 baseEnd_4844392 := by
    simpa [prefixWord, tailWord_4844392, baseEnd_4844392] using wordTrace_append hprefix tailTrace_4844392
  have hstable : (prefixWord ++ tailWord_4844392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844392).length < 2 ^ (prefixWord ++ tailWord_4844392).sum := by decide
  have hdescent : baseEnd_4844392 < baseStart_4844392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844409 : List Nat := [1, 2, 1, 3, 2, 4, 3, 1, 2, 2, 2]
def baseStart_4844409 : Nat := 118140960795 + 4844409 * 2 ^ 59
def prefixEnd_4844409 : Nat := 4983230072969 + 3 ^ 40 * 4844409 * 2
def baseEnd_4844409 : Nat := 2487510303966841961208475

theorem tailTrace_4844409 : CollatzResearch.WordTrace tailWord_4844409 prefixEnd_4844409 2487510303966841961208475 := by
  unfold tailWord_4844409
  simp only [CollatzResearch.WordTrace]
  refine ⟨176690111906541027032880281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117793407937694018021920187 176690111906541027032880281)
  ·
    refine ⟨132517583929905770274660211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176690111906541027032880281 132517583929905770274660211)
    ·
      refine ⟨198776375894858655411990317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132517583929905770274660211 198776375894858655411990317)
      ·
        refine ⟨74541140960571995779496369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198776375894858655411990317 74541140960571995779496369)
        ·
          refine ⟨55905855720428996834622277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74541140960571995779496369 55905855720428996834622277)
          ·
            refine ⟨10482347947580436906491677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55905855720428996834622277 10482347947580436906491677)
            ·
              refine ⟨3930880480342663839934379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10482347947580436906491677 3930880480342663839934379)
              ·
                refine ⟨5896320720513995759901569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3930880480342663839934379 5896320720513995759901569)
                ·
                  refine ⟨4422240540385496819926177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5896320720513995759901569 4422240540385496819926177)
                  ·
                    refine ⟨3316680405289122614944633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4422240540385496819926177 3316680405289122614944633)
                    ·
                      refine ⟨2487510303966841961208475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3316680405289122614944633 2487510303966841961208475)
                      ·
                        rfl

theorem cell23_4844409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 2, 2, 2].length) (baseStart_4844409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844409 prefixEnd_4844409 := by exact prefixLift 4844409
  have htrace : WordTrace (prefixWord ++ tailWord_4844409) baseStart_4844409 baseEnd_4844409 := by
    simpa [prefixWord, tailWord_4844409, baseEnd_4844409] using wordTrace_append hprefix tailTrace_4844409
  have hstable : (prefixWord ++ tailWord_4844409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844409).length < 2 ^ (prefixWord ++ tailWord_4844409).sum := by decide
  have hdescent : baseEnd_4844409 < baseStart_4844409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844411 : List Nat := [1, 1, 1, 1, 1, 5, 3, 2, 1, 7]
def baseStart_4844411 : Nat := 118140960795 + 4844411 * 2 ^ 59
def prefixEnd_4844411 : Nat := 4983230072969 + 3 ^ 40 * 4844411 * 2
def baseEnd_4844411 : Nat := 829170443642716984461155

theorem tailTrace_4844411 : CollatzResearch.WordTrace tailWord_4844411 prefixEnd_4844411 829170443642716984461155 := by
  unfold tailWord_4844411
  simp only [CollatzResearch.WordTrace]
  refine ⟨176690184852533781374453087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117793456568355854249635391 176690184852533781374453087)
  ·
    refine ⟨265035277278800672061679631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176690184852533781374453087 265035277278800672061679631)
    ·
      refine ⟨397552915918201008092519447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265035277278800672061679631 397552915918201008092519447)
      ·
        refine ⟨596329373877301512138779171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397552915918201008092519447 596329373877301512138779171)
        ·
          refine ⟨894494060815952268208168757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 596329373877301512138779171 894494060815952268208168757)
          ·
            refine ⟨83858818201495525144515821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 894494060815952268208168757 83858818201495525144515821)
            ·
              refine ⟨31447056825560821929193433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83858818201495525144515821 31447056825560821929193433)
              ·
                refine ⟨23585292619170616446895075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31447056825560821929193433 23585292619170616446895075)
                ·
                  refine ⟨35377938928755924670342613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23585292619170616446895075 35377938928755924670342613)
                  ·
                    refine ⟨829170443642716984461155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35377938928755924670342613 829170443642716984461155)
                    ·
                      rfl

theorem cell23_4844411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 7].length) (baseStart_4844411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844411 prefixEnd_4844411 := by exact prefixLift 4844411
  have htrace : WordTrace (prefixWord ++ tailWord_4844411) baseStart_4844411 baseEnd_4844411 := by
    simpa [prefixWord, tailWord_4844411, baseEnd_4844411] using wordTrace_append hprefix tailTrace_4844411
  have hstable : (prefixWord ++ tailWord_4844411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844411).length < 2 ^ (prefixWord ++ tailWord_4844411).sum := by decide
  have hdescent : baseEnd_4844411 < baseStart_4844411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844448 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 4]
def baseStart_4844448 : Nat := 118140960795 + 4844448 * 2 ^ 59
def prefixEnd_4844448 : Nat := 4983230072969 + 3 ^ 40 * 4844448 * 2
def baseEnd_4844448 : Nat := 2487530329712367308620795

theorem tailTrace_4844448 : CollatzResearch.WordTrace tailWord_4844448 prefixEnd_4844448 2487530329712367308620795 := by
  unfold tailWord_4844448
  simp only [CollatzResearch.WordTrace]
  refine ⟨88345767176699868346774999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117794356235599824462366665 88345767176699868346774999)
  ·
    refine ⟨132518650765049802520162499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88345767176699868346774999 132518650765049802520162499)
    ·
      refine ⟨198777976147574703780243749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132518650765049802520162499 198777976147574703780243749)
      ·
        refine ⟨37270870527670256958795703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 198777976147574703780243749 37270870527670256958795703)
        ·
          refine ⟨55906305791505385438193555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37270870527670256958795703 55906305791505385438193555)
          ·
            refine ⟨83859458687258078157290333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55906305791505385438193555 83859458687258078157290333)
            ·
              refine ⟨31447297007721779308983875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83859458687258078157290333 31447297007721779308983875)
              ·
                refine ⟨47170945511582668963475813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31447297007721779308983875 47170945511582668963475813)
                ·
                  refine ⟨8844552283421750430651715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47170945511582668963475813 8844552283421750430651715)
                  ·
                    refine ⟨13266828425132625645977573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8844552283421750430651715 13266828425132625645977573)
                    ·
                      refine ⟨2487530329712367308620795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13266828425132625645977573 2487530329712367308620795)
                      ·
                        rfl

theorem cell23_4844448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_4844448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844448 prefixEnd_4844448 := by exact prefixLift 4844448
  have htrace : WordTrace (prefixWord ++ tailWord_4844448) baseStart_4844448 baseEnd_4844448 := by
    simpa [prefixWord, tailWord_4844448, baseEnd_4844448] using wordTrace_append hprefix tailTrace_4844448
  have hstable : (prefixWord ++ tailWord_4844448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844448).length < 2 ^ (prefixWord ++ tailWord_4844448).sum := by decide
  have hdescent : baseEnd_4844448 < baseStart_4844448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844455 : List Nat := [1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 5]
def baseStart_4844455 : Nat := 118140960795 + 4844455 * 2 ^ 59
def prefixEnd_4844455 : Nat := 4983230072969 + 3 ^ 40 * 4844455 * 2
def baseEnd_4844455 : Nat := 2487533924076948781233263

theorem tailTrace_4844455 : CollatzResearch.WordTrace tailWord_4844455 prefixEnd_4844455 2487533924076948781233263 := by
  unfold tailWord_4844455
  simp only [CollatzResearch.WordTrace]
  refine ⟨176691789664374376889054819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117794526442916251259369879 176691789664374376889054819)
  ·
    refine ⟨265037684496561565333582229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176691789664374376889054819 265037684496561565333582229)
    ·
      refine ⟨12423641460776323375011667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 265037684496561565333582229 12423641460776323375011667)
      ·
        refine ⟨18635462191164485062517501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12423641460776323375011667 18635462191164485062517501)
        ·
          refine ⟨6988298321686681898444063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18635462191164485062517501 6988298321686681898444063)
          ·
            refine ⟨10482447482530022847666095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6988298321686681898444063 10482447482530022847666095)
            ·
              refine ⟨15723671223795034271499143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10482447482530022847666095 15723671223795034271499143)
              ·
                refine ⟨23585506835692551407248715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15723671223795034271499143 23585506835692551407248715)
                ·
                  refine ⟨35378260253538827110873073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23585506835692551407248715 35378260253538827110873073)
                  ·
                    refine ⟨26533695190154120333154805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35378260253538827110873073 26533695190154120333154805)
                    ·
                      refine ⟨2487533924076948781233263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26533695190154120333154805 2487533924076948781233263)
                      ·
                        rfl

theorem cell23_4844455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_4844455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844455 prefixEnd_4844455 := by exact prefixLift 4844455
  have htrace : WordTrace (prefixWord ++ tailWord_4844455) baseStart_4844455 baseEnd_4844455 := by
    simpa [prefixWord, tailWord_4844455, baseEnd_4844455] using wordTrace_append hprefix tailTrace_4844455
  have hstable : (prefixWord ++ tailWord_4844455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844455).length < 2 ^ (prefixWord ++ tailWord_4844455).sum := by decide
  have hdescent : baseEnd_4844455 < baseStart_4844455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844492 : List Nat := [2, 2, 1, 4, 1, 1, 2, 5, 1, 4]
def baseStart_4844492 : Nat := 118140960795 + 4844492 * 2 ^ 59
def prefixEnd_4844492 : Nat := 4983230072969 + 3 ^ 40 * 4844492 * 2
def baseEnd_4844492 : Nat := 829184307620388378823531

theorem tailTrace_4844492 : CollatzResearch.WordTrace tailWord_4844492 prefixEnd_4844492 829184307620388378823531 := by
  unfold tailWord_4844492
  simp only [CollatzResearch.WordTrace]
  refine ⟨88346569582620166104075865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117795426110160221472101153 88346569582620166104075865)
  ·
    refine ⟨66259927186965124578056899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88346569582620166104075865 66259927186965124578056899)
    ·
      refine ⟨99389890780447686867085349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66259927186965124578056899 99389890780447686867085349)
      ·
        refine ⟨18635604521333941287578503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99389890780447686867085349 18635604521333941287578503)
        ·
          refine ⟨27953406782000911931367755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18635604521333941287578503 27953406782000911931367755)
          ·
            refine ⟨41930110173001367897051633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27953406782000911931367755 41930110173001367897051633)
            ·
              refine ⟨31447582629751025922788725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41930110173001367897051633 31447582629751025922788725)
              ·
                refine ⟨2948210871539158680261443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31447582629751025922788725 2948210871539158680261443)
                ·
                  refine ⟨4422316307308738020392165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2948210871539158680261443 4422316307308738020392165)
                  ·
                    refine ⟨829184307620388378823531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4422316307308738020392165 829184307620388378823531)
                    ·
                      rfl

theorem cell23_4844492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 5, 1, 4].length) (baseStart_4844492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844492 prefixEnd_4844492 := by exact prefixLift 4844492
  have htrace : WordTrace (prefixWord ++ tailWord_4844492) baseStart_4844492 baseEnd_4844492 := by
    simpa [prefixWord, tailWord_4844492, baseEnd_4844492] using wordTrace_append hprefix tailTrace_4844492
  have hstable : (prefixWord ++ tailWord_4844492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844492).length < 2 ^ (prefixWord ++ tailWord_4844492).sum := by decide
  have hdescent : baseEnd_4844492 < baseStart_4844492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844505 : List Nat := [1, 2, 1, 2, 5, 2, 2, 2, 6]
def baseStart_4844505 : Nat := 118140960795 + 4844505 * 2 ^ 59
def prefixEnd_4844505 : Nat := 4983230072969 + 3 ^ 40 * 4844505 * 2
def baseEnd_4844505 : Nat := 276395510901074842845337

theorem tailTrace_4844505 : CollatzResearch.WordTrace tailWord_4844505 prefixEnd_4844505 276395510901074842845337 := by
  unfold tailWord_4844505
  simp only [CollatzResearch.WordTrace]
  refine ⟨176693613314193235428374969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117795742209462156952249979 176693613314193235428374969)
  ·
    refine ⟨132520209985644926571281227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176693613314193235428374969 132520209985644926571281227)
    ·
      refine ⟨198780314978467389856921841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132520209985644926571281227 198780314978467389856921841)
      ·
        refine ⟨149085236233850542392691381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198780314978467389856921841 149085236233850542392691381)
        ·
          refine ⟨13976740896923488349314817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 149085236233850542392691381 13976740896923488349314817)
          ·
            refine ⟨10482555672692616261986113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13976740896923488349314817 10482555672692616261986113)
            ·
              refine ⟨7861916754519462196489585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10482555672692616261986113 7861916754519462196489585)
              ·
                refine ⟨5896437565889596647367189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7861916754519462196489585 5896437565889596647367189)
                ·
                  refine ⟨276395510901074842845337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5896437565889596647367189 276395510901074842845337)
                  ·
                    rfl

theorem cell23_4844505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 6].length) (baseStart_4844505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844505 prefixEnd_4844505 := by exact prefixLift 4844505
  have htrace : WordTrace (prefixWord ++ tailWord_4844505) baseStart_4844505 baseEnd_4844505 := by
    simpa [prefixWord, tailWord_4844505, baseEnd_4844505] using wordTrace_append hprefix tailTrace_4844505
  have hstable : (prefixWord ++ tailWord_4844505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844505).length < 2 ^ (prefixWord ++ tailWord_4844505).sum := by decide
  have hdescent : baseEnd_4844505 < baseStart_4844505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844509 : List Nat := [1, 4, 3, 1, 2, 2, 1, 4, 1, 4]
def baseStart_4844509 : Nat := 118140960795 + 4844509 * 2 ^ 59
def prefixEnd_4844509 : Nat := 4983230072969 + 3 ^ 40 * 4844509 * 2
def baseEnd_4844509 : Nat := 829187217344097189986005

theorem tailTrace_4844509 : CollatzResearch.WordTrace tailWord_4844509 prefixEnd_4844509 829187217344097189986005 := by
  unfold tailWord_4844509
  simp only [CollatzResearch.WordTrace]
  refine ⟨176693759206178744111520581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117795839470785829407680387 176693759206178744111520581)
  ·
    refine ⟨33130079851158514520910109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176693759206178744111520581 33130079851158514520910109)
    ·
      refine ⟨12423779944184442945341291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33130079851158514520910109 12423779944184442945341291)
      ·
        refine ⟨18635669916276664418011937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12423779944184442945341291 18635669916276664418011937)
        ·
          refine ⟨13976752437207498313508953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18635669916276664418011937 13976752437207498313508953)
          ·
            refine ⟨10482564327905623735131715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13976752437207498313508953 10482564327905623735131715)
            ·
              refine ⟨15723846491858435602697573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10482564327905623735131715 15723846491858435602697573)
              ·
                refine ⟨2948221217223456675505795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15723846491858435602697573 2948221217223456675505795)
                ·
                  refine ⟨4422331825835185013258693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2948221217223456675505795 4422331825835185013258693)
                  ·
                    refine ⟨829187217344097189986005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4422331825835185013258693 829187217344097189986005)
                    ·
                      rfl

theorem cell23_4844509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_4844509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844509 prefixEnd_4844509 := by exact prefixLift 4844509
  have htrace : WordTrace (prefixWord ++ tailWord_4844509) baseStart_4844509 baseEnd_4844509 := by
    simpa [prefixWord, tailWord_4844509, baseEnd_4844509] using wordTrace_append hprefix tailTrace_4844509
  have hstable : (prefixWord ++ tailWord_4844509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844509).length < 2 ^ (prefixWord ++ tailWord_4844509).sum := by decide
  have hdescent : baseEnd_4844509 < baseStart_4844509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844549 : List Nat := [1, 3, 1, 1, 2, 3, 4, 3, 1, 1, 3]
def baseStart_4844549 : Nat := 118140960795 + 4844549 * 2 ^ 59
def prefixEnd_4844549 : Nat := 4983230072969 + 3 ^ 40 * 4844549 * 2
def baseEnd_4844549 : Nat := 2487582191258471413457831

theorem tailTrace_4844549 : CollatzResearch.WordTrace tailWord_4844549 prefixEnd_4844549 2487582191258471413457831 := by
  unfold tailWord_4844549
  simp only [CollatzResearch.WordTrace]
  refine ⟨176695218126033830942976701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117796812084022553961984467 176695218126033830942976701)
  ·
    refine ⟨66260706797262686603616263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176695218126033830942976701 66260706797262686603616263)
    ·
      refine ⟨99391060195894029905424395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66260706797262686603616263 99391060195894029905424395)
      ·
        refine ⟨149086590293841044858136593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99391060195894029905424395 149086590293841044858136593)
        ·
          refine ⟨111814942720380783643602445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149086590293841044858136593 111814942720380783643602445)
          ·
            refine ⟨41930603520142793866350917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111814942720380783643602445 41930603520142793866350917)
            ·
              refine ⟨7861988160026773849940797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41930603520142793866350917 7861988160026773849940797)
              ·
                refine ⟨2948245560010040193727799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7861988160026773849940797 2948245560010040193727799)
                ·
                  refine ⟨4422368340015060290591699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2948245560010040193727799 4422368340015060290591699)
                  ·
                    refine ⟨6633552510022590435887549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4422368340015060290591699 6633552510022590435887549)
                    ·
                      refine ⟨2487582191258471413457831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6633552510022590435887549 2487582191258471413457831)
                      ·
                        rfl

theorem cell23_4844549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 3, 1, 1, 3].length) (baseStart_4844549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844549 prefixEnd_4844549 := by exact prefixLift 4844549
  have htrace : WordTrace (prefixWord ++ tailWord_4844549) baseStart_4844549 baseEnd_4844549 := by
    simpa [prefixWord, tailWord_4844549, baseEnd_4844549] using wordTrace_append hprefix tailTrace_4844549
  have hstable : (prefixWord ++ tailWord_4844549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844549).length < 2 ^ (prefixWord ++ tailWord_4844549).sum := by decide
  have hdescent : baseEnd_4844549 < baseStart_4844549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844552 : List Nat := [2, 1, 3, 2, 1, 3, 4, 1, 1, 5]
def baseStart_4844552 : Nat := 118140960795 + 4844552 * 2 ^ 59
def prefixEnd_4844552 : Nat := 4983230072969 + 3 ^ 40 * 4844552 * 2
def baseEnd_4844552 : Nat := 829194577233478300573439

theorem tailTrace_4844552 : CollatzResearch.WordTrace tailWord_4844552 prefixEnd_4844552 829194577233478300573439 := by
  unfold tailWord_4844552
  simp only [CollatzResearch.WordTrace]
  refine ⟨88347663772511481227667955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117796885030015308303557273 88347663772511481227667955)
  ·
    refine ⟨132521495658767221841501933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88347663772511481227667955 132521495658767221841501933)
    ·
      refine ⟨49695560872037708190563225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132521495658767221841501933 49695560872037708190563225)
      ·
        refine ⟨37271670654028281142922419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49695560872037708190563225 37271670654028281142922419)
        ·
          refine ⟨55907505981042421714383629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37271670654028281142922419 55907505981042421714383629)
          ·
            refine ⟨20965314742890908142893861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55907505981042421714383629 20965314742890908142893861)
            ·
              refine ⟨3930996514292045276792599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20965314742890908142893861 3930996514292045276792599)
              ·
                refine ⟨5896494771438067915188899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3930996514292045276792599 5896494771438067915188899)
                ·
                  refine ⟨8844742157157101872783349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5896494771438067915188899 8844742157157101872783349)
                  ·
                    refine ⟨829194577233478300573439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8844742157157101872783349 829194577233478300573439)
                    ·
                      rfl

theorem cell23_4844552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 1, 5].length) (baseStart_4844552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844552 prefixEnd_4844552 := by exact prefixLift 4844552
  have htrace : WordTrace (prefixWord ++ tailWord_4844552) baseStart_4844552 baseEnd_4844552 := by
    simpa [prefixWord, tailWord_4844552, baseEnd_4844552] using wordTrace_append hprefix tailTrace_4844552
  have hstable : (prefixWord ++ tailWord_4844552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844552).length < 2 ^ (prefixWord ++ tailWord_4844552).sum := by decide
  have hdescent : baseEnd_4844552 < baseStart_4844552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844575 : List Nat := [1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 5]
def baseStart_4844575 : Nat := 118140960795 + 4844575 * 2 ^ 59
def prefixEnd_4844575 : Nat := 4983230072969 + 3 ^ 40 * 4844575 * 2
def baseEnd_4844575 : Nat := 2487595541755488311732711

theorem tailTrace_4844575 : CollatzResearch.WordTrace tailWord_4844575 prefixEnd_4844575 2487595541755488311732711 := by
  unfold tailWord_4844575
  simp only [CollatzResearch.WordTrace]
  refine ⟨176696166423939637383423179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117797444282626424922282119 176696166423939637383423179)
  ·
    refine ⟨265044249635909456075134769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176696166423939637383423179 265044249635909456075134769)
    ·
      refine ⟨198783187226932092056351077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265044249635909456075134769 198783187226932092056351077)
      ·
        refine ⟨37271847605049767260565827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 198783187226932092056351077 37271847605049767260565827)
        ·
          refine ⟨55907771407574650890848741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37271847605049767260565827 55907771407574650890848741)
          ·
            refine ⟨10482707138920247042034139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55907771407574650890848741 10482707138920247042034139)
            ·
              refine ⟨15724060708380370563051209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10482707138920247042034139 15724060708380370563051209)
              ·
                refine ⟨11793045531285277922288407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15724060708380370563051209 11793045531285277922288407)
                ·
                  refine ⟨17689568296927916883432611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11793045531285277922288407 17689568296927916883432611)
                  ·
                    refine ⟨26534352445391875325148917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17689568296927916883432611 26534352445391875325148917)
                    ·
                      refine ⟨2487595541755488311732711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26534352445391875325148917 2487595541755488311732711)
                      ·
                        rfl

theorem cell23_4844575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_4844575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844575 prefixEnd_4844575 := by exact prefixLift 4844575
  have htrace : WordTrace (prefixWord ++ tailWord_4844575) baseStart_4844575 baseEnd_4844575 := by
    simpa [prefixWord, tailWord_4844575, baseEnd_4844575] using wordTrace_append hprefix tailTrace_4844575
  have hstable : (prefixWord ++ tailWord_4844575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844575).length < 2 ^ (prefixWord ++ tailWord_4844575).sum := by decide
  have hdescent : baseEnd_4844575 < baseStart_4844575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844592 : List Nat := [2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 3]
def baseStart_4844592 : Nat := 118140960795 + 4844592 * 2 ^ 59
def prefixEnd_4844592 : Nat := 4983230072969 + 3 ^ 40 * 4844592 * 2
def baseEnd_4844592 : Nat := 2487604270926614745220133

theorem tailTrace_4844592 : CollatzResearch.WordTrace tailWord_4844592 prefixEnd_4844592 2487604270926614745220133 := by
  unfold tailWord_4844592
  simp only [CollatzResearch.WordTrace]
  refine ⟨88348393232439024643396015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117797857643252032857861353 88348393232439024643396015)
  ·
    refine ⟨132522589848658536965094023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88348393232439024643396015 132522589848658536965094023)
    ·
      refine ⟨198783884772987805447641035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132522589848658536965094023 198783884772987805447641035)
      ·
        refine ⟨298175827159481708171461553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198783884772987805447641035 298175827159481708171461553)
        ·
          refine ⟨223631870369611281128596165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298175827159481708171461553 223631870369611281128596165)
          ·
            refine ⟨41930975694302115211611781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 223631870369611281128596165 41930975694302115211611781)
            ·
              refine ⟨7862057942681646602177209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41930975694302115211611781 7862057942681646602177209)
              ·
                refine ⟨5896543457011234951632907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7862057942681646602177209 5896543457011234951632907)
                ·
                  refine ⟨8844815185516852427449361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5896543457011234951632907 8844815185516852427449361)
                  ·
                    refine ⟨6633611389137639320587021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8844815185516852427449361 6633611389137639320587021)
                    ·
                      refine ⟨2487604270926614745220133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6633611389137639320587021 2487604270926614745220133)
                      ·
                        rfl

theorem cell23_4844592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 3].length) (baseStart_4844592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844592 prefixEnd_4844592 := by exact prefixLift 4844592
  have htrace : WordTrace (prefixWord ++ tailWord_4844592) baseStart_4844592 baseEnd_4844592 := by
    simpa [prefixWord, tailWord_4844592, baseEnd_4844592] using wordTrace_append hprefix tailTrace_4844592
  have hstable : (prefixWord ++ tailWord_4844592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844592).length < 2 ^ (prefixWord ++ tailWord_4844592).sum := by decide
  have hdescent : baseEnd_4844592 < baseStart_4844592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844622 : List Nat := [4, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3]
def baseStart_4844622 : Nat := 118140960795 + 4844622 * 2 ^ 59
def prefixEnd_4844622 : Nat := 4983230072969 + 3 ^ 40 * 4844622 * 2
def baseEnd_4844622 : Nat := 2487619675346249627844995

theorem tailTrace_4844622 : CollatzResearch.WordTrace tailWord_4844622 prefixEnd_4844622 2487619675346249627844995 := by
  unfold tailWord_4844622
  simp only [CollatzResearch.WordTrace]
  refine ⟨22087235081846170551298015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117798587103179576273589413 22087235081846170551298015)
  ·
    refine ⟨33130852622769255826947023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22087235081846170551298015 33130852622769255826947023)
    ·
      refine ⟨49696278934153883740420535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33130852622769255826947023 49696278934153883740420535)
      ·
        refine ⟨74544418401230825610630803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49696278934153883740420535 74544418401230825610630803)
        ·
          refine ⟨111816627601846238415946205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74544418401230825610630803 111816627601846238415946205)
          ·
            refine ⟨41931235350692339405979827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111816627601846238415946205 41931235350692339405979827)
            ·
              refine ⟨62896853026038509108969741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41931235350692339405979827 62896853026038509108969741)
              ·
                refine ⟨23586319884764440915863653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62896853026038509108969741 23586319884764440915863653)
                ·
                  refine ⟨4422434978393332671724435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23586319884764440915863653 4422434978393332671724435)
                  ·
                    refine ⟨6633652467589999007586653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4422434978393332671724435 6633652467589999007586653)
                    ·
                      refine ⟨2487619675346249627844995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6633652467589999007586653 2487619675346249627844995)
                      ·
                        rfl

theorem cell23_4844622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3].length) (baseStart_4844622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844622 prefixEnd_4844622 := by exact prefixLift 4844622
  have htrace : WordTrace (prefixWord ++ tailWord_4844622) baseStart_4844622 baseEnd_4844622 := by
    simpa [prefixWord, tailWord_4844622, baseEnd_4844622] using wordTrace_append hprefix tailTrace_4844622
  have hstable : (prefixWord ++ tailWord_4844622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844622).length < 2 ^ (prefixWord ++ tailWord_4844622).sum := by decide
  have hdescent : baseEnd_4844622 < baseStart_4844622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844632 : List Nat := [2, 1, 2, 2, 1, 3, 2, 2, 3, 3, 2]
def baseStart_4844632 : Nat := 118140960795 + 4844632 * 2 ^ 59
def prefixEnd_4844632 : Nat := 4983230072969 + 3 ^ 40 * 4844632 * 2
def baseEnd_4844632 : Nat := 2487624810152794588719949

theorem tailTrace_4844632 : CollatzResearch.WordTrace tailWord_4844632 prefixEnd_4844632 2487624810152794588719949 := by
  unfold tailWord_4844632
  simp only [CollatzResearch.WordTrace]
  refine ⟨88349122692366568059124075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117798830256488757412165433 88349122692366568059124075)
  ·
    refine ⟨132523684038549852088686113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88349122692366568059124075 132523684038549852088686113)
    ·
      refine ⟨99392763028912389066514585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132523684038549852088686113 99392763028912389066514585)
      ·
        refine ⟨74544572271684291799885939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99392763028912389066514585 74544572271684291799885939)
        ·
          refine ⟨111816858407526437699828909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74544572271684291799885939 111816858407526437699828909)
          ·
            refine ⟨41931321902822414137435841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111816858407526437699828909 41931321902822414137435841)
            ·
              refine ⟨31448491427116810603076881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41931321902822414137435841 31448491427116810603076881)
              ·
                refine ⟨23586368570337607952307661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31448491427116810603076881 23586368570337607952307661)
                ·
                  refine ⟨8844888213876602982115373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23586368570337607952307661 8844888213876602982115373)
                  ·
                    refine ⟨3316833080203726118293265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8844888213876602982115373 3316833080203726118293265)
                    ·
                      refine ⟨2487624810152794588719949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3316833080203726118293265 2487624810152794588719949)
                      ·
                        rfl

theorem cell23_4844632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 3, 3, 2].length) (baseStart_4844632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844632 prefixEnd_4844632 := by exact prefixLift 4844632
  have htrace : WordTrace (prefixWord ++ tailWord_4844632) baseStart_4844632 baseEnd_4844632 := by
    simpa [prefixWord, tailWord_4844632, baseEnd_4844632] using wordTrace_append hprefix tailTrace_4844632
  have hstable : (prefixWord ++ tailWord_4844632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844632).length < 2 ^ (prefixWord ++ tailWord_4844632).sum := by decide
  have hdescent : baseEnd_4844632 < baseStart_4844632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844649 : List Nat := [1, 2, 1, 1, 1, 6, 3, 2, 1, 3, 2]
def baseStart_4844649 : Nat := 118140960795 + 4844649 * 2 ^ 59
def prefixEnd_4844649 : Nat := 4983230072969 + 3 ^ 40 * 4844649 * 2
def baseEnd_4844649 : Nat := 2487633539323921022207371

theorem tailTrace_4844649 : CollatzResearch.WordTrace tailWord_4844649 prefixEnd_4844649 2487633539323921022207371 := by
  unfold tailWord_4844649
  simp only [CollatzResearch.WordTrace]
  refine ⟨176698865425671548021617001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117799243617114365347744667 176698865425671548021617001)
  ·
    refine ⟨132524149069253661016212751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 176698865425671548021617001 132524149069253661016212751)
    ·
      refine ⟨198786223603880491524319127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132524149069253661016212751 198786223603880491524319127)
      ·
        refine ⟨298179335405820737286478691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198786223603880491524319127 298179335405820737286478691)
        ·
          refine ⟨447269003108731105929718037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298179335405820737286478691 447269003108731105929718037)
          ·
            refine ⟨20965734520721770590455533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 447269003108731105929718037 20965734520721770590455533)
            ·
              refine ⟨7862150445270663971420825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20965734520721770590455533 7862150445270663971420825)
              ·
                refine ⟨5896612833952997978565619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7862150445270663971420825 5896612833952997978565619)
                ·
                  refine ⟨8844919250929496967848429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5896612833952997978565619 8844919250929496967848429)
                  ·
                    refine ⟨3316844719098561362943161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8844919250929496967848429 3316844719098561362943161)
                    ·
                      refine ⟨2487633539323921022207371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3316844719098561362943161 2487633539323921022207371)
                      ·
                        rfl

theorem cell23_4844649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 3, 2].length) (baseStart_4844649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844649 prefixEnd_4844649 := by exact prefixLift 4844649
  have htrace : WordTrace (prefixWord ++ tailWord_4844649) baseStart_4844649 baseEnd_4844649 := by
    simpa [prefixWord, tailWord_4844649, baseEnd_4844649] using wordTrace_append hprefix tailTrace_4844649
  have hstable : (prefixWord ++ tailWord_4844649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844649).length < 2 ^ (prefixWord ++ tailWord_4844649).sum := by decide
  have hdescent : baseEnd_4844649 < baseStart_4844649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844675 : List Nat := [1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 4]
def baseStart_4844675 : Nat := 118140960795 + 4844675 * 2 ^ 59
def prefixEnd_4844675 : Nat := 4983230072969 + 3 ^ 40 * 4844675 * 2
def baseEnd_4844675 : Nat := 2487646889820937920482251

theorem tailTrace_4844675 : CollatzResearch.WordTrace tailWord_4844675 prefixEnd_4844675 2487646889820937920482251 := by
  unfold tailWord_4844675
  simp only [CollatzResearch.WordTrace]
  refine ⟨176699813723577354462063479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117799875815718236308042319 176699813723577354462063479)
  ·
    refine ⟨265049720585366031693095219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176699813723577354462063479 265049720585366031693095219)
    ·
      refine ⟨397574580878049047539642829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265049720585366031693095219 397574580878049047539642829)
      ·
        refine ⟨149090467829268392827366061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 397574580878049047539642829 149090467829268392827366061)
        ·
          refine ⟨55908925435975647310262273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149090467829268392827366061 55908925435975647310262273)
          ·
            refine ⟨41931694076981735482696705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55908925435975647310262273 41931694076981735482696705)
            ·
              refine ⟨31448770557736301612022529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41931694076981735482696705 31448770557736301612022529)
              ·
                refine ⟨23586577918302226209016897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31448770557736301612022529 23586577918302226209016897)
                ·
                  refine ⟨17689933438726669656762673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23586577918302226209016897 17689933438726669656762673)
                  ·
                    refine ⟨13267450079045002242572005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17689933438726669656762673 13267450079045002242572005)
                    ·
                      refine ⟨2487646889820937920482251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13267450079045002242572005 2487646889820937920482251)
                      ·
                        rfl

theorem cell23_4844675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_4844675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844675 prefixEnd_4844675 := by exact prefixLift 4844675
  have htrace : WordTrace (prefixWord ++ tailWord_4844675) baseStart_4844675 baseEnd_4844675 := by
    simpa [prefixWord, tailWord_4844675, baseEnd_4844675] using wordTrace_append hprefix tailTrace_4844675
  have hstable : (prefixWord ++ tailWord_4844675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844675).length < 2 ^ (prefixWord ++ tailWord_4844675).sum := by decide
  have hdescent : baseEnd_4844675 < baseStart_4844675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844696 : List Nat := [2, 1, 2, 4, 2, 1, 2, 3, 2, 2, 2]
def baseStart_4844696 : Nat := 118140960795 + 4844696 * 2 ^ 59
def prefixEnd_4844696 : Nat := 4983230072969 + 3 ^ 40 * 4844696 * 2
def baseEnd_4844696 : Nat := 2487657672914682338319655

theorem tailTrace_4844696 : CollatzResearch.WordTrace tailWord_4844696 prefixEnd_4844696 2487657672914682338319655 := by
  unfold tailWord_4844696
  simp only [CollatzResearch.WordTrace]
  refine ⟨88350289828250637524288971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117800386437667516699051961 88350289828250637524288971)
  ·
    refine ⟨132525434742375956286433457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88350289828250637524288971 132525434742375956286433457)
    ·
      refine ⟨99394076056781967214825093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132525434742375956286433457 99394076056781967214825093)
      ·
        refine ⟨18636389260646618852779705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99394076056781967214825093 18636389260646618852779705)
        ·
          refine ⟨13977291945484964139584779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18636389260646618852779705 13977291945484964139584779)
          ·
            refine ⟨20965937918227446209377169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13977291945484964139584779 20965937918227446209377169)
            ·
              refine ⟨15724453438670584657032877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20965937918227446209377169 15724453438670584657032877)
              ·
                refine ⟨5896670039501469246387329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15724453438670584657032877 5896670039501469246387329)
                ·
                  refine ⟨4422502529626101934790497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5896670039501469246387329 4422502529626101934790497)
                  ·
                    refine ⟨3316876897219576451092873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4422502529626101934790497 3316876897219576451092873)
                    ·
                      refine ⟨2487657672914682338319655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3316876897219576451092873 2487657672914682338319655)
                      ·
                        rfl

theorem cell23_4844696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_4844696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844696 prefixEnd_4844696 := by exact prefixLift 4844696
  have htrace : WordTrace (prefixWord ++ tailWord_4844696) baseStart_4844696 baseEnd_4844696 := by
    simpa [prefixWord, tailWord_4844696, baseEnd_4844696] using wordTrace_append hprefix tailTrace_4844696
  have hstable : (prefixWord ++ tailWord_4844696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844696).length < 2 ^ (prefixWord ++ tailWord_4844696).sum := by decide
  have hdescent : baseEnd_4844696 < baseStart_4844696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844702 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 9]
def baseStart_4844702 : Nat := 118140960795 + 4844702 * 2 ^ 59
def prefixEnd_4844702 : Nat := 4983230072969 + 3 ^ 40 * 4844702 * 2
def baseEnd_4844702 : Nat := 276406750422067701649403

theorem tailTrace_4844702 : CollatzResearch.WordTrace tailWord_4844702 prefixEnd_4844702 276406750422067701649403 := by
  unfold tailWord_4844702
  simp only [CollatzResearch.WordTrace]
  refine ⟨22087599811809942259162045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117800532329653025382197573 22087599811809942259162045)
  ·
    refine ⟨8282849929428728347185767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22087599811809942259162045 8282849929428728347185767)
    ·
      refine ⟨12424274894143092520778651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8282849929428728347185767 12424274894143092520778651)
      ·
        refine ⟨18636412341214638781167977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12424274894143092520778651 18636412341214638781167977)
        ·
          refine ⟨13977309255910979085875983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18636412341214638781167977 13977309255910979085875983)
          ·
            refine ⟨20965963883866468628813975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13977309255910979085875983 20965963883866468628813975)
            ·
              refine ⟨31448945825799702943220963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20965963883866468628813975 31448945825799702943220963)
              ·
                refine ⟨47173418738699554414831445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31448945825799702943220963 47173418738699554414831445)
                ·
                  refine ⟨276406750422067701649403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47173418738699554414831445 276406750422067701649403)
                  ·
                    rfl

theorem cell23_4844702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_4844702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844702 prefixEnd_4844702 := by exact prefixLift 4844702
  have htrace : WordTrace (prefixWord ++ tailWord_4844702) baseStart_4844702 baseEnd_4844702 := by
    simpa [prefixWord, tailWord_4844702, baseEnd_4844702] using wordTrace_append hprefix tailTrace_4844702
  have hstable : (prefixWord ++ tailWord_4844702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844702).length < 2 ^ (prefixWord ++ tailWord_4844702).sum := by decide
  have hdescent : baseEnd_4844702 < baseStart_4844702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844772 : List Nat := [2, 3, 1, 1, 1, 2, 4, 1, 1, 4, 3]
def baseStart_4844772 : Nat := 118140960795 + 4844772 * 2 ^ 59
def prefixEnd_4844772 : Nat := 4983230072969 + 3 ^ 40 * 4844772 * 2
def baseEnd_4844772 : Nat := 2487696697444424040969305

theorem tailTrace_4844772 : CollatzResearch.WordTrace tailWord_4844772 prefixEnd_4844772 2487696697444424040969305 := by
  unfold tailWord_4844772
  simp only [CollatzResearch.WordTrace]
  refine ⟨88351675802112970014172285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117802234402817293352229713 88351675802112970014172285)
  ·
    refine ⟨33131878425792363755314607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88351675802112970014172285 33131878425792363755314607)
    ·
      refine ⟨49697817638688545632971911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33131878425792363755314607 49697817638688545632971911)
      ·
        refine ⟨74546726458032818449457867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49697817638688545632971911 74546726458032818449457867)
        ·
          refine ⟨111820089687049227674186801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74546726458032818449457867 111820089687049227674186801)
          ·
            refine ⟨83865067265286920755640101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111820089687049227674186801 83865067265286920755640101)
            ·
              refine ⟨15724700112241297641682519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83865067265286920755640101 15724700112241297641682519)
              ·
                refine ⟨23587050168361946462523779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15724700112241297641682519 23587050168361946462523779)
                ·
                  refine ⟨35380575252542919693785669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23587050168361946462523779 35380575252542919693785669)
                  ·
                    refine ⟨6633857859851797442584813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35380575252542919693785669 6633857859851797442584813)
                    ·
                      refine ⟨2487696697444424040969305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6633857859851797442584813 2487696697444424040969305)
                      ·
                        rfl

theorem cell23_4844772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_4844772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844772 prefixEnd_4844772 := by exact prefixLift 4844772
  have htrace : WordTrace (prefixWord ++ tailWord_4844772) baseStart_4844772 baseEnd_4844772 := by
    simpa [prefixWord, tailWord_4844772, baseEnd_4844772] using wordTrace_append hprefix tailTrace_4844772
  have hstable : (prefixWord ++ tailWord_4844772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844772).length < 2 ^ (prefixWord ++ tailWord_4844772).sum := by decide
  have hdescent : baseEnd_4844772 < baseStart_4844772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844796 : List Nat := [2, 2, 2, 1, 5, 2, 1, 1, 3, 4]
def baseStart_4844796 : Nat := 118140960795 + 4844796 * 2 ^ 59
def prefixEnd_4844796 : Nat := 4983230072969 + 3 ^ 40 * 4844796 * 2
def baseEnd_4844796 : Nat := 829236340326710649023065

theorem tailTrace_4844796 : CollatzResearch.WordTrace tailWord_4844796 prefixEnd_4844796 829236340326710649023065 := by
  unfold tailWord_4844796
  simp only [CollatzResearch.WordTrace]
  refine ⟨88352113478069496063609121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117802817970759328084812161 88352113478069496063609121)
  ·
    refine ⟨66264085108552122047706841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88352113478069496063609121 66264085108552122047706841)
    ·
      refine ⟨49698063831414091535780131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66264085108552122047706841 49698063831414091535780131)
      ·
        refine ⟨74547095747121137303670197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49698063831414091535780131 74547095747121137303670197)
        ·
          refine ⟨6988790226292606622219081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74547095747121137303670197 6988790226292606622219081)
          ·
            refine ⟨5241592669719454966664311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6988790226292606622219081 5241592669719454966664311)
            ·
              refine ⟨7862389004579182449996467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5241592669719454966664311 7862389004579182449996467)
              ·
                refine ⟨11793583506868773674994701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7862389004579182449996467 11793583506868773674994701)
                ·
                  refine ⟨4422593815075790128123013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11793583506868773674994701 4422593815075790128123013)
                  ·
                    refine ⟨829236340326710649023065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4422593815075790128123013 829236340326710649023065)
                    ·
                      rfl

theorem cell23_4844796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_4844796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844796 prefixEnd_4844796 := by exact prefixLift 4844796
  have htrace : WordTrace (prefixWord ++ tailWord_4844796) baseStart_4844796 baseEnd_4844796 := by
    simpa [prefixWord, tailWord_4844796, baseEnd_4844796] using wordTrace_append hprefix tailTrace_4844796
  have hstable : (prefixWord ++ tailWord_4844796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844796).length < 2 ^ (prefixWord ++ tailWord_4844796).sum := by decide
  have hdescent : baseEnd_4844796 < baseStart_4844796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844853 : List Nat := [1, 3, 3, 1, 2, 3, 1, 4, 1, 1, 3]
def baseStart_4844853 : Nat := 118140960795 + 4844853 * 2 ^ 59
def prefixEnd_4844853 : Nat := 4983230072969 + 3 ^ 40 * 4844853 * 2
def baseEnd_4844853 : Nat := 2487738289377438224056433

theorem tailTrace_4844853 : CollatzResearch.WordTrace tailWord_4844853 prefixEnd_4844853 2487738289377438224056433 := by
  unfold tailWord_4844853
  simp only [CollatzResearch.WordTrace]
  refine ⟨176706305916932490862043213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117804203944621660574695475 176706305916932490862043213)
  ·
    refine ⟨66264864718849684073266205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176706305916932490862043213 66264864718849684073266205)
    ·
      refine ⟨24849324269568631527474827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66264864718849684073266205 24849324269568631527474827)
      ·
        refine ⟨37273986404352947291212241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24849324269568631527474827 37273986404352947291212241)
        ·
          refine ⟨27955489803264710468409181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37273986404352947291212241 27955489803264710468409181)
          ·
            refine ⟨10483308676224266425653443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27955489803264710468409181 10483308676224266425653443)
            ·
              refine ⟨15724963014336399638480165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10483308676224266425653443 15724963014336399638480165)
              ·
                refine ⟨2948430565188074932215031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15724963014336399638480165 2948430565188074932215031)
                ·
                  refine ⟨4422645847782112398322547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2948430565188074932215031 4422645847782112398322547)
                  ·
                    refine ⟨6633968771673168597483821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4422645847782112398322547 6633968771673168597483821)
                    ·
                      refine ⟨2487738289377438224056433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6633968771673168597483821 2487738289377438224056433)
                      ·
                        rfl

theorem cell23_4844853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_4844853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844853 prefixEnd_4844853 := by exact prefixLift 4844853
  have htrace : WordTrace (prefixWord ++ tailWord_4844853) baseStart_4844853 baseEnd_4844853 := by
    simpa [prefixWord, tailWord_4844853, baseEnd_4844853] using wordTrace_append hprefix tailTrace_4844853
  have hstable : (prefixWord ++ tailWord_4844853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844853).length < 2 ^ (prefixWord ++ tailWord_4844853).sum := by decide
  have hdescent : baseEnd_4844853 < baseStart_4844853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844876 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 5, 2, 2]
def baseStart_4844876 : Nat := 118140960795 + 4844876 * 2 ^ 59
def prefixEnd_4844876 : Nat := 4983230072969 + 3 ^ 40 * 4844876 * 2
def baseEnd_4844876 : Nat := 2487750099432491634068827

theorem tailTrace_4844876 : CollatzResearch.WordTrace tailWord_4844876 prefixEnd_4844876 2487750099432491634068827 := by
  unfold tailWord_4844876
  simp only [CollatzResearch.WordTrace]
  refine ⟨88353572397924582895065241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117804763197232777193420321 88353572397924582895065241)
  ·
    refine ⟨66265179298443437171298931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88353572397924582895065241 66265179298443437171298931)
    ·
      refine ⟨99397768947665155756948397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66265179298443437171298931 99397768947665155756948397)
      ·
        refine ⟨37274163355374433408855649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99397768947665155756948397 37274163355374433408855649)
        ·
          refine ⟨27955622516530825056641737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37274163355374433408855649 27955622516530825056641737)
          ·
            refine ⟨20966716887398118792481303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27955622516530825056641737 20966716887398118792481303)
            ·
              refine ⟨31450075331097178188721955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20966716887398118792481303 31450075331097178188721955)
              ·
                refine ⟨47175112996645767283082933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31450075331097178188721955 47175112996645767283082933)
                ·
                  refine ⟨4422666843435540682789025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47175112996645767283082933 4422666843435540682789025)
                  ·
                    refine ⟨3317000132576655512091769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4422666843435540682789025 3317000132576655512091769)
                    ·
                      refine ⟨2487750099432491634068827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3317000132576655512091769 2487750099432491634068827)
                      ·
                        rfl

theorem cell23_4844876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_4844876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844876 prefixEnd_4844876 := by exact prefixLift 4844876
  have htrace : WordTrace (prefixWord ++ tailWord_4844876) baseStart_4844876 baseEnd_4844876 := by
    simpa [prefixWord, tailWord_4844876, baseEnd_4844876] using wordTrace_append hprefix tailTrace_4844876
  have hstable : (prefixWord ++ tailWord_4844876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844876).length < 2 ^ (prefixWord ++ tailWord_4844876).sum := by decide
  have hdescent : baseEnd_4844876 < baseStart_4844876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844896 : List Nat := [2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 3]
def baseStart_4844896 : Nat := 118140960795 + 4844896 * 2 ^ 59
def prefixEnd_4844896 : Nat := 4983230072969 + 3 ^ 40 * 4844896 * 2
def baseEnd_4844896 : Nat := 2487760369045581555818735

theorem tailTrace_4844896 : CollatzResearch.WordTrace tailWord_4844896 prefixEnd_4844896 2487760369045581555818735 := by
  unfold tailWord_4844896
  simp only [CollatzResearch.WordTrace]
  refine ⟨88353937127888354602929271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117805249503851139470572361 88353937127888354602929271)
  ·
    refine ⟨132530905691832531904393907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88353937127888354602929271 132530905691832531904393907)
    ·
      refine ⟨198796358537748797856590861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132530905691832531904393907 198796358537748797856590861)
      ·
        refine ⟨74548634451655799196221573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198796358537748797856590861 74548634451655799196221573)
        ·
          refine ⟨13977868959685462349291545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74548634451655799196221573 13977868959685462349291545)
          ·
            refine ⟨10483401719764096761968659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13977868959685462349291545 10483401719764096761968659)
            ·
              refine ⟨15725102579646145142952989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10483401719764096761968659 15725102579646145142952989)
              ·
                refine ⟨5896913467367304428607371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15725102579646145142952989 5896913467367304428607371)
                ·
                  refine ⟨8845370201050956642911057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5896913467367304428607371 8845370201050956642911057)
                  ·
                    refine ⟨6634027650788217482183293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8845370201050956642911057 6634027650788217482183293)
                    ·
                      refine ⟨2487760369045581555818735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6634027650788217482183293 2487760369045581555818735)
                      ·
                        rfl

theorem cell23_4844896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_4844896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844896 prefixEnd_4844896 := by exact prefixLift 4844896
  have htrace : WordTrace (prefixWord ++ tailWord_4844896) baseStart_4844896 baseEnd_4844896 := by
    simpa [prefixWord, tailWord_4844896, baseEnd_4844896] using wordTrace_append hprefix tailTrace_4844896
  have hstable : (prefixWord ++ tailWord_4844896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844896).length < 2 ^ (prefixWord ++ tailWord_4844896).sum := by decide
  have hdescent : baseEnd_4844896 < baseStart_4844896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844903 : List Nat := [1, 1, 5, 1, 4, 2, 1, 2, 2, 4]
def baseStart_4844903 : Nat := 118140960795 + 4844903 * 2 ^ 59
def prefixEnd_4844903 : Nat := 4983230072969 + 3 ^ 40 * 4844903 * 2
def baseEnd_4844903 : Nat := 829254654470054342810401

theorem tailTrace_4844903 : CollatzResearch.WordTrace tailWord_4844903 prefixEnd_4844903 829254654470054342810401 := by
  unfold tailWord_4844903
  simp only [CollatzResearch.WordTrace]
  refine ⟨176708129566751349401363363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117805419711167566267575575 176708129566751349401363363)
  ·
    refine ⟨265062194350127024102045045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176708129566751349401363363 265062194350127024102045045)
    ·
      refine ⟨24849580720324408509566723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 265062194350127024102045045 24849580720324408509566723)
      ·
        refine ⟨37274371080486612764350085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24849580720324408509566723 37274371080486612764350085)
        ·
          refine ⟨6988944577591239893315641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37274371080486612764350085 6988944577591239893315641)
          ·
            refine ⟨5241708433193429919986731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6988944577591239893315641 5241708433193429919986731)
            ·
              refine ⟨7862562649790144879980097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5241708433193429919986731 7862562649790144879980097)
              ·
                refine ⟨5896921987342608659985073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7862562649790144879980097 5896921987342608659985073)
                ·
                  refine ⟨4422691490506956494988805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5896921987342608659985073 4422691490506956494988805)
                  ·
                    refine ⟨829254654470054342810401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4422691490506956494988805 829254654470054342810401)
                    ·
                      rfl

theorem cell23_4844903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_4844903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844903 prefixEnd_4844903 := by exact prefixLift 4844903
  have htrace : WordTrace (prefixWord ++ tailWord_4844903) baseStart_4844903 baseEnd_4844903 := by
    simpa [prefixWord, tailWord_4844903, baseEnd_4844903] using wordTrace_append hprefix tailTrace_4844903
  have hstable : (prefixWord ++ tailWord_4844903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844903).length < 2 ^ (prefixWord ++ tailWord_4844903).sum := by decide
  have hdescent : baseEnd_4844903 < baseStart_4844903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844930 : List Nat := [3, 4, 2, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_4844930 : Nat := 118140960795 + 4844930 * 2 ^ 59
def prefixEnd_4844930 : Nat := 4983230072969 + 3 ^ 40 * 4844930 * 2
def baseEnd_4844930 : Nat := 2487777827387834422793579

theorem tailTrace_4844930 : CollatzResearch.WordTrace tailWord_4844930 prefixEnd_4844930 2487777827387834422793579 := by
  unfold tailWord_4844930
  simp only [CollatzResearch.WordTrace]
  refine ⟨44177278584413383253149061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117806076225102355341730829 44177278584413383253149061)
  ·
    refine ⟨8283239734577509359965449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44177278584413383253149061 8283239734577509359965449)
    ·
      refine ⟨6212429800933132019974087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8283239734577509359965449 6212429800933132019974087)
      ·
        refine ⟨9318644701399698029961131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6212429800933132019974087 9318644701399698029961131)
        ·
          refine ⟨13977967052099547044941697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9318644701399698029961131 13977967052099547044941697)
          ·
            refine ⟨10483475289074660283706273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13977967052099547044941697 10483475289074660283706273)
            ·
              refine ⟨7862606466805995212779705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10483475289074660283706273 7862606466805995212779705)
              ·
                refine ⟨5896954850104496409584779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7862606466805995212779705 5896954850104496409584779)
                ·
                  refine ⟨8845432275156744614377169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5896954850104496409584779 8845432275156744614377169)
                  ·
                    refine ⟨6634074206367558460782877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8845432275156744614377169 6634074206367558460782877)
                    ·
                      refine ⟨2487777827387834422793579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6634074206367558460782877 2487777827387834422793579)
                      ·
                        rfl

theorem cell23_4844930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_4844930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844930 prefixEnd_4844930 := by exact prefixLift 4844930
  have htrace : WordTrace (prefixWord ++ tailWord_4844930) baseStart_4844930 baseEnd_4844930 := by
    simpa [prefixWord, tailWord_4844930, baseEnd_4844930] using wordTrace_append hprefix tailTrace_4844930
  have hstable : (prefixWord ++ tailWord_4844930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844930).length < 2 ^ (prefixWord ++ tailWord_4844930).sum := by decide
  have hdescent : baseEnd_4844930 < baseStart_4844930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4844983 : List Nat := [1, 1, 3, 1, 3, 2, 3, 3, 2, 2, 2]
def baseStart_4844983 : Nat := 118140960795 + 4844983 * 2 ^ 59
def prefixEnd_4844983 : Nat := 4983230072969 + 3 ^ 40 * 4844983 * 2
def baseEnd_4844983 : Nat := 2487805041862522715430835

theorem tailTrace_4844983 : CollatzResearch.WordTrace tailWord_4844983 prefixEnd_4844983 2487805041862522715430835 := by
  unfold tailWord_4844983
  simp only [CollatzResearch.WordTrace]
  refine ⟨176711047406461523064275603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117807364937641015376183735 176711047406461523064275603)
  ·
    refine ⟨265066571109692284596413405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176711047406461523064275603 265066571109692284596413405)
    ·
      refine ⟨99399964166134606723655027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 265066571109692284596413405 99399964166134606723655027)
      ·
        refine ⟨149099946249201910085482541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99399964166134606723655027 149099946249201910085482541)
        ·
          refine ⟨55912479843450716282055953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149099946249201910085482541 55912479843450716282055953)
          ·
            refine ⟨41934359882588037211541965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55912479843450716282055953 41934359882588037211541965)
            ·
              refine ⟨15725384955970513954328237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41934359882588037211541965 15725384955970513954328237)
              ·
                refine ⟨5897019358488942732873089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15725384955970513954328237 5897019358488942732873089)
                ·
                  refine ⟨4422764518866707049654817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5897019358488942732873089 4422764518866707049654817)
                  ·
                    refine ⟨3317073389150030287241113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4422764518866707049654817 3317073389150030287241113)
                    ·
                      refine ⟨2487805041862522715430835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3317073389150030287241113 2487805041862522715430835)
                      ·
                        rfl

theorem cell23_4844983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 2, 2, 2].length) (baseStart_4844983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4844983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4844983 prefixEnd_4844983 := by exact prefixLift 4844983
  have htrace : WordTrace (prefixWord ++ tailWord_4844983) baseStart_4844983 baseEnd_4844983 := by
    simpa [prefixWord, tailWord_4844983, baseEnd_4844983] using wordTrace_append hprefix tailTrace_4844983
  have hstable : (prefixWord ++ tailWord_4844983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4844983).length < 2 ^ (prefixWord ++ tailWord_4844983).sum := by decide
  have hdescent : baseEnd_4844983 < baseStart_4844983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4844983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845039 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 4]
def baseStart_4845039 : Nat := 118140960795 + 4845039 * 2 ^ 59
def prefixEnd_4845039 : Nat := 4983230072969 + 3 ^ 40 * 4845039 * 2
def baseEnd_4845039 : Nat := 2487833796779174496330577

theorem tailTrace_4845039 : CollatzResearch.WordTrace tailWord_4845039 prefixEnd_4845039 2487833796779174496330577 := by
  unfold tailWord_4845039
  simp only [CollatzResearch.WordTrace]
  refine ⟨176713089894258644628314171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117808726596172429752209447 176713089894258644628314171)
  ·
    refine ⟨265069634841387966942471257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176713089894258644628314171 265069634841387966942471257)
    ·
      refine ⟨198802226131040975206853443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265069634841387966942471257 198802226131040975206853443)
      ·
        refine ⟨298203339196561462810280165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198802226131040975206853443 298203339196561462810280165)
        ·
          refine ⟨55913126099355274276927531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 298203339196561462810280165 55913126099355274276927531)
          ·
            refine ⟨83869689149032911415391297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55913126099355274276927531 83869689149032911415391297)
            ·
              refine ⟨62902266861774683561543473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83869689149032911415391297 62902266861774683561543473)
              ·
                refine ⟨47176700146331012671157605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62902266861774683561543473 47176700146331012671157605)
                ·
                  refine ⟨8845631277437064875842051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47176700146331012671157605 8845631277437064875842051)
                  ·
                    refine ⟨13268446916155597313763077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8845631277437064875842051 13268446916155597313763077)
                    ·
                      refine ⟨2487833796779174496330577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13268446916155597313763077 2487833796779174496330577)
                      ·
                        rfl

theorem cell23_4845039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 4].length) (baseStart_4845039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845039 prefixEnd_4845039 := by exact prefixLift 4845039
  have htrace : WordTrace (prefixWord ++ tailWord_4845039) baseStart_4845039 baseEnd_4845039 := by
    simpa [prefixWord, tailWord_4845039, baseEnd_4845039] using wordTrace_append hprefix tailTrace_4845039
  have hstable : (prefixWord ++ tailWord_4845039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845039).length < 2 ^ (prefixWord ++ tailWord_4845039).sum := by decide
  have hdescent : baseEnd_4845039 < baseStart_4845039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845117 : List Nat := [1, 4, 1, 3, 3, 2, 1, 3, 1, 4]
def baseStart_4845117 : Nat := 118140960795 + 4845117 * 2 ^ 59
def prefixEnd_4845117 : Nat := 4983230072969 + 3 ^ 40 * 4845117 * 2
def baseEnd_4845117 : Nat := 829291282756741730385073

theorem tailTrace_4845117 : CollatzResearch.WordTrace tailWord_4845117 prefixEnd_4845117 829291282756741730385073 := by
  unfold tailWord_4845117
  simp only [CollatzResearch.WordTrace]
  refine ⟨176715934787976063949653605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117810623191984042633102403 176715934787976063949653605)
  ·
    refine ⟨33134237772745511990560051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176715934787976063949653605 33134237772745511990560051)
    ·
      refine ⟨49701356659118267985840077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33134237772745511990560051 49701356659118267985840077)
      ·
        refine ⟨18638008747169350494690029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49701356659118267985840077 18638008747169350494690029)
        ·
          refine ⟨6989253280188506435508761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18638008747169350494690029 6989253280188506435508761)
          ·
            refine ⟨5241939960141379826631571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6989253280188506435508761 5241939960141379826631571)
            ·
              refine ⟨7862909940212069739947357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5241939960141379826631571 7862909940212069739947357)
              ·
                refine ⟨2948591227579526152480259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7862909940212069739947357 2948591227579526152480259)
                ·
                  refine ⟨4422886841369289228720389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2948591227579526152480259 4422886841369289228720389)
                  ·
                    refine ⟨829291282756741730385073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4422886841369289228720389 829291282756741730385073)
                    ·
                      rfl

theorem cell23_4845117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 3, 1, 4].length) (baseStart_4845117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845117 prefixEnd_4845117 := by exact prefixLift 4845117
  have htrace : WordTrace (prefixWord ++ tailWord_4845117) baseStart_4845117 baseEnd_4845117 := by
    simpa [prefixWord, tailWord_4845117, baseEnd_4845117] using wordTrace_append hprefix tailTrace_4845117
  have hstable : (prefixWord ++ tailWord_4845117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845117).length < 2 ^ (prefixWord ++ tailWord_4845117).sum := by decide
  have hdescent : baseEnd_4845117 < baseStart_4845117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845160 : List Nat := [2, 1, 4, 3, 1, 3, 1, 2, 1, 5]
def baseStart_4845160 : Nat := 118140960795 + 4845160 * 2 ^ 59
def prefixEnd_4845160 : Nat := 4983230072969 + 3 ^ 40 * 4845160 * 2
def baseEnd_4845160 : Nat := 829298642646122840972507

theorem tailTrace_4845160 : CollatzResearch.WordTrace tailWord_4845160 prefixEnd_4845160 829298642646122840972507 := by
  unfold tailWord_4845160
  simp only [CollatzResearch.WordTrace]
  refine ⟨88358751563410141146734467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117811668751213521528979289 88358751563410141146734467)
  ·
    refine ⟨132538127345115211720101701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88358751563410141146734467 132538127345115211720101701)
    ·
      refine ⟨24850898877209102197519069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132538127345115211720101701 24850898877209102197519069)
      ·
        refine ⟨9319087078953413324069651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24850898877209102197519069 9319087078953413324069651)
        ·
          refine ⟨13978630618430119986104477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9319087078953413324069651 13978630618430119986104477)
          ·
            refine ⟨5241986481911294994789179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13978630618430119986104477 5241986481911294994789179)
            ·
              refine ⟨7862979722866942492183769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5241986481911294994789179 7862979722866942492183769)
              ·
                refine ⟨5897234792150206869137827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7862979722866942492183769 5897234792150206869137827)
                ·
                  refine ⟨8845852188225310303706741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5897234792150206869137827 8845852188225310303706741)
                  ·
                    refine ⟨829298642646122840972507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8845852188225310303706741 829298642646122840972507)
                    ·
                      rfl

theorem cell23_4845160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_4845160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845160 prefixEnd_4845160 := by exact prefixLift 4845160
  have htrace : WordTrace (prefixWord ++ tailWord_4845160) baseStart_4845160 baseEnd_4845160 := by
    simpa [prefixWord, tailWord_4845160, baseEnd_4845160] using wordTrace_append hprefix tailTrace_4845160
  have hstable : (prefixWord ++ tailWord_4845160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845160).length < 2 ^ (prefixWord ++ tailWord_4845160).sum := by decide
  have hdescent : baseEnd_4845160 < baseStart_4845160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845173 : List Nat := [1, 3, 4, 2, 1, 2, 1, 2, 1, 6]
def baseStart_4845173 : Nat := 118140960795 + 4845173 * 2 ^ 59
def prefixEnd_4845173 : Nat := 4983230072969 + 3 ^ 40 * 4845173 * 2
def baseEnd_4845173 : Nat := 829300867728958990684987

theorem tailTrace_4845173 : CollatzResearch.WordTrace tailWord_4845173 prefixEnd_4845173 829300867728958990684987 := by
  unfold tailWord_4845173
  simp only [CollatzResearch.WordTrace]
  refine ⟨176717977275773185513692173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117811984850515457009128115 176717977275773185513692173)
  ·
    refine ⟨66269241478414944567634565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176717977275773185513692173 66269241478414944567634565)
    ·
      refine ⟨12425482777202802106431481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66269241478414944567634565 12425482777202802106431481)
      ·
        refine ⟨9319112082902101579823611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12425482777202802106431481 9319112082902101579823611)
        ·
          refine ⟨13978668124353152369735417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9319112082902101579823611 13978668124353152369735417)
          ·
            refine ⟨10484001093264864277301563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13978668124353152369735417 10484001093264864277301563)
            ·
              refine ⟨15726001639897296415952345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10484001093264864277301563 15726001639897296415952345)
              ·
                refine ⟨11794501229922972311964259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15726001639897296415952345 11794501229922972311964259)
                ·
                  refine ⟨17691751844884458467946389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11794501229922972311964259 17691751844884458467946389)
                  ·
                    refine ⟨829300867728958990684987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17691751844884458467946389 829300867728958990684987)
                    ·
                      rfl

theorem cell23_4845173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_4845173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845173 prefixEnd_4845173 := by exact prefixLift 4845173
  have htrace : WordTrace (prefixWord ++ tailWord_4845173) baseStart_4845173 baseEnd_4845173 := by
    simpa [prefixWord, tailWord_4845173, baseEnd_4845173] using wordTrace_append hprefix tailTrace_4845173
  have hstable : (prefixWord ++ tailWord_4845173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845173).length < 2 ^ (prefixWord ++ tailWord_4845173).sum := by decide
  have hdescent : baseEnd_4845173 < baseStart_4845173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845196 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 3, 3, 3]
def baseStart_4845196 : Nat := 118140960795 + 4845196 * 2 ^ 59
def prefixEnd_4845196 : Nat := 4983230072969 + 3 ^ 40 * 4845196 * 2
def baseEnd_4845196 : Nat := 2487914413241930382067355

theorem tailTrace_4845196 : CollatzResearch.WordTrace tailWord_4845196 prefixEnd_4845196 2487914413241930382067355 := by
  unfold tailWord_4845196
  simp only [CollatzResearch.WordTrace]
  refine ⟨88359408077344930220889721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117812544103126573627852961 88359408077344930220889721)
  ·
    refine ⟨66269556058008697665667291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88359408077344930220889721 66269556058008697665667291)
    ·
      refine ⟨99404334087013046498500937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66269556058008697665667291 99404334087013046498500937)
      ·
        refine ⟨74553250565259784873875703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99404334087013046498500937 74553250565259784873875703)
        ·
          refine ⟨111829875847889677310813555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74553250565259784873875703 111829875847889677310813555)
          ·
            refine ⟨167744813771834515966220333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111829875847889677310813555 167744813771834515966220333)
            ·
              refine ⟨62904305164437943487332625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167744813771834515966220333 62904305164437943487332625)
              ·
                refine ⟨47178228873328457615499469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62904305164437943487332625 47178228873328457615499469)
                ·
                  refine ⟨17691835827498171605812301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47178228873328457615499469 17691835827498171605812301)
                  ·
                    refine ⟨6634438435311814352179613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17691835827498171605812301 6634438435311814352179613)
                    ·
                      refine ⟨2487914413241930382067355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6634438435311814352179613 2487914413241930382067355)
                      ·
                        rfl

theorem cell23_4845196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_4845196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845196 prefixEnd_4845196 := by exact prefixLift 4845196
  have htrace : WordTrace (prefixWord ++ tailWord_4845196) baseStart_4845196 baseEnd_4845196 := by
    simpa [prefixWord, tailWord_4845196, baseEnd_4845196] using wordTrace_append hprefix tailTrace_4845196
  have hstable : (prefixWord ++ tailWord_4845196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845196).length < 2 ^ (prefixWord ++ tailWord_4845196).sum := by decide
  have hdescent : baseEnd_4845196 < baseStart_4845196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845213 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 6, 1, 3]
def baseStart_4845213 : Nat := 118140960795 + 4845213 * 2 ^ 59
def prefixEnd_4845213 : Nat := 4983230072969 + 3 ^ 40 * 4845213 * 2
def baseEnd_4845213 : Nat := 2487923142413056815554777

theorem tailTrace_4845213 : CollatzResearch.WordTrace tailWord_4845213 prefixEnd_4845213 2487923142413056815554777 := by
  unfold tailWord_4845213
  simp only [CollatzResearch.WordTrace]
  refine ⟨176719436195628272345148293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117812957463752181563432195 176719436195628272345148293)
  ·
    refine ⟨33134894286680301064715305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176719436195628272345148293 33134894286680301064715305)
    ·
      refine ⟨24851170715010225798536479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33134894286680301064715305 24851170715010225798536479)
      ·
        refine ⟨37276756072515338697804719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24851170715010225798536479 37276756072515338697804719)
        ·
          refine ⟨55915134108773008046707079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37276756072515338697804719 55915134108773008046707079)
          ·
            refine ⟨83872701163159512070060619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55915134108773008046707079 83872701163159512070060619)
            ·
              refine ⟨125809051744739268105090929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83872701163159512070060619 125809051744739268105090929)
              ·
                refine ⟨94356788808554451078818197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125809051744739268105090929 94356788808554451078818197)
                ·
                  refine ⟨4422974475400989894319603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 94356788808554451078818197 4422974475400989894319603)
                  ·
                    refine ⟨6634461713101484841479405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4422974475400989894319603 6634461713101484841479405)
                    ·
                      refine ⟨2487923142413056815554777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6634461713101484841479405 2487923142413056815554777)
                      ·
                        rfl

theorem cell23_4845213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_4845213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845213 prefixEnd_4845213 := by exact prefixLift 4845213
  have htrace : WordTrace (prefixWord ++ tailWord_4845213) baseStart_4845213 baseEnd_4845213 := by
    simpa [prefixWord, tailWord_4845213, baseEnd_4845213] using wordTrace_append hprefix tailTrace_4845213
  have hstable : (prefixWord ++ tailWord_4845213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845213).length < 2 ^ (prefixWord ++ tailWord_4845213).sum := by decide
  have hdescent : baseEnd_4845213 < baseStart_4845213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845325 : List Nat := [1, 7, 2, 1, 1, 2, 1, 2, 1, 3, 2]
def baseStart_4845325 : Nat := 118140960795 + 4845325 * 2 ^ 59
def prefixEnd_4845325 : Nat := 4983230072969 + 3 ^ 40 * 4845325 * 2
def baseEnd_4845325 : Nat := 2487980652246360377354263

theorem tailTrace_4845325 : CollatzResearch.WordTrace tailWord_4845325 prefixEnd_4845325 2487980652246360377354263 := by
  unfold tailWord_4845325
  simp only [CollatzResearch.WordTrace]
  refine ⟨176723521171222515473225429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117815680780815010315483619 176723521171222515473225429)
  ·
    refine ⟨4141957527450527706403721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 176723521171222515473225429 4141957527450527706403721)
    ·
      refine ⟨3106468145587895779802791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4141957527450527706403721 3106468145587895779802791)
      ·
        refine ⟨4659702218381843669704187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3106468145587895779802791 4659702218381843669704187)
        ·
          refine ⟨6989553327572765504556281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4659702218381843669704187 6989553327572765504556281)
          ·
            refine ⟨5242164995679574128417211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6989553327572765504556281 5242164995679574128417211)
            ·
              refine ⟨7863247493519361192625817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5242164995679574128417211 7863247493519361192625817)
              ·
                refine ⟨5897435620139520894469363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7863247493519361192625817 5897435620139520894469363)
                ·
                  refine ⟨8846153430209281341704045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5897435620139520894469363 8846153430209281341704045)
                  ·
                    refine ⟨3317307536328480503139017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8846153430209281341704045 3317307536328480503139017)
                    ·
                      refine ⟨2487980652246360377354263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3317307536328480503139017 2487980652246360377354263)
                      ·
                        rfl

theorem cell23_4845325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_4845325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845325 prefixEnd_4845325 := by exact prefixLift 4845325
  have htrace : WordTrace (prefixWord ++ tailWord_4845325) baseStart_4845325 baseEnd_4845325 := by
    simpa [prefixWord, tailWord_4845325, baseEnd_4845325] using wordTrace_append hprefix tailTrace_4845325
  have hstable : (prefixWord ++ tailWord_4845325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845325).length < 2 ^ (prefixWord ++ tailWord_4845325).sum := by decide
  have hdescent : baseEnd_4845325 < baseStart_4845325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845336 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 2, 8]
def baseStart_4845336 : Nat := 118140960795 + 4845336 * 2 ^ 59
def prefixEnd_4845336 : Nat := 4983230072969 + 3 ^ 40 * 4845336 * 2
def baseEnd_4845336 : Nat := 829328766844519944772237

theorem tailTrace_4845336 : CollatzResearch.WordTrace tailWord_4845336 prefixEnd_4845336 829328766844519944772237 := by
  unfold tailWord_4845336
  simp only [CollatzResearch.WordTrace]
  refine ⟨88361961187091332175937931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117815948249455109567917241 88361961187091332175937931)
  ·
    refine ⟨132542941780636998263906897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88361961187091332175937931 132542941780636998263906897)
    ·
      refine ⟨99407206335477748697930173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132542941780636998263906897 99407206335477748697930173)
      ·
        refine ⟨37277702375804155761723815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99407206335477748697930173 37277702375804155761723815)
        ·
          refine ⟨55916553563706233642585723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37277702375804155761723815 55916553563706233642585723)
          ·
            refine ⟨83874830345559350463878585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55916553563706233642585723 83874830345559350463878585)
            ·
              refine ⟨62906122759169512847908939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83874830345559350463878585 62906122759169512847908939)
              ·
                refine ⟨94359184138754269271863409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62906122759169512847908939 94359184138754269271863409)
                ·
                  refine ⟨70769388104065701953897557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94359184138754269271863409 70769388104065701953897557)
                  ·
                    refine ⟨829328766844519944772237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70769388104065701953897557 829328766844519944772237)
                    ·
                      rfl

theorem cell23_4845336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 2, 8].length) (baseStart_4845336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845336 prefixEnd_4845336 := by exact prefixLift 4845336
  have htrace : WordTrace (prefixWord ++ tailWord_4845336) baseStart_4845336 baseEnd_4845336 := by
    simpa [prefixWord, tailWord_4845336, baseEnd_4845336] using wordTrace_append hprefix tailTrace_4845336
  have hstable : (prefixWord ++ tailWord_4845336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845336).length < 2 ^ (prefixWord ++ tailWord_4845336).sum := by decide
  have hdescent : baseEnd_4845336 < baseStart_4845336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845383 : List Nat := [1, 1, 4, 1, 2, 1, 4, 3, 6]
def baseStart_4845383 : Nat := 118140960795 + 4845383 * 2 ^ 59
def prefixEnd_4845383 : Nat := 4983230072969 + 3 ^ 40 * 4845383 * 2
def baseEnd_4845383 : Nat := 276445603791591238936555

theorem tailTrace_4845383 : CollatzResearch.WordTrace tailWord_4845383 prefixEnd_4845383 276445603791591238936555 := by
  unfold tailWord_4845383
  simp only [CollatzResearch.WordTrace]
  refine ⟨176725636605012391378836803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117817091070008260919224535 176725636605012391378836803)
  ·
    refine ⟨265088454907518587068255205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176725636605012391378836803 265088454907518587068255205)
    ·
      refine ⟨49704085295159735075297851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 265088454907518587068255205 49704085295159735075297851)
      ·
        refine ⟨74556127942739602612946777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49704085295159735075297851 74556127942739602612946777)
        ·
          refine ⟨55917095957054701959710083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74556127942739602612946777 55917095957054701959710083)
          ·
            refine ⟨83875643935582052939565125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55917095957054701959710083 83875643935582052939565125)
            ·
              refine ⟨15726683237921634926168461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83875643935582052939565125 15726683237921634926168461)
              ·
                refine ⟨5897506214220613097313173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15726683237921634926168461 5897506214220613097313173)
                ·
                  refine ⟨276445603791591238936555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5897506214220613097313173 276445603791591238936555)
                  ·
                    rfl

theorem cell23_4845383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 6].length) (baseStart_4845383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845383 prefixEnd_4845383 := by exact prefixLift 4845383
  have htrace : WordTrace (prefixWord ++ tailWord_4845383) baseStart_4845383 baseEnd_4845383 := by
    simpa [prefixWord, tailWord_4845383, baseEnd_4845383] using wordTrace_append hprefix tailTrace_4845383
  have hstable : (prefixWord ++ tailWord_4845383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845383).length < 2 ^ (prefixWord ++ tailWord_4845383).sum := by decide
  have hdescent : baseEnd_4845383 < baseStart_4845383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845397 : List Nat := [1, 3, 2, 2, 2, 4, 1, 1, 2, 2, 3]
def baseStart_4845397 : Nat := 118140960795 + 4845397 * 2 ^ 59
def prefixEnd_4845397 : Nat := 4983230072969 + 3 ^ 40 * 4845397 * 2
def baseEnd_4845397 : Nat := 2488017622853484095653931

theorem tailTrace_4845397 : CollatzResearch.WordTrace tailWord_4845397 prefixEnd_4845397 2488017622853484095653931 := by
  unfold tailWord_4845397
  simp only [CollatzResearch.WordTrace]
  refine ⟨176726147226961671769846445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117817431484641114513230963 176726147226961671769846445)
  ·
    refine ⟨66272305210110626913692417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 176726147226961671769846445 66272305210110626913692417)
    ·
      refine ⟨49704228907582970185269313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66272305210110626913692417 49704228907582970185269313)
      ·
        refine ⟨37278171680687227638951985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49704228907582970185269313 37278171680687227638951985)
        ·
          refine ⟨27958628760515420729213989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37278171680687227638951985 27958628760515420729213989)
          ·
            refine ⟨5242242892596641386727623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27958628760515420729213989 5242242892596641386727623)
            ·
              refine ⟨7863364338894962080091435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5242242892596641386727623 7863364338894962080091435)
              ·
                refine ⟨11795046508342443120137153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7863364338894962080091435 11795046508342443120137153)
                ·
                  refine ⟨8846284881256832340102865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11795046508342443120137153 8846284881256832340102865)
                  ·
                    refine ⟨6634713660942624255077149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8846284881256832340102865 6634713660942624255077149)
                    ·
                      refine ⟨2488017622853484095653931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6634713660942624255077149 2488017622853484095653931)
                      ·
                        rfl

theorem cell23_4845397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_4845397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845397 prefixEnd_4845397 := by exact prefixLift 4845397
  have htrace : WordTrace (prefixWord ++ tailWord_4845397) baseStart_4845397 baseEnd_4845397 := by
    simpa [prefixWord, tailWord_4845397, baseEnd_4845397] using wordTrace_append hprefix tailTrace_4845397
  have hstable : (prefixWord ++ tailWord_4845397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845397).length < 2 ^ (prefixWord ++ tailWord_4845397).sum := by decide
  have hdescent : baseEnd_4845397 < baseStart_4845397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845447 : List Nat := [1, 1, 4, 2, 4, 1, 2, 2, 1, 5]
def baseStart_4845447 : Nat := 118140960795 + 4845447 * 2 ^ 59
def prefixEnd_4845447 : Nat := 4983230072969 + 3 ^ 40 * 4845447 * 2
def baseEnd_4845447 : Nat := 829347765628736300009567

theorem tailTrace_4845447 : CollatzResearch.WordTrace tailWord_4845447 prefixEnd_4845447 829347765628736300009567 := by
  unfold tailWord_4845447
  simp only [CollatzResearch.WordTrace]
  refine ⟨176727970876780530309166595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117818647251187020206111063 176727970876780530309166595)
  ·
    refine ⟨265091956315170795463749893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176727970876780530309166595 265091956315170795463749893)
    ·
      refine ⟨49704741809094524149453105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 265091956315170795463749893 49704741809094524149453105)
      ·
        refine ⟨37278556356820893112089829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49704741809094524149453105 37278556356820893112089829)
        ·
          refine ⟨6989729316903917458516843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37278556356820893112089829 6989729316903917458516843)
          ·
            refine ⟨10484593975355876187775265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6989729316903917458516843 10484593975355876187775265)
            ·
              refine ⟨7863445481516907140831449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10484593975355876187775265 7863445481516907140831449)
              ·
                refine ⟨5897584111137680355623587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7863445481516907140831449 5897584111137680355623587)
                ·
                  refine ⟨8846376166706520533435381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5897584111137680355623587 8846376166706520533435381)
                  ·
                    refine ⟨829347765628736300009567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8846376166706520533435381 829347765628736300009567)
                    ·
                      rfl

theorem cell23_4845447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_4845447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845447 prefixEnd_4845447 := by exact prefixLift 4845447
  have htrace : WordTrace (prefixWord ++ tailWord_4845447) baseStart_4845447 baseEnd_4845447 := by
    simpa [prefixWord, tailWord_4845447, baseEnd_4845447] using wordTrace_append hprefix tailTrace_4845447
  have hstable : (prefixWord ++ tailWord_4845447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845447).length < 2 ^ (prefixWord ++ tailWord_4845447).sum := by decide
  have hdescent : baseEnd_4845447 < baseStart_4845447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845483 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 2, 7, 3]
def baseStart_4845483 : Nat := 118140960795 + 4845483 * 2 ^ 59
def prefixEnd_4845483 : Nat := 4983230072969 + 3 ^ 40 * 4845483 * 2
def baseEnd_4845483 : Nat := 2488061782189770759178535

theorem tailTrace_4845483 : CollatzResearch.WordTrace tailWord_4845483 prefixEnd_4845483 2488061782189770759178535 := by
  unfold tailWord_4845483
  simp only [CollatzResearch.WordTrace]
  refine ⟨176729283904650108457477103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117819522603100072304984735 176729283904650108457477103)
  ·
    refine ⟨265093925856975162686215655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176729283904650108457477103 265093925856975162686215655)
    ·
      refine ⟨397640888785462744029323483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265093925856975162686215655 397640888785462744029323483)
      ·
        refine ⟨596461333178194116043985225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397640888785462744029323483 596461333178194116043985225)
        ·
          refine ⟨447345999883645587032988919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 596461333178194116043985225 447345999883645587032988919)
          ·
            refine ⟨671018999825468380549483379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447345999883645587032988919 671018999825468380549483379)
            ·
              refine ⟨1006528499738202570824225069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 671018999825468380549483379 1006528499738202570824225069)
              ·
                refine ⟨377448187401825964059084401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1006528499738202570824225069 377448187401825964059084401)
                ·
                  refine ⟨283086140551369473044313301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 377448187401825964059084401 283086140551369473044313301)
                  ·
                    refine ⟨6634831419172722024476093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 283086140551369473044313301 6634831419172722024476093)
                    ·
                      refine ⟨2488061782189770759178535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6634831419172722024476093 2488061782189770759178535)
                      ·
                        rfl

theorem cell23_4845483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 7, 3].length) (baseStart_4845483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845483 prefixEnd_4845483 := by exact prefixLift 4845483
  have htrace : WordTrace (prefixWord ++ tailWord_4845483) baseStart_4845483 baseEnd_4845483 := by
    simpa [prefixWord, tailWord_4845483, baseEnd_4845483] using wordTrace_append hprefix tailTrace_4845483
  have hstable : (prefixWord ++ tailWord_4845483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845483).length < 2 ^ (prefixWord ++ tailWord_4845483).sum := by decide
  have hdescent : baseEnd_4845483 < baseStart_4845483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845550 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 1, 8]
def baseStart_4845550 : Nat := 118140960795 + 4845550 * 2 ^ 59
def prefixEnd_4845550 : Nat := 4983230072969 + 3 ^ 40 * 4845550 * 2
def baseEnd_4845550 : Nat := 829365395131207332346909

theorem tailTrace_4845550 : CollatzResearch.WordTrace tailWord_4845550 prefixEnd_4845550 829365395131207332346909 := by
  unfold tailWord_4845550
  simp only [CollatzResearch.WordTrace]
  refine ⟨22091465949425922362520763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 117821151730271585933444069 22091465949425922362520763)
  ·
    refine ⟨33137198924138883543781145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22091465949425922362520763 33137198924138883543781145)
    ·
      refine ⟨24852899193104162657835859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33137198924138883543781145 24852899193104162657835859)
      ·
        refine ⟨37279348789656243986753789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24852899193104162657835859 37279348789656243986753789)
        ·
          refine ⟨13979755796121091495032671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37279348789656243986753789 13979755796121091495032671)
          ·
            refine ⟨20969633694181637242549007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13979755796121091495032671 20969633694181637242549007)
            ·
              refine ⟨31454450541272455863823511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20969633694181637242549007 31454450541272455863823511)
              ·
                refine ⟨47181675811908683795735267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31454450541272455863823511 47181675811908683795735267)
                ·
                  refine ⟨70772513717863025693602901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47181675811908683795735267 70772513717863025693602901)
                  ·
                    refine ⟨829365395131207332346909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 70772513717863025693602901 829365395131207332346909)
                    ·
                      rfl

theorem cell23_4845550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_4845550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845550 prefixEnd_4845550 := by exact prefixLift 4845550
  have htrace : WordTrace (prefixWord ++ tailWord_4845550) baseStart_4845550 baseEnd_4845550 := by
    simpa [prefixWord, tailWord_4845550, baseEnd_4845550] using wordTrace_append hprefix tailTrace_4845550
  have hstable : (prefixWord ++ tailWord_4845550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845550).length < 2 ^ (prefixWord ++ tailWord_4845550).sum := by decide
  have hdescent : baseEnd_4845550 < baseStart_4845550 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845563 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 9]
def baseStart_4845563 : Nat := 118140960795 + 4845563 * 2 ^ 59
def prefixEnd_4845563 : Nat := 4983230072969 + 3 ^ 40 * 4845563 * 2
def baseEnd_4845563 : Nat := 276455873404681160686463

theorem tailTrace_4845563 : CollatzResearch.WordTrace tailWord_4845563 prefixEnd_4845563 276455873404681160686463 := by
  unfold tailWord_4845563
  simp only [CollatzResearch.WordTrace]
  refine ⟨176732201744360282120389343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117821467829573521413592895 176732201744360282120389343)
  ·
    refine ⟨265098302616540423180584015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176732201744360282120389343 265098302616540423180584015)
    ·
      refine ⟨397647453924810634770876023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265098302616540423180584015 397647453924810634770876023)
      ·
        refine ⟨596471180887215952156314035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397647453924810634770876023 596471180887215952156314035)
        ·
          refine ⟨894706771330823928234471053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 596471180887215952156314035 894706771330823928234471053)
          ·
            refine ⟨335515039249058973087926645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 894706771330823928234471053 335515039249058973087926645)
            ·
              refine ⟨31454534929599278726993123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 335515039249058973087926645 31454534929599278726993123)
              ·
                refine ⟨47181802394398918090489685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31454534929599278726993123 47181802394398918090489685)
                ·
                  refine ⟨276455873404681160686463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47181802394398918090489685 276455873404681160686463)
                  ·
                    rfl

theorem cell23_4845563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 9].length) (baseStart_4845563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845563 prefixEnd_4845563 := by exact prefixLift 4845563
  have htrace : WordTrace (prefixWord ++ tailWord_4845563) baseStart_4845563 baseEnd_4845563 := by
    simpa [prefixWord, tailWord_4845563, baseEnd_4845563] using wordTrace_append hprefix tailTrace_4845563
  have hstable : (prefixWord ++ tailWord_4845563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845563).length < 2 ^ (prefixWord ++ tailWord_4845563).sum := by decide
  have hdescent : baseEnd_4845563 < baseStart_4845563 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845578 : List Nat := [3, 1, 2, 2, 4, 2, 2, 1, 1, 3, 2]
def baseStart_4845578 : Nat := 118140960795 + 4845578 * 2 ^ 59
def prefixEnd_4845578 : Nat := 4983230072969 + 3 ^ 40 * 4845578 * 2
def baseEnd_4845578 : Nat := 2488110562851947887490599

theorem tailTrace_4845578 : CollatzResearch.WordTrace tailWord_4845578 prefixEnd_4845578 2488110562851947887490599 := by
  unfold tailWord_4845578
  simp only [CollatzResearch.WordTrace]
  refine ⟨44183187209826484920546347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 117821832559537293121456925 44183187209826484920546347)
  ·
    refine ⟨66274780814739727380819521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44183187209826484920546347 66274780814739727380819521)
    ·
      refine ⟨49706085611054795535614641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66274780814739727380819521 49706085611054795535614641)
      ·
        refine ⟨37279564208291096651710981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49706085611054795535614641 37279564208291096651710981)
        ·
          refine ⟨6989918289054580622195809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37279564208291096651710981 6989918289054580622195809)
          ·
            refine ⟨5242438716790935466646857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6989918289054580622195809 5242438716790935466646857)
            ·
              refine ⟨3931829037593201599985143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5242438716790935466646857 3931829037593201599985143)
              ·
                refine ⟨5897743556389802399977715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3931829037593201599985143 5897743556389802399977715)
                ·
                  refine ⟨8846615334584703599966573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5897743556389802399977715 8846615334584703599966573)
                  ·
                    refine ⟨3317480750469263849987465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8846615334584703599966573 3317480750469263849987465)
                    ·
                      refine ⟨2488110562851947887490599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3317480750469263849987465 2488110562851947887490599)
                      ·
                        rfl

theorem cell23_4845578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_4845578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845578 prefixEnd_4845578 := by exact prefixLift 4845578
  have htrace : WordTrace (prefixWord ++ tailWord_4845578) baseStart_4845578 baseEnd_4845578 := by
    simpa [prefixWord, tailWord_4845578, baseEnd_4845578] using wordTrace_append hprefix tailTrace_4845578
  have hstable : (prefixWord ++ tailWord_4845578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845578).length < 2 ^ (prefixWord ++ tailWord_4845578).sum := by decide
  have hdescent : baseEnd_4845578 < baseStart_4845578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845583 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 6]
def baseStart_4845583 : Nat := 118140960795 + 4845583 * 2 ^ 59
def prefixEnd_4845583 : Nat := 4983230072969 + 3 ^ 40 * 4845583 * 2
def baseEnd_4845583 : Nat := 2488113130255220367928075

theorem tailTrace_4845583 : CollatzResearch.WordTrace tailWord_4845583 prefixEnd_4845583 2488113130255220367928075 := by
  unfold tailWord_4845583
  simp only [CollatzResearch.WordTrace]
  refine ⟨176732931204287825536117403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117821954136191883690744935 176732931204287825536117403)
  ·
    refine ⟨265099396806431738304176105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176732931204287825536117403 265099396806431738304176105)
    ·
      refine ⟨198824547604823803728132079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265099396806431738304176105 198824547604823803728132079)
      ·
        refine ⟨298236821407235705592198119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198824547604823803728132079 298236821407235705592198119)
        ·
          refine ⟨447355232110853558388297179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298236821407235705592198119 447355232110853558388297179)
          ·
            refine ⟨671032848166280337582445769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447355232110853558388297179 671032848166280337582445769)
            ·
              refine ⟨503274636124710253186834327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 671032848166280337582445769 503274636124710253186834327)
              ·
                refine ⟨754911954187065379780251491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 503274636124710253186834327 754911954187065379780251491)
                ·
                  refine ⟨1132367931280598069670377237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 754911954187065379780251491 1132367931280598069670377237)
                  ·
                    refine ⟨53079746778778034515798933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1132367931280598069670377237 53079746778778034515798933)
                    ·
                      refine ⟨2488113130255220367928075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53079746778778034515798933 2488113130255220367928075)
                      ·
                        rfl

theorem cell23_4845583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 6].length) (baseStart_4845583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845583 prefixEnd_4845583 := by exact prefixLift 4845583
  have htrace : WordTrace (prefixWord ++ tailWord_4845583) baseStart_4845583 baseEnd_4845583 := by
    simpa [prefixWord, tailWord_4845583, baseEnd_4845583] using wordTrace_append hprefix tailTrace_4845583
  have hstable : (prefixWord ++ tailWord_4845583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845583).length < 2 ^ (prefixWord ++ tailWord_4845583).sum := by decide
  have hdescent : baseEnd_4845583 < baseStart_4845583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845591 : List Nat := [1, 1, 3, 5, 2, 1, 1, 1, 4, 2, 2]
def baseStart_4845591 : Nat := 118140960795 + 4845591 * 2 ^ 59
def prefixEnd_4845591 : Nat := 4983230072969 + 3 ^ 40 * 4845591 * 2
def baseEnd_4845591 : Nat := 2488117238100456336628039

theorem tailTrace_4845591 : CollatzResearch.WordTrace tailWord_4845591 prefixEnd_4845591 2488117238100456336628039 := by
  unfold tailWord_4845591
  simp only [CollatzResearch.WordTrace]
  refine ⟨176733222988258842902408627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117822148658839228601605751 176733222988258842902408627)
  ·
    refine ⟨265099834482388264353612941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176733222988258842902408627 265099834482388264353612941)
    ·
      refine ⟨99412437930895599132604853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 265099834482388264353612941 99412437930895599132604853)
      ·
        refine ⟨9319916056021462418681705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99412437930895599132604853 9319916056021462418681705)
        ·
          refine ⟨6989937042016096814011279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9319916056021462418681705 6989937042016096814011279)
          ·
            refine ⟨10484905563024145221016919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6989937042016096814011279 10484905563024145221016919)
            ·
              refine ⟨15727358344536217831525379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10484905563024145221016919 15727358344536217831525379)
              ·
                refine ⟨23591037516804326747288069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15727358344536217831525379 23591037516804326747288069)
                ·
                  refine ⟨4423319534400811265116513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23591037516804326747288069 4423319534400811265116513)
                  ·
                    refine ⟨3317489650800608448837385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4423319534400811265116513 3317489650800608448837385)
                    ·
                      refine ⟨2488117238100456336628039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3317489650800608448837385 2488117238100456336628039)
                      ·
                        rfl

theorem cell23_4845591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_4845591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845591 prefixEnd_4845591 := by exact prefixLift 4845591
  have htrace : WordTrace (prefixWord ++ tailWord_4845591) baseStart_4845591 baseEnd_4845591 := by
    simpa [prefixWord, tailWord_4845591, baseEnd_4845591] using wordTrace_append hprefix tailTrace_4845591
  have hstable : (prefixWord ++ tailWord_4845591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845591).length < 2 ^ (prefixWord ++ tailWord_4845591).sum := by decide
  have hdescent : baseEnd_4845591 < baseStart_4845591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845597 : List Nat := [1, 4, 2, 2, 2, 2, 2, 1, 7]
def baseStart_4845597 : Nat := 118140960795 + 4845597 * 2 ^ 59
def prefixEnd_4845597 : Nat := 4983230072969 + 3 ^ 40 * 4845597 * 2
def baseEnd_4845597 : Nat := 276457813220487034794779

theorem tailTrace_4845597 : CollatzResearch.WordTrace tailWord_4845597 prefixEnd_4845597 276457813220487034794779 := by
  unfold tailWord_4845597
  simp only [CollatzResearch.WordTrace]
  refine ⟨176733441826237105927127045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 117822294550824737284751363 176733441826237105927127045)
  ·
    refine ⟨33137520342419457361336321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 176733441826237105927127045 33137520342419457361336321)
    ·
      refine ⟨24853140256814593021002241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33137520342419457361336321 24853140256814593021002241)
      ·
        refine ⟨18639855192610944765751681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24853140256814593021002241 18639855192610944765751681)
        ·
          refine ⟨13979891394458208574313761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18639855192610944765751681 13979891394458208574313761)
          ·
            refine ⟨10484918545843656430735321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13979891394458208574313761 10484918545843656430735321)
            ·
              refine ⟨7863688909382742323051491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10484918545843656430735321 7863688909382742323051491)
              ·
                refine ⟨11795533364074113484577237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7863688909382742323051491 11795533364074113484577237)
                ·
                  refine ⟨276457813220487034794779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11795533364074113484577237 276457813220487034794779)
                  ·
                    rfl

theorem cell23_4845597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 7].length) (baseStart_4845597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845597 prefixEnd_4845597 := by exact prefixLift 4845597
  have htrace : WordTrace (prefixWord ++ tailWord_4845597) baseStart_4845597 baseEnd_4845597 := by
    simpa [prefixWord, tailWord_4845597, baseEnd_4845597] using wordTrace_append hprefix tailTrace_4845597
  have hstable : (prefixWord ++ tailWord_4845597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845597).length < 2 ^ (prefixWord ++ tailWord_4845597).sum := by decide
  have hdescent : baseEnd_4845597 < baseStart_4845597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4845608 : List Nat := [2, 1, 5, 3, 1, 2, 1, 1, 1, 4, 2]
def baseStart_4845608 : Nat := 118140960795 + 4845608 * 2 ^ 59
def prefixEnd_4845608 : Nat := 4983230072969 + 3 ^ 40 * 4845608 * 2
def baseEnd_4845608 : Nat := 2488125967271582770115461

theorem tailTrace_4845608 : CollatzResearch.WordTrace tailWord_4845608 prefixEnd_4845608 2488125967271582770115461 := by
  unfold tailWord_4845608
  simp only [CollatzResearch.WordTrace]
  refine ⟨88366921514598627402888739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 117822562019464836537184985 88366921514598627402888739)
  ·
    refine ⟨132550382271897941104333109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88366921514598627402888739 132550382271897941104333109)
    ·
      refine ⟨12426598337990431978531229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 132550382271897941104333109 12426598337990431978531229)
      ·
        refine ⟨4659974376746411991949211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12426598337990431978531229 4659974376746411991949211)
        ·
          refine ⟨6989961565119617987923817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4659974376746411991949211 6989961565119617987923817)
          ·
            refine ⟨5242471173839713490942863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6989961565119617987923817 5242471173839713490942863)
            ·
              refine ⟨7863706760759570236414295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5242471173839713490942863 7863706760759570236414295)
              ·
                refine ⟨11795560141139355354621443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7863706760759570236414295 11795560141139355354621443)
                ·
                  refine ⟨17693340211709033031932165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11795560141139355354621443 17693340211709033031932165)
                  ·
                    refine ⟨3317501289695443693487281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17693340211709033031932165 3317501289695443693487281)
                    ·
                      refine ⟨2488125967271582770115461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3317501289695443693487281 2488125967271582770115461)
                      ·
                        rfl

theorem cell23_4845608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_4845608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4845608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4845608 prefixEnd_4845608 := by exact prefixLift 4845608
  have htrace : WordTrace (prefixWord ++ tailWord_4845608) baseStart_4845608 baseEnd_4845608 := by
    simpa [prefixWord, tailWord_4845608, baseEnd_4845608] using wordTrace_append hprefix tailTrace_4845608
  have hstable : (prefixWord ++ tailWord_4845608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4845608).length < 2 ^ (prefixWord ++ tailWord_4845608).sum := by decide
  have hdescent : baseEnd_4845608 < baseStart_4845608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4845608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
