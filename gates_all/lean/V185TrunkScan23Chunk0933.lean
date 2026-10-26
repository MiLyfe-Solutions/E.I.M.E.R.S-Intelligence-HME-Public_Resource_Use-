import V185TrunkScan23Chunk0932

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5522025 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 2, 6, 3]
def baseStart_5522025 : Nat := 118140960795 + 5522025 * 2 ^ 59
def prefixEnd_5522025 : Nat := 4983230072969 + 3 ^ 40 * 5522025 * 2
def baseEnd_5522025 : Nat := 2835453011143862785492175

theorem tailTrace_5522025 : CollatzResearch.WordTrace tailWord_5522025 prefixEnd_5522025 2835453011143862785492175 := by
  unfold tailWord_5522025
  simp only [CollatzResearch.WordTrace]
  refine ⟨201404797819653986632135529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134269865213102657754757019 201404797819653986632135529)
  ·
    refine ⟨151053598364740489974101647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201404797819653986632135529 151053598364740489974101647)
    ·
      refine ⟨226580397547110734961152471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151053598364740489974101647 226580397547110734961152471)
      ·
        refine ⟨339870596320666102441728707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226580397547110734961152471 339870596320666102441728707)
        ·
          refine ⟨509805894480999153662593061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339870596320666102441728707 509805894480999153662593061)
          ·
            refine ⟨95588605215187341311736199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 509805894480999153662593061 95588605215187341311736199)
            ·
              refine ⟨143382907822781011967604299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95588605215187341311736199 143382907822781011967604299)
              ·
                refine ⟨215074361734171517951406449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143382907822781011967604299 215074361734171517951406449)
                ·
                  refine ⟨161305771300628638463554837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 215074361734171517951406449 161305771300628638463554837)
                  ·
                    refine ⟨7561208029716967427979133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 161305771300628638463554837 7561208029716967427979133)
                    ·
                      refine ⟨2835453011143862785492175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7561208029716967427979133 2835453011143862785492175)
                      ·
                        rfl

theorem cell23_5522025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 6, 3].length) (baseStart_5522025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522025 prefixEnd_5522025 := by exact prefixLift 5522025
  have htrace : WordTrace (prefixWord ++ tailWord_5522025) baseStart_5522025 baseEnd_5522025 := by
    simpa [prefixWord, tailWord_5522025, baseEnd_5522025] using wordTrace_append hprefix tailTrace_5522025
  have hstable : (prefixWord ++ tailWord_5522025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522025).length < 2 ^ (prefixWord ++ tailWord_5522025).sum := by decide
  have hdescent : baseEnd_5522025 < baseStart_5522025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522039 : List Nat := [1, 1, 3, 1, 1, 3, 2, 4, 3, 2, 2]
def baseStart_5522039 : Nat := 118140960795 + 5522039 * 2 ^ 59
def prefixEnd_5522039 : Nat := 4983230072969 + 3 ^ 40 * 5522039 * 2
def baseEnd_5522039 : Nat := 2835460199873025730717111

theorem tailTrace_5522039 : CollatzResearch.WordTrace tailWord_5522039 prefixEnd_5522039 2835460199873025730717111 := by
  unfold tailWord_5522039
  simp only [CollatzResearch.WordTrace]
  refine ⟨201405308441603267023145171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134270205627735511348763447 201405308441603267023145171)
  ·
    refine ⟨302107962662404900534717757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201405308441603267023145171 302107962662404900534717757)
    ·
      refine ⟨113290485998401837700519159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302107962662404900534717757 113290485998401837700519159)
      ·
        refine ⟨169935728997602756550778739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113290485998401837700519159 169935728997602756550778739)
        ·
          refine ⟨254903593496404134826168109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169935728997602756550778739 254903593496404134826168109)
          ·
            refine ⟨95588847561151550559813041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 254903593496404134826168109 95588847561151550559813041)
            ·
              refine ⟨71691635670863662919859781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95588847561151550559813041 71691635670863662919859781)
              ·
                refine ⟨13442181688286936797473709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71691635670863662919859781 13442181688286936797473709)
                ·
                  refine ⟨5040818133107601299052641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13442181688286936797473709 5040818133107601299052641)
                  ·
                    refine ⟨3780613599830700974289481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5040818133107601299052641 3780613599830700974289481)
                    ·
                      refine ⟨2835460199873025730717111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3780613599830700974289481 2835460199873025730717111)
                      ·
                        rfl

theorem cell23_5522039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 3, 2, 2].length) (baseStart_5522039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522039 prefixEnd_5522039 := by exact prefixLift 5522039
  have htrace : WordTrace (prefixWord ++ tailWord_5522039) baseStart_5522039 baseEnd_5522039 := by
    simpa [prefixWord, tailWord_5522039, baseEnd_5522039] using wordTrace_append hprefix tailTrace_5522039
  have hstable : (prefixWord ++ tailWord_5522039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522039).length < 2 ^ (prefixWord ++ tailWord_5522039).sum := by decide
  have hdescent : baseEnd_5522039 < baseStart_5522039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522052 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 3, 2, 4]
def baseStart_5522052 : Nat := 118140960795 + 5522052 * 2 ^ 59
def prefixEnd_5522052 : Nat := 4983230072969 + 3 ^ 40 * 5522052 * 2
def baseEnd_5522052 : Nat := 2835466875121534179854551

theorem tailTrace_5522052 : CollatzResearch.WordTrace tailWord_5522052 prefixEnd_5522052 2835466875121534179854551 := by
  unfold tailWord_5522052
  simp only [CollatzResearch.WordTrace]
  refine ⟨100702891295278085121684205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134270521727037446828912273 100702891295278085121684205)
  ·
    refine ⟨37763584235729281920631577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100702891295278085121684205 37763584235729281920631577)
    ·
      refine ⟨28322688176796961440473683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37763584235729281920631577 28322688176796961440473683)
      ·
        refine ⟨42484032265195442160710525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28322688176796961440473683 42484032265195442160710525)
        ·
          refine ⟨15931512099448290810266447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42484032265195442160710525 15931512099448290810266447)
          ·
            refine ⟨23897268149172436215399671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15931512099448290810266447 23897268149172436215399671)
            ·
              refine ⟨35845902223758654323099507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23897268149172436215399671 35845902223758654323099507)
              ·
                refine ⟨53768853335637981484649261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35845902223758654323099507 53768853335637981484649261)
                ·
                  refine ⟨20163320000864243056743473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53768853335637981484649261 20163320000864243056743473)
                  ·
                    refine ⟨15122490000648182292557605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20163320000864243056743473 15122490000648182292557605)
                    ·
                      refine ⟨2835466875121534179854551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15122490000648182292557605 2835466875121534179854551)
                      ·
                        rfl

theorem cell23_5522052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_5522052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522052 prefixEnd_5522052 := by exact prefixLift 5522052
  have htrace : WordTrace (prefixWord ++ tailWord_5522052) baseStart_5522052 baseEnd_5522052 := by
    simpa [prefixWord, tailWord_5522052, baseEnd_5522052] using wordTrace_append hprefix tailTrace_5522052
  have hstable : (prefixWord ++ tailWord_5522052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522052).length < 2 ^ (prefixWord ++ tailWord_5522052).sum := by decide
  have hdescent : baseEnd_5522052 < baseStart_5522052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522066 : List Nat := [3, 2, 3, 1, 2, 2, 2, 2, 2, 4]
def baseStart_5522066 : Nat := 118140960795 + 5522066 * 2 ^ 59
def prefixEnd_5522066 : Nat := 4983230072969 + 3 ^ 40 * 5522066 * 2
def baseEnd_5522066 : Nat := 945158021283565708359829

theorem tailTrace_5522066 : CollatzResearch.WordTrace tailWord_5522066 prefixEnd_5522066 945158021283565708359829 := by
  unfold tailWord_5522066
  simp only [CollatzResearch.WordTrace]
  refine ⟨50351573303126362658594513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134270862141670300422918701 50351573303126362658594513)
  ·
    refine ⟨37763679977344771993945885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50351573303126362658594513 37763679977344771993945885)
    ·
      refine ⟨14161379991504289497729707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37763679977344771993945885 14161379991504289497729707)
      ·
        refine ⟨21242069987256434246594561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14161379991504289497729707 21242069987256434246594561)
        ·
          refine ⟨15931552490442325684945921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21242069987256434246594561 15931552490442325684945921)
          ·
            refine ⟨11948664367831744263709441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15931552490442325684945921 11948664367831744263709441)
            ·
              refine ⟨8961498275873808197782081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11948664367831744263709441 8961498275873808197782081)
              ·
                refine ⟨6721123706905356148336561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8961498275873808197782081 6721123706905356148336561)
                ·
                  refine ⟨5040842780179017111252421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6721123706905356148336561 5040842780179017111252421)
                  ·
                    refine ⟨945158021283565708359829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5040842780179017111252421 945158021283565708359829)
                    ·
                      rfl

theorem cell23_5522066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_5522066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522066 prefixEnd_5522066 := by exact prefixLift 5522066
  have htrace : WordTrace (prefixWord ++ tailWord_5522066) baseStart_5522066 baseEnd_5522066 := by
    simpa [prefixWord, tailWord_5522066, baseEnd_5522066] using wordTrace_append hprefix tailTrace_5522066
  have hstable : (prefixWord ++ tailWord_5522066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522066).length < 2 ^ (prefixWord ++ tailWord_5522066).sum := by decide
  have hdescent : baseEnd_5522066 < baseStart_5522066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522072 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 3, 3, 3]
def baseStart_5522072 : Nat := 118140960795 + 5522072 * 2 ^ 59
def prefixEnd_5522072 : Nat := 4983230072969 + 3 ^ 40 * 5522072 * 2
def baseEnd_5522072 : Nat := 2835477144734624101604459

theorem tailTrace_5522072 : CollatzResearch.WordTrace tailWord_5522072 prefixEnd_5522072 2835477144734624101604459 := by
  unfold tailWord_5522072
  simp only [CollatzResearch.WordTrace]
  refine ⟨100703256025241856829548235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134271008033655809106064313 100703256025241856829548235)
  ·
    refine ⟨151054884037862785244322353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100703256025241856829548235 151054884037862785244322353)
    ·
      refine ⟨113291163028397088933241765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151054884037862785244322353 113291163028397088933241765)
      ·
        refine ⟨21242093067824454174982831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113291163028397088933241765 21242093067824454174982831)
        ·
          refine ⟨31863139601736681262474247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21242093067824454174982831 31863139601736681262474247)
          ·
            refine ⟨47794709402605021893711371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31863139601736681262474247 47794709402605021893711371)
            ·
              refine ⟨71692064103907532840567057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47794709402605021893711371 71692064103907532840567057)
              ·
                refine ⟨53769048077930649630425293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71692064103907532840567057 53769048077930649630425293)
                ·
                  refine ⟨20163393029223993611409485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53769048077930649630425293 20163393029223993611409485)
                  ·
                    refine ⟨7561272385958997604278557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20163393029223993611409485 7561272385958997604278557)
                    ·
                      refine ⟨2835477144734624101604459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7561272385958997604278557 2835477144734624101604459)
                      ·
                        rfl

theorem cell23_5522072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_5522072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522072 prefixEnd_5522072 := by exact prefixLift 5522072
  have htrace : WordTrace (prefixWord ++ tailWord_5522072) baseStart_5522072 baseEnd_5522072 := by
    simpa [prefixWord, tailWord_5522072, baseEnd_5522072] using wordTrace_append hprefix tailTrace_5522072
  have hstable : (prefixWord ++ tailWord_5522072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522072).length < 2 ^ (prefixWord ++ tailWord_5522072).sum := by decide
  have hdescent : baseEnd_5522072 < baseStart_5522072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522085 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 1, 4, 5]
def baseStart_5522085 : Nat := 118140960795 + 5522085 * 2 ^ 59
def prefixEnd_5522085 : Nat := 4983230072969 + 3 ^ 40 * 5522085 * 2
def baseEnd_5522085 : Nat := 2835483819983132550741899

theorem tailTrace_5522085 : CollatzResearch.WordTrace tailWord_5522085 prefixEnd_5522085 2835483819983132550741899 := by
  unfold tailWord_5522085
  simp only [CollatzResearch.WordTrace]
  refine ⟨201406986199436616879319709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134271324132957744586213139 201406986199436616879319709)
  ·
    refine ⟨75527619824788731329744891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201406986199436616879319709 75527619824788731329744891)
    ·
      refine ⟨113291429737183096994617337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75527619824788731329744891 113291429737183096994617337)
      ·
        refine ⟨84968572302887322745963003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113291429737183096994617337 84968572302887322745963003)
        ·
          refine ⟨127452858454330984118944505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84968572302887322745963003 127452858454330984118944505)
          ·
            refine ⟨95589643840748238089208379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127452858454330984118944505 95589643840748238089208379)
            ·
              refine ⟨143384465761122357133812569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95589643840748238089208379 143384465761122357133812569)
              ·
                refine ⟨107538349320841767850359427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143384465761122357133812569 107538349320841767850359427)
                ·
                  refine ⟨161307523981262651775539141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107538349320841767850359427 161307523981262651775539141)
                  ·
                    refine ⟨30245160746486747207913589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 161307523981262651775539141 30245160746486747207913589)
                    ·
                      refine ⟨2835483819983132550741899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30245160746486747207913589 2835483819983132550741899)
                      ·
                        rfl

theorem cell23_5522085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_5522085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522085 prefixEnd_5522085 := by exact prefixLift 5522085
  have htrace : WordTrace (prefixWord ++ tailWord_5522085) baseStart_5522085 baseEnd_5522085 := by
    simpa [prefixWord, tailWord_5522085, baseEnd_5522085] using wordTrace_append hprefix tailTrace_5522085
  have hstable : (prefixWord ++ tailWord_5522085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522085).length < 2 ^ (prefixWord ++ tailWord_5522085).sum := by decide
  have hdescent : baseEnd_5522085 < baseStart_5522085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522090 : List Nat := [3, 1, 5, 2, 1, 1, 1, 2, 3, 2, 2]
def baseStart_5522090 : Nat := 118140960795 + 5522090 * 2 ^ 59
def prefixEnd_5522090 : Nat := 4983230072969 + 3 ^ 40 * 5522090 * 2
def baseEnd_5522090 : Nat := 2835486387386405031179377

theorem tailTrace_5522090 : CollatzResearch.WordTrace tailWord_5522090 prefixEnd_5522090 2835486387386405031179377 := by
  unfold tailWord_5522090
  simp only [CollatzResearch.WordTrace]
  refine ⟨50351792141104625683312931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134271445709612335155501149 50351792141104625683312931)
  ·
    refine ⟨75527688211656938524969397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50351792141104625683312931 75527688211656938524969397)
    ·
      refine ⟨7080720769842837986715881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75527688211656938524969397 7080720769842837986715881)
      ·
        refine ⟨5310540577382128490036911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7080720769842837986715881 5310540577382128490036911)
        ·
          refine ⟨7965810866073192735055367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5310540577382128490036911 7965810866073192735055367)
          ·
            refine ⟨11948716299109789102583051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7965810866073192735055367 11948716299109789102583051)
            ·
              refine ⟨17923074448664683653874577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11948716299109789102583051 17923074448664683653874577)
              ·
                refine ⟨13442305836498512740405933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17923074448664683653874577 13442305836498512740405933)
                ·
                  refine ⟨5040864688686942277652225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13442305836498512740405933 5040864688686942277652225)
                  ·
                    refine ⟨3780648516515206708239169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5040864688686942277652225 3780648516515206708239169)
                    ·
                      refine ⟨2835486387386405031179377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3780648516515206708239169 2835486387386405031179377)
                      ·
                        rfl

theorem cell23_5522090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_5522090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522090 prefixEnd_5522090 := by exact prefixLift 5522090
  have htrace : WordTrace (prefixWord ++ tailWord_5522090) baseStart_5522090 baseEnd_5522090 := by
    simpa [prefixWord, tailWord_5522090, baseEnd_5522090] using wordTrace_append hprefix tailTrace_5522090
  have hstable : (prefixWord ++ tailWord_5522090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522090).length < 2 ^ (prefixWord ++ tailWord_5522090).sum := by decide
  have hdescent : baseEnd_5522090 < baseStart_5522090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522099 : List Nat := [1, 1, 1, 2, 3, 4, 2, 1, 3, 3, 2]
def baseStart_5522099 : Nat := 118140960795 + 5522099 * 2 ^ 59
def prefixEnd_5522099 : Nat := 4983230072969 + 3 ^ 40 * 5522099 * 2
def baseEnd_5522099 : Nat := 2835491008712295495966835

theorem tailTrace_5522099 : CollatzResearch.WordTrace tailWord_5522099 prefixEnd_5522099 2835491008712295495966835 := by
  unfold tailWord_5522099
  simp only [CollatzResearch.WordTrace]
  refine ⟨201407496821385897270329351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134271664547590598180219567 201407496821385897270329351)
  ·
    refine ⟨302111245232078845905494027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201407496821385897270329351 302111245232078845905494027)
    ·
      refine ⟨453166867848118268858241041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302111245232078845905494027 453166867848118268858241041)
      ·
        refine ⟨339875150886088701643680781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 453166867848118268858241041 339875150886088701643680781)
        ·
          refine ⟨127453181582283263116380293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 339875150886088701643680781 127453181582283263116380293)
          ·
            refine ⟨23897471546678111834321305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127453181582283263116380293 23897471546678111834321305)
            ·
              refine ⟨17923103660008583875740979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23897471546678111834321305 17923103660008583875740979)
              ·
                refine ⟨26884655490012875813611469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17923103660008583875740979 26884655490012875813611469)
                ·
                  refine ⟨10081745808754828430104301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26884655490012875813611469 10081745808754828430104301)
                  ·
                    refine ⟨3780654678283060661289113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10081745808754828430104301 3780654678283060661289113)
                    ·
                      refine ⟨2835491008712295495966835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3780654678283060661289113 2835491008712295495966835)
                      ·
                        rfl

theorem cell23_5522099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 3, 2].length) (baseStart_5522099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522099 prefixEnd_5522099 := by exact prefixLift 5522099
  have htrace : WordTrace (prefixWord ++ tailWord_5522099) baseStart_5522099 baseEnd_5522099 := by
    simpa [prefixWord, tailWord_5522099, baseEnd_5522099] using wordTrace_append hprefix tailTrace_5522099
  have hstable : (prefixWord ++ tailWord_5522099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522099).length < 2 ^ (prefixWord ++ tailWord_5522099).sum := by decide
  have hdescent : baseEnd_5522099 < baseStart_5522099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522105 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 3, 8]
def baseStart_5522105 : Nat := 118140960795 + 5522105 * 2 ^ 59
def prefixEnd_5522105 : Nat := 4983230072969 + 3 ^ 40 * 5522105 * 2
def baseEnd_5522105 : Nat := 945164696532074157497269

theorem tailTrace_5522105 : CollatzResearch.WordTrace tailWord_5522105 prefixEnd_5522105 945164696532074157497269 := by
  unfold tailWord_5522105
  simp only [CollatzResearch.WordTrace]
  refine ⟨201407715659364160295047769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134271810439576106863365179 201407715659364160295047769)
  ·
    refine ⟨151055786744523120221285827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201407715659364160295047769 151055786744523120221285827)
    ·
      refine ⟨226583680116784680331928741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151055786744523120221285827 226583680116784680331928741)
      ·
        refine ⟨42484440021897127562236639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 226583680116784680331928741 42484440021897127562236639)
        ·
          refine ⟨63726660032845691343354959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42484440021897127562236639 63726660032845691343354959)
          ·
            refine ⟨95589990049268537015032439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63726660032845691343354959 95589990049268537015032439)
            ·
              refine ⟨143384985073902805522548659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95589990049268537015032439 143384985073902805522548659)
              ·
                refine ⟨215077477610854208283822989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143384985073902805522548659 215077477610854208283822989)
                ·
                  refine ⟨80654054104070328106433621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 215077477610854208283822989 80654054104070328106433621)
                  ·
                    refine ⟨945164696532074157497269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80654054104070328106433621 945164696532074157497269)
                    ·
                      rfl

theorem cell23_5522105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 8].length) (baseStart_5522105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522105 prefixEnd_5522105 := by exact prefixLift 5522105
  have htrace : WordTrace (prefixWord ++ tailWord_5522105) baseStart_5522105 baseEnd_5522105 := by
    simpa [prefixWord, tailWord_5522105, baseEnd_5522105] using wordTrace_append hprefix tailTrace_5522105
  have hstable : (prefixWord ++ tailWord_5522105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522105).length < 2 ^ (prefixWord ++ tailWord_5522105).sum := by decide
  have hdescent : baseEnd_5522105 < baseStart_5522105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522122 : List Nat := [3, 1, 2, 1, 4, 1, 1, 2, 2, 6]
def baseStart_5522122 : Nat := 118140960795 + 5522122 * 2 ^ 59
def prefixEnd_5522122 : Nat := 4983230072969 + 3 ^ 40 * 5522122 * 2
def baseEnd_5522122 : Nat := 945167606255782968659743

theorem tailTrace_5522122 : CollatzResearch.WordTrace tailWord_5522122 prefixEnd_5522122 945167606255782968659743 := by
  unfold tailWord_5522122
  simp only [CollatzResearch.WordTrace]
  refine ⟨50352083925075643049604155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134272223800201714798944413 50352083925075643049604155)
  ·
    refine ⟨75528125887613464574406233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50352083925075643049604155 75528125887613464574406233)
    ·
      refine ⟨56646094415710098430804675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75528125887613464574406233 56646094415710098430804675)
      ·
        refine ⟨84969141623565147646207013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56646094415710098430804675 84969141623565147646207013)
        ·
          refine ⟨15931714054418465183663815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84969141623565147646207013 15931714054418465183663815)
          ·
            refine ⟨23897571081627697775495723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15931714054418465183663815 23897571081627697775495723)
            ·
              refine ⟨35846356622441546663243585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23897571081627697775495723 35846356622441546663243585)
              ·
                refine ⟨26884767466831159997432689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35846356622441546663243585 26884767466831159997432689)
                ·
                  refine ⟨20163575600123369998074517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26884767466831159997432689 20163575600123369998074517)
                  ·
                    refine ⟨945167606255782968659743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20163575600123369998074517 945167606255782968659743)
                    ·
                      rfl

theorem cell23_5522122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_5522122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522122 prefixEnd_5522122 := by exact prefixLift 5522122
  have htrace : WordTrace (prefixWord ++ tailWord_5522122) baseStart_5522122 baseEnd_5522122 := by
    simpa [prefixWord, tailWord_5522122, baseEnd_5522122] using wordTrace_append hprefix tailTrace_5522122
  have hstable : (prefixWord ++ tailWord_5522122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522122).length < 2 ^ (prefixWord ++ tailWord_5522122).sum := by decide
  have hdescent : baseEnd_5522122 < baseStart_5522122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522140 : List Nat := [2, 2, 5, 1, 1, 2, 3, 1, 2, 1, 3]
def baseStart_5522140 : Nat := 118140960795 + 5522140 * 2 ^ 59
def prefixEnd_5522140 : Nat := 4983230072969 + 3 ^ 40 * 5522140 * 2
def baseEnd_5522140 : Nat := 2835512061419129835554147

theorem tailTrace_5522140 : CollatzResearch.WordTrace tailWord_5522140 prefixEnd_5522140 2835512061419129835554147 := by
  unfold tailWord_5522140
  simp only [CollatzResearch.WordTrace]
  refine ⟨100704496107118680636285937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134272661476158240848381249 100704496107118680636285937)
  ·
    refine ⟨75528372080339010477214453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100704496107118680636285937 75528372080339010477214453)
    ·
      refine ⟨7080784882531782232238855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 75528372080339010477214453 7080784882531782232238855)
      ·
        refine ⟨10621177323797673348358283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7080784882531782232238855 10621177323797673348358283)
        ·
          refine ⟨15931765985696510022537425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10621177323797673348358283 15931765985696510022537425)
          ·
            refine ⟨11948824489272382516903069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15931765985696510022537425 11948824489272382516903069)
            ·
              refine ⟨4480809183477143443838651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11948824489272382516903069 4480809183477143443838651)
              ·
                refine ⟨6721213775215715165757977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4480809183477143443838651 6721213775215715165757977)
                ·
                  refine ⟨5040910331411786374318483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6721213775215715165757977 5040910331411786374318483)
                  ·
                    refine ⟨7561365497117679561477725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5040910331411786374318483 7561365497117679561477725)
                    ·
                      refine ⟨2835512061419129835554147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7561365497117679561477725 2835512061419129835554147)
                      ·
                        rfl

theorem cell23_5522140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_5522140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522140 prefixEnd_5522140 := by exact prefixLift 5522140
  have htrace : WordTrace (prefixWord ++ tailWord_5522140) baseStart_5522140 baseEnd_5522140 := by
    simpa [prefixWord, tailWord_5522140, baseEnd_5522140] using wordTrace_append hprefix tailTrace_5522140
  have hstable : (prefixWord ++ tailWord_5522140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522140).length < 2 ^ (prefixWord ++ tailWord_5522140).sum := by decide
  have hdescent : baseEnd_5522140 < baseStart_5522140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522186 : List Nat := [3, 1, 2, 2, 1, 2, 5, 2, 5]
def baseStart_5522186 : Nat := 118140960795 + 5522186 * 2 ^ 59
def prefixEnd_5522186 : Nat := 4983230072969 + 3 ^ 40 * 5522186 * 2
def baseEnd_5522186 : Nat := 315059520169915183953215

theorem tailTrace_5522186 : CollatzResearch.WordTrace tailWord_5522186 prefixEnd_5522186 315059520169915183953215 := by
  unfold tailWord_5522186
  simp only [CollatzResearch.WordTrace]
  refine ⟨50352667493017677782186603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134273779981380474085830941 50352667493017677782186603)
  ·
    refine ⟨75529001239526516673279905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50352667493017677782186603 75529001239526516673279905)
    ·
      refine ⟨56646750929644887504959929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75529001239526516673279905 56646750929644887504959929)
      ·
        refine ⟨42485063197233665628719947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56646750929644887504959929 42485063197233665628719947)
        ·
          refine ⟨63727594795850498443079921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42485063197233665628719947 63727594795850498443079921)
          ·
            refine ⟨47795696096887873832309941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63727594795850498443079921 47795696096887873832309941)
            ·
              refine ⟨4480846509083238171779057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47795696096887873832309941 4480846509083238171779057)
              ·
                refine ⟨3360634881812428628834293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4480846509083238171779057 3360634881812428628834293)
                ·
                  refine ⟨315059520169915183953215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3360634881812428628834293 315059520169915183953215)
                  ·
                    rfl

theorem cell23_5522186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 2, 5].length) (baseStart_5522186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522186 prefixEnd_5522186 := by exact prefixLift 5522186
  have htrace : WordTrace (prefixWord ++ tailWord_5522186) baseStart_5522186 baseEnd_5522186 := by
    simpa [prefixWord, tailWord_5522186, baseEnd_5522186] using wordTrace_append hprefix tailTrace_5522186
  have hstable : (prefixWord ++ tailWord_5522186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522186).length < 2 ^ (prefixWord ++ tailWord_5522186).sum := by decide
  have hdescent : baseEnd_5522186 < baseStart_5522186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522232 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 2, 1, 6]
def baseStart_5522232 : Nat := 118140960795 + 5522232 * 2 ^ 59
def prefixEnd_5522232 : Nat := 4983230072969 + 3 ^ 40 * 5522232 * 2
def baseEnd_5522232 : Nat := 2835559301639343475603723

theorem tailTrace_5522232 : CollatzResearch.WordTrace tailWord_5522232 prefixEnd_5522232 2835559301639343475603723 := by
  unfold tailWord_5522232
  simp only [CollatzResearch.WordTrace]
  refine ⟨100706173864952030492460475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134274898486602707323280633 100706173864952030492460475)
  ·
    refine ⟨151059260797428045738690713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100706173864952030492460475 151059260797428045738690713)
    ·
      refine ⟨113294445598071034304018035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151059260797428045738690713 113294445598071034304018035)
      ·
        refine ⟨169941668397106551456027053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113294445598071034304018035 169941668397106551456027053)
        ·
          refine ⟨63728125648914956796010145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169941668397106551456027053 63728125648914956796010145)
          ·
            refine ⟨47796094236686217597007609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63728125648914956796010145 47796094236686217597007609)
            ·
              refine ⟨35847070677514663197755707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47796094236686217597007609 35847070677514663197755707)
              ·
                refine ⟨53770606016271994796633561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35847070677514663197755707 53770606016271994796633561)
                ·
                  refine ⟨40327954512203996097475171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53770606016271994796633561 40327954512203996097475171)
                  ·
                    refine ⟨60491931768305994146212757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40327954512203996097475171 60491931768305994146212757)
                    ·
                      refine ⟨2835559301639343475603723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60491931768305994146212757 2835559301639343475603723)
                      ·
                        rfl

theorem cell23_5522232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_5522232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522232 prefixEnd_5522232 := by exact prefixLift 5522232
  have htrace : WordTrace (prefixWord ++ tailWord_5522232) baseStart_5522232 baseEnd_5522232 := by
    simpa [prefixWord, tailWord_5522232, baseEnd_5522232] using wordTrace_append hprefix tailTrace_5522232
  have hstable : (prefixWord ++ tailWord_5522232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522232).length < 2 ^ (prefixWord ++ tailWord_5522232).sum := by decide
  have hdescent : baseEnd_5522232 < baseStart_5522232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522303 : List Nat := [1, 1, 2, 2, 1, 1, 6, 4, 1, 1, 3]
def baseStart_5522303 : Nat := 118140960795 + 5522303 * 2 ^ 59
def prefixEnd_5522303 : Nat := 4983230072969 + 3 ^ 40 * 5522303 * 2
def baseEnd_5522303 : Nat := 2835595758765812697815897

theorem tailTrace_5522303 : CollatzResearch.WordTrace tailWord_5522303 prefixEnd_5522303 2835595758765812697815897 := by
  unfold tailWord_5522303
  simp only [CollatzResearch.WordTrace]
  refine ⟨201414937312646840110755563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134276624875097893407170375 201414937312646840110755563)
  ·
    refine ⟨302122405968970260166133345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201414937312646840110755563 302122405968970260166133345)
    ·
      refine ⟨226591804476727695124600009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302122405968970260166133345 226591804476727695124600009)
      ·
        refine ⟨169943853357545771343450007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226591804476727695124600009 169943853357545771343450007)
        ·
          refine ⟨254915780036318657015175011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169943853357545771343450007 254915780036318657015175011)
          ·
            refine ⟨382373670054477985522762517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254915780036318657015175011 382373670054477985522762517)
            ·
              refine ⟨17923765783803655571379493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 382373670054477985522762517 17923765783803655571379493)
              ·
                refine ⟨3360706084463185419633655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17923765783803655571379493 3360706084463185419633655)
                ·
                  refine ⟨5041059126694778129450483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3360706084463185419633655 5041059126694778129450483)
                  ·
                    refine ⟨7561588690042167194175725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5041059126694778129450483 7561588690042167194175725)
                    ·
                      refine ⟨2835595758765812697815897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7561588690042167194175725 2835595758765812697815897)
                      ·
                        rfl

theorem cell23_5522303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 4, 1, 1, 3].length) (baseStart_5522303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522303 prefixEnd_5522303 := by exact prefixLift 5522303
  have htrace : WordTrace (prefixWord ++ tailWord_5522303) baseStart_5522303 baseEnd_5522303 := by
    simpa [prefixWord, tailWord_5522303, baseEnd_5522303] using wordTrace_append hprefix tailTrace_5522303
  have hstable : (prefixWord ++ tailWord_5522303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522303).length < 2 ^ (prefixWord ++ tailWord_5522303).sum := by decide
  have hdescent : baseEnd_5522303 < baseStart_5522303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522337 : List Nat := [1, 2, 3, 4, 1, 3, 1, 3, 1, 1, 3]
def baseStart_5522337 : Nat := 118140960795 + 5522337 * 2 ^ 59
def prefixEnd_5522337 : Nat := 4983230072969 + 3 ^ 40 * 5522337 * 2
def baseEnd_5522337 : Nat := 2835613217108065564790741

theorem tailTrace_5522337 : CollatzResearch.WordTrace tailWord_5522337 prefixEnd_5522337 2835613217108065564790741 := by
  unfold tailWord_5522337
  simp only [CollatzResearch.WordTrace]
  refine ⟨201416177394523663917493265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134277451596349109278328843 201416177394523663917493265)
  ·
    refine ⟨151062133045892747938119949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201416177394523663917493265 151062133045892747938119949)
    ·
      refine ⟨56648299892209780476794981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151062133045892747938119949 56648299892209780476794981)
      ·
        refine ⟨10621556229789333839399059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56648299892209780476794981 10621556229789333839399059)
        ·
          refine ⟨15932334344684000759098589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10621556229789333839399059 15932334344684000759098589)
          ·
            refine ⟨5974625379256500284661971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15932334344684000759098589 5974625379256500284661971)
            ·
              refine ⟨8961938068884750426992957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5974625379256500284661971 8961938068884750426992957)
              ·
                refine ⟨3360726775831781410122359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8961938068884750426992957 3360726775831781410122359)
                ·
                  refine ⟨5041090163747672115183539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3360726775831781410122359 5041090163747672115183539)
                  ·
                    refine ⟨7561635245621508172775309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5041090163747672115183539 7561635245621508172775309)
                    ·
                      refine ⟨2835613217108065564790741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7561635245621508172775309 2835613217108065564790741)
                      ·
                        rfl

theorem cell23_5522337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_5522337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522337 prefixEnd_5522337 := by exact prefixLift 5522337
  have htrace : WordTrace (prefixWord ++ tailWord_5522337) baseStart_5522337 baseEnd_5522337 := by
    simpa [prefixWord, tailWord_5522337, baseEnd_5522337] using wordTrace_append hprefix tailTrace_5522337
  have hstable : (prefixWord ++ tailWord_5522337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522337).length < 2 ^ (prefixWord ++ tailWord_5522337).sum := by decide
  have hdescent : baseEnd_5522337 < baseStart_5522337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522339 : List Nat := [1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 4]
def baseStart_5522339 : Nat := 118140960795 + 5522339 * 2 ^ 59
def prefixEnd_5522339 : Nat := 4983230072969 + 3 ^ 40 * 5522339 * 2
def baseEnd_5522339 : Nat := 2835614244069374556965731

theorem tailTrace_5522339 : CollatzResearch.WordTrace tailWord_5522339 prefixEnd_5522339 2835614244069374556965731 := by
  unfold tailWord_5522339
  simp only [CollatzResearch.WordTrace]
  refine ⟨201416250340516418259066071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134277500227010945506044047 201416250340516418259066071)
  ·
    refine ⟨302124375510774627388599107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201416250340516418259066071 302124375510774627388599107)
    ·
      refine ⟨453186563266161941082898661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302124375510774627388599107 453186563266161941082898661)
      ·
        refine ⟨84972480612405363953043499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 453186563266161941082898661 84972480612405363953043499)
        ·
          refine ⟨127458720918608045929565249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84972480612405363953043499 127458720918608045929565249)
          ·
            refine ⟨95594040688956034447173937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127458720918608045929565249 95594040688956034447173937)
            ·
              refine ⟨71695530516717025835380453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95594040688956034447173937 71695530516717025835380453)
              ·
                refine ⟨13442911971884442344133835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71695530516717025835380453 13442911971884442344133835)
                ·
                  refine ⟨20164367957826663516200753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13442911971884442344133835 20164367957826663516200753)
                  ·
                    refine ⟨15123275968369997637150565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20164367957826663516200753 15123275968369997637150565)
                    ·
                      refine ⟨2835614244069374556965731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15123275968369997637150565 2835614244069374556965731)
                      ·
                        rfl

theorem cell23_5522339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_5522339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522339 prefixEnd_5522339 := by exact prefixLift 5522339
  have htrace : WordTrace (prefixWord ++ tailWord_5522339) baseStart_5522339 baseEnd_5522339 := by
    simpa [prefixWord, tailWord_5522339, baseEnd_5522339] using wordTrace_append hprefix tailTrace_5522339
  have hstable : (prefixWord ++ tailWord_5522339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522339).length < 2 ^ (prefixWord ++ tailWord_5522339).sum := by decide
  have hdescent : baseEnd_5522339 < baseStart_5522339 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522360 : List Nat := [2, 1, 2, 1, 2, 6, 1, 1, 3, 2, 2]
def baseStart_5522360 : Nat := 118140960795 + 5522360 * 2 ^ 59
def prefixEnd_5522360 : Nat := 4983230072969 + 3 ^ 40 * 5522360 * 2
def baseEnd_5522360 : Nat := 2835625027163118974803135

theorem tailTrace_5522360 : CollatzResearch.WordTrace tailWord_5522360 prefixEnd_5522360 2835625027163118974803135 := by
  unfold tailWord_5522360
  simp only [CollatzResearch.WordTrace]
  refine ⟨100708508136720169422790267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134278010848960225897053689 100708508136720169422790267)
  ·
    refine ⟨151062762205080254134185401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100708508136720169422790267 151062762205080254134185401)
    ·
      refine ⟨113297071653810190600639051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151062762205080254134185401 113297071653810190600639051)
      ·
        refine ⟨169945607480715285900958577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113297071653810190600639051 169945607480715285900958577)
        ·
          refine ⟨127459205610536464425718933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169945607480715285900958577 127459205610536464425718933)
          ·
            refine ⟨5974650262993896769955575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 127459205610536464425718933 5974650262993896769955575)
            ·
              refine ⟨8961975394490845154933363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5974650262993896769955575 8961975394490845154933363)
              ·
                refine ⟨13442963091736267732400045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8961975394490845154933363 13442963091736267732400045)
                ·
                  refine ⟨5041111159401100399650017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13442963091736267732400045 5041111159401100399650017)
                  ·
                    refine ⟨3780833369550825299737513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5041111159401100399650017 3780833369550825299737513)
                    ·
                      refine ⟨2835625027163118974803135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3780833369550825299737513 2835625027163118974803135)
                      ·
                        rfl

theorem cell23_5522360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 3, 2, 2].length) (baseStart_5522360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522360 prefixEnd_5522360 := by exact prefixLift 5522360
  have htrace : WordTrace (prefixWord ++ tailWord_5522360) baseStart_5522360 baseEnd_5522360 := by
    simpa [prefixWord, tailWord_5522360, baseEnd_5522360] using wordTrace_append hprefix tailTrace_5522360
  have hstable : (prefixWord ++ tailWord_5522360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522360).length < 2 ^ (prefixWord ++ tailWord_5522360).sum := by decide
  have hdescent : baseEnd_5522360 < baseStart_5522360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522410 : List Nat := [3, 1, 3, 1, 2, 3, 2, 2, 2, 1, 3]
def baseStart_5522410 : Nat := 118140960795 + 5522410 * 2 ^ 59
def prefixEnd_5522410 : Nat := 4983230072969 + 3 ^ 40 * 5522410 * 2
def baseEnd_5522410 : Nat := 2835650701195843779177905

theorem tailTrace_5522410 : CollatzResearch.WordTrace tailWord_5522410 prefixEnd_5522410 2835650701195843779177905 := by
  unfold tailWord_5522410
  simp only [CollatzResearch.WordTrace]
  refine ⟨50354709980814799346225171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134279226615506131589933789 50354709980814799346225171)
  ·
    refine ⟨75532064971222199019337757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50354709980814799346225171 75532064971222199019337757)
    ·
      refine ⟨28324524364208324632251659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75532064971222199019337757 28324524364208324632251659)
      ·
        refine ⟨42486786546312486948377489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28324524364208324632251659 42486786546312486948377489)
        ·
          refine ⟨31865089909734365211283117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42486786546312486948377489 31865089909734365211283117)
          ·
            refine ⟨11949408716150386954231169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31865089909734365211283117 11949408716150386954231169)
            ·
              refine ⟨8962056537112790215673377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11949408716150386954231169 8962056537112790215673377)
              ·
                refine ⟨6721542402834592661755033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8962056537112790215673377 6721542402834592661755033)
                ·
                  refine ⟨5041156802125944496316275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6721542402834592661755033 5041156802125944496316275)
                  ·
                    refine ⟨7561735203188916744474413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5041156802125944496316275 7561735203188916744474413)
                    ·
                      refine ⟨2835650701195843779177905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7561735203188916744474413 2835650701195843779177905)
                      ·
                        rfl

theorem cell23_5522410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_5522410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522410 prefixEnd_5522410 := by exact prefixLift 5522410
  have htrace : WordTrace (prefixWord ++ tailWord_5522410) baseStart_5522410 baseEnd_5522410 := by
    simpa [prefixWord, tailWord_5522410, baseEnd_5522410] using wordTrace_append hprefix tailTrace_5522410
  have hstable : (prefixWord ++ tailWord_5522410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522410).length < 2 ^ (prefixWord ++ tailWord_5522410).sum := by decide
  have hdescent : baseEnd_5522410 < baseStart_5522410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522416 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 5, 4, 2]
def baseStart_5522416 : Nat := 118140960795 + 5522416 * 2 ^ 59
def prefixEnd_5522416 : Nat := 4983230072969 + 3 ^ 40 * 5522416 * 2
def baseEnd_5522416 : Nat := 2835653782079770755702877

theorem tailTrace_5522416 : CollatzResearch.WordTrace tailWord_5522416 prefixEnd_5522416 2835653782079770755702877 := by
  unfold tailWord_5522416
  simp only [CollatzResearch.WordTrace]
  refine ⟨100709529380618730204809551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134279372507491640273079401 100709529380618730204809551)
  ·
    refine ⟨151064294070928095307214327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100709529380618730204809551 151064294070928095307214327)
    ·
      refine ⟨226596441106392142960821491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151064294070928095307214327 226596441106392142960821491)
      ·
        refine ⟨339894661659588214441232237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226596441106392142960821491 339894661659588214441232237)
        ·
          refine ⟨127460498122345580415462089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 339894661659588214441232237 127460498122345580415462089)
          ·
            refine ⟨95595373591759185311596567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127460498122345580415462089 95595373591759185311596567)
            ·
              refine ⟨143393060387638777967394851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95595373591759185311596567 143393060387638777967394851)
              ·
                refine ⟨215089590581458166951092277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143393060387638777967394851 215089590581458166951092277)
                ·
                  refine ⟨20164649117011703151664901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 215089590581458166951092277 20164649117011703151664901)
                  ·
                    refine ⟨3780871709439694340937169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20164649117011703151664901 3780871709439694340937169)
                    ·
                      refine ⟨2835653782079770755702877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3780871709439694340937169 2835653782079770755702877)
                      ·
                        rfl

theorem cell23_5522416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 5, 4, 2].length) (baseStart_5522416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522416 prefixEnd_5522416 := by exact prefixLift 5522416
  have htrace : WordTrace (prefixWord ++ tailWord_5522416) baseStart_5522416 baseEnd_5522416 := by
    simpa [prefixWord, tailWord_5522416, baseEnd_5522416] using wordTrace_append hprefix tailTrace_5522416
  have hstable : (prefixWord ++ tailWord_5522416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522416).length < 2 ^ (prefixWord ++ tailWord_5522416).sum := by decide
  have hdescent : baseEnd_5522416 < baseStart_5522416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522433 : List Nat := [1, 2, 4, 1, 2, 2, 1, 3, 1, 4, 2]
def baseStart_5522433 : Nat := 118140960795 + 5522433 * 2 ^ 59
def prefixEnd_5522433 : Nat := 4983230072969 + 3 ^ 40 * 5522433 * 2
def baseEnd_5522433 : Nat := 2835662511250897189190299

theorem tailTrace_5522433 : CollatzResearch.WordTrace tailWord_5522433 prefixEnd_5522433 2835662511250897189190299 := by
  unfold tailWord_5522433
  simp only [CollatzResearch.WordTrace]
  refine ⟨201419678802175872312987953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134279785868117248208658635 201419678802175872312987953)
  ·
    refine ⟨151064759101631904234740965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201419678802175872312987953 151064759101631904234740965)
    ·
      refine ⟨28324642331555982044013931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151064759101631904234740965 28324642331555982044013931)
      ·
        refine ⟨42486963497333973066020897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28324642331555982044013931 42486963497333973066020897)
        ·
          refine ⟨31865222623000479799515673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42486963497333973066020897 31865222623000479799515673)
          ·
            refine ⟨23898916967250359849636755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31865222623000479799515673 23898916967250359849636755)
            ·
              refine ⟨35848375450875539774455133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23898916967250359849636755 35848375450875539774455133)
              ·
                refine ⟨13443140794078327415420675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35848375450875539774455133 13443140794078327415420675)
                ·
                  refine ⟨20164711191117491123131013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13443140794078327415420675 20164711191117491123131013)
                  ·
                    refine ⟨3780883348334529585587065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20164711191117491123131013 3780883348334529585587065)
                    ·
                      refine ⟨2835662511250897189190299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3780883348334529585587065 2835662511250897189190299)
                      ·
                        rfl

theorem cell23_5522433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_5522433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522433 prefixEnd_5522433 := by exact prefixLift 5522433
  have htrace : WordTrace (prefixWord ++ tailWord_5522433) baseStart_5522433 baseEnd_5522433 := by
    simpa [prefixWord, tailWord_5522433, baseEnd_5522433] using wordTrace_append hprefix tailTrace_5522433
  have hstable : (prefixWord ++ tailWord_5522433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522433).length < 2 ^ (prefixWord ++ tailWord_5522433).sum := by decide
  have hdescent : baseEnd_5522433 < baseStart_5522433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522467 : List Nat := [1, 1, 1, 4, 3, 4, 1, 2, 2, 2, 2]
def baseStart_5522467 : Nat := 118140960795 + 5522467 * 2 ^ 59
def prefixEnd_5522467 : Nat := 4983230072969 + 3 ^ 40 * 5522467 * 2
def baseEnd_5522467 : Nat := 2835679969593150056165143

theorem tailTrace_5522467 : CollatzResearch.WordTrace tailWord_5522467 prefixEnd_5522467 2835679969593150056165143 := by
  unfold tailWord_5522467
  simp only [CollatzResearch.WordTrace]
  refine ⟨201420918884052696119725655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134280612589368464079817103 201420918884052696119725655)
  ·
    refine ⟨302131378326079044179588483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201420918884052696119725655 302131378326079044179588483)
    ·
      refine ⟨453197067489118566269382725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302131378326079044179588483 453197067489118566269382725)
      ·
        refine ⟨84974450154209731175509261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 453197067489118566269382725 84974450154209731175509261)
        ·
          refine ⟨31865418807828649190815973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84974450154209731175509261 31865418807828649190815973)
          ·
            refine ⟨5974766026467871723277995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31865418807828649190815973 5974766026467871723277995)
            ·
              refine ⟨8962149039701807584916993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5974766026467871723277995 8962149039701807584916993)
              ·
                refine ⟨6721611779776355688687745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8962149039701807584916993 6721611779776355688687745)
                ·
                  refine ⟨5041208834832266766515809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6721611779776355688687745 5041208834832266766515809)
                  ·
                    refine ⟨3780906626124200074886857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5041208834832266766515809 3780906626124200074886857)
                    ·
                      refine ⟨2835679969593150056165143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3780906626124200074886857 2835679969593150056165143)
                      ·
                        rfl

theorem cell23_5522467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 2, 2, 2].length) (baseStart_5522467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522467 prefixEnd_5522467 := by exact prefixLift 5522467
  have htrace : WordTrace (prefixWord ++ tailWord_5522467) baseStart_5522467 baseEnd_5522467 := by
    simpa [prefixWord, tailWord_5522467, baseEnd_5522467] using wordTrace_append hprefix tailTrace_5522467
  have hstable : (prefixWord ++ tailWord_5522467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522467).length < 2 ^ (prefixWord ++ tailWord_5522467).sum := by decide
  have hdescent : baseEnd_5522467 < baseStart_5522467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522479 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 5]
def baseStart_5522479 : Nat := 118140960795 + 5522479 * 2 ^ 59
def prefixEnd_5522479 : Nat := 4983230072969 + 3 ^ 40 * 5522479 * 2
def baseEnd_5522479 : Nat := 2835686131361004009215087

theorem tailTrace_5522479 : CollatzResearch.WordTrace tailWord_5522479 prefixEnd_5522479 2835686131361004009215087 := by
  unfold tailWord_5522479
  simp only [CollatzResearch.WordTrace]
  refine ⟨201421356560009222169162491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134280904373339481446108327 201421356560009222169162491)
  ·
    refine ⟨302132034840013833253743737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201421356560009222169162491 302132034840013833253743737)
    ·
      refine ⟨226599026130010374940307803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302132034840013833253743737 226599026130010374940307803)
      ·
        refine ⟨339898539195015562410461705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226599026130010374940307803 339898539195015562410461705)
        ·
          refine ⟨254923904396261671807846279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 339898539195015562410461705 254923904396261671807846279)
          ·
            refine ⟨382385856594392507711769419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254923904396261671807846279 382385856594392507711769419)
            ·
              refine ⟨573578784891588761567654129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382385856594392507711769419 573578784891588761567654129)
              ·
                refine ⟨430184088668691571175740597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 573578784891588761567654129 430184088668691571175740597)
                ·
                  refine ⟨40329758312689834797725681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 430184088668691571175740597 40329758312689834797725681)
                  ·
                    refine ⟨30247318734517376098294261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40329758312689834797725681 30247318734517376098294261)
                    ·
                      refine ⟨2835686131361004009215087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30247318734517376098294261 2835686131361004009215087)
                      ·
                        rfl

theorem cell23_5522479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 5].length) (baseStart_5522479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522479 prefixEnd_5522479 := by exact prefixLift 5522479
  have htrace : WordTrace (prefixWord ++ tailWord_5522479) baseStart_5522479 baseEnd_5522479 := by
    simpa [prefixWord, tailWord_5522479, baseEnd_5522479] using wordTrace_append hprefix tailTrace_5522479
  have hstable : (prefixWord ++ tailWord_5522479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522479).length < 2 ^ (prefixWord ++ tailWord_5522479).sum := by decide
  have hdescent : baseEnd_5522479 < baseStart_5522479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522499 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 2, 8]
def baseStart_5522499 : Nat := 118140960795 + 5522499 * 2 ^ 59
def prefixEnd_5522499 : Nat := 4983230072969 + 3 ^ 40 * 5522499 * 2
def baseEnd_5522499 : Nat := 945232133658031310321665

theorem tailTrace_5522499 : CollatzResearch.WordTrace tailWord_5522499 prefixEnd_5522499 945232133658031310321665 := by
  unfold tailWord_5522499
  simp only [CollatzResearch.WordTrace]
  refine ⟨201422086019936765584890551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134281390679957843723260367 201422086019936765584890551)
  ·
    refine ⟨302133129029905148377335827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201422086019936765584890551 302133129029905148377335827)
    ·
      refine ⟨453199693544857722566003741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302133129029905148377335827 453199693544857722566003741)
      ·
        refine ⟨169949885079321645962251403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 453199693544857722566003741 169949885079321645962251403)
        ·
          refine ⟨254924827618982468943377105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169949885079321645962251403 254924827618982468943377105)
          ·
            refine ⟨191193620714236851707532829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254924827618982468943377105 191193620714236851707532829)
            ·
              refine ⟨71697607767838819390324811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191193620714236851707532829 71697607767838819390324811)
              ·
                refine ⟨107546411651758229085487217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71697607767838819390324811 107546411651758229085487217)
                ·
                  refine ⟨80659808738818671814115413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107546411651758229085487217 80659808738818671814115413)
                  ·
                    refine ⟨945232133658031310321665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80659808738818671814115413 945232133658031310321665)
                    ·
                      rfl

theorem cell23_5522499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 8].length) (baseStart_5522499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522499 prefixEnd_5522499 := by exact prefixLift 5522499
  have htrace : WordTrace (prefixWord ++ tailWord_5522499) baseStart_5522499 baseEnd_5522499 := by
    simpa [prefixWord, tailWord_5522499, baseEnd_5522499] using wordTrace_append hprefix tailTrace_5522499
  have hstable : (prefixWord ++ tailWord_5522499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522499).length < 2 ^ (prefixWord ++ tailWord_5522499).sum := by decide
  have hdescent : baseEnd_5522499 < baseStart_5522499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522506 : List Nat := [3, 1, 2, 1, 1, 2, 4, 1, 1, 3, 4]
def baseStart_5522506 : Nat := 118140960795 + 5522506 * 2 ^ 59
def prefixEnd_5522506 : Nat := 4983230072969 + 3 ^ 40 * 5522506 * 2
def baseEnd_5522506 : Nat := 2835699995338675403577463

theorem tailTrace_5522506 : CollatzResearch.WordTrace tailWord_5522506 prefixEnd_5522506 2835699995338675403577463 := by
  unfold tailWord_5522506
  simp only [CollatzResearch.WordTrace]
  refine ⟨50355585332727851445098843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134281560887274270520263581 50355585332727851445098843)
  ·
    refine ⟨75533377999091777167648265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50355585332727851445098843 75533377999091777167648265)
    ·
      refine ⟨56650033499318832875736199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75533377999091777167648265 56650033499318832875736199)
      ·
        refine ⟨84975050248978249313604299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56650033499318832875736199 84975050248978249313604299)
        ·
          refine ⟨127462575373467373970406449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84975050248978249313604299 127462575373467373970406449)
          ·
            refine ⟨95596931530100530477804837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127462575373467373970406449 95596931530100530477804837)
            ·
              refine ⟨17924424661893849464588407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95596931530100530477804837 17924424661893849464588407)
              ·
                refine ⟨26886636992840774196882611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17924424661893849464588407 26886636992840774196882611)
                ·
                  refine ⟨40329955489261161295323917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26886636992840774196882611 40329955489261161295323917)
                  ·
                    refine ⟨15123733308472935485746469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40329955489261161295323917 15123733308472935485746469)
                    ·
                      refine ⟨2835699995338675403577463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15123733308472935485746469 2835699995338675403577463)
                      ·
                        rfl

theorem cell23_5522506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_5522506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522506 prefixEnd_5522506 := by exact prefixLift 5522506
  have htrace : WordTrace (prefixWord ++ tailWord_5522506) baseStart_5522506 baseEnd_5522506 := by
    simpa [prefixWord, tailWord_5522506, baseEnd_5522506] using wordTrace_append hprefix tailTrace_5522506
  have hstable : (prefixWord ++ tailWord_5522506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522506).length < 2 ^ (prefixWord ++ tailWord_5522506).sum := by decide
  have hdescent : baseEnd_5522506 < baseStart_5522506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522584 : List Nat := [2, 1, 2, 4, 2, 3, 2, 2, 1, 4]
def baseStart_5522584 : Nat := 118140960795 + 5522584 * 2 ^ 59
def prefixEnd_5522584 : Nat := 4983230072969 + 3 ^ 40 * 5522584 * 2
def baseEnd_5522584 : Nat := 945246682276575366134035

theorem tailTrace_5522584 : CollatzResearch.WordTrace tailWord_5522584 prefixEnd_5522584 945246682276575366134035 := by
  unfold tailWord_5522584
  simp only [CollatzResearch.WordTrace]
  refine ⟨100712593112314412550867403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134283457483085883401156537 100712593112314412550867403)
  ·
    refine ⟨151068889668471618826301105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100712593112314412550867403 151068889668471618826301105)
    ·
      refine ⟨113301667251353714119725829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151068889668471618826301105 113301667251353714119725829)
      ·
        refine ⟨21244062609628821397448593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113301667251353714119725829 21244062609628821397448593)
        ·
          refine ⟨15933046957221616048086445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21244062609628821397448593 15933046957221616048086445)
          ·
            refine ⟨5974892608958106018032417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15933046957221616048086445 5974892608958106018032417)
            ·
              refine ⟨4481169456718579513524313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5974892608958106018032417 4481169456718579513524313)
              ·
                refine ⟨3360877092538934635143235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4481169456718579513524313 3360877092538934635143235)
                ·
                  refine ⟨5041315638808401952714853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3360877092538934635143235 5041315638808401952714853)
                  ·
                    refine ⟨945246682276575366134035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5041315638808401952714853 945246682276575366134035)
                    ·
                      rfl

theorem cell23_5522584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 2, 1, 4].length) (baseStart_5522584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522584 prefixEnd_5522584 := by exact prefixLift 5522584
  have htrace : WordTrace (prefixWord ++ tailWord_5522584) baseStart_5522584 baseEnd_5522584 := by
    simpa [prefixWord, tailWord_5522584, baseEnd_5522584] using wordTrace_append hprefix tailTrace_5522584
  have hstable : (prefixWord ++ tailWord_5522584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522584).length < 2 ^ (prefixWord ++ tailWord_5522584).sum := by decide
  have hdescent : baseEnd_5522584 < baseStart_5522584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522616 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 5, 1, 5]
def baseStart_5522616 : Nat := 118140960795 + 5522616 * 2 ^ 59
def prefixEnd_5522616 : Nat := 4983230072969 + 3 ^ 40 * 5522616 * 2
def baseEnd_5522616 : Nat := 2835756478210669973201957

theorem tailTrace_5522616 : CollatzResearch.WordTrace tailWord_5522616 prefixEnd_5522616 2835756478210669973201957 := by
  unfold tailWord_5522616
  simp only [CollatzResearch.WordTrace]
  refine ⟨100713176680256447283449851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134284235573675263044599801 100713176680256447283449851)
  ·
    refine ⟨151069765020384670925174777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100713176680256447283449851 151069765020384670925174777)
    ·
      refine ⟨113302323765288503193881083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151069765020384670925174777 113302323765288503193881083)
      ·
        refine ⟨169953485647932754790821625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113302323765288503193881083 169953485647932754790821625)
        ·
          refine ⟨127465114235949566093116219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169953485647932754790821625 127465114235949566093116219)
          ·
            refine ⟨191197671353924349139674329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127465114235949566093116219 191197671353924349139674329)
            ·
              refine ⟨143398253515443261854755747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191197671353924349139674329 143398253515443261854755747)
              ·
                refine ⟨215097380273164892782133621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143398253515443261854755747 215097380273164892782133621)
                ·
                  refine ⟨20165379400609208698325027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 215097380273164892782133621 20165379400609208698325027)
                  ·
                    refine ⟨30248069100913813047487541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20165379400609208698325027 30248069100913813047487541)
                    ·
                      refine ⟨2835756478210669973201957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30248069100913813047487541 2835756478210669973201957)
                      ·
                        rfl

theorem cell23_5522616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_5522616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522616 prefixEnd_5522616 := by exact prefixLift 5522616
  have htrace : WordTrace (prefixWord ++ tailWord_5522616) baseStart_5522616 baseEnd_5522616 := by
    simpa [prefixWord, tailWord_5522616, baseEnd_5522616] using wordTrace_append hprefix tailTrace_5522616
  have hstable : (prefixWord ++ tailWord_5522616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522616).length < 2 ^ (prefixWord ++ tailWord_5522616).sum := by decide
  have hdescent : baseEnd_5522616 < baseStart_5522616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522617 : List Nat := [1, 2, 1, 4, 1, 5, 1, 1, 2, 3, 2]
def baseStart_5522617 : Nat := 118140960795 + 5522617 * 2 ^ 59
def prefixEnd_5522617 : Nat := 4983230072969 + 3 ^ 40 * 5522617 * 2
def baseEnd_5522617 : Nat := 2835756991691324469289453

theorem tailTrace_5522617 : CollatzResearch.WordTrace tailWord_5522617 prefixEnd_5522617 2835756991691324469289453 := by
  unfold tailWord_5522617
  simp only [CollatzResearch.WordTrace]
  refine ⟨201426389833509271737686105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134284259889006181158457403 201426389833509271737686105)
  ·
    refine ⟨151069792375131953803264579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201426389833509271737686105 151069792375131953803264579)
    ·
      refine ⟨226604688562697930704896869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151069792375131953803264579 226604688562697930704896869)
      ·
        refine ⟨42488379105505862007168163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 226604688562697930704896869 42488379105505862007168163)
        ·
          refine ⟨63732568658258793010752245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42488379105505862007168163 63732568658258793010752245)
          ·
            refine ⟨5974928311711761844758023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63732568658258793010752245 5974928311711761844758023)
            ·
              refine ⟨8962392467567642767137035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5974928311711761844758023 8962392467567642767137035)
              ·
                refine ⟨13443588701351464150705553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8962392467567642767137035 13443588701351464150705553)
                ·
                  refine ⟨10082691526013598113029165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13443588701351464150705553 10082691526013598113029165)
                  ·
                    refine ⟨3781009322255099292385937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10082691526013598113029165 3781009322255099292385937)
                    ·
                      refine ⟨2835756991691324469289453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3781009322255099292385937 2835756991691324469289453)
                      ·
                        rfl

theorem cell23_5522617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_5522617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522617 prefixEnd_5522617 := by exact prefixLift 5522617
  have htrace : WordTrace (prefixWord ++ tailWord_5522617) baseStart_5522617 baseEnd_5522617 := by
    simpa [prefixWord, tailWord_5522617, baseEnd_5522617] using wordTrace_append hprefix tailTrace_5522617
  have hstable : (prefixWord ++ tailWord_5522617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522617).length < 2 ^ (prefixWord ++ tailWord_5522617).sum := by decide
  have hdescent : baseEnd_5522617 < baseStart_5522617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522624 : List Nat := [2, 1, 1, 2, 6, 1, 2, 3, 1, 1, 3]
def baseStart_5522624 : Nat := 118140960795 + 5522624 * 2 ^ 59
def prefixEnd_5522624 : Nat := 4983230072969 + 3 ^ 40 * 5522624 * 2
def baseEnd_5522624 : Nat := 2835760586055905941901921

theorem tailTrace_5522624 : CollatzResearch.WordTrace tailWord_5522624 prefixEnd_5522624 2835760586055905941901921 := by
  unfold tailWord_5522624
  simp only [CollatzResearch.WordTrace]
  refine ⟨100713322572241955966595463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134284430096322607955460617 100713322572241955966595463)
  ·
    refine ⟨151069983858362933949893195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100713322572241955966595463 151069983858362933949893195)
    ·
      refine ⟨226604975787544400924839793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151069983858362933949893195 226604975787544400924839793)
      ·
        refine ⟨169953731840658300693629845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226604975787544400924839793 169953731840658300693629845)
        ·
          refine ⟨7966581180030857845013899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 169953731840658300693629845 7966581180030857845013899)
          ·
            refine ⟨11949871770046286767520849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7966581180030857845013899 11949871770046286767520849)
            ·
              refine ⟨8962403827534715075640637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11949871770046286767520849 8962403827534715075640637)
              ·
                refine ⟨3360901435325518153365239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8962403827534715075640637 3360901435325518153365239)
                ·
                  refine ⟨5041352152988277230047859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3360901435325518153365239 5041352152988277230047859)
                  ·
                    refine ⟨7562028229482415845071789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5041352152988277230047859 7562028229482415845071789)
                    ·
                      refine ⟨2835760586055905941901921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7562028229482415845071789 2835760586055905941901921)
                      ·
                        rfl

theorem cell23_5522624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 3, 1, 1, 3].length) (baseStart_5522624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522624 prefixEnd_5522624 := by exact prefixLift 5522624
  have htrace : WordTrace (prefixWord ++ tailWord_5522624) baseStart_5522624 baseEnd_5522624 := by
    simpa [prefixWord, tailWord_5522624, baseEnd_5522624] using wordTrace_append hprefix tailTrace_5522624
  have hstable : (prefixWord ++ tailWord_5522624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522624).length < 2 ^ (prefixWord ++ tailWord_5522624).sum := by decide
  have hdescent : baseEnd_5522624 < baseStart_5522624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522657 : List Nat := [1, 2, 3, 1, 3, 3, 3, 1, 2, 4]
def baseStart_5522657 : Nat := 118140960795 + 5522657 * 2 ^ 59
def prefixEnd_5522657 : Nat := 4983230072969 + 3 ^ 40 * 5522657 * 2
def baseEnd_5522657 : Nat := 945259176972501437596423

theorem tailTrace_5522657 : CollatzResearch.WordTrace tailWord_5522657 prefixEnd_5522657 945259176972501437596423 := by
  unfold tailWord_5522657
  simp only [CollatzResearch.WordTrace]
  refine ⟨201427848753364358569142225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134285232502242905712761483 201427848753364358569142225)
  ·
    refine ⟨151070886565023268926856669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201427848753364358569142225 151070886565023268926856669)
    ·
      refine ⟨56651582461883725847571251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151070886565023268926856669 56651582461883725847571251)
      ·
        refine ⟨84977373692825588771356877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56651582461883725847571251 84977373692825588771356877)
        ·
          refine ⟨31866515134809595789258829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84977373692825588771356877 31866515134809595789258829)
          ·
            refine ⟨11949943175553598420972061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31866515134809595789258829 11949943175553598420972061)
            ·
              refine ⟨4481228690832599407864523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11949943175553598420972061 4481228690832599407864523)
              ·
                refine ⟨6721843036248899111796785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4481228690832599407864523 6721843036248899111796785)
                ·
                  refine ⟨5041382277186674333847589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6721843036248899111796785 5041382277186674333847589)
                  ·
                    refine ⟨945259176972501437596423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5041382277186674333847589 945259176972501437596423)
                    ·
                      rfl

theorem cell23_5522657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 2, 4].length) (baseStart_5522657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522657 prefixEnd_5522657 := by exact prefixLift 5522657
  have htrace : WordTrace (prefixWord ++ tailWord_5522657) baseStart_5522657 baseEnd_5522657 := by
    simpa [prefixWord, tailWord_5522657, baseEnd_5522657] using wordTrace_append hprefix tailTrace_5522657
  have hstable : (prefixWord ++ tailWord_5522657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522657).length < 2 ^ (prefixWord ++ tailWord_5522657).sum := by decide
  have hdescent : baseEnd_5522657 < baseStart_5522657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522714 : List Nat := [3, 1, 1, 3, 3, 1, 4, 1, 2, 1, 3]
def baseStart_5522714 : Nat := 118140960795 + 5522714 * 2 ^ 59
def prefixEnd_5522714 : Nat := 4983230072969 + 3 ^ 40 * 5522714 * 2
def baseEnd_5522714 : Nat := 2835806799314810589776507

theorem tailTrace_5522714 : CollatzResearch.WordTrace tailWord_5522714 prefixEnd_5522714 2835806799314810589776507 := by
  unfold tailWord_5522714
  simp only [CollatzResearch.WordTrace]
  refine ⟨50357481928539464325991799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134286618476105238202644797 50357481928539464325991799)
  ·
    refine ⟨75536222892809196488987699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50357481928539464325991799 75536222892809196488987699)
    ·
      refine ⟨113304334339213794733481549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75536222892809196488987699 113304334339213794733481549)
      ·
        refine ⟨42489125377205173025055581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113304334339213794733481549 42489125377205173025055581)
        ·
          refine ⟨15933422016451939884395843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42489125377205173025055581 15933422016451939884395843)
          ·
            refine ⟨23900133024677909826593765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15933422016451939884395843 23900133024677909826593765)
            ·
              refine ⟨4481274942127108092486331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23900133024677909826593765 4481274942127108092486331)
              ·
                refine ⟨6721912413190662138729497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4481274942127108092486331 6721912413190662138729497)
                ·
                  refine ⟨5041434309892996604047123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6721912413190662138729497 5041434309892996604047123)
                  ·
                    refine ⟨7562151464839494906070685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5041434309892996604047123 7562151464839494906070685)
                    ·
                      refine ⟨2835806799314810589776507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7562151464839494906070685 2835806799314810589776507)
                      ·
                        rfl

theorem cell23_5522714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_5522714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522714 prefixEnd_5522714 := by exact prefixLift 5522714
  have htrace : WordTrace (prefixWord ++ tailWord_5522714) baseStart_5522714 baseEnd_5522714 := by
    simpa [prefixWord, tailWord_5522714, baseEnd_5522714] using wordTrace_append hprefix tailTrace_5522714
  have hstable : (prefixWord ++ tailWord_5522714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522714).length < 2 ^ (prefixWord ++ tailWord_5522714).sum := by decide
  have hdescent : baseEnd_5522714 < baseStart_5522714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522718 : List Nat := [4, 3, 2, 1, 3, 1, 1, 2, 1, 2, 3]
def baseStart_5522718 : Nat := 118140960795 + 5522718 * 2 ^ 59
def prefixEnd_5522718 : Nat := 4983230072969 + 3 ^ 40 * 5522718 * 2
def baseEnd_5522718 : Nat := 2835808853237428574126489

theorem tailTrace_5522718 : CollatzResearch.WordTrace tailWord_5522718 prefixEnd_5522718 2835808853237428574126489 := by
  unfold tailWord_5522718
  simp only [CollatzResearch.WordTrace]
  refine ⟨25178759200767920748389101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134286715737428910658075205 25178759200767920748389101)
  ·
    refine ⟨9442034700287970280645913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25178759200767920748389101 9442034700287970280645913)
    ·
      refine ⟨7081526025215977710484435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9442034700287970280645913 7081526025215977710484435)
      ·
        refine ⟨10622289037823966565726653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7081526025215977710484435 10622289037823966565726653)
        ·
          refine ⟨3983358389183987462147495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10622289037823966565726653 3983358389183987462147495)
          ·
            refine ⟨5975037583775981193221243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3983358389183987462147495 5975037583775981193221243)
            ·
              refine ⟨8962556375663971789831865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5975037583775981193221243 8962556375663971789831865)
              ·
                refine ⟨6721917281747978842373899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8962556375663971789831865 6721917281747978842373899)
                ·
                  refine ⟨10082875922621968263560849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6721917281747978842373899 10082875922621968263560849)
                  ·
                    refine ⟨7562156941966476197670637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10082875922621968263560849 7562156941966476197670637)
                    ·
                      refine ⟨2835808853237428574126489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7562156941966476197670637 2835808853237428574126489)
                      ·
                        rfl

theorem cell23_5522718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_5522718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522718 prefixEnd_5522718 := by exact prefixLift 5522718
  have htrace : WordTrace (prefixWord ++ tailWord_5522718) baseStart_5522718 baseEnd_5522718 := by
    simpa [prefixWord, tailWord_5522718, baseEnd_5522718] using wordTrace_append hprefix tailTrace_5522718
  have hstable : (prefixWord ++ tailWord_5522718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522718).length < 2 ^ (prefixWord ++ tailWord_5522718).sum := by decide
  have hdescent : baseEnd_5522718 < baseStart_5522718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522723 : List Nat := [1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 5]
def baseStart_5522723 : Nat := 118140960795 + 5522723 * 2 ^ 59
def prefixEnd_5522723 : Nat := 4983230072969 + 3 ^ 40 * 5522723 * 2
def baseEnd_5522723 : Nat := 2835811420640701054563965

theorem tailTrace_5522723 : CollatzResearch.WordTrace tailWord_5522723 prefixEnd_5522723 2835811420640701054563965 := by
  unfold tailWord_5522723
  simp only [CollatzResearch.WordTrace]
  refine ⟨201430255971125251841044823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134286837314083501227363215 201430255971125251841044823)
  ·
    refine ⟨302145383956687877761567235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201430255971125251841044823 302145383956687877761567235)
    ·
      refine ⟨453218075935031816642350853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302145383956687877761567235 453218075935031816642350853)
      ·
        refine ⟨84978389237818465620440785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 453218075935031816642350853 84978389237818465620440785)
        ·
          refine ⟨63733791928363849215330589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84978389237818465620440785 63733791928363849215330589)
          ·
            refine ⟨23900171973136443455748971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63733791928363849215330589 23900171973136443455748971)
            ·
              refine ⟨35850257959704665183623457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23900171973136443455748971 35850257959704665183623457)
              ·
                refine ⟨26887693469778498887717593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35850257959704665183623457 26887693469778498887717593)
                ·
                  refine ⟨20165770102333874165788195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26887693469778498887717593 20165770102333874165788195)
                  ·
                    refine ⟨30248655153500811248682293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20165770102333874165788195 30248655153500811248682293)
                    ·
                      refine ⟨2835811420640701054563965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30248655153500811248682293 2835811420640701054563965)
                      ·
                        rfl

theorem cell23_5522723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_5522723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522723 prefixEnd_5522723 := by exact prefixLift 5522723
  have htrace : WordTrace (prefixWord ++ tailWord_5522723) baseStart_5522723 baseEnd_5522723 := by
    simpa [prefixWord, tailWord_5522723, baseEnd_5522723] using wordTrace_append hprefix tailTrace_5522723
  have hstable : (prefixWord ++ tailWord_5522723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522723).length < 2 ^ (prefixWord ++ tailWord_5522723).sum := by decide
  have hdescent : baseEnd_5522723 < baseStart_5522723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522737 : List Nat := [1, 2, 2, 3, 3, 2, 1, 2, 1, 4, 2]
def baseStart_5522737 : Nat := 118140960795 + 5522737 * 2 ^ 59
def prefixEnd_5522737 : Nat := 4983230072969 + 3 ^ 40 * 5522737 * 2
def baseEnd_5522737 : Nat := 2835818609369863999788901

theorem tailTrace_5522737 : CollatzResearch.WordTrace tailWord_5522737 prefixEnd_5522737 2835818609369863999788901 := by
  unfold tailWord_5522737
  simp only [CollatzResearch.WordTrace]
  refine ⟨201430766593074532232054465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134287177728716354821369643 201430766593074532232054465)
  ·
    refine ⟨151073074944805899174040849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201430766593074532232054465 151073074944805899174040849)
    ·
      refine ⟨113304806208604424380530637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151073074944805899174040849 113304806208604424380530637)
      ·
        refine ⟨42489302328226659142698989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113304806208604424380530637 42489302328226659142698989)
        ·
          refine ⟨15933488373084997178512121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42489302328226659142698989 15933488373084997178512121)
          ·
            refine ⟨11950116279813747883884091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15933488373084997178512121 11950116279813747883884091)
            ·
              refine ⟨17925174419720621825826137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11950116279813747883884091 17925174419720621825826137)
              ·
                refine ⟨13443880814790466369369603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17925174419720621825826137 13443880814790466369369603)
                ·
                  refine ⟨20165821222185699554054405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13443880814790466369369603 20165821222185699554054405)
                  ·
                    refine ⟨3781091479159818666385201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20165821222185699554054405 3781091479159818666385201)
                    ·
                      refine ⟨2835818609369863999788901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3781091479159818666385201 2835818609369863999788901)
                      ·
                        rfl

theorem cell23_5522737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_5522737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522737 prefixEnd_5522737 := by exact prefixLift 5522737
  have htrace : WordTrace (prefixWord ++ tailWord_5522737) baseStart_5522737 baseEnd_5522737 := by
    simpa [prefixWord, tailWord_5522737, baseEnd_5522737] using wordTrace_append hprefix tailTrace_5522737
  have hstable : (prefixWord ++ tailWord_5522737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522737).length < 2 ^ (prefixWord ++ tailWord_5522737).sum := by decide
  have hdescent : baseEnd_5522737 < baseStart_5522737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522740 : List Nat := [2, 5, 1, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_5522740 : Nat := 118140960795 + 5522740 * 2 ^ 59
def prefixEnd_5522740 : Nat := 4983230072969 + 3 ^ 40 * 5522740 * 2
def baseEnd_5522740 : Nat := 2835820149811827488051387

theorem tailTrace_5522740 : CollatzResearch.WordTrace tailWord_5522740 prefixEnd_5522740 2835820149811827488051387 := by
  unfold tailWord_5522740
  simp only [CollatzResearch.WordTrace]
  refine ⟨100715438006031831872206837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134287250674709109162942449 100715438006031831872206837)
  ·
    refine ⟨9442072313065484238019391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 100715438006031831872206837 9442072313065484238019391)
    ·
      refine ⟨14163108469598226357029087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9442072313065484238019391 14163108469598226357029087)
      ·
        refine ⟨21244662704397339535543631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14163108469598226357029087 21244662704397339535543631)
        ·
          refine ⟨31866994056596009303315447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21244662704397339535543631 31866994056596009303315447)
          ·
            refine ⟨47800491084894013954973171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31866994056596009303315447 47800491084894013954973171)
            ·
              refine ⟨71700736627341020932459757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47800491084894013954973171 71700736627341020932459757)
              ·
                refine ⟨26887776235252882849672409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71700736627341020932459757 26887776235252882849672409)
                ·
                  refine ⟨20165832176439662137254307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26887776235252882849672409 20165832176439662137254307)
                  ·
                    refine ⟨30248748264659493205881461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20165832176439662137254307 30248748264659493205881461)
                    ·
                      refine ⟨2835820149811827488051387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30248748264659493205881461 2835820149811827488051387)
                      ·
                        rfl

theorem cell23_5522740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_5522740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522740 prefixEnd_5522740 := by exact prefixLift 5522740
  have htrace : WordTrace (prefixWord ++ tailWord_5522740) baseStart_5522740 baseEnd_5522740 := by
    simpa [prefixWord, tailWord_5522740, baseEnd_5522740] using wordTrace_append hprefix tailTrace_5522740
  have hstable : (prefixWord ++ tailWord_5522740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522740).length < 2 ^ (prefixWord ++ tailWord_5522740).sum := by decide
  have hdescent : baseEnd_5522740 < baseStart_5522740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522750 : List Nat := [4, 2, 1, 2, 1, 1, 2, 2, 2, 2, 4]
def baseStart_5522750 : Nat := 118140960795 + 5522750 * 2 ^ 59
def prefixEnd_5522750 : Nat := 4983230072969 + 3 ^ 40 * 5522750 * 2
def baseEnd_5522750 : Nat := 2835825284618372448926341

theorem tailTrace_5522750 : CollatzResearch.WordTrace tailWord_5522750 prefixEnd_5522750 2835825284618372448926341 := by
  unfold tailWord_5522750
  simp only [CollatzResearch.WordTrace]
  refine ⟨25178905092753429431534713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134287493828018290301518469 25178905092753429431534713)
  ·
    refine ⟨18884178819565072073651035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25178905092753429431534713 18884178819565072073651035)
    ·
      refine ⟨28326268229347608110476553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18884178819565072073651035 28326268229347608110476553)
      ·
        refine ⟨21244701172010706082857415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28326268229347608110476553 21244701172010706082857415)
        ·
          refine ⟨31867051758016059124286123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21244701172010706082857415 31867051758016059124286123)
          ·
            refine ⟨47800577637024088686429185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31867051758016059124286123 47800577637024088686429185)
            ·
              refine ⟨35850433227768066514821889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47800577637024088686429185 35850433227768066514821889)
              ·
                refine ⟨26887824920826049886116417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35850433227768066514821889 26887824920826049886116417)
                ·
                  refine ⟨20165868690619537414587313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26887824920826049886116417 20165868690619537414587313)
                  ·
                    refine ⟨15124401517964653060940485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20165868690619537414587313 15124401517964653060940485)
                    ·
                      refine ⟨2835825284618372448926341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15124401517964653060940485 2835825284618372448926341)
                      ·
                        rfl

theorem cell23_5522750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_5522750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522750 prefixEnd_5522750 := by exact prefixLift 5522750
  have htrace : WordTrace (prefixWord ++ tailWord_5522750) baseStart_5522750 baseEnd_5522750 := by
    simpa [prefixWord, tailWord_5522750, baseEnd_5522750] using wordTrace_append hprefix tailTrace_5522750
  have hstable : (prefixWord ++ tailWord_5522750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522750).length < 2 ^ (prefixWord ++ tailWord_5522750).sum := by decide
  have hdescent : baseEnd_5522750 < baseStart_5522750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522794 : List Nat := [3, 1, 3, 3, 2, 1, 2, 3, 5]
def baseStart_5522794 : Nat := 118140960795 + 5522794 * 2 ^ 59
def prefixEnd_5522794 : Nat := 4983230072969 + 3 ^ 40 * 5522794 * 2
def baseEnd_5522794 : Nat := 315094208640796697419571

theorem tailTrace_5522794 : CollatzResearch.WordTrace tailWord_5522794 prefixEnd_5522794 315094208640796697419571 := by
  unfold tailWord_5522794
  simp only [CollatzResearch.WordTrace]
  refine ⟨50358211388467007741719859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134288563702578687311252957 50358211388467007741719859)
  ·
    refine ⟨75537317082700511612579789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50358211388467007741719859 75537317082700511612579789)
    ·
      refine ⟨28326493906012691854717421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75537317082700511612579789 28326493906012691854717421)
      ·
        refine ⟨10622435214754759445519033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28326493906012691854717421 10622435214754759445519033)
        ·
          refine ⟨7966826411066069584139275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10622435214754759445519033 7966826411066069584139275)
          ·
            refine ⟨11950239616599104376208913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7966826411066069584139275 11950239616599104376208913)
            ·
              refine ⟨8962679712449328282156685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11950239616599104376208913 8962679712449328282156685)
              ·
                refine ⟨3361004892168498105808757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8962679712449328282156685 3361004892168498105808757)
                ·
                  refine ⟨315094208640796697419571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3361004892168498105808757 315094208640796697419571)
                  ·
                    rfl

theorem cell23_5522794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 3, 5].length) (baseStart_5522794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522794 prefixEnd_5522794 := by exact prefixLift 5522794
  have htrace : WordTrace (prefixWord ++ tailWord_5522794) baseStart_5522794 baseEnd_5522794 := by
    simpa [prefixWord, tailWord_5522794, baseEnd_5522794] using wordTrace_append hprefix tailTrace_5522794
  have hstable : (prefixWord ++ tailWord_5522794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522794).length < 2 ^ (prefixWord ++ tailWord_5522794).sum := by decide
  have hdescent : baseEnd_5522794 < baseStart_5522794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522810 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 3, 6, 2]
def baseStart_5522810 : Nat := 118140960795 + 5522810 * 2 ^ 59
def prefixEnd_5522810 : Nat := 4983230072969 + 3 ^ 40 * 5522810 * 2
def baseEnd_5522810 : Nat := 2835856093457642214176065

theorem tailTrace_5522810 : CollatzResearch.WordTrace tailWord_5522810 prefixEnd_5522810 2835856093457642214176065 := by
  unfold tailWord_5522810
  simp only [CollatzResearch.WordTrace]
  refine ⟨50358357280452516424865471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134288952747873377132974589 50358357280452516424865471)
  ·
    refine ⟨75537535920678774637298207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50358357280452516424865471 75537535920678774637298207)
    ·
      refine ⟨113306303881018161955947311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75537535920678774637298207 113306303881018161955947311)
      ·
        refine ⟨169959455821527242933920967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113306303881018161955947311 169959455821527242933920967)
        ·
          refine ⟨254939183732290864400881451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169959455821527242933920967 254939183732290864400881451)
          ·
            refine ⟨382408775598436296601322177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254939183732290864400881451 382408775598436296601322177)
            ·
              refine ⟨286806581698827222450991633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 382408775598436296601322177 286806581698827222450991633)
              ·
                refine ⟨215104936274120416838243725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 286806581698827222450991633 215104936274120416838243725)
                ·
                  refine ⟨80664351102795156314341397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 215104936274120416838243725 80664351102795156314341397)
                  ·
                    refine ⟨3781141457943522952234753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 80664351102795156314341397 3781141457943522952234753)
                    ·
                      refine ⟨2835856093457642214176065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3781141457943522952234753 2835856093457642214176065)
                      ·
                        rfl

theorem cell23_5522810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 3, 6, 2].length) (baseStart_5522810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522810 prefixEnd_5522810 := by exact prefixLift 5522810
  have htrace : WordTrace (prefixWord ++ tailWord_5522810) baseStart_5522810 baseEnd_5522810 := by
    simpa [prefixWord, tailWord_5522810, baseEnd_5522810] using wordTrace_append hprefix tailTrace_5522810
  have hstable : (prefixWord ++ tailWord_5522810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522810).length < 2 ^ (prefixWord ++ tailWord_5522810).sum := by decide
  have hdescent : baseEnd_5522810 < baseStart_5522810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522850 : List Nat := [3, 3, 1, 2, 1, 2, 1, 2, 8]
def baseStart_5522850 : Nat := 118140960795 + 5522850 * 2 ^ 59
def prefixEnd_5522850 : Nat := 4983230072969 + 3 ^ 40 * 5522850 * 2
def baseEnd_5522850 : Nat := 315097403631535784186209

theorem tailTrace_5522850 : CollatzResearch.WordTrace tailWord_5522850 prefixEnd_5522850 315097403631535784186209 := by
  unfold tailWord_5522850
  simp only [CollatzResearch.WordTrace]
  refine ⟨50358722010416288132729501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134289925361110101687278669 50358722010416288132729501)
  ·
    refine ⟨18884520753906108049773563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50358722010416288132729501 18884520753906108049773563)
    ·
      refine ⟨28326781130859162074660345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18884520753906108049773563 28326781130859162074660345)
      ·
        refine ⟨21245085848144371555995259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28326781130859162074660345 21245085848144371555995259)
        ·
          refine ⟨31867628772216557333992889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21245085848144371555995259 31867628772216557333992889)
          ·
            refine ⟨23900721579162418000494667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31867628772216557333992889 23900721579162418000494667)
            ·
              refine ⟨35851082368743627000742001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23900721579162418000494667 35851082368743627000742001)
              ·
                refine ⟨26888311776557720250556501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35851082368743627000742001 26888311776557720250556501)
                ·
                  refine ⟨315097403631535784186209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26888311776557720250556501 315097403631535784186209)
                  ·
                    rfl

theorem cell23_5522850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_5522850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522850 prefixEnd_5522850 := by exact prefixLift 5522850
  have htrace : WordTrace (prefixWord ++ tailWord_5522850) baseStart_5522850 baseEnd_5522850 := by
    simpa [prefixWord, tailWord_5522850, baseEnd_5522850] using wordTrace_append hprefix tailTrace_5522850
  have hstable : (prefixWord ++ tailWord_5522850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522850).length < 2 ^ (prefixWord ++ tailWord_5522850).sum := by decide
  have hdescent : baseEnd_5522850 < baseStart_5522850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522853 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 1, 1, 8]
def baseStart_5522853 : Nat := 118140960795 + 5522853 * 2 ^ 59
def prefixEnd_5522853 : Nat := 4983230072969 + 3 ^ 40 * 5522853 * 2
def baseEnd_5522853 : Nat := 2835878173125785545938367

theorem tailTrace_5522853 : CollatzResearch.WordTrace tailWord_5522853 prefixEnd_5522853 2835878173125785545938367 := by
  unfold tailWord_5522853
  simp only [CollatzResearch.WordTrace]
  refine ⟨201434997460654284043277213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134289998307102856028851475 201434997460654284043277213)
  ·
    refine ⟨75538124047745356516228955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201434997460654284043277213 75538124047745356516228955)
    ·
      refine ⟨113307186071618034774343433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75538124047745356516228955 113307186071618034774343433)
      ·
        refine ⟨84980389553713526080757575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113307186071618034774343433 84980389553713526080757575)
        ·
          refine ⟨127470584330570289121136363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84980389553713526080757575 127470584330570289121136363)
          ·
            refine ⟨191205876495855433681704545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127470584330570289121136363 191205876495855433681704545)
            ·
              refine ⟨143404407371891575261278409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191205876495855433681704545 143404407371891575261278409)
              ·
                refine ⟨107553305528918681445958807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143404407371891575261278409 107553305528918681445958807)
                ·
                  refine ⟨161329958293378022168938211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107553305528918681445958807 161329958293378022168938211)
                  ·
                    refine ⟨241994937440067033253407317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 161329958293378022168938211 241994937440067033253407317)
                    ·
                      refine ⟨2835878173125785545938367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 241994937440067033253407317 2835878173125785545938367)
                      ·
                        rfl

theorem cell23_5522853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_5522853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522853 prefixEnd_5522853 := by exact prefixLift 5522853
  have htrace : WordTrace (prefixWord ++ tailWord_5522853) baseStart_5522853 baseEnd_5522853 := by
    simpa [prefixWord, tailWord_5522853, baseEnd_5522853] using wordTrace_append hprefix tailTrace_5522853
  have hstable : (prefixWord ++ tailWord_5522853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522853).length < 2 ^ (prefixWord ++ tailWord_5522853).sum := by decide
  have hdescent : baseEnd_5522853 < baseStart_5522853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522884 : List Nat := [2, 3, 3, 2, 1, 1, 4, 1, 6]
def baseStart_5522884 : Nat := 118140960795 + 5522884 * 2 ^ 59
def prefixEnd_5522884 : Nat := 4983230072969 + 3 ^ 40 * 5522884 * 2
def baseEnd_5522884 : Nat := 315099343447341658294525

theorem tailTrace_5522884 : CollatzResearch.WordTrace tailWord_5522884 prefixEnd_5522884 315099343447341658294525 := by
  unfold tailWord_5522884
  simp only [CollatzResearch.WordTrace]
  refine ⟨100718064061770988168827853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134290752082361317558437137 100718064061770988168827853)
  ·
    refine ⟨37769274023164120563310445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100718064061770988168827853 37769274023164120563310445)
    ·
      refine ⟨14163477758686545211241417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37769274023164120563310445 14163477758686545211241417)
      ·
        refine ⟨10622608319014908908431063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14163477758686545211241417 10622608319014908908431063)
        ·
          refine ⟨15933912478522363362646595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10622608319014908908431063 15933912478522363362646595)
          ·
            refine ⟨23900868717783545043969893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15933912478522363362646595 23900868717783545043969893)
            ·
              refine ⟨4481412884584414695744355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23900868717783545043969893 4481412884584414695744355)
              ·
                refine ⟨6722119326876622043616533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4481412884584414695744355 6722119326876622043616533)
                ·
                  refine ⟨315099343447341658294525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6722119326876622043616533 315099343447341658294525)
                  ·
                    rfl

theorem cell23_5522884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 6].length) (baseStart_5522884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522884 prefixEnd_5522884 := by exact prefixLift 5522884
  have htrace : WordTrace (prefixWord ++ tailWord_5522884) baseStart_5522884 baseEnd_5522884 := by
    simpa [prefixWord, tailWord_5522884, baseEnd_5522884] using wordTrace_append hprefix tailTrace_5522884
  have hstable : (prefixWord ++ tailWord_5522884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522884).length < 2 ^ (prefixWord ++ tailWord_5522884).sum := by decide
  have hdescent : baseEnd_5522884 < baseStart_5522884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522887 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 4, 3, 2]
def baseStart_5522887 : Nat := 118140960795 + 5522887 * 2 ^ 59
def prefixEnd_5522887 : Nat := 4983230072969 + 3 ^ 40 * 5522887 * 2
def baseEnd_5522887 : Nat := 2835895631468038412913211

theorem tailTrace_5522887 : CollatzResearch.WordTrace tailWord_5522887 prefixEnd_5522887 2835895631468038412913211 := by
  unfold tailWord_5522887
  simp only [CollatzResearch.WordTrace]
  refine ⟨201436237542531107850014915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134290825028354071900009943 201436237542531107850014915)
  ·
    refine ⟨302154356313796661775022373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201436237542531107850014915 302154356313796661775022373)
    ·
      refine ⟨56653941808836874082816695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 302154356313796661775022373 56653941808836874082816695)
      ·
        refine ⟨84980912713255311124225043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56653941808836874082816695 84980912713255311124225043)
        ·
          refine ⟨127471369069882966686337565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84980912713255311124225043 127471369069882966686337565)
          ·
            refine ⟨47801763401206112507376587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127471369069882966686337565 47801763401206112507376587)
            ·
              refine ⟨71702645101809168761064881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47801763401206112507376587 71702645101809168761064881)
              ·
                refine ⟨53776983826356876570798661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71702645101809168761064881 53776983826356876570798661)
                ·
                  refine ⟨10083184467441914357024749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53776983826356876570798661 10083184467441914357024749)
                  ·
                    refine ⟨3781194175290717883884281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10083184467441914357024749 3781194175290717883884281)
                    ·
                      refine ⟨2835895631468038412913211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3781194175290717883884281 2835895631468038412913211)
                      ·
                        rfl

theorem cell23_5522887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 4, 3, 2].length) (baseStart_5522887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522887 prefixEnd_5522887 := by exact prefixLift 5522887
  have htrace : WordTrace (prefixWord ++ tailWord_5522887) baseStart_5522887 baseEnd_5522887 := by
    simpa [prefixWord, tailWord_5522887, baseEnd_5522887] using wordTrace_append hprefix tailTrace_5522887
  have hstable : (prefixWord ++ tailWord_5522887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522887).length < 2 ^ (prefixWord ++ tailWord_5522887).sum := by decide
  have hdescent : baseEnd_5522887 < baseStart_5522887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522927 : List Nat := [1, 1, 2, 1, 4, 1, 3, 4, 2, 4]
def baseStart_5522927 : Nat := 118140960795 + 5522927 * 2 ^ 59
def prefixEnd_5522927 : Nat := 4983230072969 + 3 ^ 40 * 5522927 * 2
def baseEnd_5522927 : Nat := 945305390231406085471009

theorem tailTrace_5522927 : CollatzResearch.WordTrace tailWord_5522927 prefixEnd_5522927 945305390231406085471009 := by
  unfold tailWord_5522927
  simp only [CollatzResearch.WordTrace]
  refine ⟨201437696462386194681471035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134291797641590796454314023 201437696462386194681471035)
  ·
    refine ⟨302156544693579292022206553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201437696462386194681471035 302156544693579292022206553)
    ·
      refine ⟨226617408520184469016654915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302156544693579292022206553 226617408520184469016654915)
      ·
        refine ⟨339926112780276703524982373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226617408520184469016654915 339926112780276703524982373)
        ·
          refine ⟨63736146146301881910934195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 339926112780276703524982373 63736146146301881910934195)
          ·
            refine ⟨95604219219452822866401293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63736146146301881910934195 95604219219452822866401293)
            ·
              refine ⟨35851582207294808574900485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95604219219452822866401293 35851582207294808574900485)
              ·
                refine ⟨6722171663867776607793841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35851582207294808574900485 6722171663867776607793841)
                ·
                  refine ⟨5041628747900832455845381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6722171663867776607793841 5041628747900832455845381)
                  ·
                    refine ⟨945305390231406085471009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5041628747900832455845381 945305390231406085471009)
                    ·
                      rfl

theorem cell23_5522927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 2, 4].length) (baseStart_5522927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522927 prefixEnd_5522927 := by exact prefixLift 5522927
  have htrace : WordTrace (prefixWord ++ tailWord_5522927) baseStart_5522927 baseEnd_5522927 := by
    simpa [prefixWord, tailWord_5522927, baseEnd_5522927] using wordTrace_append hprefix tailTrace_5522927
  have hstable : (prefixWord ++ tailWord_5522927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522927).length < 2 ^ (prefixWord ++ tailWord_5522927).sum := by decide
  have hdescent : baseEnd_5522927 < baseStart_5522927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522928 : List Nat := [2, 1, 1, 1, 3, 6, 2, 2, 1, 1, 3]
def baseStart_5522928 : Nat := 118140960795 + 5522928 * 2 ^ 59
def prefixEnd_5522928 : Nat := 4983230072969 + 3 ^ 40 * 5522928 * 2
def baseEnd_5522928 : Nat := 2835916684174872752500523

theorem tailTrace_5522928 : CollatzResearch.WordTrace tailWord_5522928 prefixEnd_5522928 2835916684174872752500523 := by
  unfold tailWord_5522928
  simp only [CollatzResearch.WordTrace]
  refine ⟨100718866467691285926128719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134291821956921714568171625 100718866467691285926128719)
  ·
    refine ⟨151078299701536928889193079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100718866467691285926128719 151078299701536928889193079)
    ·
      refine ⟨226617449552305393333789619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151078299701536928889193079 226617449552305393333789619)
      ·
        refine ⟨339926174328458090000684429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226617449552305393333789619 339926174328458090000684429)
        ·
          refine ⟨127472315373171783750256661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 339926174328458090000684429 127472315373171783750256661)
          ·
            refine ⟨5975264783117427363293281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 127472315373171783750256661 5975264783117427363293281)
            ·
              refine ⟨4481448587338070522469961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5975264783117427363293281 4481448587338070522469961)
              ·
                refine ⟨3361086440503552891852471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4481448587338070522469961 3361086440503552891852471)
                ·
                  refine ⟨5041629660755329337778707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3361086440503552891852471 5041629660755329337778707)
                  ·
                    refine ⟨7562444491132994006668061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5041629660755329337778707 7562444491132994006668061)
                    ·
                      refine ⟨2835916684174872752500523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7562444491132994006668061 2835916684174872752500523)
                      ·
                        rfl

theorem cell23_5522928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 2, 1, 1, 3].length) (baseStart_5522928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522928 prefixEnd_5522928 := by exact prefixLift 5522928
  have htrace : WordTrace (prefixWord ++ tailWord_5522928) baseStart_5522928 baseEnd_5522928 := by
    simpa [prefixWord, tailWord_5522928, baseEnd_5522928] using wordTrace_append hprefix tailTrace_5522928
  have hstable : (prefixWord ++ tailWord_5522928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522928).length < 2 ^ (prefixWord ++ tailWord_5522928).sum := by decide
  have hdescent : baseEnd_5522928 < baseStart_5522928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522940 : List Nat := [2, 2, 2, 1, 2, 1, 5, 8]
def baseStart_5522940 : Nat := 118140960795 + 5522940 * 2 ^ 59
def prefixEnd_5522940 : Nat := 4983230072969 + 3 ^ 40 * 5522940 * 2
def baseEnd_5522940 : Nat := 105034179479360248353721

theorem tailTrace_5522940 : CollatzResearch.WordTrace tailWord_5522940 prefixEnd_5522940 105034179479360248353721 := by
  unfold tailWord_5522940
  simp only [CollatzResearch.WordTrace]
  refine ⟨100719085305669548950847137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134292113740892731934462849 100719085305669548950847137)
  ·
    refine ⟨75539313979252161713135353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100719085305669548950847137 75539313979252161713135353)
    ·
      refine ⟨56654485484439121284851515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75539313979252161713135353 56654485484439121284851515)
      ·
        refine ⟨84981728226658681927277273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56654485484439121284851515 84981728226658681927277273)
        ·
          refine ⟨63736296169994011445457955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84981728226658681927277273 63736296169994011445457955)
          ·
            refine ⟨95604444254991017168186933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63736296169994011445457955 95604444254991017168186933)
            ·
              refine ⟨8962916648905407859517525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95604444254991017168186933 8962916648905407859517525)
              ·
                refine ⟨105034179479360248353721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8962916648905407859517525 105034179479360248353721)
                ·
                  rfl

theorem cell23_5522940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 8].length) (baseStart_5522940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522940 prefixEnd_5522940 := by exact prefixLift 5522940
  have htrace : WordTrace (prefixWord ++ tailWord_5522940) baseStart_5522940 baseEnd_5522940 := by
    simpa [prefixWord, tailWord_5522940, baseEnd_5522940] using wordTrace_append hprefix tailTrace_5522940
  have hstable : (prefixWord ++ tailWord_5522940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522940).length < 2 ^ (prefixWord ++ tailWord_5522940).sum := by decide
  have hdescent : baseEnd_5522940 < baseStart_5522940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522951 : List Nat := [1, 1, 4, 3, 2, 2, 1, 2, 3, 2, 2]
def baseStart_5522951 : Nat := 118140960795 + 5522951 * 2 ^ 59
def prefixEnd_5522951 : Nat := 4983230072969 + 3 ^ 40 * 5522951 * 2
def baseEnd_5522951 : Nat := 2835928494229926162512917

theorem tailTrace_5522951 : CollatzResearch.WordTrace tailWord_5522951 prefixEnd_5522951 2835928494229926162512917 := by
  unfold tailWord_5522951
  simp only [CollatzResearch.WordTrace]
  refine ⟨201438571814299246780344707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134292381209532831186896471 201438571814299246780344707)
  ·
    refine ⟨302157857721448870170517061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201438571814299246780344707 302157857721448870170517061)
    ·
      refine ⟨56654598322771663156971949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 302157857721448870170517061 56654598322771663156971949)
      ·
        refine ⟨21245474371039373683864481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56654598322771663156971949 21245474371039373683864481)
        ·
          refine ⟨15934105778279530262898361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21245474371039373683864481 15934105778279530262898361)
          ·
            refine ⟨11950579333709647697173771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15934105778279530262898361 11950579333709647697173771)
            ·
              refine ⟨17925869000564471545760657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11950579333709647697173771 17925869000564471545760657)
              ·
                refine ⟨13444401750423353659320493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17925869000564471545760657 13444401750423353659320493)
                ·
                  refine ⟨5041650656408757622245185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13444401750423353659320493 5041650656408757622245185)
                  ·
                    refine ⟨3781237992306568216683889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5041650656408757622245185 3781237992306568216683889)
                    ·
                      refine ⟨2835928494229926162512917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3781237992306568216683889 2835928494229926162512917)
                      ·
                        rfl

theorem cell23_5522951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_5522951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522951 prefixEnd_5522951 := by exact prefixLift 5522951
  have htrace : WordTrace (prefixWord ++ tailWord_5522951) baseStart_5522951 baseEnd_5522951 := by
    simpa [prefixWord, tailWord_5522951, baseEnd_5522951] using wordTrace_append hprefix tailTrace_5522951
  have hstable : (prefixWord ++ tailWord_5522951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522951).length < 2 ^ (prefixWord ++ tailWord_5522951).sum := by decide
  have hdescent : baseEnd_5522951 < baseStart_5522951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522968 : List Nat := [2, 1, 2, 3, 5, 1, 2, 1, 1, 1, 4]
def baseStart_5522968 : Nat := 118140960795 + 5522968 * 2 ^ 59
def prefixEnd_5522968 : Nat := 4983230072969 + 3 ^ 40 * 5522968 * 2
def baseEnd_5522968 : Nat := 2835937223401052596000339

theorem tailTrace_5522968 : CollatzResearch.WordTrace tailWord_5522968 prefixEnd_5522968 2835937223401052596000339 := by
  unfold tailWord_5522968
  simp only [CollatzResearch.WordTrace]
  refine ⟨100719595927618829341856779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134292794570158439122475705 100719595927618829341856779)
  ·
    refine ⟨151079393891428244012785169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100719595927618829341856779 151079393891428244012785169)
    ·
      refine ⟨113309545418571183009588877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151079393891428244012785169 113309545418571183009588877)
      ·
        refine ⟨42491079531964193628595829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113309545418571183009588877 42491079531964193628595829)
        ·
          refine ⟨3983538706121643152680859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42491079531964193628595829 3983538706121643152680859)
          ·
            refine ⟨5975308059182464729021289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3983538706121643152680859 5975308059182464729021289)
            ·
              refine ⟨4481481044386848546765967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5975308059182464729021289 4481481044386848546765967)
              ·
                refine ⟨6722221566580272820148951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4481481044386848546765967 6722221566580272820148951)
                ·
                  refine ⟨10083332349870409230223427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6722221566580272820148951 10083332349870409230223427)
                  ·
                    refine ⟨15124998524805613845335141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10083332349870409230223427 15124998524805613845335141)
                    ·
                      refine ⟨2835937223401052596000339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15124998524805613845335141 2835937223401052596000339)
                      ·
                        rfl

theorem cell23_5522968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_5522968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522968 prefixEnd_5522968 := by exact prefixLift 5522968
  have htrace : WordTrace (prefixWord ++ tailWord_5522968) baseStart_5522968 baseEnd_5522968 := by
    simpa [prefixWord, tailWord_5522968, baseEnd_5522968] using wordTrace_append hprefix tailTrace_5522968
  have hstable : (prefixWord ++ tailWord_5522968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522968).length < 2 ^ (prefixWord ++ tailWord_5522968).sum := by decide
  have hdescent : baseEnd_5522968 < baseStart_5522968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5522998 : List Nat := [5, 1, 2, 1, 4, 1, 1, 1, 1, 2, 4]
def baseStart_5522998 : Nat := 118140960795 + 5522998 * 2 ^ 59
def prefixEnd_5522998 : Nat := 4983230072969 + 3 ^ 40 * 5522998 * 2
def baseEnd_5522998 : Nat := 2835952627820687478625201

theorem tailTrace_5522998 : CollatzResearch.WordTrace tailWord_5522998 prefixEnd_5522998 2835952627820687478625201 := by
  unfold tailWord_5522998
  simp only [CollatzResearch.WordTrace]
  refine ⟨12590017877820560862956603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134293524030085982538203765 12590017877820560862956603)
  ·
    refine ⟨18885026816730841294434905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12590017877820560862956603 18885026816730841294434905)
    ·
      refine ⟨14163770112548130970826179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18885026816730841294434905 14163770112548130970826179)
      ·
        refine ⟨21245655168822196456239269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14163770112548130970826179 21245655168822196456239269)
        ·
          refine ⟨3983560344154161835544863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21245655168822196456239269 3983560344154161835544863)
          ·
            refine ⟨5975340516231242753317295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3983560344154161835544863 5975340516231242753317295)
            ·
              refine ⟨8963010774346864129975943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5975340516231242753317295 8963010774346864129975943)
              ·
                refine ⟨13444516161520296194963915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8963010774346864129975943 13444516161520296194963915)
                ·
                  refine ⟨20166774242280444292445873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13444516161520296194963915 20166774242280444292445873)
                  ·
                    refine ⟨15125080681710333219334405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20166774242280444292445873 15125080681710333219334405)
                    ·
                      refine ⟨2835952627820687478625201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15125080681710333219334405 2835952627820687478625201)
                      ·
                        rfl

theorem cell23_5522998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_5522998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5522998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5522998 prefixEnd_5522998 := by exact prefixLift 5522998
  have htrace : WordTrace (prefixWord ++ tailWord_5522998) baseStart_5522998 baseEnd_5522998 := by
    simpa [prefixWord, tailWord_5522998, baseEnd_5522998] using wordTrace_append hprefix tailTrace_5522998
  have hstable : (prefixWord ++ tailWord_5522998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5522998).length < 2 ^ (prefixWord ++ tailWord_5522998).sum := by decide
  have hdescent : baseEnd_5522998 < baseStart_5522998 := by decide
  rcases family_descends (prefixWord ++ tailWord_5522998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523024 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 6, 2, 2]
def baseStart_5523024 : Nat := 118140960795 + 5523024 * 2 ^ 59
def prefixEnd_5523024 : Nat := 4983230072969 + 3 ^ 40 * 5523024 * 2
def baseEnd_5523024 : Nat := 2835965978317704376900081

theorem tailTrace_5523024 : CollatzResearch.WordTrace tailWord_5523024 prefixEnd_5523024 2835965978317704376900081 := by
  unfold tailWord_5523024
  simp only [CollatzResearch.WordTrace]
  refine ⟨100720617171517390123876063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134294156228689853498501417 100720617171517390123876063)
  ·
    refine ⟨151080925757276085185814095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100720617171517390123876063 151080925757276085185814095)
    ·
      refine ⟨226621388635914127778721143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151080925757276085185814095 226621388635914127778721143)
      ·
        refine ⟨339932082953871191668081715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226621388635914127778721143 339932082953871191668081715)
        ·
          refine ⟨509898124430806787502122573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339932082953871191668081715 509898124430806787502122573)
          ·
            refine ⟨191211796661552545313295965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 509898124430806787502122573 191211796661552545313295965)
            ·
              refine ⟨71704423748082204492485987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191211796661552545313295965 71704423748082204492485987)
              ·
                refine ⟨107556635622123306738728981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71704423748082204492485987 107556635622123306738728981)
                ·
                  refine ⟨5041717294787030003377921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 107556635622123306738728981 5041717294787030003377921)
                  ·
                    refine ⟨3781287971090272502533441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5041717294787030003377921 3781287971090272502533441)
                    ·
                      refine ⟨2835965978317704376900081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3781287971090272502533441 2835965978317704376900081)
                      ·
                        rfl

theorem cell23_5523024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 6, 2, 2].length) (baseStart_5523024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523024 prefixEnd_5523024 := by exact prefixLift 5523024
  have htrace : WordTrace (prefixWord ++ tailWord_5523024) baseStart_5523024 baseEnd_5523024 := by
    simpa [prefixWord, tailWord_5523024, baseEnd_5523024] using wordTrace_append hprefix tailTrace_5523024
  have hstable : (prefixWord ++ tailWord_5523024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523024).length < 2 ^ (prefixWord ++ tailWord_5523024).sum := by decide
  have hdescent : baseEnd_5523024 < baseStart_5523024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523040 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 9]
def baseStart_5523040 : Nat := 118140960795 + 5523040 * 2 ^ 59
def prefixEnd_5523040 : Nat := 4983230072969 + 3 ^ 40 * 5523040 * 2
def baseEnd_5523040 : Nat := 2835974194008176314300007

theorem tailTrace_5523040 : CollatzResearch.WordTrace tailWord_5523040 prefixEnd_5523040 2835974194008176314300007 := by
  unfold tailWord_5523040
  simp only [CollatzResearch.WordTrace]
  refine ⟨100720908955488407490167287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134294545273984543320223049 100720908955488407490167287)
  ·
    refine ⟨151081363433232611235250931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100720908955488407490167287 151081363433232611235250931)
    ·
      refine ⟨226622045149848916852876397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151081363433232611235250931 226622045149848916852876397)
      ·
        refine ⟨84983266931193343819828649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226622045149848916852876397 84983266931193343819828649)
        ·
          refine ⟨63737450198395007864871487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84983266931193343819828649 63737450198395007864871487)
          ·
            refine ⟨95606175297592511797307231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63737450198395007864871487 95606175297592511797307231)
            ·
              refine ⟨143409262946388767695960847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95606175297592511797307231 143409262946388767695960847)
              ·
                refine ⟨215113894419583151543941271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143409262946388767695960847 215113894419583151543941271)
                ·
                  refine ⟨322670841629374727315911907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215113894419583151543941271 322670841629374727315911907)
                  ·
                    refine ⟨484006262444062090973867861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 322670841629374727315911907 484006262444062090973867861)
                    ·
                      refine ⟨2835974194008176314300007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 484006262444062090973867861 2835974194008176314300007)
                      ·
                        rfl

theorem cell23_5523040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_5523040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523040 prefixEnd_5523040 := by exact prefixLift 5523040
  have htrace : WordTrace (prefixWord ++ tailWord_5523040) baseStart_5523040 baseEnd_5523040 := by
    simpa [prefixWord, tailWord_5523040, baseEnd_5523040] using wordTrace_append hprefix tailTrace_5523040
  have hstable : (prefixWord ++ tailWord_5523040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523040).length < 2 ^ (prefixWord ++ tailWord_5523040).sum := by decide
  have hdescent : baseEnd_5523040 < baseStart_5523040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523041 : List Nat := [1, 2, 3, 1, 1, 3, 2, 4, 2, 2, 2]
def baseStart_5523041 : Nat := 118140960795 + 5523041 * 2 ^ 59
def prefixEnd_5523041 : Nat := 4983230072969 + 3 ^ 40 * 5523041 * 2
def baseEnd_5523041 : Nat := 2835974707488830810387503

theorem tailTrace_5523041 : CollatzResearch.WordTrace tailWord_5523041 prefixEnd_5523041 2835974707488830810387503 := by
  unfold tailWord_5523041
  simp only [CollatzResearch.WordTrace]
  refine ⟨201441854383973192151120977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134294569589315461434080651 201441854383973192151120977)
  ·
    refine ⟨151081390787979894113340733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201441854383973192151120977 151081390787979894113340733)
    ·
      refine ⟨56655521545492460292502775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151081390787979894113340733 56655521545492460292502775)
      ·
        refine ⟨84983282318238690438754163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56655521545492460292502775 84983282318238690438754163)
        ·
          refine ⟨127474923477358035658131245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84983282318238690438754163 127474923477358035658131245)
          ·
            refine ⟨47803096304009263371799217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127474923477358035658131245 47803096304009263371799217)
            ·
              refine ⟨35852322228006947528849413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47803096304009263371799217 35852322228006947528849413)
              ·
                refine ⟨6722310417751302661659265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35852322228006947528849413 6722310417751302661659265)
                ·
                  refine ⟨5041732813313476996244449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6722310417751302661659265 5041732813313476996244449)
                  ·
                    refine ⟨3781299609985107747183337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5041732813313476996244449 3781299609985107747183337)
                    ·
                      refine ⟨2835974707488830810387503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3781299609985107747183337 2835974707488830810387503)
                      ·
                        rfl

theorem cell23_5523041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 2, 2, 2].length) (baseStart_5523041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523041 prefixEnd_5523041 := by exact prefixLift 5523041
  have htrace : WordTrace (prefixWord ++ tailWord_5523041) baseStart_5523041 baseEnd_5523041 := by
    simpa [prefixWord, tailWord_5523041, baseEnd_5523041] using wordTrace_append hprefix tailTrace_5523041
  have hstable : (prefixWord ++ tailWord_5523041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523041).length < 2 ^ (prefixWord ++ tailWord_5523041).sum := by decide
  have hdescent : baseEnd_5523041 < baseStart_5523041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523047 : List Nat := [1, 1, 5, 1, 1, 1, 5, 1, 7]
def baseStart_5523047 : Nat := 118140960795 + 5523047 * 2 ^ 59
def prefixEnd_5523047 : Nat := 4983230072969 + 3 ^ 40 * 5523047 * 2
def baseEnd_5523047 : Nat := 315108643152528642990275

theorem tailTrace_5523047 : CollatzResearch.WordTrace tailWord_5523047 prefixEnd_5523047 315108643152528642990275 := by
  unfold tailWord_5523047
  simp only [CollatzResearch.WordTrace]
  refine ⟨201442073221951455175839395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134294715481300970117226263 201442073221951455175839395)
  ·
    refine ⟨302163109832927182763759093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201442073221951455175839395 302163109832927182763759093)
    ·
      refine ⟨28327791546836923384102415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 302163109832927182763759093 28327791546836923384102415)
      ·
        refine ⟨42491687320255385076153623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28327791546836923384102415 42491687320255385076153623)
        ·
          refine ⟨63737530980383077614230435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42491687320255385076153623 63737530980383077614230435)
          ·
            refine ⟨95606296470574616421345653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63737530980383077614230435 95606296470574616421345653)
            ·
              refine ⟨8963090294116370289501155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95606296470574616421345653 8963090294116370289501155)
              ·
                refine ⟨13444635441174555434251733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8963090294116370289501155 13444635441174555434251733)
                ·
                  refine ⟨315108643152528642990275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13444635441174555434251733 315108643152528642990275)
                  ·
                    rfl

theorem cell23_5523047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 7].length) (baseStart_5523047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523047 prefixEnd_5523047 := by exact prefixLift 5523047
  have htrace : WordTrace (prefixWord ++ tailWord_5523047) baseStart_5523047 baseEnd_5523047 := by
    simpa [prefixWord, tailWord_5523047, baseEnd_5523047] using wordTrace_append hprefix tailTrace_5523047
  have hstable : (prefixWord ++ tailWord_5523047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523047).length < 2 ^ (prefixWord ++ tailWord_5523047).sum := by decide
  have hdescent : baseEnd_5523047 < baseStart_5523047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523057 : List Nat := [1, 2, 2, 2, 1, 1, 1, 5, 2, 3, 3]
def baseStart_5523057 : Nat := 118140960795 + 5523057 * 2 ^ 59
def prefixEnd_5523057 : Nat := 4983230072969 + 3 ^ 40 * 5523057 * 2
def baseEnd_5523057 : Nat := 2835982923179302747787429

theorem tailTrace_5523057 : CollatzResearch.WordTrace tailWord_5523057 prefixEnd_5523057 2835982923179302747787429 := by
  unfold tailWord_5523057
  simp only [CollatzResearch.WordTrace]
  refine ⟨201442437951915226883703425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134294958634610151255802283 201442437951915226883703425)
  ·
    refine ⟨151081828463936420162777569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201442437951915226883703425 151081828463936420162777569)
    ·
      refine ⟨113311371347952315122083177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151081828463936420162777569 113311371347952315122083177)
      ·
        refine ⟨84983528510964236341562383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113311371347952315122083177 84983528510964236341562383)
        ·
          refine ⟨127475292766446354512343575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84983528510964236341562383 127475292766446354512343575)
          ·
            refine ⟨191212939149669531768515363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127475292766446354512343575 191212939149669531768515363)
            ·
              refine ⟨286819408724504297652773045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191212939149669531768515363 286819408724504297652773045)
              ·
                refine ⟨26889319567922277904947473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 286819408724504297652773045 26889319567922277904947473)
                ·
                  refine ⟨20166989675941708428710605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26889319567922277904947473 20166989675941708428710605)
                  ·
                    refine ⟨7562621128478140660766477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20166989675941708428710605 7562621128478140660766477)
                    ·
                      refine ⟨2835982923179302747787429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7562621128478140660766477 2835982923179302747787429)
                      ·
                        rfl

theorem cell23_5523057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_5523057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523057 prefixEnd_5523057 := by exact prefixLift 5523057
  have htrace : WordTrace (prefixWord ++ tailWord_5523057) baseStart_5523057 baseEnd_5523057 := by
    simpa [prefixWord, tailWord_5523057, baseEnd_5523057] using wordTrace_append hprefix tailTrace_5523057
  have hstable : (prefixWord ++ tailWord_5523057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523057).length < 2 ^ (prefixWord ++ tailWord_5523057).sum := by decide
  have hdescent : baseEnd_5523057 < baseStart_5523057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523058 : List Nat := [3, 2, 1, 2, 3, 2, 1, 3, 2, 2, 2]
def baseStart_5523058 : Nat := 118140960795 + 5523058 * 2 ^ 59
def prefixEnd_5523058 : Nat := 4983230072969 + 3 ^ 40 * 5523058 * 2
def baseEnd_5523058 : Nat := 2835983436659957243874925

theorem tailTrace_5523058 : CollatzResearch.WordTrace tailWord_5523058 prefixEnd_5523058 2835983436659957243874925 := by
  unfold tailWord_5523058
  simp only [CollatzResearch.WordTrace]
  refine ⟨50360618606227901013622457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134294982949941069369659885 50360618606227901013622457)
  ·
    refine ⟨37770463954670925760216843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50360618606227901013622457 37770463954670925760216843)
    ·
      refine ⟨56655695932006388640325265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37770463954670925760216843 56655695932006388640325265)
      ·
        refine ⟨42491771949004791480243949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56655695932006388640325265 42491771949004791480243949)
        ·
          refine ⟨15934414480876796805091481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42491771949004791480243949 15934414480876796805091481)
          ·
            refine ⟨11950810860657597603818611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15934414480876796805091481 11950810860657597603818611)
            ·
              refine ⟨17926216290986396405727917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11950810860657597603818611 17926216290986396405727917)
              ·
                refine ⟨6722331109119898652147969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17926216290986396405727917 6722331109119898652147969)
                ·
                  refine ⟨5041748331839923989110977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6722331109119898652147969 5041748331839923989110977)
                  ·
                    refine ⟨3781311248879942991833233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5041748331839923989110977 3781311248879942991833233)
                    ·
                      refine ⟨2835983436659957243874925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3781311248879942991833233 2835983436659957243874925)
                      ·
                        rfl

theorem cell23_5523058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_5523058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523058 prefixEnd_5523058 := by exact prefixLift 5523058
  have htrace : WordTrace (prefixWord ++ tailWord_5523058) baseStart_5523058 baseEnd_5523058 := by
    simpa [prefixWord, tailWord_5523058, baseEnd_5523058] using wordTrace_append hprefix tailTrace_5523058
  have hstable : (prefixWord ++ tailWord_5523058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523058).length < 2 ^ (prefixWord ++ tailWord_5523058).sum := by decide
  have hdescent : baseEnd_5523058 < baseStart_5523058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523097 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 4, 1, 4]
def baseStart_5523097 : Nat := 118140960795 + 5523097 * 2 ^ 59
def prefixEnd_5523097 : Nat := 4983230072969 + 3 ^ 40 * 5523097 * 2
def baseEnd_5523097 : Nat := 2836003462405482591287245

theorem tailTrace_5523097 : CollatzResearch.WordTrace tailWord_5523097 prefixEnd_5523097 2836003462405482591287245 := by
  unfold tailWord_5523097
  simp only [CollatzResearch.WordTrace]
  refine ⟨201443896871770313715159545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134295931247846875810106363 201443896871770313715159545)
  ·
    refine ⟨151082922653827735286369659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201443896871770313715159545 151082922653827735286369659)
    ·
      refine ⟨226624383980741602929554489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151082922653827735286369659 226624383980741602929554489)
      ·
        refine ⟨169968287985556202197165867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226624383980741602929554489 169968287985556202197165867)
        ·
          refine ⟨254952431978334303295748801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169968287985556202197165867 254952431978334303295748801)
          ·
            refine ⟨191214323983750727471811601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254952431978334303295748801 191214323983750727471811601)
            ·
              refine ⟨143410742987813045603858701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191214323983750727471811601 143410742987813045603858701)
              ·
                refine ⟨53779028620429892101447013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143410742987813045603858701 53779028620429892101447013)
                ·
                  refine ⟨10083567866330604769021315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53779028620429892101447013 10083567866330604769021315)
                  ·
                    refine ⟨15125351799495907153531973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10083567866330604769021315 15125351799495907153531973)
                    ·
                      refine ⟨2836003462405482591287245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15125351799495907153531973 2836003462405482591287245)
                      ·
                        rfl

theorem cell23_5523097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 1, 4].length) (baseStart_5523097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523097 prefixEnd_5523097 := by exact prefixLift 5523097
  have htrace : WordTrace (prefixWord ++ tailWord_5523097) baseStart_5523097 baseEnd_5523097 := by
    simpa [prefixWord, tailWord_5523097, baseEnd_5523097] using wordTrace_append hprefix tailTrace_5523097
  have hstable : (prefixWord ++ tailWord_5523097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523097).length < 2 ^ (prefixWord ++ tailWord_5523097).sum := by decide
  have hdescent : baseEnd_5523097 < baseStart_5523097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523147 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 1, 7, 3]
def baseStart_5523147 : Nat := 118140960795 + 5523147 * 2 ^ 59
def prefixEnd_5523147 : Nat := 4983230072969 + 3 ^ 40 * 5523147 * 2
def baseEnd_5523147 : Nat := 2836029136438207395662015

theorem tailTrace_5523147 : CollatzResearch.WordTrace tailWord_5523147 prefixEnd_5523147 2836029136438207395662015 := by
  unfold tailWord_5523147
  simp only [CollatzResearch.WordTrace]
  refine ⟨201445720521589172254479695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134297147014392781502986463 201445720521589172254479695)
  ·
    refine ⟨302168580782383758381719543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201445720521589172254479695 302168580782383758381719543)
    ·
      refine ⟨453252871173575637572579315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302168580782383758381719543 453252871173575637572579315)
      ·
        refine ⟨679879306760363456358868973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 453252871173575637572579315 679879306760363456358868973)
        ·
          refine ⟨254954740035136296134575865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 679879306760363456358868973 254954740035136296134575865)
          ·
            refine ⟨191216055026352222100931899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254954740035136296134575865 191216055026352222100931899)
            ·
              refine ⟨286824082539528333151397849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191216055026352222100931899 286824082539528333151397849)
              ·
                refine ⟨215118061904646249863548387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 286824082539528333151397849 215118061904646249863548387)
                ·
                  refine ⟨322677092856969374795322581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215118061904646249863548387 322677092856969374795322581)
                  ·
                    refine ⟨7562744363835219721765373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 322677092856969374795322581 7562744363835219721765373)
                    ·
                      refine ⟨2836029136438207395662015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7562744363835219721765373 2836029136438207395662015)
                      ·
                        rfl

theorem cell23_5523147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 7, 3].length) (baseStart_5523147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523147 prefixEnd_5523147 := by exact prefixLift 5523147
  have htrace : WordTrace (prefixWord ++ tailWord_5523147) baseStart_5523147 baseEnd_5523147 := by
    simpa [prefixWord, tailWord_5523147, baseEnd_5523147] using wordTrace_append hprefix tailTrace_5523147
  have hstable : (prefixWord ++ tailWord_5523147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523147).length < 2 ^ (prefixWord ++ tailWord_5523147).sum := by decide
  have hdescent : baseEnd_5523147 < baseStart_5523147 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523154 : List Nat := [3, 2, 2, 2, 2, 2, 1, 1, 8]
def baseStart_5523154 : Nat := 118140960795 + 5523154 * 2 ^ 59
def prefixEnd_5523154 : Nat := 4983230072969 + 3 ^ 40 * 5523154 * 2
def baseEnd_5523154 : Nat := 315114747866976540919387

theorem tailTrace_5523154 : CollatzResearch.WordTrace tailWord_5523154 prefixEnd_5523154 315114747866976540919387 := by
  unfold tailWord_5523154
  simp only [CollatzResearch.WordTrace]
  refine ⟨50361493958140953112496129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134297317221709208299989677 50361493958140953112496129)
  ·
    refine ⟨37771120468605714834372097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50361493958140953112496129 37771120468605714834372097)
    ·
      refine ⟨28328340351454286125779073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37771120468605714834372097 28328340351454286125779073)
      ·
        refine ⟨21246255263590714594334305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28328340351454286125779073 21246255263590714594334305)
        ·
          refine ⟨15934691447693035945750729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21246255263590714594334305 15934691447693035945750729)
          ·
            refine ⟨11951018585769776959313047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15934691447693035945750729 11951018585769776959313047)
            ·
              refine ⟨17926527878654665438969571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11951018585769776959313047 17926527878654665438969571)
              ·
                refine ⟨26889791817981998158454357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17926527878654665438969571 26889791817981998158454357)
                ·
                  refine ⟨315114747866976540919387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26889791817981998158454357 315114747866976540919387)
                  ·
                    rfl

theorem cell23_5523154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 8].length) (baseStart_5523154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523154 prefixEnd_5523154 := by exact prefixLift 5523154
  have htrace : WordTrace (prefixWord ++ tailWord_5523154) baseStart_5523154 baseEnd_5523154 := by
    simpa [prefixWord, tailWord_5523154, baseEnd_5523154] using wordTrace_append hprefix tailTrace_5523154
  have hstable : (prefixWord ++ tailWord_5523154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523154).length < 2 ^ (prefixWord ++ tailWord_5523154).sum := by decide
  have hdescent : baseEnd_5523154 < baseStart_5523154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523224 : List Nat := [2, 1, 2, 3, 1, 1, 4, 2, 1, 1, 5]
def baseStart_5523224 : Nat := 118140960795 + 5523224 * 2 ^ 59
def prefixEnd_5523224 : Nat := 4983230072969 + 3 ^ 40 * 5523224 * 2
def baseEnd_5523224 : Nat := 2836068674448603594399161

theorem tailTrace_5523224 : CollatzResearch.WordTrace tailWord_5523224 prefixEnd_5523224 2836068674448603594399161 := by
  unfold tailWord_5523224
  simp only [CollatzResearch.WordTrace]
  refine ⟨100724264471155107202516363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134299019294873476270021817 100724264471155107202516363)
  ·
    refine ⟨151086396706732660803774545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100724264471155107202516363 151086396706732660803774545)
    ·
      refine ⟨113314797530049495602830909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151086396706732660803774545 113314797530049495602830909)
      ·
        refine ⟨42493049073768560851061591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113314797530049495602830909 42493049073768560851061591)
        ·
          refine ⟨63739573610652841276592387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42493049073768560851061591 63739573610652841276592387)
          ·
            refine ⟨95609360415979261914888581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63739573610652841276592387 95609360415979261914888581)
            ·
              refine ⟨17926755077996111609041609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95609360415979261914888581 17926755077996111609041609)
              ·
                refine ⟨13445066308497083706781207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17926755077996111609041609 13445066308497083706781207)
                ·
                  refine ⟨20167599462745625560171811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13445066308497083706781207 20167599462745625560171811)
                  ·
                    refine ⟨30251399194118438340257717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20167599462745625560171811 30251399194118438340257717)
                    ·
                      refine ⟨2836068674448603594399161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30251399194118438340257717 2836068674448603594399161)
                      ·
                        rfl

theorem cell23_5523224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_5523224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523224 prefixEnd_5523224 := by exact prefixLift 5523224
  have htrace : WordTrace (prefixWord ++ tailWord_5523224) baseStart_5523224 baseEnd_5523224 := by
    simpa [prefixWord, tailWord_5523224, baseEnd_5523224] using wordTrace_append hprefix tailTrace_5523224
  have hstable : (prefixWord ++ tailWord_5523224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523224).length < 2 ^ (prefixWord ++ tailWord_5523224).sum := by decide
  have hdescent : baseEnd_5523224 < baseStart_5523224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523231 : List Nat := [1, 1, 2, 4, 2, 1, 3, 3, 2, 4]
def baseStart_5523231 : Nat := 118140960795 + 5523231 * 2 ^ 59
def prefixEnd_5523231 : Nat := 4983230072969 + 3 ^ 40 * 5523231 * 2
def baseEnd_5523231 : Nat := 945357422937728355670543

theorem tailTrace_5523231 : CollatzResearch.WordTrace tailWord_5523231 prefixEnd_5523231 945357422937728355670543 := by
  unfold tailWord_5523231
  simp only [CollatzResearch.WordTrace]
  refine ⟨201448784253284854600537547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134299189502189903067025031 201448784253284854600537547)
  ·
    refine ⟨302173176379927281900806321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201448784253284854600537547 302173176379927281900806321)
    ·
      refine ⟨226629882284945461425604741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302173176379927281900806321 226629882284945461425604741)
      ·
        refine ⟨42493102928427274017300889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 226629882284945461425604741 42493102928427274017300889)
        ·
          refine ⟨31869827196320455512975667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42493102928427274017300889 31869827196320455512975667)
          ·
            refine ⟨47804740794480683269463501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31869827196320455512975667 47804740794480683269463501)
            ·
              refine ⟨17926777797930256226048813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47804740794480683269463501 17926777797930256226048813)
              ·
                refine ⟨6722541674223846084768305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17926777797930256226048813 6722541674223846084768305)
                ·
                  refine ⟨5041906255667884563576229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6722541674223846084768305 5041906255667884563576229)
                  ·
                    refine ⟨945357422937728355670543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5041906255667884563576229 945357422937728355670543)
                    ·
                      rfl

theorem cell23_5523231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 2, 4].length) (baseStart_5523231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523231 prefixEnd_5523231 := by exact prefixLift 5523231
  have htrace : WordTrace (prefixWord ++ tailWord_5523231) baseStart_5523231 baseEnd_5523231 := by
    simpa [prefixWord, tailWord_5523231, baseEnd_5523231] using wordTrace_append hprefix tailTrace_5523231
  have hstable : (prefixWord ++ tailWord_5523231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523231).length < 2 ^ (prefixWord ++ tailWord_5523231).sum := by decide
  have hdescent : baseEnd_5523231 < baseStart_5523231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523234 : List Nat := [3, 3, 1, 1, 2, 1, 1, 3, 1, 1, 6]
def baseStart_5523234 : Nat := 118140960795 + 5523234 * 2 ^ 59
def prefixEnd_5523234 : Nat := 4983230072969 + 3 ^ 40 * 5523234 * 2
def baseEnd_5523234 : Nat := 2836073809255148555274115

theorem tailTrace_5523234 : CollatzResearch.WordTrace tailWord_5523234 prefixEnd_5523234 2836073809255148555274115 := by
  unfold tailWord_5523234
  simp only [CollatzResearch.WordTrace]
  refine ⟨50362223418068496528224189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134299262448182657408597837 50362223418068496528224189)
  ·
    refine ⟨18885833781775686198084071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50362223418068496528224189 18885833781775686198084071)
    ·
      refine ⟨28328750672663529297126107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18885833781775686198084071 28328750672663529297126107)
      ·
        refine ⟨42493126008995293945689161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28328750672663529297126107 42493126008995293945689161)
        ·
          refine ⟨31869844506746470459266871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42493126008995293945689161 31869844506746470459266871)
          ·
            refine ⟨47804766760119705688900307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31869844506746470459266871 47804766760119705688900307)
            ·
              refine ⟨71707150140179558533350461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47804766760119705688900307 71707150140179558533350461)
              ·
                refine ⟨26890181302567334450006423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71707150140179558533350461 26890181302567334450006423)
                ·
                  refine ⟨40335271953851001675009635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26890181302567334450006423 40335271953851001675009635)
                  ·
                    refine ⟨60502907930776502512514453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40335271953851001675009635 60502907930776502512514453)
                    ·
                      refine ⟨2836073809255148555274115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60502907930776502512514453 2836073809255148555274115)
                      ·
                        rfl

theorem cell23_5523234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_5523234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523234 prefixEnd_5523234 := by exact prefixLift 5523234
  have htrace : WordTrace (prefixWord ++ tailWord_5523234) baseStart_5523234 baseEnd_5523234 := by
    simpa [prefixWord, tailWord_5523234, baseEnd_5523234] using wordTrace_append hprefix tailTrace_5523234
  have hstable : (prefixWord ++ tailWord_5523234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523234).length < 2 ^ (prefixWord ++ tailWord_5523234).sum := by decide
  have hdescent : baseEnd_5523234 < baseStart_5523234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523247 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 6]
def baseStart_5523247 : Nat := 118140960795 + 5523247 * 2 ^ 59
def prefixEnd_5523247 : Nat := 4983230072969 + 3 ^ 40 * 5523247 * 2
def baseEnd_5523247 : Nat := 2836080484503657004411555

theorem tailTrace_5523247 : CollatzResearch.WordTrace tailWord_5523247 prefixEnd_5523247 2836080484503657004411555 := by
  unfold tailWord_5523247
  simp only [CollatzResearch.WordTrace]
  refine ⟨201449367821226889333119995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134299578547484592888746663 201449367821226889333119995)
  ·
    refine ⟨302174051731840333999679993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201449367821226889333119995 302174051731840333999679993)
    ·
      refine ⟨226630538798880250499759995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302174051731840333999679993 226630538798880250499759995)
      ·
        refine ⟨339945808198320375749639993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226630538798880250499759995 339945808198320375749639993)
        ·
          refine ⟨254959356148740281812229995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 339945808198320375749639993 254959356148740281812229995)
          ·
            refine ⟨382439034223110422718344993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254959356148740281812229995 382439034223110422718344993)
            ·
              refine ⟨286829275667332817038758745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 382439034223110422718344993 286829275667332817038758745)
              ·
                refine ⟨215121956750499612779069059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 286829275667332817038758745 215121956750499612779069059)
                ·
                  refine ⟨322682935125749419168603589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215121956750499612779069059 322682935125749419168603589)
                  ·
                    refine ⟨60503050336078016094113173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 322682935125749419168603589 60503050336078016094113173)
                    ·
                      refine ⟨2836080484503657004411555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60503050336078016094113173 2836080484503657004411555)
                      ·
                        rfl

theorem cell23_5523247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 6].length) (baseStart_5523247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523247 prefixEnd_5523247 := by exact prefixLift 5523247
  have htrace : WordTrace (prefixWord ++ tailWord_5523247) baseStart_5523247 baseEnd_5523247 := by
    simpa [prefixWord, tailWord_5523247, baseEnd_5523247] using wordTrace_append hprefix tailTrace_5523247
  have hstable : (prefixWord ++ tailWord_5523247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523247).length < 2 ^ (prefixWord ++ tailWord_5523247).sum := by decide
  have hdescent : baseEnd_5523247 < baseStart_5523247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523251 : List Nat := [1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 4]
def baseStart_5523251 : Nat := 118140960795 + 5523251 * 2 ^ 59
def prefixEnd_5523251 : Nat := 4983230072969 + 3 ^ 40 * 5523251 * 2
def baseEnd_5523251 : Nat := 2836082538426274988761537

theorem tailTrace_5523251 : CollatzResearch.WordTrace tailWord_5523251 prefixEnd_5523251 2836082538426274988761537 := by
  unfold tailWord_5523251
  simp only [CollatzResearch.WordTrace]
  refine ⟨201449513713212398016265607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134299675808808265344177071 201449513713212398016265607)
  ·
    refine ⟨302174270569818597024398411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201449513713212398016265607 302174270569818597024398411)
    ·
      refine ⟨453261405854727895536597617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302174270569818597024398411 453261405854727895536597617)
      ·
        refine ⟨339946054391045921652448213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 453261405854727895536597617 339946054391045921652448213)
        ·
          refine ⟨7967485649790138788729255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 339946054391045921652448213 7967485649790138788729255)
          ·
            refine ⟨11951228474685208183093883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7967485649790138788729255 11951228474685208183093883)
            ·
              refine ⟨17926842712027812274640825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11951228474685208183093883 17926842712027812274640825)
              ·
                refine ⟨13445132034020859205980619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17926842712027812274640825 13445132034020859205980619)
                ·
                  refine ⟨20167698051031288808970929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13445132034020859205980619 20167698051031288808970929)
                  ·
                    refine ⟨15125773538273466606728197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20167698051031288808970929 15125773538273466606728197)
                    ·
                      refine ⟨2836082538426274988761537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15125773538273466606728197 2836082538426274988761537)
                      ·
                        rfl

theorem cell23_5523251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 4].length) (baseStart_5523251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523251 prefixEnd_5523251 := by exact prefixLift 5523251
  have htrace : WordTrace (prefixWord ++ tailWord_5523251) baseStart_5523251 baseEnd_5523251 := by
    simpa [prefixWord, tailWord_5523251, baseEnd_5523251] using wordTrace_append hprefix tailTrace_5523251
  have hstable : (prefixWord ++ tailWord_5523251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523251).length < 2 ^ (prefixWord ++ tailWord_5523251).sum := by decide
  have hdescent : baseEnd_5523251 < baseStart_5523251 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523271 : List Nat := [1, 1, 4, 1, 2, 1, 2, 3, 4, 1, 3]
def baseStart_5523271 : Nat := 118140960795 + 5523271 * 2 ^ 59
def prefixEnd_5523271 : Nat := 4983230072969 + 3 ^ 40 * 5523271 * 2
def baseEnd_5523271 : Nat := 2836092808039364910511445

theorem tailTrace_5523271 : CollatzResearch.WordTrace tailWord_5523271 prefixEnd_5523271 2836092808039364910511445 := by
  unfold tailWord_5523271
  simp only [CollatzResearch.WordTrace]
  refine ⟨201450243173139941431993667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134300162115426627621329111 201450243173139941431993667)
  ·
    refine ⟨302175364759709912147990501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201450243173139941431993667 302175364759709912147990501)
    ·
      refine ⟨56657880892445608527748219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 302175364759709912147990501 56657880892445608527748219)
      ·
        refine ⟨84986821338668412791622329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56657880892445608527748219 84986821338668412791622329)
        ·
          refine ⟨63740116004001309593716747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84986821338668412791622329 63740116004001309593716747)
          ·
            refine ⟨95610174006001964390575121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63740116004001309593716747 95610174006001964390575121)
            ·
              refine ⟨71707630504501473292931341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95610174006001964390575121 71707630504501473292931341)
              ·
                refine ⟨26890361439188052484849253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71707630504501473292931341 26890361439188052484849253)
                ·
                  refine ⟨5041942769847759840909235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26890361439188052484849253 5041942769847759840909235)
                  ·
                    refine ⟨7562914154771639761363853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5041942769847759840909235 7562914154771639761363853)
                    ·
                      refine ⟨2836092808039364910511445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7562914154771639761363853 2836092808039364910511445)
                      ·
                        rfl

theorem cell23_5523271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 4, 1, 3].length) (baseStart_5523271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523271 prefixEnd_5523271 := by exact prefixLift 5523271
  have htrace : WordTrace (prefixWord ++ tailWord_5523271) baseStart_5523271 baseEnd_5523271 := by
    simpa [prefixWord, tailWord_5523271, baseEnd_5523271] using wordTrace_append hprefix tailTrace_5523271
  have hstable : (prefixWord ++ tailWord_5523271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523271).length < 2 ^ (prefixWord ++ tailWord_5523271).sum := by decide
  have hdescent : baseEnd_5523271 < baseStart_5523271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523272 : List Nat := [2, 1, 3, 1, 1, 4, 4, 2, 1, 2, 2]
def baseStart_5523272 : Nat := 118140960795 + 5523272 * 2 ^ 59
def prefixEnd_5523272 : Nat := 4983230072969 + 3 ^ 40 * 5523272 * 2
def baseEnd_5523272 : Nat := 2836093321520019406598941

theorem tailTrace_5523272 : CollatzResearch.WordTrace tailWord_5523272 prefixEnd_5523272 2836093321520019406598941 := by
  unfold tailWord_5523272
  simp only [CollatzResearch.WordTrace]
  refine ⟨100725139823068159301390035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134300186430757545735186713 100725139823068159301390035)
  ·
    refine ⟨151087709734602238952085053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100725139823068159301390035 151087709734602238952085053)
    ·
      refine ⟨56657891150475839607031895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151087709734602238952085053 56657891150475839607031895)
      ·
        refine ⟨84986836725713759410547843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56657891150475839607031895 84986836725713759410547843)
        ·
          refine ⟨127480255088570639115821765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84986836725713759410547843 127480255088570639115821765)
          ·
            refine ⟨23902547829106994834216581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127480255088570639115821765 23902547829106994834216581)
            ·
              refine ⟨4481727717957561531415609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23902547829106994834216581 4481727717957561531415609)
              ·
                refine ⟨3361295788468171148561707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4481727717957561531415609 3361295788468171148561707)
                ·
                  refine ⟨5041943682702256722842561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3361295788468171148561707 5041943682702256722842561)
                  ·
                    refine ⟨3781457762026692542131921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5041943682702256722842561 3781457762026692542131921)
                    ·
                      refine ⟨2836093321520019406598941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3781457762026692542131921 2836093321520019406598941)
                      ·
                        rfl

theorem cell23_5523272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 2, 1, 2, 2].length) (baseStart_5523272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523272 prefixEnd_5523272 := by exact prefixLift 5523272
  have htrace : WordTrace (prefixWord ++ tailWord_5523272) baseStart_5523272 baseEnd_5523272 := by
    simpa [prefixWord, tailWord_5523272, baseEnd_5523272] using wordTrace_append hprefix tailTrace_5523272
  have hstable : (prefixWord ++ tailWord_5523272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523272).length < 2 ^ (prefixWord ++ tailWord_5523272).sum := by decide
  have hdescent : baseEnd_5523272 < baseStart_5523272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523304 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 1, 8]
def baseStart_5523304 : Nat := 118140960795 + 5523304 * 2 ^ 59
def prefixEnd_5523304 : Nat := 4983230072969 + 3 ^ 40 * 5523304 * 2
def baseEnd_5523304 : Nat := 945369917633654427132931

theorem tailTrace_5523304 : CollatzResearch.WordTrace tailWord_5523304 prefixEnd_5523304 945369917633654427132931 := by
  unfold tailWord_5523304
  simp only [CollatzResearch.WordTrace]
  refine ⟨100725723391010194033972483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134300964521346925378629977 100725723391010194033972483)
  ·
    refine ⟨151088585086515291050958725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100725723391010194033972483 151088585086515291050958725)
    ·
      refine ⟨28329109703721617072054761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151088585086515291050958725 28329109703721617072054761)
      ·
        refine ⟨21246832277791212804041071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28329109703721617072054761 21246832277791212804041071)
        ·
          refine ⟨31870248416686819206061607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21246832277791212804041071 31870248416686819206061607)
          ·
            refine ⟨47805372625030228809092411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31870248416686819206061607 47805372625030228809092411)
            ·
              refine ⟨71708058937545343213638617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47805372625030228809092411 71708058937545343213638617)
              ·
                refine ⟨53781044203159007410228963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71708058937545343213638617 53781044203159007410228963)
                ·
                  refine ⟨80671566304738511115343445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53781044203159007410228963 80671566304738511115343445)
                  ·
                    refine ⟨945369917633654427132931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80671566304738511115343445 945369917633654427132931)
                    ·
                      rfl

theorem cell23_5523304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_5523304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523304 prefixEnd_5523304 := by exact prefixLift 5523304
  have htrace : WordTrace (prefixWord ++ tailWord_5523304) baseStart_5523304 baseEnd_5523304 := by
    simpa [prefixWord, tailWord_5523304, baseEnd_5523304] using wordTrace_append hprefix tailTrace_5523304
  have hstable : (prefixWord ++ tailWord_5523304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523304).length < 2 ^ (prefixWord ++ tailWord_5523304).sum := by decide
  have hdescent : baseEnd_5523304 < baseStart_5523304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523314 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 1, 3, 5]
def baseStart_5523314 : Nat := 118140960795 + 5523314 * 2 ^ 59
def prefixEnd_5523314 : Nat := 4983230072969 + 3 ^ 40 * 5523314 * 2
def baseEnd_5523314 : Nat := 2836114887707508242273747

theorem tailTrace_5523314 : CollatzResearch.WordTrace tailWord_5523314 prefixEnd_5523314 2836114887707508242273747 := by
  unfold tailWord_5523314
  simp only [CollatzResearch.WordTrace]
  refine ⟨50362952877996039943952249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134301207674656106517205997 50362952877996039943952249)
  ·
    refine ⟨37772214658497029957964187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50362952877996039943952249 37772214658497029957964187)
    ·
      refine ⟨56658321987745544936946281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37772214658497029957964187 56658321987745544936946281)
      ·
        refine ⟨42493741490809158702709711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56658321987745544936946281 42493741490809158702709711)
        ·
          refine ⟨63740612236213738054064567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42493741490809158702709711 63740612236213738054064567)
          ·
            refine ⟨95610918354320607081096851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63740612236213738054064567 95610918354320607081096851)
            ·
              refine ⟨143416377531480910621645277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95610918354320607081096851 143416377531480910621645277)
              ·
                refine ⟨53781141574305341483116979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143416377531480910621645277 53781141574305341483116979)
                ·
                  refine ⟨80671712361458012224675469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53781141574305341483116979 80671712361458012224675469)
                  ·
                    refine ⟨30251892135546754584253301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80671712361458012224675469 30251892135546754584253301)
                    ·
                      refine ⟨2836114887707508242273747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30251892135546754584253301 2836114887707508242273747)
                      ·
                        rfl

theorem cell23_5523314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_5523314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523314 prefixEnd_5523314 := by exact prefixLift 5523314
  have htrace : WordTrace (prefixWord ++ tailWord_5523314) baseStart_5523314 baseEnd_5523314 := by
    simpa [prefixWord, tailWord_5523314, baseEnd_5523314] using wordTrace_append hprefix tailTrace_5523314
  have hstable : (prefixWord ++ tailWord_5523314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523314).length < 2 ^ (prefixWord ++ tailWord_5523314).sum := by decide
  have hdescent : baseEnd_5523314 < baseStart_5523314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523328 : List Nat := [2, 1, 1, 2, 1, 2, 5, 1, 4, 2, 2]
def baseStart_5523328 : Nat := 118140960795 + 5523328 * 2 ^ 59
def prefixEnd_5523328 : Nat := 4983230072969 + 3 ^ 40 * 5523328 * 2
def baseEnd_5523328 : Nat := 2836122076436671187498683

theorem tailTrace_5523328 : CollatzResearch.WordTrace tailWord_5523328 prefixEnd_5523328 2836122076436671187498683 := by
  unfold tailWord_5523328
  simp only [CollatzResearch.WordTrace]
  refine ⟨100726161066966720083409319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134301548089288960111212425 100726161066966720083409319)
  ·
    refine ⟨151089241600450080125113979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100726161066966720083409319 151089241600450080125113979)
    ·
      refine ⟨226633862400675120187670969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151089241600450080125113979 226633862400675120187670969)
      ·
        refine ⟨169975396800506340140753227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226633862400675120187670969 169975396800506340140753227)
        ·
          refine ⟨254963095200759510211129841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169975396800506340140753227 254963095200759510211129841)
          ·
            refine ⟨191222321400569632658347381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254963095200759510211129841 191222321400569632658347381)
            ·
              refine ⟨17927092631303403061720067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 191222321400569632658347381 17927092631303403061720067)
              ·
                refine ⟨26890638946955104592580101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17927092631303403061720067 26890638946955104592580101)
                ·
                  refine ⟨5041994802554082111108769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26890638946955104592580101 5041994802554082111108769)
                  ·
                    refine ⟨3781496101915561583331577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5041994802554082111108769 3781496101915561583331577)
                    ·
                      refine ⟨2836122076436671187498683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3781496101915561583331577 2836122076436671187498683)
                      ·
                        rfl

theorem cell23_5523328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 4, 2, 2].length) (baseStart_5523328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523328 prefixEnd_5523328 := by exact prefixLift 5523328
  have htrace : WordTrace (prefixWord ++ tailWord_5523328) baseStart_5523328 baseEnd_5523328 := by
    simpa [prefixWord, tailWord_5523328, baseEnd_5523328] using wordTrace_append hprefix tailTrace_5523328
  have hstable : (prefixWord ++ tailWord_5523328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523328).length < 2 ^ (prefixWord ++ tailWord_5523328).sum := by decide
  have hdescent : baseEnd_5523328 < baseStart_5523328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523381 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 4, 5]
def baseStart_5523381 : Nat := 118140960795 + 5523381 * 2 ^ 59
def prefixEnd_5523381 : Nat := 4983230072969 + 3 ^ 40 * 5523381 * 2
def baseEnd_5523381 : Nat := 945383096970453160045313

theorem tailTrace_5523381 : CollatzResearch.WordTrace tailWord_5523381 prefixEnd_5523381 945383096970453160045313 := by
  unfold tailWord_5523381
  simp only [CollatzResearch.WordTrace]
  refine ⟨201454255202741430218497997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134302836801827620145665331 201454255202741430218497997)
  ·
    refine ⟨75545345701028036331936749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201454255202741430218497997 75545345701028036331936749)
    ·
      refine ⟨28329504637885513624476281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75545345701028036331936749 28329504637885513624476281)
      ·
        refine ⟨21247128478414135218357211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28329504637885513624476281 21247128478414135218357211)
        ·
          refine ⟨31870692717621202827535817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21247128478414135218357211 31870692717621202827535817)
          ·
            refine ⟨23903019538215902120651863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31870692717621202827535817 23903019538215902120651863)
            ·
              refine ⟨35854529307323853180977795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23903019538215902120651863 35854529307323853180977795)
              ·
                refine ⟨53781793960985779771466693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35854529307323853180977795 53781793960985779771466693)
                ·
                  refine ⟨10084086367684833707150005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53781793960985779771466693 10084086367684833707150005)
                  ·
                    refine ⟨945383096970453160045313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10084086367684833707150005 945383096970453160045313)
                    ·
                      rfl

theorem cell23_5523381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_5523381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523381 prefixEnd_5523381 := by exact prefixLift 5523381
  have htrace : WordTrace (prefixWord ++ tailWord_5523381) baseStart_5523381 baseEnd_5523381 := by
    simpa [prefixWord, tailWord_5523381, baseEnd_5523381] using wordTrace_append hprefix tailTrace_5523381
  have hstable : (prefixWord ++ tailWord_5523381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523381).length < 2 ^ (prefixWord ++ tailWord_5523381).sum := by decide
  have hdescent : baseEnd_5523381 < baseStart_5523381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523424 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 10]
def baseStart_5523424 : Nat := 118140960795 + 5523424 * 2 ^ 59
def prefixEnd_5523424 : Nat := 4983230072969 + 3 ^ 40 * 5523424 * 2
def baseEnd_5523424 : Nat := 315130152286611423544249

theorem tailTrace_5523424 : CollatzResearch.WordTrace tailWord_5523424 prefixEnd_5523424 315130152286611423544249 := by
  unfold tailWord_5523424
  simp only [CollatzResearch.WordTrace]
  refine ⟨100727911770792824281156663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134303882361057099041542217 100727911770792824281156663)
  ·
    refine ⟨151091867656189236421734995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100727911770792824281156663 151091867656189236421734995)
    ·
      refine ⟨226637801484283854632602493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151091867656189236421734995 226637801484283854632602493)
      ·
        refine ⟨84989175556606445487225935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226637801484283854632602493 84989175556606445487225935)
        ·
          refine ⟨127483763334909668230838903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84989175556606445487225935 127483763334909668230838903)
          ·
            refine ⟨191225645002364502346258355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127483763334909668230838903 191225645002364502346258355)
            ·
              refine ⟨286838467503546753519387533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191225645002364502346258355 286838467503546753519387533)
              ·
                refine ⟨107564425313830032569770325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 286838467503546753519387533 107564425313830032569770325)
                ·
                  refine ⟨315130152286611423544249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 107564425313830032569770325 315130152286611423544249)
                  ·
                    rfl

theorem cell23_5523424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 10].length) (baseStart_5523424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523424 prefixEnd_5523424 := by exact prefixLift 5523424
  have htrace : WordTrace (prefixWord ++ tailWord_5523424) baseStart_5523424 baseEnd_5523424 := by
    simpa [prefixWord, tailWord_5523424, baseEnd_5523424] using wordTrace_append hprefix tailTrace_5523424
  have hstable : (prefixWord ++ tailWord_5523424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523424).length < 2 ^ (prefixWord ++ tailWord_5523424).sum := by decide
  have hdescent : baseEnd_5523424 < baseStart_5523424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523492 : List Nat := [2, 3, 1, 4, 3, 1, 1, 2, 6]
def baseStart_5523492 : Nat := 118140960795 + 5523492 * 2 ^ 59
def prefixEnd_5523492 : Nat := 4983230072969 + 3 ^ 40 * 5523492 * 2
def baseEnd_5523492 : Nat := 315134031918223171760881

theorem tailTrace_5523492 : CollatzResearch.WordTrace tailWord_5523492 prefixEnd_5523492 315134031918223171760881 := by
  unfold tailWord_5523492
  simp only [CollatzResearch.WordTrace]
  refine ⟨100729151852669648087894365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134305535803559530783859153 100729151852669648087894365)
  ·
    refine ⟨37773431944751118032960387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100729151852669648087894365 37773431944751118032960387)
    ·
      refine ⟨56660147917126677049440581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37773431944751118032960387 56660147917126677049440581)
      ·
        refine ⟨10623777734461251946770109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56660147917126677049440581 10623777734461251946770109)
        ·
          refine ⟨3983916650422969480038791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10623777734461251946770109 3983916650422969480038791)
          ·
            refine ⟨5975874975634454220058187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3983916650422969480038791 5975874975634454220058187)
            ·
              refine ⟨8963812463451681330087281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5975874975634454220058187 8963812463451681330087281)
              ·
                refine ⟨6722859347588760997565461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8963812463451681330087281 6722859347588760997565461)
                ·
                  refine ⟨315134031918223171760881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6722859347588760997565461 315134031918223171760881)
                  ·
                    rfl

theorem cell23_5523492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 6].length) (baseStart_5523492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523492 prefixEnd_5523492 := by exact prefixLift 5523492
  have htrace : WordTrace (prefixWord ++ tailWord_5523492) baseStart_5523492 baseEnd_5523492 := by
    simpa [prefixWord, tailWord_5523492, baseEnd_5523492] using wordTrace_append hprefix tailTrace_5523492
  have hstable : (prefixWord ++ tailWord_5523492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523492).length < 2 ^ (prefixWord ++ tailWord_5523492).sum := by decide
  have hdescent : baseEnd_5523492 < baseStart_5523492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523502 : List Nat := [4, 1, 3, 1, 1, 3, 2, 1, 3, 1, 3]
def baseStart_5523502 : Nat := 118140960795 + 5523502 * 2 ^ 59
def prefixEnd_5523502 : Nat := 4983230072969 + 3 ^ 40 * 5523502 * 2
def baseEnd_5523502 : Nat := 2836211422070553506722883

theorem tailTrace_5523502 : CollatzResearch.WordTrace tailWord_5523502 prefixEnd_5523502 2836211422070553506722883 := by
  unfold tailWord_5523502
  simp only [CollatzResearch.WordTrace]
  refine ⟨25182333554412883485456595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134305778956868711922435173 25182333554412883485456595)
  ·
    refine ⟨37773500331619325228184893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25182333554412883485456595 37773500331619325228184893)
    ·
      refine ⟨14165062624357246960569335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37773500331619325228184893 14165062624357246960569335)
      ·
        refine ⟨21247593936535870440854003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14165062624357246960569335 21247593936535870440854003)
        ·
          refine ⟨31871390904803805661281005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21247593936535870440854003 31871390904803805661281005)
          ·
            refine ⟨11951771589301427122980377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31871390904803805661281005 11951771589301427122980377)
            ·
              refine ⟨8963828691976070342235283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11951771589301427122980377 8963828691976070342235283)
              ·
                refine ⟨13445743037964105513352925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8963828691976070342235283 13445743037964105513352925)
                ·
                  refine ⟨5042153639236539567507347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13445743037964105513352925 5042153639236539567507347)
                  ·
                    refine ⟨7563230458854809351261021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5042153639236539567507347 7563230458854809351261021)
                    ·
                      refine ⟨2836211422070553506722883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7563230458854809351261021 2836211422070553506722883)
                      ·
                        rfl

theorem cell23_5523502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_5523502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523502 prefixEnd_5523502 := by exact prefixLift 5523502
  have htrace : WordTrace (prefixWord ++ tailWord_5523502) baseStart_5523502 baseEnd_5523502 := by
    simpa [prefixWord, tailWord_5523502, baseEnd_5523502] using wordTrace_append hprefix tailTrace_5523502
  have hstable : (prefixWord ++ tailWord_5523502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523502).length < 2 ^ (prefixWord ++ tailWord_5523502).sum := by decide
  have hdescent : baseEnd_5523502 < baseStart_5523502 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523511 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 5]
def baseStart_5523511 : Nat := 118140960795 + 5523511 * 2 ^ 59
def prefixEnd_5523511 : Nat := 4983230072969 + 3 ^ 40 * 5523511 * 2
def baseEnd_5523511 : Nat := 2836216043396443971510341

theorem tailTrace_5523511 : CollatzResearch.WordTrace tailWord_5523511 prefixEnd_5523511 2836216043396443971510341 := by
  unfold tailWord_5523511
  simp only [CollatzResearch.WordTrace]
  refine ⟨201458996692270462420730387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134305997794846974947153591 201458996692270462420730387)
  ·
    refine ⟨302188495038405693631095581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201458996692270462420730387 302188495038405693631095581)
    ·
      refine ⟨113320685639402135111660843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302188495038405693631095581 113320685639402135111660843)
      ·
        refine ⟨169981028459103202667491265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113320685639402135111660843 169981028459103202667491265)
        ·
          refine ⟨127485771344327402000618449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169981028459103202667491265 127485771344327402000618449)
          ·
            refine ⟨95614328508245551500463837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127485771344327402000618449 95614328508245551500463837)
            ·
              refine ⟨35855373190592081812673939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95614328508245551500463837 35855373190592081812673939)
              ·
                refine ⟨53783059785888122719010909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35855373190592081812673939 53783059785888122719010909)
                ·
                  refine ⟨20168647419708046019629091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53783059785888122719010909 20168647419708046019629091)
                  ·
                    refine ⟨30252971129562069029443637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20168647419708046019629091 30252971129562069029443637)
                    ·
                      refine ⟨2836216043396443971510341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30252971129562069029443637 2836216043396443971510341)
                      ·
                        rfl

theorem cell23_5523511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_5523511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523511 prefixEnd_5523511 := by exact prefixLift 5523511
  have htrace : WordTrace (prefixWord ++ tailWord_5523511) baseStart_5523511 baseEnd_5523511 := by
    simpa [prefixWord, tailWord_5523511, baseEnd_5523511] using wordTrace_append hprefix tailTrace_5523511
  have hstable : (prefixWord ++ tailWord_5523511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523511).length < 2 ^ (prefixWord ++ tailWord_5523511).sum := by decide
  have hdescent : baseEnd_5523511 < baseStart_5523511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523548 : List Nat := [2, 2, 4, 1, 1, 4, 9]
def baseStart_5523548 : Nat := 118140960795 + 5523548 * 2 ^ 59
def prefixEnd_5523548 : Nat := 4983230072969 + 3 ^ 40 * 5523548 * 2
def baseEnd_5523548 : Nat := 35015247434329139836391

theorem tailTrace_5523548 : CollatzResearch.WordTrace tailWord_5523548 prefixEnd_5523548 35015247434329139836391 := by
  unfold tailWord_5523548
  simp only [CollatzResearch.WordTrace]
  refine ⟨100730173096568208869913649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134306897462090945159884865 100730173096568208869913649)
  ·
    refine ⟨75547629822426156652435237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100730173096568208869913649 75547629822426156652435237)
    ·
      refine ⟨14165180591704904372331607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75547629822426156652435237 14165180591704904372331607)
      ·
        refine ⟨21247770887557356558497411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14165180591704904372331607 21247770887557356558497411)
        ·
          refine ⟨31871656331336034837746117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21247770887557356558497411 31871656331336034837746117)
          ·
            refine ⟨5975935562125506532077397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31871656331336034837746117 5975935562125506532077397)
            ·
              refine ⟨35015247434329139836391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5975935562125506532077397 35015247434329139836391)
              ·
                rfl

theorem cell23_5523548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 9].length) (baseStart_5523548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523548 prefixEnd_5523548 := by exact prefixLift 5523548
  have htrace : WordTrace (prefixWord ++ tailWord_5523548) baseStart_5523548 baseEnd_5523548 := by
    simpa [prefixWord, tailWord_5523548, baseEnd_5523548] using wordTrace_append hprefix tailTrace_5523548
  have hstable : (prefixWord ++ tailWord_5523548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523548).length < 2 ^ (prefixWord ++ tailWord_5523548).sum := by decide
  have hdescent : baseEnd_5523548 < baseStart_5523548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523561 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 2, 7]
def baseStart_5523561 : Nat := 118140960795 + 5523561 * 2 ^ 59
def prefixEnd_5523561 : Nat := 4983230072969 + 3 ^ 40 * 5523561 * 2
def baseEnd_5523561 : Nat := 945413905809722925295037

theorem tailTrace_5523561 : CollatzResearch.WordTrace tailWord_5523561 prefixEnd_5523561 945413905809722925295037 := by
  unfold tailWord_5523561
  simp only [CollatzResearch.WordTrace]
  refine ⟨201460820342089320960050537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134307213561392880640033691 201460820342089320960050537)
  ·
    refine ⟨151095615256566990720037903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201460820342089320960050537 151095615256566990720037903)
    ·
      refine ⟨226643422884850486080056855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151095615256566990720037903 226643422884850486080056855)
      ·
        refine ⟨339965134327275729120085283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226643422884850486080056855 339965134327275729120085283)
        ·
          refine ⟨509947701490913593680127925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339965134327275729120085283 509947701490913593680127925)
          ·
            refine ⟨47807597014773149407511993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 509947701490913593680127925 47807597014773149407511993)
            ·
              refine ⟨35855697761079862055633995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47807597014773149407511993 35855697761079862055633995)
              ·
                refine ⟨53783546641619793083450993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35855697761079862055633995 53783546641619793083450993)
                ·
                  refine ⟨40337659981214844812588245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53783546641619793083450993 40337659981214844812588245)
                  ·
                    refine ⟨945413905809722925295037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40337659981214844812588245 945413905809722925295037)
                    ·
                      rfl

theorem cell23_5523561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 7].length) (baseStart_5523561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523561 prefixEnd_5523561 := by exact prefixLift 5523561
  have htrace : WordTrace (prefixWord ++ tailWord_5523561) baseStart_5523561 baseEnd_5523561 := by
    simpa [prefixWord, tailWord_5523561, baseEnd_5523561] using wordTrace_append hprefix tailTrace_5523561
  have hstable : (prefixWord ++ tailWord_5523561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523561).length < 2 ^ (prefixWord ++ tailWord_5523561).sum := by decide
  have hdescent : baseEnd_5523561 < baseStart_5523561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523610 : List Nat := [3, 1, 1, 5, 3, 1, 2, 2, 1, 2, 2]
def baseStart_5523610 : Nat := 118140960795 + 5523610 * 2 ^ 59
def prefixEnd_5523610 : Nat := 4983230072969 + 3 ^ 40 * 5523610 * 2
def baseEnd_5523610 : Nat := 2836266877981239084172387

theorem tailTrace_5523610 : CollatzResearch.WordTrace tailWord_5523610 prefixEnd_5523610 2836266877981239084172387 := by
  unfold tailWord_5523610
  simp only [CollatzResearch.WordTrace]
  refine ⟨50365651879727950582146071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134308405012607868219056189 50365651879727950582146071)
  ·
    refine ⟨75548477819591925873219107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50365651879727950582146071 75548477819591925873219107)
    ·
      refine ⟨113322716729387888809828661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75548477819591925873219107 113322716729387888809828661)
      ·
        refine ⟨10624004693380114575921437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113322716729387888809828661 10624004693380114575921437)
        ·
          refine ⟨3984001760017542965970539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10624004693380114575921437 3984001760017542965970539)
          ·
            refine ⟨5976002640026314448955809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3984001760017542965970539 5976002640026314448955809)
            ·
              refine ⟨4482001980019735836716857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5976002640026314448955809 4482001980019735836716857)
              ·
                refine ⟨3361501485014801877537643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4482001980019735836716857 3361501485014801877537643)
                ·
                  refine ⟨5042252227522202816306465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3361501485014801877537643 5042252227522202816306465)
                  ·
                    refine ⟨3781689170641652112229849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5042252227522202816306465 3781689170641652112229849)
                    ·
                      refine ⟨2836266877981239084172387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3781689170641652112229849 2836266877981239084172387)
                      ·
                        rfl

theorem cell23_5523610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_5523610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523610 prefixEnd_5523610 := by exact prefixLift 5523610
  have htrace : WordTrace (prefixWord ++ tailWord_5523610) baseStart_5523610 baseEnd_5523610 := by
    simpa [prefixWord, tailWord_5523610, baseEnd_5523610] using wordTrace_append hprefix tailTrace_5523610
  have hstable : (prefixWord ++ tailWord_5523610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523610).length < 2 ^ (prefixWord ++ tailWord_5523610).sum := by decide
  have hdescent : baseEnd_5523610 < baseStart_5523610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523666 : List Nat := [3, 2, 2, 2, 1, 4, 1, 2, 2, 2, 2]
def baseStart_5523666 : Nat := 118140960795 + 5523666 * 2 ^ 59
def prefixEnd_5523666 : Nat := 4983230072969 + 3 ^ 40 * 5523666 * 2
def baseEnd_5523666 : Nat := 2836295632897890865072129

theorem tailTrace_5523666 : CollatzResearch.WordTrace tailWord_5523666 prefixEnd_5523666 2836295632897890865072129 := by
  unfold tailWord_5523666
  simp only [CollatzResearch.WordTrace]
  refine ⟨50366162501677230973155713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134309766671139282595081901 50366162501677230973155713)
  ·
    refine ⟨37774621876257923229866785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50366162501677230973155713 37774621876257923229866785)
    ·
      refine ⟨28330966407193442422400089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37774621876257923229866785 28330966407193442422400089)
      ·
        refine ⟨21248224805395081816800067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28330966407193442422400089 21248224805395081816800067)
        ·
          refine ⟨31872337208092622725200101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21248224805395081816800067 31872337208092622725200101)
          ·
            refine ⟨5976063226517366760975019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31872337208092622725200101 5976063226517366760975019)
            ·
              refine ⟨8964094839776050141462529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5976063226517366760975019 8964094839776050141462529)
              ·
                refine ⟨6723071129832037606096897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8964094839776050141462529 6723071129832037606096897)
                ·
                  refine ⟨5042303347374028204572673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6723071129832037606096897 5042303347374028204572673)
                  ·
                    refine ⟨3781727510530521153429505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5042303347374028204572673 3781727510530521153429505)
                    ·
                      refine ⟨2836295632897890865072129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3781727510530521153429505 2836295632897890865072129)
                      ·
                        rfl

theorem cell23_5523666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_5523666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523666 prefixEnd_5523666 := by exact prefixLift 5523666
  have htrace : WordTrace (prefixWord ++ tailWord_5523666) baseStart_5523666 baseEnd_5523666 := by
    simpa [prefixWord, tailWord_5523666, baseEnd_5523666] using wordTrace_append hprefix tailTrace_5523666
  have hstable : (prefixWord ++ tailWord_5523666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523666).length < 2 ^ (prefixWord ++ tailWord_5523666).sum := by decide
  have hdescent : baseEnd_5523666 < baseStart_5523666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523683 : List Nat := [1, 1, 1, 8, 1, 1, 3, 1, 2, 2, 2]
def baseStart_5523683 : Nat := 118140960795 + 5523683 * 2 ^ 59
def prefixEnd_5523683 : Nat := 4983230072969 + 3 ^ 40 * 5523683 * 2
def baseEnd_5523683 : Nat := 2836304362069017298559551

theorem tailTrace_5523683 : CollatzResearch.WordTrace tailWord_5523683 prefixEnd_5523683 2836304362069017298559551 := by
  unfold tailWord_5523683
  simp only [CollatzResearch.WordTrace]
  refine ⟨201465270047647335795991703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134310180031764890530661135 201465270047647335795991703)
  ·
    refine ⟨302197905071471003693987555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201465270047647335795991703 302197905071471003693987555)
    ·
      refine ⟨453296857607206505540981333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302197905071471003693987555 453296857607206505540981333)
      ·
        refine ⟨5312072550084451236808375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 453296857607206505540981333 5312072550084451236808375)
        ·
          refine ⟨7968108825126676855212563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5312072550084451236808375 7968108825126676855212563)
          ·
            refine ⟨11952163237690015282818845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7968108825126676855212563 11952163237690015282818845)
            ·
              refine ⟨4482061214133755731057067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11952163237690015282818845 4482061214133755731057067)
              ·
                refine ⟨6723091821200633596585601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4482061214133755731057067 6723091821200633596585601)
                ·
                  refine ⟨5042318865900475197439201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6723091821200633596585601 5042318865900475197439201)
                  ·
                    refine ⟨3781739149425356398079401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5042318865900475197439201 3781739149425356398079401)
                    ·
                      refine ⟨2836304362069017298559551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3781739149425356398079401 2836304362069017298559551)
                      ·
                        rfl

theorem cell23_5523683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_5523683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523683 prefixEnd_5523683 := by exact prefixLift 5523683
  have htrace : WordTrace (prefixWord ++ tailWord_5523683) baseStart_5523683 baseEnd_5523683 := by
    simpa [prefixWord, tailWord_5523683, baseEnd_5523683] using wordTrace_append hprefix tailTrace_5523683
  have hstable : (prefixWord ++ tailWord_5523683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523683).length < 2 ^ (prefixWord ++ tailWord_5523683).sum := by decide
  have hdescent : baseEnd_5523683 < baseStart_5523683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523705 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 4, 4, 2]
def baseStart_5523705 : Nat := 118140960795 + 5523705 * 2 ^ 59
def prefixEnd_5523705 : Nat := 4983230072969 + 3 ^ 40 * 5523705 * 2
def baseEnd_5523705 : Nat := 2836315658643416212484449

theorem tailTrace_5523705 : CollatzResearch.WordTrace tailWord_5523705 prefixEnd_5523705 2836315658643416212484449 := by
  unfold tailWord_5523705
  simp only [CollatzResearch.WordTrace]
  refine ⟨201466072453567633553292569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134310714969045089035528379 201466072453567633553292569)
  ·
    refine ⟨151099554340175725164969427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201466072453567633553292569 151099554340175725164969427)
    ·
      refine ⟨226649331510263587747454141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151099554340175725164969427 226649331510263587747454141)
      ·
        refine ⟨84993499316348845405295303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226649331510263587747454141 84993499316348845405295303)
        ·
          refine ⟨127490248974523268107942955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84993499316348845405295303 127490248974523268107942955)
          ·
            refine ⟨191235373461784902161914433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127490248974523268107942955 191235373461784902161914433)
            ·
              refine ⟨143426530096338676621435825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191235373461784902161914433 143426530096338676621435825)
              ·
                refine ⟨107569897572254007466076869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143426530096338676621435825 107569897572254007466076869)
                ·
                  refine ⟨20169355794797626399889413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107569897572254007466076869 20169355794797626399889413)
                  ·
                    refine ⟨3781754211524554949979265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20169355794797626399889413 3781754211524554949979265)
                    ·
                      refine ⟨2836315658643416212484449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3781754211524554949979265 2836315658643416212484449)
                      ·
                        rfl

theorem cell23_5523705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 4, 2].length) (baseStart_5523705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523705 prefixEnd_5523705 := by exact prefixLift 5523705
  have htrace : WordTrace (prefixWord ++ tailWord_5523705) baseStart_5523705 baseEnd_5523705 := by
    simpa [prefixWord, tailWord_5523705, baseEnd_5523705] using wordTrace_append hprefix tailTrace_5523705
  have hstable : (prefixWord ++ tailWord_5523705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523705).length < 2 ^ (prefixWord ++ tailWord_5523705).sum := by decide
  have hdescent : baseEnd_5523705 < baseStart_5523705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523812 : List Nat := [2, 3, 1, 1, 3, 1, 2, 4, 1, 1, 4]
def baseStart_5523812 : Nat := 118140960795 + 5523812 * 2 ^ 59
def prefixEnd_5523812 : Nat := 4983230072969 + 3 ^ 40 * 5523812 * 2
def baseEnd_5523812 : Nat := 2836370601073447293846457

theorem tailTrace_5523812 : CollatzResearch.WordTrace tailWord_5523812 prefixEnd_5523812 2836370601073447293846457 := by
  unfold tailWord_5523812
  simp only [CollatzResearch.WordTrace]
  refine ⟨100734987532089995413718845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134313316709453327218291793 100734987532089995413718845)
  ·
    refine ⟨37775620324533748280144567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100734987532089995413718845 37775620324533748280144567)
    ·
      refine ⟨56663430486800622420216851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37775620324533748280144567 56663430486800622420216851)
      ·
        refine ⟨84995145730200933630325277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56663430486800622420216851 84995145730200933630325277)
        ·
          refine ⟨31873179648825350111371979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84995145730200933630325277 31873179648825350111371979)
          ·
            refine ⟨47809769473238025167057969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31873179648825350111371979 47809769473238025167057969)
            ·
              refine ⟨35857327104928518875293477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47809769473238025167057969 35857327104928518875293477)
              ·
                refine ⟨6723248832174097289117527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35857327104928518875293477 6723248832174097289117527)
                ·
                  refine ⟨10084873248261145933676291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6723248832174097289117527 10084873248261145933676291)
                  ·
                    refine ⟨15127309872391718900514437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10084873248261145933676291 15127309872391718900514437)
                    ·
                      refine ⟨2836370601073447293846457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15127309872391718900514437 2836370601073447293846457)
                      ·
                        rfl

theorem cell23_5523812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_5523812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523812 prefixEnd_5523812 := by exact prefixLift 5523812
  have htrace : WordTrace (prefixWord ++ tailWord_5523812) baseStart_5523812 baseEnd_5523812 := by
    simpa [prefixWord, tailWord_5523812, baseEnd_5523812] using wordTrace_append hprefix tailTrace_5523812
  have hstable : (prefixWord ++ tailWord_5523812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523812).length < 2 ^ (prefixWord ++ tailWord_5523812).sum := by decide
  have hdescent : baseEnd_5523812 < baseStart_5523812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523816 : List Nat := [2, 1, 4, 2, 2, 3, 1, 1, 2, 3, 2]
def baseStart_5523816 : Nat := 118140960795 + 5523816 * 2 ^ 59
def prefixEnd_5523816 : Nat := 4983230072969 + 3 ^ 40 * 5523816 * 2
def baseEnd_5523816 : Nat := 2836372654996065278196439

theorem tailTrace_5523816 : CollatzResearch.WordTrace tailWord_5523816 prefixEnd_5523816 2836372654996065278196439 := by
  unfold tailWord_5523816
  simp only [CollatzResearch.WordTrace]
  refine ⟨100735060478082749755291651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134313413970776999673722201 100735060478082749755291651)
  ·
    refine ⟨151102590717124124632937477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100735060478082749755291651 151102590717124124632937477)
    ·
      refine ⟨28331735759460773368675777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151102590717124124632937477 28331735759460773368675777)
      ·
        refine ⟨21248801819595580026506833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28331735759460773368675777 21248801819595580026506833)
        ·
          refine ⟨15936601364696685019880125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21248801819595580026506833 15936601364696685019880125)
          ·
            refine ⟨5976225511761256882455047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15936601364696685019880125 5976225511761256882455047)
            ·
              refine ⟨8964338267641885323682571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5976225511761256882455047 8964338267641885323682571)
              ·
                refine ⟨13446507401462827985523857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8964338267641885323682571 13446507401462827985523857)
                ·
                  refine ⟨10084880551097120989142893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13446507401462827985523857 10084880551097120989142893)
                  ·
                    refine ⟨3781830206661420370928585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10084880551097120989142893 3781830206661420370928585)
                    ·
                      refine ⟨2836372654996065278196439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3781830206661420370928585 2836372654996065278196439)
                      ·
                        rfl

theorem cell23_5523816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_5523816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523816 prefixEnd_5523816 := by exact prefixLift 5523816
  have htrace : WordTrace (prefixWord ++ tailWord_5523816) baseStart_5523816 baseEnd_5523816 := by
    simpa [prefixWord, tailWord_5523816, baseEnd_5523816] using wordTrace_append hprefix tailTrace_5523816
  have hstable : (prefixWord ++ tailWord_5523816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523816).length < 2 ^ (prefixWord ++ tailWord_5523816).sum := by decide
  have hdescent : baseEnd_5523816 < baseStart_5523816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523829 : List Nat := [1, 3, 4, 1, 2, 2, 1, 3, 1, 1, 4]
def baseStart_5523829 : Nat := 118140960795 + 5523829 * 2 ^ 59
def prefixEnd_5523829 : Nat := 4983230072969 + 3 ^ 40 * 5523829 * 2
def baseEnd_5523829 : Nat := 2836379330244573727333879

theorem tailTrace_5523829 : CollatzResearch.WordTrace tailWord_5523829 prefixEnd_5523829 2836379330244573727333879 := by
  unfold tailWord_5523829
  simp only [CollatzResearch.WordTrace]
  refine ⟨201470595105118402730806541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134313730070078935153871027 201470595105118402730806541)
  ·
    refine ⟨75551473164419401024052453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201470595105118402730806541 75551473164419401024052453)
    ·
      refine ⟨14165901218328637692009835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75551473164419401024052453 14165901218328637692009835)
      ·
        refine ⟨21248851827492956538014753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14165901218328637692009835 21248851827492956538014753)
        ·
          refine ⟨15936638870619717403511065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21248851827492956538014753 15936638870619717403511065)
          ·
            refine ⟨11952479152964788052633299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15936638870619717403511065 11952479152964788052633299)
            ·
              refine ⟨17928718729447182078949949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11952479152964788052633299 17928718729447182078949949)
              ·
                refine ⟨6723269523542693279606231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17928718729447182078949949 6723269523542693279606231)
                ·
                  refine ⟨10084904285314039919409347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6723269523542693279606231 10084904285314039919409347)
                  ·
                    refine ⟨15127356427971059879114021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10084904285314039919409347 15127356427971059879114021)
                    ·
                      refine ⟨2836379330244573727333879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15127356427971059879114021 2836379330244573727333879)
                      ·
                        rfl

theorem cell23_5523829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_5523829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523829 prefixEnd_5523829 := by exact prefixLift 5523829
  have htrace : WordTrace (prefixWord ++ tailWord_5523829) baseStart_5523829 baseEnd_5523829 := by
    simpa [prefixWord, tailWord_5523829, baseEnd_5523829] using wordTrace_append hprefix tailTrace_5523829
  have hstable : (prefixWord ++ tailWord_5523829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523829).length < 2 ^ (prefixWord ++ tailWord_5523829).sum := by decide
  have hdescent : baseEnd_5523829 < baseStart_5523829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523869 : List Nat := [1, 4, 2, 1, 4, 2, 2, 7]
def baseStart_5523869 : Nat := 118140960795 + 5523869 * 2 ^ 59
def prefixEnd_5523869 : Nat := 4983230072969 + 3 ^ 40 * 5523869 * 2
def baseEnd_5523869 : Nat := 105051847017435317438285

theorem tailTrace_5523869 : CollatzResearch.WordTrace tailWord_5523869 prefixEnd_5523869 105051847017435317438285 := by
  unfold tailWord_5523869
  simp only [CollatzResearch.WordTrace]
  refine ⟨201472054024973489562262661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134314702683315659708175107 201472054024973489562262661)
  ·
    refine ⟨37776010129682529292924249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201472054024973489562262661 37776010129682529292924249)
    ·
      refine ⟨28332007597261896969693187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37776010129682529292924249 28332007597261896969693187)
      ·
        refine ⟨42498011395892845454539781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28332007597261896969693187 42498011395892845454539781)
        ·
          refine ⟨7968377136729908522726209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42498011395892845454539781 7968377136729908522726209)
          ·
            refine ⟨5976282852547431392044657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7968377136729908522726209 5976282852547431392044657)
            ·
              refine ⟨4482212139410573544033493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5976282852547431392044657 4482212139410573544033493)
              ·
                refine ⟨105051847017435317438285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4482212139410573544033493 105051847017435317438285)
                ·
                  rfl

theorem cell23_5523869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 7].length) (baseStart_5523869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523869 prefixEnd_5523869 := by exact prefixLift 5523869
  have htrace : WordTrace (prefixWord ++ tailWord_5523869) baseStart_5523869 baseEnd_5523869 := by
    simpa [prefixWord, tailWord_5523869, baseEnd_5523869] using wordTrace_append hprefix tailTrace_5523869
  have hstable : (prefixWord ++ tailWord_5523869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523869).length < 2 ^ (prefixWord ++ tailWord_5523869).sum := by decide
  have hdescent : baseEnd_5523869 < baseStart_5523869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523875 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 5]
def baseStart_5523875 : Nat := 118140960795 + 5523875 * 2 ^ 59
def prefixEnd_5523875 : Nat := 4983230072969 + 3 ^ 40 * 5523875 * 2
def baseEnd_5523875 : Nat := 2836402950354680547358667

theorem tailTrace_5523875 : CollatzResearch.WordTrace tailWord_5523875 prefixEnd_5523875 2836402950354680547358667 := by
  unfold tailWord_5523875
  simp only [CollatzResearch.WordTrace]
  refine ⟨201472272862951752586981079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134314848575301168391320719 201472272862951752586981079)
  ·
    refine ⟨302208409294427628880471619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201472272862951752586981079 302208409294427628880471619)
    ·
      refine ⟨453312613941641443320707429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302208409294427628880471619 453312613941641443320707429)
      ·
        refine ⟨84996115114057770622632643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 453312613941641443320707429 84996115114057770622632643)
        ·
          refine ⟨127494172671086655933948965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84996115114057770622632643 127494172671086655933948965)
          ·
            refine ⟨23905157375828747987615431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127494172671086655933948965 23905157375828747987615431)
            ·
              refine ⟨35857736063743121981423147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23905157375828747987615431 35857736063743121981423147)
              ·
                refine ⟨53786604095614682972134721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35857736063743121981423147 53786604095614682972134721)
                ·
                  refine ⟨40339953071711012229101041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53786604095614682972134721 40339953071711012229101041)
                  ·
                    refine ⟨30254964803783259171825781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40339953071711012229101041 30254964803783259171825781)
                    ·
                      refine ⟨2836402950354680547358667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30254964803783259171825781 2836402950354680547358667)
                      ·
                        rfl

theorem cell23_5523875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_5523875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523875 prefixEnd_5523875 := by exact prefixLift 5523875
  have htrace : WordTrace (prefixWord ++ tailWord_5523875) baseStart_5523875 baseEnd_5523875 := by
    simpa [prefixWord, tailWord_5523875, baseEnd_5523875] using wordTrace_append hprefix tailTrace_5523875
  have hstable : (prefixWord ++ tailWord_5523875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523875).length < 2 ^ (prefixWord ++ tailWord_5523875).sum := by decide
  have hdescent : baseEnd_5523875 < baseStart_5523875 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523879 : List Nat := [1, 1, 6, 1, 1, 2, 1, 2, 4, 1, 3]
def baseStart_5523879 : Nat := 118140960795 + 5523879 * 2 ^ 59
def prefixEnd_5523879 : Nat := 4983230072969 + 3 ^ 40 * 5523879 * 2
def baseEnd_5523879 : Nat := 2836405004277298531708649

theorem tailTrace_5523879 : CollatzResearch.WordTrace tailWord_5523879 prefixEnd_5523879 2836405004277298531708649 := by
  unfold tailWord_5523879
  simp only [CollatzResearch.WordTrace]
  refine ⟨201472418754937261270126691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134314945836624840846751127 201472418754937261270126691)
  ·
    refine ⟨302208628132405891905190037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201472418754937261270126691 302208628132405891905190037)
    ·
      refine ⟨14166029443706526183055783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 302208628132405891905190037 14166029443706526183055783)
      ·
        refine ⟨21249044165559789274583675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14166029443706526183055783 21249044165559789274583675)
        ·
          refine ⟨31873566248339683911875513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21249044165559789274583675 31873566248339683911875513)
          ·
            refine ⟨23905174686254762933906635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31873566248339683911875513 23905174686254762933906635)
            ·
              refine ⟨35857762029382144400859953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23905174686254762933906635 35857762029382144400859953)
              ·
                refine ⟨26893321522036608300644965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35857762029382144400859953 26893321522036608300644965)
                ·
                  refine ⟨5042497785381864056370931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26893321522036608300644965 5042497785381864056370931)
                  ·
                    refine ⟨7563746678072796084556397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5042497785381864056370931 7563746678072796084556397)
                    ·
                      refine ⟨2836405004277298531708649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7563746678072796084556397 2836405004277298531708649)
                      ·
                        rfl

theorem cell23_5523879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_5523879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523879 prefixEnd_5523879 := by exact prefixLift 5523879
  have htrace : WordTrace (prefixWord ++ tailWord_5523879) baseStart_5523879 baseEnd_5523879 := by
    simpa [prefixWord, tailWord_5523879, baseEnd_5523879] using wordTrace_append hprefix tailTrace_5523879
  have hstable : (prefixWord ++ tailWord_5523879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523879).length < 2 ^ (prefixWord ++ tailWord_5523879).sum := by decide
  have hdescent : baseEnd_5523879 < baseStart_5523879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523880 : List Nat := [2, 1, 6, 1, 1, 1, 3, 3, 1, 2, 2]
def baseStart_5523880 : Nat := 118140960795 + 5523880 * 2 ^ 59
def prefixEnd_5523880 : Nat := 4983230072969 + 3 ^ 40 * 5523880 * 2
def baseEnd_5523880 : Nat := 2836405517757953027796145

theorem tailTrace_5523880 : CollatzResearch.WordTrace tailWord_5523880 prefixEnd_5523880 2836405517757953027796145 := by
  unfold tailWord_5523880
  simp only [CollatzResearch.WordTrace]
  refine ⟨100736227613966819220456547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134314970151955758960608729 100736227613966819220456547)
  ·
    refine ⟨151104341420950228830684821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100736227613966819220456547 151104341420950228830684821)
    ·
      refine ⟨7083016004107041976438351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 151104341420950228830684821 7083016004107041976438351)
      ·
        refine ⟨10624524006160562964657527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7083016004107041976438351 10624524006160562964657527)
        ·
          refine ⟨15936786009240844446986291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10624524006160562964657527 15936786009240844446986291)
          ·
            refine ⟨23905179013861266670479437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15936786009240844446986291 23905179013861266670479437)
            ·
              refine ⟨8964442130197975001429789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23905179013861266670479437 8964442130197975001429789)
              ·
                refine ⟨3361665798824240625536171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8964442130197975001429789 3361665798824240625536171)
                ·
                  refine ⟨5042498698236360938304257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3361665798824240625536171 5042498698236360938304257)
                  ·
                    refine ⟨3781874023677270703728193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5042498698236360938304257 3781874023677270703728193)
                    ·
                      refine ⟨2836405517757953027796145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3781874023677270703728193 2836405517757953027796145)
                      ·
                        rfl

theorem cell23_5523880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_5523880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523880 prefixEnd_5523880 := by exact prefixLift 5523880
  have htrace : WordTrace (prefixWord ++ tailWord_5523880) baseStart_5523880 baseEnd_5523880 := by
    simpa [prefixWord, tailWord_5523880, baseEnd_5523880] using wordTrace_append hprefix tailTrace_5523880
  have hstable : (prefixWord ++ tailWord_5523880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523880).length < 2 ^ (prefixWord ++ tailWord_5523880).sum := by decide
  have hdescent : baseEnd_5523880 < baseStart_5523880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523915 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 4]
def baseStart_5523915 : Nat := 118140960795 + 5523915 * 2 ^ 59
def prefixEnd_5523915 : Nat := 4983230072969 + 3 ^ 40 * 5523915 * 2
def baseEnd_5523915 : Nat := 2836423489580860390858483

theorem tailTrace_5523915 : CollatzResearch.WordTrace tailWord_5523915 prefixEnd_5523915 2836423489580860390858483 := by
  unfold tailWord_5523915
  simp only [CollatzResearch.WordTrace]
  refine ⟨201473731782806839418437199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134315821188537892945624799 201473731782806839418437199)
  ·
    refine ⟨302210597674210259127655799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201473731782806839418437199 302210597674210259127655799)
    ·
      refine ⟨453315896511315388691483699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302210597674210259127655799 453315896511315388691483699)
      ·
        refine ⟨679973844766973083037225549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 453315896511315388691483699 679973844766973083037225549)
        ·
          refine ⟨254990191787614906138959581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 679973844766973083037225549 254990191787614906138959581)
          ·
            refine ⟨95621321920355589802109843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 254990191787614906138959581 95621321920355589802109843)
            ·
              refine ⟨143431982880533384703164765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95621321920355589802109843 143431982880533384703164765)
              ·
                refine ⟨53786993580200019263686787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143431982880533384703164765 53786993580200019263686787)
                ·
                  refine ⟨80680490370300028895530181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53786993580200019263686787 80680490370300028895530181)
                  ·
                    refine ⟨15127591944431255417911909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80680490370300028895530181 15127591944431255417911909)
                    ·
                      refine ⟨2836423489580860390858483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15127591944431255417911909 2836423489580860390858483)
                      ·
                        rfl

theorem cell23_5523915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 4].length) (baseStart_5523915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523915 prefixEnd_5523915 := by exact prefixLift 5523915
  have htrace : WordTrace (prefixWord ++ tailWord_5523915) baseStart_5523915 baseEnd_5523915 := by
    simpa [prefixWord, tailWord_5523915, baseEnd_5523915] using wordTrace_append hprefix tailTrace_5523915
  have hstable : (prefixWord ++ tailWord_5523915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523915).length < 2 ^ (prefixWord ++ tailWord_5523915).sum := by decide
  have hdescent : baseEnd_5523915 < baseStart_5523915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523952 : List Nat := [2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 3]
def baseStart_5523952 : Nat := 118140960795 + 5523952 * 2 ^ 59
def prefixEnd_5523952 : Nat := 4983230072969 + 3 ^ 40 * 5523952 * 2
def baseEnd_5523952 : Nat := 2836442488365076746095813

theorem tailTrace_5523952 : CollatzResearch.WordTrace tailWord_5523952 prefixEnd_5523952 2836442488365076746095813 := by
  unfold tailWord_5523952
  simp only [CollatzResearch.WordTrace]
  refine ⟨100737540641836397368767055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134316720855781863158356073 100737540641836397368767055)
  ·
    refine ⟨151106310962754596053150583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100737540641836397368767055 151106310962754596053150583)
    ·
      refine ⟨226659466444131894079725875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151106310962754596053150583 226659466444131894079725875)
      ·
        refine ⟨339989199666197841119588813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226659466444131894079725875 339989199666197841119588813)
        ·
          refine ⟨127495949874824190419845805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 339989199666197841119588813 127495949874824190419845805)
          ·
            refine ⟨47810981203059071407442177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127495949874824190419845805 47810981203059071407442177)
            ·
              refine ⟨35858235902294303555581633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47810981203059071407442177 35858235902294303555581633)
              ·
                refine ⟨26893676926720727666686225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35858235902294303555581633 26893676926720727666686225)
                ·
                  refine ⟨20170257695040545750014669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26893676926720727666686225 20170257695040545750014669)
                  ·
                    refine ⟨7563846635640204656255501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20170257695040545750014669 7563846635640204656255501)
                    ·
                      refine ⟨2836442488365076746095813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7563846635640204656255501 2836442488365076746095813)
                      ·
                        rfl

theorem cell23_5523952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 3].length) (baseStart_5523952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523952 prefixEnd_5523952 := by exact prefixLift 5523952
  have htrace : WordTrace (prefixWord ++ tailWord_5523952) baseStart_5523952 baseEnd_5523952 := by
    simpa [prefixWord, tailWord_5523952, baseEnd_5523952] using wordTrace_append hprefix tailTrace_5523952
  have hstable : (prefixWord ++ tailWord_5523952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523952).length < 2 ^ (prefixWord ++ tailWord_5523952).sum := by decide
  have hdescent : baseEnd_5523952 < baseStart_5523952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523969 : List Nat := [1, 2, 4, 1, 3, 2, 1, 1, 2, 3, 3]
def baseStart_5523969 : Nat := 118140960795 + 5523969 * 2 ^ 59
def prefixEnd_5523969 : Nat := 4983230072969 + 3 ^ 40 * 5523969 * 2
def baseEnd_5523969 : Nat := 2836451217536203179583235

theorem tailTrace_5523969 : CollatzResearch.WordTrace tailWord_5523969 prefixEnd_5523969 2836451217536203179583235 := by
  unfold tailWord_5523969
  simp only [CollatzResearch.WordTrace]
  refine ⟨201475701324611206640902961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134317134216407471093935307 201475701324611206640902961)
  ·
    refine ⟨151106775993458404980677221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201475701324611206640902961 151106775993458404980677221)
    ·
      refine ⟨28332520498773450933876979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151106775993458404980677221 28332520498773450933876979)
      ·
        refine ⟨42498780748160176400815469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28332520498773450933876979 42498780748160176400815469)
        ·
          refine ⟨15937042780560066150305801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42498780748160176400815469 15937042780560066150305801)
          ·
            refine ⟨11952782085420049612729351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15937042780560066150305801 11952782085420049612729351)
            ·
              refine ⟨17929173128130074419094027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11952782085420049612729351 17929173128130074419094027)
              ·
                refine ⟨26893759692195111628641041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17929173128130074419094027 26893759692195111628641041)
                ·
                  refine ⟨20170319769146333721480781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26893759692195111628641041 20170319769146333721480781)
                  ·
                    refine ⟨7563869913429875145555293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20170319769146333721480781 7563869913429875145555293)
                    ·
                      refine ⟨2836451217536203179583235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7563869913429875145555293 2836451217536203179583235)
                      ·
                        rfl

theorem cell23_5523969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_5523969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523969 prefixEnd_5523969 := by exact prefixLift 5523969
  have htrace : WordTrace (prefixWord ++ tailWord_5523969) baseStart_5523969 baseEnd_5523969 := by
    simpa [prefixWord, tailWord_5523969, baseEnd_5523969] using wordTrace_append hprefix tailTrace_5523969
  have hstable : (prefixWord ++ tailWord_5523969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523969).length < 2 ^ (prefixWord ++ tailWord_5523969).sum := by decide
  have hdescent : baseEnd_5523969 < baseStart_5523969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5523985 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 1, 10]
def baseStart_5523985 : Nat := 118140960795 + 5523985 * 2 ^ 59
def prefixEnd_5523985 : Nat := 4983230072969 + 3 ^ 40 * 5523985 * 2
def baseEnd_5523985 : Nat := 945486477742225038994387

theorem tailTrace_5523985 : CollatzResearch.WordTrace tailWord_5523985 prefixEnd_5523985 945486477742225038994387 := by
  unfold tailWord_5523985
  simp only [CollatzResearch.WordTrace]
  refine ⟨201476284892553241373485409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134317523261702160915656939 201476284892553241373485409)
  ·
    refine ⟨151107213669414931030114057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201476284892553241373485409 151107213669414931030114057)
    ·
      refine ⟨113330410252061198272585543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151107213669414931030114057 113330410252061198272585543)
      ·
        refine ⟨169995615378091797408878315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113330410252061198272585543 169995615378091797408878315)
        ·
          refine ⟨254993423067137696113317473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169995615378091797408878315 254993423067137696113317473)
          ·
            refine ⟨191245067300353272084988105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254993423067137696113317473 191245067300353272084988105)
            ·
              refine ⟨143433800475264954063741079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191245067300353272084988105 143433800475264954063741079)
              ·
                refine ⟨215150700712897431095611619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143433800475264954063741079 215150700712897431095611619)
                ·
                  refine ⟨322726051069346146643417429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215150700712897431095611619 322726051069346146643417429)
                  ·
                    refine ⟨945486477742225038994387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 322726051069346146643417429 945486477742225038994387)
                    ·
                      rfl

theorem cell23_5523985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 10].length) (baseStart_5523985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5523985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5523985 prefixEnd_5523985 := by exact prefixLift 5523985
  have htrace : WordTrace (prefixWord ++ tailWord_5523985) baseStart_5523985 baseEnd_5523985 := by
    simpa [prefixWord, tailWord_5523985, baseEnd_5523985] using wordTrace_append hprefix tailTrace_5523985
  have hstable : (prefixWord ++ tailWord_5523985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5523985).length < 2 ^ (prefixWord ++ tailWord_5523985).sum := by decide
  have hdescent : baseEnd_5523985 < baseStart_5523985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5523985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524019 : List Nat := [1, 1, 1, 2, 4, 2, 4, 1, 3, 4]
def baseStart_5524019 : Nat := 118140960795 + 5524019 * 2 ^ 59
def prefixEnd_5524019 : Nat := 4983230072969 + 3 ^ 40 * 5524019 * 2
def baseEnd_5524019 : Nat := 945492297189642661319335

theorem tailTrace_5524019 : CollatzResearch.WordTrace tailWord_5524019 prefixEnd_5524019 945492297189642661319335 := by
  unfold tailWord_5524019
  simp only [CollatzResearch.WordTrace]
  refine ⟨201477524974430065180223111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134318349982953376786815407 201477524974430065180223111)
  ·
    refine ⟨302216287461645097770334667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201477524974430065180223111 302216287461645097770334667)
    ·
      refine ⟨453324431192467646655502001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302216287461645097770334667 453324431192467646655502001)
      ·
        refine ⟨339993323394350734991626501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 453324431192467646655502001 339993323394350734991626501)
        ·
          refine ⟨63748748136440762810929969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 339993323394350734991626501 63748748136440762810929969)
          ·
            refine ⟨47811561102330572108197477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63748748136440762810929969 47811561102330572108197477)
            ·
              refine ⟨8964667706686982270287027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47811561102330572108197477 8964667706686982270287027)
              ·
                refine ⟨13447001560030473405430541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8964667706686982270287027 13447001560030473405430541)
                ·
                  refine ⟨5042625585011427527036453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13447001560030473405430541 5042625585011427527036453)
                  ·
                    refine ⟨945492297189642661319335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5042625585011427527036453 945492297189642661319335)
                    ·
                      rfl

theorem cell23_5524019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 3, 4].length) (baseStart_5524019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524019 prefixEnd_5524019 := by exact prefixLift 5524019
  have htrace : WordTrace (prefixWord ++ tailWord_5524019) baseStart_5524019 baseEnd_5524019 := by
    simpa [prefixWord, tailWord_5524019, baseEnd_5524019] using wordTrace_append hprefix tailTrace_5524019
  have hstable : (prefixWord ++ tailWord_5524019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524019).length < 2 ^ (prefixWord ++ tailWord_5524019).sum := by decide
  have hdescent : baseEnd_5524019 < baseStart_5524019 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524029 : List Nat := [1, 4, 1, 3, 2, 1, 1, 2, 1, 4, 3]
def baseStart_5524029 : Nat := 118140960795 + 5524029 * 2 ^ 59
def prefixEnd_5524029 : Nat := 4983230072969 + 3 ^ 40 * 5524029 * 2
def baseEnd_5524029 : Nat := 2836482026375472944832959

theorem tailTrace_5524029 : CollatzResearch.WordTrace tailWord_5524029 prefixEnd_5524029 2836482026375472944832959 := by
  unfold tailWord_5524029
  simp only [CollatzResearch.WordTrace]
  refine ⟨201477889704393836888087141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134318593136262557925391427 201477889704393836888087141)
  ·
    refine ⟨37777104319573844416516339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201477889704393836888087141 37777104319573844416516339)
    ·
      refine ⟨56665656479360766624774509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37777104319573844416516339 56665656479360766624774509)
      ·
        refine ⟨21249621179760287484290441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56665656479360766624774509 21249621179760287484290441)
        ·
          refine ⟨15937215884820215613217831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21249621179760287484290441 15937215884820215613217831)
          ·
            refine ⟨23905823827230323419826747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15937215884820215613217831 23905823827230323419826747)
            ·
              refine ⟨35858735740845485129740121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23905823827230323419826747 35858735740845485129740121)
              ·
                refine ⟨26894051805634113847305091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35858735740845485129740121 26894051805634113847305091)
                ·
                  refine ⟨40341077708451170770957637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26894051805634113847305091 40341077708451170770957637)
                  ·
                    refine ⟨7563952070334594519554557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40341077708451170770957637 7563952070334594519554557)
                    ·
                      refine ⟨2836482026375472944832959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7563952070334594519554557 2836482026375472944832959)
                      ·
                        rfl

theorem cell23_5524029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_5524029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524029 prefixEnd_5524029 := by exact prefixLift 5524029
  have htrace : WordTrace (prefixWord ++ tailWord_5524029) baseStart_5524029 baseEnd_5524029 := by
    simpa [prefixWord, tailWord_5524029, baseEnd_5524029] using wordTrace_append hprefix tailTrace_5524029
  have hstable : (prefixWord ++ tailWord_5524029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524029).length < 2 ^ (prefixWord ++ tailWord_5524029).sum := by decide
  have hdescent : baseEnd_5524029 < baseStart_5524029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524032 : List Nat := [2, 1, 1, 2, 2, 2, 2, 5, 6]
def baseStart_5524032 : Nat := 118140960795 + 5524032 * 2 ^ 59
def prefixEnd_5524032 : Nat := 4983230072969 + 3 ^ 40 * 5524032 * 2
def baseEnd_5524032 : Nat := 315164840757492937010605

theorem tailTrace_5524032 : CollatzResearch.WordTrace tailWord_5524032 prefixEnd_5524032 315164840757492937010605 := by
  unfold tailWord_5524032
  simp only [CollatzResearch.WordTrace]
  refine ⟨100738999561691484200223175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134318666082255312266964233 100738999561691484200223175)
  ·
    refine ⟨151108499342537226300334763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100738999561691484200223175 151108499342537226300334763)
    ·
      refine ⟨226662749013805839450502145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151108499342537226300334763 226662749013805839450502145)
      ·
        refine ⟨169997061760354379587876609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226662749013805839450502145 169997061760354379587876609)
        ·
          refine ⟨127497796320265784690907457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169997061760354379587876609 127497796320265784690907457)
          ·
            refine ⟨95623347240199338518180593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127497796320265784690907457 95623347240199338518180593)
            ·
              refine ⟨71717510430149503888635445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95623347240199338518180593 71717510430149503888635445)
              ·
                refine ⟨6723516602826515989559573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71717510430149503888635445 6723516602826515989559573)
                ·
                  refine ⟨315164840757492937010605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6723516602826515989559573 315164840757492937010605)
                  ·
                    rfl

theorem cell23_5524032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 6].length) (baseStart_5524032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524032 prefixEnd_5524032 := by exact prefixLift 5524032
  have htrace : WordTrace (prefixWord ++ tailWord_5524032) baseStart_5524032 baseEnd_5524032 := by
    simpa [prefixWord, tailWord_5524032, baseEnd_5524032] using wordTrace_append hprefix tailTrace_5524032
  have hstable : (prefixWord ++ tailWord_5524032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524032).length < 2 ^ (prefixWord ++ tailWord_5524032).sum := by decide
  have hdescent : baseEnd_5524032 < baseStart_5524032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524076 : List Nat := [2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 3]
def baseStart_5524076 : Nat := 118140960795 + 5524076 * 2 ^ 59
def prefixEnd_5524076 : Nat := 4983230072969 + 3 ^ 40 * 5524076 * 2
def baseEnd_5524076 : Nat := 2836506159966234260945243

theorem tailTrace_5524076 : CollatzResearch.WordTrace tailWord_5524076 prefixEnd_5524076 2836506159966234260945243 := by
  unfold tailWord_5524076
  simp only [CollatzResearch.WordTrace]
  refine ⟨100739801967611781957524041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134319735956815709276698721 100739801967611781957524041)
  ·
    refine ⟨75554851475708836468143031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100739801967611781957524041 75554851475708836468143031)
    ·
      refine ⟨113332277213563254702214547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75554851475708836468143031 113332277213563254702214547)
      ·
        refine ⟨169998415820344882053321821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113332277213563254702214547 169998415820344882053321821)
        ·
          refine ⟨63749405932629330769995683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169998415820344882053321821 63749405932629330769995683)
          ·
            refine ⟨95624108898943996154993525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63749405932629330769995683 95624108898943996154993525)
            ·
              refine ⟨8964760209275999639530643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95624108898943996154993525 8964760209275999639530643)
              ·
                refine ⟨13447140313913999459295965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8964760209275999639530643 13447140313913999459295965)
                ·
                  refine ⟨5042677617717749797235987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13447140313913999459295965 5042677617717749797235987)
                  ·
                    refine ⟨7564016426576624695853981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5042677617717749797235987 7564016426576624695853981)
                    ·
                      refine ⟨2836506159966234260945243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7564016426576624695853981 2836506159966234260945243)
                      ·
                        rfl

theorem cell23_5524076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 3].length) (baseStart_5524076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524076 prefixEnd_5524076 := by exact prefixLift 5524076
  have htrace : WordTrace (prefixWord ++ tailWord_5524076) baseStart_5524076 baseEnd_5524076 := by
    simpa [prefixWord, tailWord_5524076, baseEnd_5524076] using wordTrace_append hprefix tailTrace_5524076
  have hstable : (prefixWord ++ tailWord_5524076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524076).length < 2 ^ (prefixWord ++ tailWord_5524076).sum := by decide
  have hdescent : baseEnd_5524076 < baseStart_5524076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524096 : List Nat := [2, 1, 1, 2, 1, 7, 1, 2, 1, 5]
def baseStart_5524096 : Nat := 118140960795 + 5524096 * 2 ^ 59
def prefixEnd_5524096 : Nat := 4983230072969 + 3 ^ 40 * 5524096 * 2
def baseEnd_5524096 : Nat := 945505476526441394231717

theorem tailTrace_5524096 : CollatzResearch.WordTrace tailWord_5524096 prefixEnd_5524096 945505476526441394231717 := by
  unfold tailWord_5524096
  simp only [CollatzResearch.WordTrace]
  refine ⟨100740166697575553665388071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134320222263434071553850761 100740166697575553665388071)
  ·
    refine ⟨151110250046363330498082107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100740166697575553665388071 151110250046363330498082107)
    ·
      refine ⟨226665375069544995747123161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151110250046363330498082107 226665375069544995747123161)
      ·
        refine ⟨169999031302158746810342371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226665375069544995747123161 169999031302158746810342371)
        ·
          refine ⟨254998546953238120215513557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169999031302158746810342371 254998546953238120215513557)
          ·
            refine ⟨5976528444216518442551099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 254998546953238120215513557 5976528444216518442551099)
            ·
              refine ⟨8964792666324777663826649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5976528444216518442551099 8964792666324777663826649)
              ·
                refine ⟨6723594499743583247869987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8964792666324777663826649 6723594499743583247869987)
                ·
                  refine ⟨10085391749615374871804981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6723594499743583247869987 10085391749615374871804981)
                  ·
                    refine ⟨945505476526441394231717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10085391749615374871804981 945505476526441394231717)
                    ·
                      rfl

theorem cell23_5524096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 1, 5].length) (baseStart_5524096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524096 prefixEnd_5524096 := by exact prefixLift 5524096
  have htrace : WordTrace (prefixWord ++ tailWord_5524096) baseStart_5524096 baseEnd_5524096 := by
    simpa [prefixWord, tailWord_5524096, baseEnd_5524096] using wordTrace_append hprefix tailTrace_5524096
  have hstable : (prefixWord ++ tailWord_5524096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524096).length < 2 ^ (prefixWord ++ tailWord_5524096).sum := by decide
  have hdescent : baseEnd_5524096 < baseStart_5524096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524099 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 2, 6, 2]
def baseStart_5524099 : Nat := 118140960795 + 5524099 * 2 ^ 59
def prefixEnd_5524099 : Nat := 4983230072969 + 3 ^ 40 * 5524099 * 2
def baseEnd_5524099 : Nat := 2836517970021287670957637

theorem tailTrace_5524099 : CollatzResearch.WordTrace tailWord_5524099 prefixEnd_5524099 2836517970021287670957637 := by
  unfold tailWord_5524099
  simp only [CollatzResearch.WordTrace]
  refine ⟨201480442814140238843135351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134320295209426825895423567 201480442814140238843135351)
  ·
    refine ⟨302220664221210358264703027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201480442814140238843135351 302220664221210358264703027)
    ·
      refine ⟨453330996331815537397054541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302220664221210358264703027 453330996331815537397054541)
      ·
        refine ⟨169999123624430826523895453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 453330996331815537397054541 169999123624430826523895453)
        ·
          refine ⟨63749671359161559946460795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169999123624430826523895453 63749671359161559946460795)
          ·
            refine ⟨95624507038742339919691193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63749671359161559946460795 95624507038742339919691193)
            ·
              refine ⟨71718380279056754939768395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95624507038742339919691193 71718380279056754939768395)
              ·
                refine ⟨107577570418585132409652593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71718380279056754939768395 107577570418585132409652593)
                ·
                  refine ⟨80683177813938849307239445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107577570418585132409652593 80683177813938849307239445)
                  ·
                    refine ⟨3782023960028383561276849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 80683177813938849307239445 3782023960028383561276849)
                    ·
                      refine ⟨2836517970021287670957637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3782023960028383561276849 2836517970021287670957637)
                      ·
                        rfl

theorem cell23_5524099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 6, 2].length) (baseStart_5524099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524099 prefixEnd_5524099 := by exact prefixLift 5524099
  have htrace : WordTrace (prefixWord ++ tailWord_5524099) baseStart_5524099 baseEnd_5524099 := by
    simpa [prefixWord, tailWord_5524099, baseEnd_5524099] using wordTrace_append hprefix tailTrace_5524099
  have hstable : (prefixWord ++ tailWord_5524099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524099).length < 2 ^ (prefixWord ++ tailWord_5524099).sum := by decide
  have hdescent : baseEnd_5524099 < baseStart_5524099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524170 : List Nat := [3, 1, 2, 1, 4, 3, 2, 1, 1, 2, 3]
def baseStart_5524170 : Nat := 118140960795 + 5524170 * 2 ^ 59
def prefixEnd_5524170 : Nat := 4983230072969 + 3 ^ 40 * 5524170 * 2
def baseEnd_5524170 : Nat := 2836554427147756893169811

theorem tailTrace_5524170 : CollatzResearch.WordTrace tailWord_5524170 prefixEnd_5524170 2836554427147756893169811 := by
  unfold tailWord_5524170
  simp only [CollatzResearch.WordTrace]
  refine ⟨50370758099220754492242491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134322021597922011979313309 50370758099220754492242491)
  ·
    refine ⟨75556137148831131738363737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50370758099220754492242491 75556137148831131738363737)
    ·
      refine ⟨56667102861623348803772803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75556137148831131738363737 56667102861623348803772803)
      ·
        refine ⟨85000654292435023205659205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56667102861623348803772803 85000654292435023205659205)
        ·
          refine ⟨15937622679831566851061101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85000654292435023205659205 15937622679831566851061101)
          ·
            refine ⟨5976608504936837569147913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15937622679831566851061101 5976608504936837569147913)
            ·
              refine ⟨4482456378702628176860935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5976608504936837569147913 4482456378702628176860935)
              ·
                refine ⟨6723684568053942265291403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4482456378702628176860935 6723684568053942265291403)
                ·
                  refine ⟨10085526852080913397937105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6723684568053942265291403 10085526852080913397937105)
                  ·
                    refine ⟨7564145139060685048452829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10085526852080913397937105 7564145139060685048452829)
                    ·
                      refine ⟨2836554427147756893169811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7564145139060685048452829 2836554427147756893169811)
                      ·
                        rfl

theorem cell23_5524170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 1, 2, 3].length) (baseStart_5524170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524170 prefixEnd_5524170 := by exact prefixLift 5524170
  have htrace : WordTrace (prefixWord ++ tailWord_5524170) baseStart_5524170 baseEnd_5524170 := by
    simpa [prefixWord, tailWord_5524170, baseEnd_5524170] using wordTrace_append hprefix tailTrace_5524170
  have hstable : (prefixWord ++ tailWord_5524170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524170).length < 2 ^ (prefixWord ++ tailWord_5524170).sum := by decide
  have hdescent : baseEnd_5524170 < baseStart_5524170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524183 : List Nat := [1, 1, 3, 2, 1, 4, 3, 2, 2, 1, 3]
def baseStart_5524183 : Nat := 118140960795 + 5524183 * 2 ^ 59
def prefixEnd_5524183 : Nat := 4983230072969 + 3 ^ 40 * 5524183 * 2
def baseEnd_5524183 : Nat := 2836561102396265342307251

theorem tailTrace_5524183 : CollatzResearch.WordTrace tailWord_5524183 prefixEnd_5524183 2836561102396265342307251 := by
  unfold tailWord_5524183
  simp only [CollatzResearch.WordTrace]
  refine ⟨201483506545835921189193203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134322337697223947459462135 201483506545835921189193203)
  ·
    refine ⟨302225259818753881783789805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201483506545835921189193203 302225259818753881783789805)
    ·
      refine ⟨113334472432032705668921177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302225259818753881783789805 113334472432032705668921177)
      ·
        refine ⟨85000854324024529251690883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113334472432032705668921177 85000854324024529251690883)
        ·
          refine ⟨127501281486036793877536325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85000854324024529251690883 127501281486036793877536325)
          ·
            refine ⟨23906490278631898852038061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127501281486036793877536325 23906490278631898852038061)
            ·
              refine ⟨8964933854486962069514273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23906490278631898852038061 8964933854486962069514273)
              ·
                refine ⟨6723700390865221552135705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8964933854486962069514273 6723700390865221552135705)
                ·
                  refine ⟨5042775293148916164101779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6723700390865221552135705 5042775293148916164101779)
                  ·
                    refine ⟨7564162939723374246152669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5042775293148916164101779 7564162939723374246152669)
                    ·
                      refine ⟨2836561102396265342307251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7564162939723374246152669 2836561102396265342307251)
                      ·
                        rfl

theorem cell23_5524183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 2, 1, 3].length) (baseStart_5524183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524183 prefixEnd_5524183 := by exact prefixLift 5524183
  have htrace : WordTrace (prefixWord ++ tailWord_5524183) baseStart_5524183 baseEnd_5524183 := by
    simpa [prefixWord, tailWord_5524183, baseEnd_5524183] using wordTrace_append hprefix tailTrace_5524183
  have hstable : (prefixWord ++ tailWord_5524183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524183).length < 2 ^ (prefixWord ++ tailWord_5524183).sum := by decide
  have hdescent : baseEnd_5524183 < baseStart_5524183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524200 : List Nat := [2, 1, 4, 1, 5, 1, 1, 1, 1, 3, 3]
def baseStart_5524200 : Nat := 118140960795 + 5524200 * 2 ^ 59
def prefixEnd_5524200 : Nat := 4983230072969 + 3 ^ 40 * 5524200 * 2
def baseEnd_5524200 : Nat := 2836569831567391775794673

theorem tailTrace_5524200 : CollatzResearch.WordTrace tailWord_5524200 prefixEnd_5524200 2836569831567391775794673 := by
  unfold tailWord_5524200
  simp only [CollatzResearch.WordTrace]
  refine ⟨100742063293387166546281027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134322751057849555395041369 100742063293387166546281027)
  ·
    refine ⟨151113094940080749819421541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100742063293387166546281027 151113094940080749819421541)
    ·
      refine ⟨28333705301265140591141539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151113094940080749819421541 28333705301265140591141539)
      ·
        refine ⟨42500557951897710886712309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28333705301265140591141539 42500557951897710886712309)
        ·
          refine ⟨3984427307990410395629279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42500557951897710886712309 3984427307990410395629279)
          ·
            refine ⟨5976640961985615593443919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3984427307990410395629279 5976640961985615593443919)
            ·
              refine ⟨8964961442978423390165879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5976640961985615593443919 8964961442978423390165879)
              ·
                refine ⟨13447442164467635085248819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8964961442978423390165879 13447442164467635085248819)
                ·
                  refine ⟨20171163246701452627873229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13447442164467635085248819 20171163246701452627873229)
                  ·
                    refine ⟨7564186217513044735452461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20171163246701452627873229 7564186217513044735452461)
                    ·
                      refine ⟨2836569831567391775794673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7564186217513044735452461 2836569831567391775794673)
                      ·
                        rfl

theorem cell23_5524200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_5524200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524200 prefixEnd_5524200 := by exact prefixLift 5524200
  have htrace : WordTrace (prefixWord ++ tailWord_5524200) baseStart_5524200 baseEnd_5524200 := by
    simpa [prefixWord, tailWord_5524200, baseEnd_5524200] using wordTrace_append hprefix tailTrace_5524200
  have hstable : (prefixWord ++ tailWord_5524200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524200).length < 2 ^ (prefixWord ++ tailWord_5524200).sum := by decide
  have hdescent : baseEnd_5524200 < baseStart_5524200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524209 : List Nat := [1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 5]
def baseStart_5524209 : Nat := 118140960795 + 5524209 * 2 ^ 59
def prefixEnd_5524209 : Nat := 4983230072969 + 3 ^ 40 * 5524209 * 2
def baseEnd_5524209 : Nat := 2836574452893282240582131

theorem tailTrace_5524209 : CollatzResearch.WordTrace tailWord_5524209 prefixEnd_5524209 2836574452893282240582131 := by
  unfold tailWord_5524209
  simp only [CollatzResearch.WordTrace]
  refine ⟨201484454843741727629639681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134322969895827818419759787 201484454843741727629639681)
  ·
    refine ⟨151113341132806295722229761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201484454843741727629639681 151113341132806295722229761)
    ·
      refine ⟨113335005849604721791672321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151113341132806295722229761 113335005849604721791672321)
      ·
        refine ⟨85001254387203541343754241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113335005849604721791672321 85001254387203541343754241)
        ·
          refine ⟨63750940790402656007815681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85001254387203541343754241 63750940790402656007815681)
          ·
            refine ⟨47813205592801992005861761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63750940790402656007815681 47813205592801992005861761)
            ·
              refine ⟨35859904194601494004396321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47813205592801992005861761 35859904194601494004396321)
              ·
                refine ⟨26894928145951120503297241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35859904194601494004396321 26894928145951120503297241)
                ·
                  refine ⟨20171196109463340377472931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26894928145951120503297241 20171196109463340377472931)
                  ·
                    refine ⟨30256794164195010566209397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20171196109463340377472931 30256794164195010566209397)
                    ·
                      refine ⟨2836574452893282240582131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30256794164195010566209397 2836574452893282240582131)
                      ·
                        rfl

theorem cell23_5524209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_5524209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524209 prefixEnd_5524209 := by exact prefixLift 5524209
  have htrace : WordTrace (prefixWord ++ tailWord_5524209) baseStart_5524209 baseEnd_5524209 := by
    simpa [prefixWord, tailWord_5524209, baseEnd_5524209] using wordTrace_append hprefix tailTrace_5524209
  have hstable : (prefixWord ++ tailWord_5524209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524209).length < 2 ^ (prefixWord ++ tailWord_5524209).sum := by decide
  have hdescent : baseEnd_5524209 < baseStart_5524209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524210 : List Nat := [3, 2, 1, 3, 1, 3, 2, 2, 1, 3, 2]
def baseStart_5524210 : Nat := 118140960795 + 5524210 * 2 ^ 59
def prefixEnd_5524210 : Nat := 4983230072969 + 3 ^ 40 * 5524210 * 2
def baseEnd_5524210 : Nat := 2836574966373936736669627

theorem tailTrace_5524210 : CollatzResearch.WordTrace tailWord_5524210 prefixEnd_5524210 2836574966373936736669627 := by
  unfold tailWord_5524210
  simp only [CollatzResearch.WordTrace]
  refine ⟨50371122829184526200106521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134322994211158736533617389 50371122829184526200106521)
  ·
    refine ⟨37778342121888394650079891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50371122829184526200106521 37778342121888394650079891)
    ·
      refine ⟨56667513182832591975119837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37778342121888394650079891 56667513182832591975119837)
      ·
        refine ⟨21250317443562221990669939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56667513182832591975119837 21250317443562221990669939)
        ·
          refine ⟨31875476165343332986004909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21250317443562221990669939 31875476165343332986004909)
          ·
            refine ⟨11953303562003749869751841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31875476165343332986004909 11953303562003749869751841)
            ·
              refine ⟨8964977671502812402313881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11953303562003749869751841 8964977671502812402313881)
              ·
                refine ⟨6723733253627109301735411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8964977671502812402313881 6723733253627109301735411)
                ·
                  refine ⟨10085599880440663952603117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6723733253627109301735411 10085599880440663952603117)
                  ·
                    refine ⟨3782099955165248982226169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10085599880440663952603117 3782099955165248982226169)
                    ·
                      refine ⟨2836574966373936736669627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3782099955165248982226169 2836574966373936736669627)
                      ·
                        rfl

theorem cell23_5524210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_5524210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524210 prefixEnd_5524210 := by exact prefixLift 5524210
  have htrace : WordTrace (prefixWord ++ tailWord_5524210) baseStart_5524210 baseEnd_5524210 := by
    simpa [prefixWord, tailWord_5524210, baseEnd_5524210] using wordTrace_append hprefix tailTrace_5524210
  have hstable : (prefixWord ++ tailWord_5524210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524210).length < 2 ^ (prefixWord ++ tailWord_5524210).sum := by decide
  have hdescent : baseEnd_5524210 < baseStart_5524210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524226 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_5524226 : Nat := 118140960795 + 5524226 * 2 ^ 59
def prefixEnd_5524226 : Nat := 4983230072969 + 3 ^ 40 * 5524226 * 2
def baseEnd_5524226 : Nat := 2836583182064408674069553

theorem tailTrace_5524226 : CollatzResearch.WordTrace tailWord_5524226 prefixEnd_5524226 2836583182064408674069553 := by
  unfold tailWord_5524226
  simp only [CollatzResearch.WordTrace]
  refine ⟨50371268721170034883252133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134323383256453426355339021 50371268721170034883252133)
  ·
    refine ⟨9444612885219381540609775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50371268721170034883252133 9444612885219381540609775)
    ·
      refine ⟨14166919327829072310914663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9444612885219381540609775 14166919327829072310914663)
      ·
        refine ⟨21250378991743608466371995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14166919327829072310914663 21250378991743608466371995)
        ·
          refine ⟨31875568487615412699557993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21250378991743608466371995 31875568487615412699557993)
          ·
            refine ⟨23906676365711559524668495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31875568487615412699557993 23906676365711559524668495)
            ·
              refine ⟨35860014548567339287002743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23906676365711559524668495 35860014548567339287002743)
              ·
                refine ⟨53790021822851008930504115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35860014548567339287002743 53790021822851008930504115)
                ·
                  refine ⟨80685032734276513395756173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53790021822851008930504115 80685032734276513395756173)
                  ·
                    refine ⟨30256887275353692523408565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80685032734276513395756173 30256887275353692523408565)
                    ·
                      refine ⟨2836583182064408674069553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30256887275353692523408565 2836583182064408674069553)
                      ·
                        rfl

theorem cell23_5524226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_5524226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524226 prefixEnd_5524226 := by exact prefixLift 5524226
  have htrace : WordTrace (prefixWord ++ tailWord_5524226) baseStart_5524226 baseEnd_5524226 := by
    simpa [prefixWord, tailWord_5524226, baseEnd_5524226] using wordTrace_append hprefix tailTrace_5524226
  have hstable : (prefixWord ++ tailWord_5524226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524226).length < 2 ^ (prefixWord ++ tailWord_5524226).sum := by decide
  have hdescent : baseEnd_5524226 < baseStart_5524226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524259 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 6, 5]
def baseStart_5524259 : Nat := 118140960795 + 5524259 * 2 ^ 59
def prefixEnd_5524259 : Nat := 4983230072969 + 3 ^ 40 * 5524259 * 2
def baseEnd_5524259 : Nat := 945533375642002348318967

theorem tailTrace_5524259 : CollatzResearch.WordTrace tailWord_5524259 prefixEnd_5524259 945533375642002348318967 := by
  unfold tailWord_5524259
  simp only [CollatzResearch.WordTrace]
  refine ⟨201486278493560586168959831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134324185662373724112639887 201486278493560586168959831)
  ·
    refine ⟨302229417740340879253439747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201486278493560586168959831 302229417740340879253439747)
    ·
      refine ⟨453344126610511318880159621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302229417740340879253439747 453344126610511318880159621)
      ·
        refine ⟨85002023739470872290029929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 453344126610511318880159621 85002023739470872290029929)
        ·
          refine ⟨63751517804603154217522447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85002023739470872290029929 63751517804603154217522447)
          ·
            refine ⟨95627276706904731326283671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63751517804603154217522447 95627276706904731326283671)
            ·
              refine ⟨143440915060357096989425507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95627276706904731326283671 143440915060357096989425507)
              ·
                refine ⟨215161372590535645484138261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143440915060357096989425507 215161372590535645484138261)
                ·
                  refine ⟨10085689340181358382068981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 215161372590535645484138261 10085689340181358382068981)
                  ·
                    refine ⟨945533375642002348318967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10085689340181358382068981 945533375642002348318967)
                    ·
                      rfl

theorem cell23_5524259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6, 5].length) (baseStart_5524259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524259 prefixEnd_5524259 := by exact prefixLift 5524259
  have htrace : WordTrace (prefixWord ++ tailWord_5524259) baseStart_5524259 baseEnd_5524259 := by
    simpa [prefixWord, tailWord_5524259, baseEnd_5524259] using wordTrace_append hprefix tailTrace_5524259
  have hstable : (prefixWord ++ tailWord_5524259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524259).length < 2 ^ (prefixWord ++ tailWord_5524259).sum := by decide
  have hdescent : baseEnd_5524259 < baseStart_5524259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524296 : List Nat := [2, 1, 3, 1, 1, 3, 1, 4, 2, 1, 4]
def baseStart_5524296 : Nat := 118140960795 + 5524296 * 2 ^ 59
def prefixEnd_5524296 : Nat := 4983230072969 + 3 ^ 40 * 5524296 * 2
def baseEnd_5524296 : Nat := 2836619125710223400194231

theorem tailTrace_5524296 : CollatzResearch.WordTrace tailWord_5524296 prefixEnd_5524296 2836619125710223400194231 := by
  unfold tailWord_5524296
  simp only [CollatzResearch.WordTrace]
  refine ⟨100743813997213270744028371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134325085329617694325371161 100743813997213270744028371)
  ·
    refine ⟨151115720995819906116042557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100743813997213270744028371 151115720995819906116042557)
    ·
      refine ⟨56668395373432464793515959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151115720995819906116042557 56668395373432464793515959)
      ·
        refine ⟨85002593060148697190273939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56668395373432464793515959 85002593060148697190273939)
        ·
          refine ⟨127503889590223045785410909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85002593060148697190273939 127503889590223045785410909)
          ·
            refine ⟨47813958596333642169529091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127503889590223045785410909 47813958596333642169529091)
            ·
              refine ⟨71720937894500463254293637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47813958596333642169529091 71720937894500463254293637)
              ·
                refine ⟨13447675855218836860180057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71720937894500463254293637 13447675855218836860180057)
                ·
                  refine ⟨10085756891414127645135043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13447675855218836860180057 10085756891414127645135043)
                  ·
                    refine ⟨15128635337121191467702565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10085756891414127645135043 15128635337121191467702565)
                    ·
                      refine ⟨2836619125710223400194231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15128635337121191467702565 2836619125710223400194231)
                      ·
                        rfl

theorem cell23_5524296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_5524296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524296 prefixEnd_5524296 := by exact prefixLift 5524296
  have htrace : WordTrace (prefixWord ++ tailWord_5524296) baseStart_5524296 baseEnd_5524296 := by
    simpa [prefixWord, tailWord_5524296, baseEnd_5524296] using wordTrace_append hprefix tailTrace_5524296
  have hstable : (prefixWord ++ tailWord_5524296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524296).length < 2 ^ (prefixWord ++ tailWord_5524296).sum := by decide
  have hdescent : baseEnd_5524296 < baseStart_5524296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524313 : List Nat := [1, 2, 1, 2, 2, 5, 1, 1, 2, 4, 2]
def baseStart_5524313 : Nat := 118140960795 + 5524313 * 2 ^ 59
def prefixEnd_5524313 : Nat := 4983230072969 + 3 ^ 40 * 5524313 * 2
def baseEnd_5524313 : Nat := 2836627854881349833681653

theorem tailTrace_5524313 : CollatzResearch.WordTrace tailWord_5524313 prefixEnd_5524313 2836627854881349833681653 := by
  unfold tailWord_5524313
  simp only [CollatzResearch.WordTrace]
  refine ⟨201488248035364953391425593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134325498690243302260950395 201488248035364953391425593)
  ·
    refine ⟨151116186026523715043569195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201488248035364953391425593 151116186026523715043569195)
    ·
      refine ⟨226674279039785572565353793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151116186026523715043569195 226674279039785572565353793)
      ·
        refine ⟨170005709279839179424015345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226674279039785572565353793 170005709279839179424015345)
        ·
          refine ⟨127504281959879384568011509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170005709279839179424015345 127504281959879384568011509)
          ·
            refine ⟨11953526433738692303251079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 127504281959879384568011509 11953526433738692303251079)
            ·
              refine ⟨17930289650608038454876619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11953526433738692303251079 17930289650608038454876619)
              ·
                refine ⟨26895434475912057682314929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17930289650608038454876619 26895434475912057682314929)
                ·
                  refine ⟨20171575856934043261736197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26895434475912057682314929 20171575856934043261736197)
                  ·
                    refine ⟨3782170473175133111575537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20171575856934043261736197 3782170473175133111575537)
                    ·
                      refine ⟨2836627854881349833681653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3782170473175133111575537 2836627854881349833681653)
                      ·
                        rfl

theorem cell23_5524313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 4, 2].length) (baseStart_5524313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524313 prefixEnd_5524313 := by exact prefixLift 5524313
  have htrace : WordTrace (prefixWord ++ tailWord_5524313) baseStart_5524313 baseEnd_5524313 := by
    simpa [prefixWord, tailWord_5524313, baseEnd_5524313] using wordTrace_append hprefix tailTrace_5524313
  have hstable : (prefixWord ++ tailWord_5524313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524313).length < 2 ^ (prefixWord ++ tailWord_5524313).sum := by decide
  have hdescent : baseEnd_5524313 < baseStart_5524313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524323 : List Nat := [1, 1, 1, 5, 3, 2, 1, 2, 3, 4]
def baseStart_5524323 : Nat := 118140960795 + 5524323 * 2 ^ 59
def prefixEnd_5524323 : Nat := 4983230072969 + 3 ^ 40 * 5524323 * 2
def baseEnd_5524323 : Nat := 945544329895964931518869

theorem tailTrace_5524323 : CollatzResearch.WordTrace tailWord_5524323 prefixEnd_5524323 945544329895964931518869 := by
  unfold tailWord_5524323
  simp only [CollatzResearch.WordTrace]
  refine ⟨201488612765328725099289623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134325741843552483399526415 201488612765328725099289623)
  ·
    refine ⟨302232919147993087648934435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201488612765328725099289623 302232919147993087648934435)
    ·
      refine ⟨453349378721989631473401653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302232919147993087648934435 453349378721989631473401653)
      ·
        refine ⟨42501504255186527950631405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 453349378721989631473401653 42501504255186527950631405)
        ·
          refine ⟨15938064095694947981486777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42501504255186527950631405 15938064095694947981486777)
          ·
            refine ⟨11953548071771210986115083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15938064095694947981486777 11953548071771210986115083)
            ·
              refine ⟨17930322107656816479172625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11953548071771210986115083 17930322107656816479172625)
              ·
                refine ⟨13447741580742612359379469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17930322107656816479172625 13447741580742612359379469)
                ·
                  refine ⟨5042903092778479634767301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13447741580742612359379469 5042903092778479634767301)
                  ·
                    refine ⟨945544329895964931518869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5042903092778479634767301 945544329895964931518869)
                    ·
                      rfl

theorem cell23_5524323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 3, 4].length) (baseStart_5524323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524323 prefixEnd_5524323 := by exact prefixLift 5524323
  have htrace : WordTrace (prefixWord ++ tailWord_5524323) baseStart_5524323 baseEnd_5524323 := by
    simpa [prefixWord, tailWord_5524323, baseEnd_5524323] using wordTrace_append hprefix tailTrace_5524323
  have hstable : (prefixWord ++ tailWord_5524323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524323).length < 2 ^ (prefixWord ++ tailWord_5524323).sum := by decide
  have hdescent : baseEnd_5524323 < baseStart_5524323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524363 : List Nat := [1, 1, 1, 1, 4, 2, 3, 3, 3, 1, 3]
def baseStart_5524363 : Nat := 118140960795 + 5524363 * 2 ^ 59
def prefixEnd_5524363 : Nat := 4983230072969 + 3 ^ 40 * 5524363 * 2
def baseEnd_5524363 : Nat := 2836653528914074638056423

theorem tailTrace_5524363 : CollatzResearch.WordTrace tailWord_5524363 prefixEnd_5524363 2836653528914074638056423 := by
  unfold tailWord_5524363
  simp only [CollatzResearch.WordTrace]
  refine ⟨201490071685183811930745743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134326714456789207953830495 201490071685183811930745743)
  ·
    refine ⟨302235107527775717896118615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201490071685183811930745743 302235107527775717896118615)
    ·
      refine ⟨453352661291663576844177923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302235107527775717896118615 453352661291663576844177923)
      ·
        refine ⟨680028991937495365266266885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 453352661291663576844177923 680028991937495365266266885)
        ·
          refine ⟨127505435988280380987425041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 680028991937495365266266885 127505435988280380987425041)
          ·
            refine ⟨95629076991210285740568781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127505435988280380987425041 95629076991210285740568781)
            ·
              refine ⟨35860903871703857152713293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95629076991210285740568781 35860903871703857152713293)
              ·
                refine ⟨13447838951888946432267485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35860903871703857152713293 13447838951888946432267485)
                ·
                  refine ⟨5042939606958354912100307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13447838951888946432267485 5042939606958354912100307)
                  ·
                    refine ⟨7564409410437532368150461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5042939606958354912100307 7564409410437532368150461)
                    ·
                      refine ⟨2836653528914074638056423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7564409410437532368150461 2836653528914074638056423)
                      ·
                        rfl

theorem cell23_5524363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 3, 1, 3].length) (baseStart_5524363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524363 prefixEnd_5524363 := by exact prefixLift 5524363
  have htrace : WordTrace (prefixWord ++ tailWord_5524363) baseStart_5524363 baseEnd_5524363 := by
    simpa [prefixWord, tailWord_5524363, baseEnd_5524363] using wordTrace_append hprefix tailTrace_5524363
  have hstable : (prefixWord ++ tailWord_5524363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524363).length < 2 ^ (prefixWord ++ tailWord_5524363).sum := by decide
  have hdescent : baseEnd_5524363 < baseStart_5524363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524373 : List Nat := [1, 3, 2, 1, 1, 4, 1, 2, 1, 5, 2]
def baseStart_5524373 : Nat := 118140960795 + 5524373 * 2 ^ 59
def prefixEnd_5524373 : Nat := 4983230072969 + 3 ^ 40 * 5524373 * 2
def baseEnd_5524373 : Nat := 2836658663720619598931377

theorem tailTrace_5524373 : CollatzResearch.WordTrace tailWord_5524373 prefixEnd_5524373 2836658663720619598931377 := by
  unfold tailWord_5524373
  simp only [CollatzResearch.WordTrace]
  refine ⟨201490436415147583638609773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134326957610098389092406515 201490436415147583638609773)
  ·
    refine ⟨75558913655680343864478665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201490436415147583638609773 75558913655680343864478665)
    ·
      refine ⟨56669185241760257898358999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75558913655680343864478665 56669185241760257898358999)
      ·
        refine ⟨85003777862640386847538499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56669185241760257898358999 85003777862640386847538499)
        ·
          refine ⟨127505666793960580271307749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85003777862640386847538499 127505666793960580271307749)
          ·
            refine ⟨23907312523867608800870203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127505666793960580271307749 23907312523867608800870203)
            ·
              refine ⟨35860968785801413201305305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23907312523867608800870203 35860968785801413201305305)
              ·
                refine ⟨26895726589351059900978979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35860968785801413201305305 26895726589351059900978979)
                ·
                  refine ⟨40343589884026589851468469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26895726589351059900978979 40343589884026589851468469)
                  ·
                    refine ⟨3782211551627492798575169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40343589884026589851468469 3782211551627492798575169)
                    ·
                      refine ⟨2836658663720619598931377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3782211551627492798575169 2836658663720619598931377)
                      ·
                        rfl

theorem cell23_5524373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 5, 2].length) (baseStart_5524373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524373 prefixEnd_5524373 := by exact prefixLift 5524373
  have htrace : WordTrace (prefixWord ++ tailWord_5524373) baseStart_5524373 baseEnd_5524373 := by
    simpa [prefixWord, tailWord_5524373, baseEnd_5524373] using wordTrace_append hprefix tailTrace_5524373
  have hstable : (prefixWord ++ tailWord_5524373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524373).length < 2 ^ (prefixWord ++ tailWord_5524373).sum := by decide
  have hdescent : baseEnd_5524373 < baseStart_5524373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524383 : List Nat := [1, 1, 2, 5, 2, 1, 1, 4, 1, 5]
def baseStart_5524383 : Nat := 118140960795 + 5524383 * 2 ^ 59
def prefixEnd_5524383 : Nat := 4983230072969 + 3 ^ 40 * 5524383 * 2
def baseEnd_5524383 : Nat := 945554599509054853268777

theorem tailTrace_5524383 : CollatzResearch.WordTrace tailWord_5524383 prefixEnd_5524383 945554599509054853268777 := by
  unfold tailWord_5524383
  simp only [CollatzResearch.WordTrace]
  refine ⟨201490801145111355346473803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134327200763407570230982535 201490801145111355346473803)
  ·
    refine ⟨302236201717667033019710705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201490801145111355346473803 302236201717667033019710705)
    ·
      refine ⟨226677151288250274764783029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302236201717667033019710705 226677151288250274764783029)
      ·
        refine ⟨21250982933273463259198409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 226677151288250274764783029 21250982933273463259198409)
        ·
          refine ⟨15938237199955097444398807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21250982933273463259198409 15938237199955097444398807)
          ·
            refine ⟨23907355799932646166598211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15938237199955097444398807 23907355799932646166598211)
            ·
              refine ⟨35861033699898969249897317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23907355799932646166598211 35861033699898969249897317)
              ·
                refine ⟨6723943818731056734355747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35861033699898969249897317 6723943818731056734355747)
                ·
                  refine ⟨10085915728096585101533621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6723943818731056734355747 10085915728096585101533621)
                  ·
                    refine ⟨945554599509054853268777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10085915728096585101533621 945554599509054853268777)
                    ·
                      rfl

theorem cell23_5524383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 5].length) (baseStart_5524383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524383 prefixEnd_5524383 := by exact prefixLift 5524383
  have htrace : WordTrace (prefixWord ++ tailWord_5524383) baseStart_5524383 baseEnd_5524383 := by
    simpa [prefixWord, tailWord_5524383, baseEnd_5524383] using wordTrace_append hprefix tailTrace_5524383
  have hstable : (prefixWord ++ tailWord_5524383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524383).length < 2 ^ (prefixWord ++ tailWord_5524383).sum := by decide
  have hdescent : baseEnd_5524383 < baseStart_5524383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524414 : List Nat := [4, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3]
def baseStart_5524414 : Nat := 118140960795 + 5524414 * 2 ^ 59
def prefixEnd_5524414 : Nat := 4983230072969 + 3 ^ 40 * 5524414 * 2
def baseEnd_5524414 : Nat := 2836679716427453938518689

theorem tailTrace_5524414 : CollatzResearch.WordTrace tailWord_5524414 prefixEnd_5524414 2836679716427453938518689 := by
  unfold tailWord_5524414
  simp only [CollatzResearch.WordTrace]
  refine ⟨25186491475999880955106537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134327954538666031760568197 25186491475999880955106537)
  ·
    refine ⟨18889868606999910716329903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25186491475999880955106537 18889868606999910716329903)
    ·
      refine ⟨28334802910499866074494855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18889868606999910716329903 28334802910499866074494855)
      ·
        refine ⟨42502204365749799111742283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28334802910499866074494855 42502204365749799111742283)
        ·
          refine ⟨63753306548624698667613425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42502204365749799111742283 63753306548624698667613425)
          ·
            refine ⟨47814979911468524000710069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63753306548624698667613425 47814979911468524000710069)
            ·
              refine ⟨4482654366700174125066569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47814979911468524000710069 4482654366700174125066569)
              ·
                refine ⟨3361990775025130593799927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4482654366700174125066569 3361990775025130593799927)
                ·
                  refine ⟨5042986162537695890699891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3361990775025130593799927 5042986162537695890699891)
                  ·
                    refine ⟨7564479243806543836049837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5042986162537695890699891 7564479243806543836049837)
                    ·
                      refine ⟨2836679716427453938518689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7564479243806543836049837 2836679716427453938518689)
                      ·
                        rfl

theorem cell23_5524414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_5524414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524414 prefixEnd_5524414 := by exact prefixLift 5524414
  have htrace : WordTrace (prefixWord ++ tailWord_5524414) baseStart_5524414 baseEnd_5524414 := by
    simpa [prefixWord, tailWord_5524414, baseEnd_5524414] using wordTrace_append hprefix tailTrace_5524414
  have hstable : (prefixWord ++ tailWord_5524414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524414).length < 2 ^ (prefixWord ++ tailWord_5524414).sum := by decide
  have hdescent : baseEnd_5524414 < baseStart_5524414 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524416 : List Nat := [2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 6]
def baseStart_5524416 : Nat := 118140960795 + 5524416 * 2 ^ 59
def prefixEnd_5524416 : Nat := 4983230072969 + 3 ^ 40 * 5524416 * 2
def baseEnd_5524416 : Nat := 2836680743388762930693679

theorem tailTrace_5524416 : CollatzResearch.WordTrace tailWord_5524416 prefixEnd_5524416 2836680743388762930693679 := by
  unfold tailWord_5524416
  simp only [CollatzResearch.WordTrace]
  refine ⟨100746002376995900991212551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134328003169327867988283401 100746002376995900991212551)
  ·
    refine ⟨151119003565493851486818827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100746002376995900991212551 151119003565493851486818827)
    ·
      refine ⟨226678505348240777230228241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151119003565493851486818827 226678505348240777230228241)
      ·
        refine ⟨170008879011180582922671181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226678505348240777230228241 170008879011180582922671181)
        ·
          refine ⟨63753329629192718596001693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170008879011180582922671181 63753329629192718596001693)
          ·
            refine ⟨23907498610947269473500635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63753329629192718596001693 23907498610947269473500635)
            ·
              refine ⟨35861247916420904210250953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23907498610947269473500635 35861247916420904210250953)
              ·
                refine ⟨26895935937315678157688215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35861247916420904210250953 26895935937315678157688215)
                ·
                  refine ⟨40343903905973517236532323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26895935937315678157688215 40343903905973517236532323)
                  ·
                    refine ⟨60515855858960275854798485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40343903905973517236532323 60515855858960275854798485)
                    ·
                      refine ⟨2836680743388762930693679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60515855858960275854798485 2836680743388762930693679)
                      ·
                        rfl

theorem cell23_5524416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_5524416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524416 prefixEnd_5524416 := by exact prefixLift 5524416
  have htrace : WordTrace (prefixWord ++ tailWord_5524416) baseStart_5524416 baseEnd_5524416 := by
    simpa [prefixWord, tailWord_5524416, baseEnd_5524416] using wordTrace_append hprefix tailTrace_5524416
  have hstable : (prefixWord ++ tailWord_5524416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524416).length < 2 ^ (prefixWord ++ tailWord_5524416).sum := by decide
  have hdescent : baseEnd_5524416 < baseStart_5524416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524430 : List Nat := [4, 1, 1, 1, 2, 4, 1, 3, 2, 4]
def baseStart_5524430 : Nat := 118140960795 + 5524430 * 2 ^ 59
def prefixEnd_5524430 : Nat := 4983230072969 + 3 ^ 40 * 5524430 * 2
def baseEnd_5524430 : Nat := 945562644039308625306205

theorem tailTrace_5524430 : CollatzResearch.WordTrace tailWord_5524430 prefixEnd_5524430 945562644039308625306205 := by
  unfold tailWord_5524430
  simp only [CollatzResearch.WordTrace]
  refine ⟨25186564421992635296679343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134328343583960721582289829 25186564421992635296679343)
  ·
    refine ⟨37779846632988952945019015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25186564421992635296679343 37779846632988952945019015)
    ·
      refine ⟨56669769949483429417528523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37779846632988952945019015 56669769949483429417528523)
      ·
        refine ⟨85004654924225144126292785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56669769949483429417528523 85004654924225144126292785)
        ·
          refine ⟨63753491193168858094719589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85004654924225144126292785 63753491193168858094719589)
          ·
            refine ⟨11953779598719160892759923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63753491193168858094719589 11953779598719160892759923)
            ·
              refine ⟨17930669398078741339139885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11953779598719160892759923 17930669398078741339139885)
              ·
                refine ⟨6724001024279528002177457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17930669398078741339139885 6724001024279528002177457)
                ·
                  refine ⟨5043000768209646001633093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6724001024279528002177457 5043000768209646001633093)
                  ·
                    refine ⟨945562644039308625306205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5043000768209646001633093 945562644039308625306205)
                    ·
                      rfl

theorem cell23_5524430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_5524430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524430 prefixEnd_5524430 := by exact prefixLift 5524430
  have htrace : WordTrace (prefixWord ++ tailWord_5524430) baseStart_5524430 baseEnd_5524430 := by
    simpa [prefixWord, tailWord_5524430, baseEnd_5524430] using wordTrace_append hprefix tailTrace_5524430
  have hstable : (prefixWord ++ tailWord_5524430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524430).length < 2 ^ (prefixWord ++ tailWord_5524430).sum := by decide
  have hdescent : baseEnd_5524430 < baseStart_5524430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524437 : List Nat := [1, 3, 2, 3, 3, 2, 1, 2, 1, 1, 4]
def baseStart_5524437 : Nat := 118140960795 + 5524437 * 2 ^ 59
def prefixEnd_5524437 : Nat := 4983230072969 + 3 ^ 40 * 5524437 * 2
def baseEnd_5524437 : Nat := 2836691526482507348531083

theorem tailTrace_5524437 : CollatzResearch.WordTrace tailWord_5524437 prefixEnd_5524437 2836691526482507348531083 := by
  unfold tailWord_5524437
  simp only [CollatzResearch.WordTrace]
  refine ⟨201492770686915722568939565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134328513791277148379293043 201492770686915722568939565)
  ·
    refine ⟨75559789007593395963352337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201492770686915722568939565 75559789007593395963352337)
    ·
      refine ⟨56669841755695046972514253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75559789007593395963352337 56669841755695046972514253)
      ·
        refine ⟨21251190658385642614692845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56669841755695046972514253 21251190658385642614692845)
        ·
          refine ⟨7969196496894615980509817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21251190658385642614692845 7969196496894615980509817)
          ·
            refine ⟨5976897372670961985382363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7969196496894615980509817 5976897372670961985382363)
            ·
              refine ⟨8965346059006442978073545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5976897372670961985382363 8965346059006442978073545)
              ·
                refine ⟨6724009544254832233555159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8965346059006442978073545 6724009544254832233555159)
                ·
                  refine ⟨10086014316382248350332739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6724009544254832233555159 10086014316382248350332739)
                  ·
                    refine ⟨15129021474573372525499109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10086014316382248350332739 15129021474573372525499109)
                    ·
                      refine ⟨2836691526482507348531083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15129021474573372525499109 2836691526482507348531083)
                      ·
                        rfl

theorem cell23_5524437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_5524437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524437 prefixEnd_5524437 := by exact prefixLift 5524437
  have htrace : WordTrace (prefixWord ++ tailWord_5524437) baseStart_5524437 baseEnd_5524437 := by
    simpa [prefixWord, tailWord_5524437, baseEnd_5524437] using wordTrace_append hprefix tailTrace_5524437
  have hstable : (prefixWord ++ tailWord_5524437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524437).length < 2 ^ (prefixWord ++ tailWord_5524437).sum := by decide
  have hdescent : baseEnd_5524437 < baseStart_5524437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524440 : List Nat := [2, 1, 2, 2, 2, 3, 3, 2, 1, 2, 3]
def baseStart_5524440 : Nat := 118140960795 + 5524440 * 2 ^ 59
def prefixEnd_5524440 : Nat := 4983230072969 + 3 ^ 40 * 5524440 * 2
def baseEnd_5524440 : Nat := 2836693066924470836793569

theorem tailTrace_5524440 : CollatzResearch.WordTrace tailWord_5524440 prefixEnd_5524440 2836693066924470836793569 := by
  unfold tailWord_5524440
  simp only [CollatzResearch.WordTrace]
  refine ⟨100746440052952427040649387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134328586737269902720865849 100746440052952427040649387)
  ·
    refine ⟨151119660079428640560974081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100746440052952427040649387 151119660079428640560974081)
    ·
      refine ⟨113339745059571480420730561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151119660079428640560974081 113339745059571480420730561)
      ·
        refine ⟨85004808794678610315547921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113339745059571480420730561 85004808794678610315547921)
        ·
          refine ⟨63753606596008957736660941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85004808794678610315547921 63753606596008957736660941)
          ·
            refine ⟨23907602473503359151247853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63753606596008957736660941 23907602473503359151247853)
            ·
              refine ⟨8965350927563759681717945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23907602473503359151247853 8965350927563759681717945)
              ·
                refine ⟨6724013195672819761288459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8965350927563759681717945 6724013195672819761288459)
                ·
                  refine ⟨10086019793509229641932689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6724013195672819761288459 10086019793509229641932689)
                  ·
                    refine ⟨7564514845131922231449517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10086019793509229641932689 7564514845131922231449517)
                    ·
                      refine ⟨2836693066924470836793569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7564514845131922231449517 2836693066924470836793569)
                      ·
                        rfl

theorem cell23_5524440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_5524440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524440 prefixEnd_5524440 := by exact prefixLift 5524440
  have htrace : WordTrace (prefixWord ++ tailWord_5524440) baseStart_5524440 baseEnd_5524440 := by
    simpa [prefixWord, tailWord_5524440, baseEnd_5524440] using wordTrace_append hprefix tailTrace_5524440
  have hstable : (prefixWord ++ tailWord_5524440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524440).length < 2 ^ (prefixWord ++ tailWord_5524440).sum := by decide
  have hdescent : baseEnd_5524440 < baseStart_5524440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524450 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_5524450 : Nat := 118140960795 + 5524450 * 2 ^ 59
def prefixEnd_5524450 : Nat := 4983230072969 + 3 ^ 40 * 5524450 * 2
def baseEnd_5524450 : Nat := 2836698201731015797668523

theorem tailTrace_5524450 : CollatzResearch.WordTrace tailWord_5524450 prefixEnd_5524450 2836698201731015797668523 := by
  unfold tailWord_5524450
  simp only [CollatzResearch.WordTrace]
  refine ⟨50373311208967156447290701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134328829890579083859441869 50373311208967156447290701)
  ·
    refine ⟨18889991703362683667734013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50373311208967156447290701 18889991703362683667734013)
    ·
      refine ⟨7083746888761006375400255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18889991703362683667734013 7083746888761006375400255)
      ·
        refine ⟨10625620333141509563100383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7083746888761006375400255 10625620333141509563100383)
        ·
          refine ⟨15938430499712264344650575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10625620333141509563100383 15938430499712264344650575)
          ·
            refine ⟨23907645749568396516975863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15938430499712264344650575 23907645749568396516975863)
            ·
              refine ⟨35861468624352594775463795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23907645749568396516975863 35861468624352594775463795)
              ·
                refine ⟨53792202936528892163195693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35861468624352594775463795 53792202936528892163195693)
                ·
                  refine ⟨20172076101198334561198385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53792202936528892163195693 20172076101198334561198385)
                  ·
                    refine ⟨15129057075898750920898789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20172076101198334561198385 15129057075898750920898789)
                    ·
                      refine ⟨2836698201731015797668523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15129057075898750920898789 2836698201731015797668523)
                      ·
                        rfl

theorem cell23_5524450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_5524450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524450 prefixEnd_5524450 := by exact prefixLift 5524450
  have htrace : WordTrace (prefixWord ++ tailWord_5524450) baseStart_5524450 baseEnd_5524450 := by
    simpa [prefixWord, tailWord_5524450, baseEnd_5524450] using wordTrace_append hprefix tailTrace_5524450
  have hstable : (prefixWord ++ tailWord_5524450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524450).length < 2 ^ (prefixWord ++ tailWord_5524450).sum := by decide
  have hdescent : baseEnd_5524450 < baseStart_5524450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524514 : List Nat := [3, 3, 1, 1, 1, 3, 4, 1, 1, 3, 2]
def baseStart_5524514 : Nat := 118140960795 + 5524514 * 2 ^ 59
def prefixEnd_5524514 : Nat := 4983230072969 + 3 ^ 40 * 5524514 * 2
def baseEnd_5524514 : Nat := 2836731064492903547268229

theorem tailTrace_5524514 : CollatzResearch.WordTrace tailWord_5524514 prefixEnd_5524514 2836731064492903547268229 := by
  unfold tailWord_5524514
  simp only [CollatzResearch.WordTrace]
  refine ⟨50373894776909191179873149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134330386071757843146328397 50373894776909191179873149)
  ·
    refine ⟨18890210541340946692452431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50373894776909191179873149 18890210541340946692452431)
    ·
      refine ⟨28335315812011420038678647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18890210541340946692452431 28335315812011420038678647)
      ·
        refine ⟨42502973718017130058017971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28335315812011420038678647 42502973718017130058017971)
        ·
          refine ⟨63754460577025695087026957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42502973718017130058017971 63754460577025695087026957)
          ·
            refine ⟨23907922716384635657635109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63754460577025695087026957 23907922716384635657635109)
            ·
              refine ⟨4482735509322119185806583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23907922716384635657635109 4482735509322119185806583)
              ·
                refine ⟨6724103263983178778709875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4482735509322119185806583 6724103263983178778709875)
                ·
                  refine ⟨10086154895974768168064813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6724103263983178778709875 10086154895974768168064813)
                  ·
                    refine ⟨3782308085990538063024305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10086154895974768168064813 3782308085990538063024305)
                    ·
                      refine ⟨2836731064492903547268229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3782308085990538063024305 2836731064492903547268229)
                      ·
                        rfl

theorem cell23_5524514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_5524514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524514 prefixEnd_5524514 := by exact prefixLift 5524514
  have htrace : WordTrace (prefixWord ++ tailWord_5524514) baseStart_5524514 baseEnd_5524514 := by
    simpa [prefixWord, tailWord_5524514, baseEnd_5524514] using wordTrace_append hprefix tailTrace_5524514
  have hstable : (prefixWord ++ tailWord_5524514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524514).length < 2 ^ (prefixWord ++ tailWord_5524514).sum := by decide
  have hdescent : baseEnd_5524514 < baseStart_5524514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524544 : List Nat := [2, 1, 1, 2, 2, 3, 5, 1, 2, 2, 2]
def baseStart_5524544 : Nat := 118140960795 + 5524544 * 2 ^ 59
def prefixEnd_5524544 : Nat := 4983230072969 + 3 ^ 40 * 5524544 * 2
def baseEnd_5524544 : Nat := 2836746468912538429893091

theorem tailTrace_5524544 : CollatzResearch.WordTrace tailWord_5524544 prefixEnd_5524544 2836746468912538429893091 := by
  unfold tailWord_5524544
  simp only [CollatzResearch.WordTrace]
  refine ⟨100748336648764039921542343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134331115531685386562056457 100748336648764039921542343)
  ·
    refine ⟨151122504973146059882313515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100748336648764039921542343 151122504973146059882313515)
    ·
      refine ⟨226683757459719089823470273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151122504973146059882313515 226683757459719089823470273)
      ·
        refine ⟨170012818094789317367602705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226683757459719089823470273 170012818094789317367602705)
        ·
          refine ⟨127509613571091988025702029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170012818094789317367602705 127509613571091988025702029)
          ·
            refine ⟨47816105089159495509638261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127509613571091988025702029 47816105089159495509638261)
            ·
              refine ⟨4482759852108702704028587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47816105089159495509638261 4482759852108702704028587)
              ·
                refine ⟨6724139778163054056042881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4482759852108702704028587 6724139778163054056042881)
                ·
                  refine ⟨5043104833622290542032161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6724139778163054056042881 5043104833622290542032161)
                  ·
                    refine ⟨3782328625216717906524121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5043104833622290542032161 3782328625216717906524121)
                    ·
                      refine ⟨2836746468912538429893091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3782328625216717906524121 2836746468912538429893091)
                      ·
                        rfl

theorem cell23_5524544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 2, 2, 2].length) (baseStart_5524544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524544 prefixEnd_5524544 := by exact prefixLift 5524544
  have htrace : WordTrace (prefixWord ++ tailWord_5524544) baseStart_5524544 baseEnd_5524544 := by
    simpa [prefixWord, tailWord_5524544, baseEnd_5524544] using wordTrace_append hprefix tailTrace_5524544
  have hstable : (prefixWord ++ tailWord_5524544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524544).length < 2 ^ (prefixWord ++ tailWord_5524544).sum := by decide
  have hdescent : baseEnd_5524544 < baseStart_5524544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524584 : List Nat := [2, 1, 4, 4, 2, 1, 1, 1, 7]
def baseStart_5524584 : Nat := 118140960795 + 5524584 * 2 ^ 59
def prefixEnd_5524584 : Nat := 4983230072969 + 3 ^ 40 * 5524584 * 2
def baseEnd_5524584 : Nat := 315196334237635363710323

theorem tailTrace_5524584 : CollatzResearch.WordTrace tailWord_5524584 prefixEnd_5524584 315196334237635363710323 := by
  unfold tailWord_5524584
  simp only [CollatzResearch.WordTrace]
  refine ⟨100749066108691583337270403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134332088144922111116360537 100749066108691583337270403)
  ·
    refine ⟨151123599163037375005905605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100749066108691583337270403 151123599163037375005905605)
    ·
      refine ⟨28335674843069507813607301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151123599163037375005905605 28335674843069507813607301)
      ·
        refine ⟨5312939033075532715051369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28335674843069507813607301 5312939033075532715051369)
        ·
          refine ⟨3984704274806649536288527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5312939033075532715051369 3984704274806649536288527)
          ·
            refine ⟨5977056412209974304432791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3984704274806649536288527 5977056412209974304432791)
            ·
              refine ⟨8965584618314961456649187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5977056412209974304432791 8965584618314961456649187)
              ·
                refine ⟨13448376927472442184973781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8965584618314961456649187 13448376927472442184973781)
                ·
                  refine ⟨315196334237635363710323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13448376927472442184973781 315196334237635363710323)
                  ·
                    rfl

theorem cell23_5524584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 7].length) (baseStart_5524584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524584 prefixEnd_5524584 := by exact prefixLift 5524584
  have htrace : WordTrace (prefixWord ++ tailWord_5524584) baseStart_5524584 baseEnd_5524584 := by
    simpa [prefixWord, tailWord_5524584, baseEnd_5524584] using wordTrace_append hprefix tailTrace_5524584
  have hstable : (prefixWord ++ tailWord_5524584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524584).length < 2 ^ (prefixWord ++ tailWord_5524584).sum := by decide
  have hdescent : baseEnd_5524584 < baseStart_5524584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524590 : List Nat := [4, 1, 2, 2, 1, 3, 1, 1, 1, 2, 5]
def baseStart_5524590 : Nat := 118140960795 + 5524590 * 2 ^ 59
def prefixEnd_5524590 : Nat := 4983230072969 + 3 ^ 40 * 5524590 * 2
def baseEnd_5524590 : Nat := 2836770089022645249917879

theorem tailTrace_5524590 : CollatzResearch.WordTrace tailWord_5524590 prefixEnd_5524590 2836770089022645249917879 := by
  unfold tailWord_5524590
  simp only [CollatzResearch.WordTrace]
  refine ⟨25187293881920178712407403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134332234036907619799506149 25187293881920178712407403)
  ·
    refine ⟨37780940822880268068611105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25187293881920178712407403 37780940822880268068611105)
    ·
      refine ⟨28335705617160201051458329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37780940822880268068611105 28335705617160201051458329)
      ·
        refine ⟨21251779212870150788593747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28335705617160201051458329 21251779212870150788593747)
        ·
          refine ⟨31877668819305226182890621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21251779212870150788593747 31877668819305226182890621)
          ·
            refine ⟨11954125807239459818583983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31877668819305226182890621 11954125807239459818583983)
            ·
              refine ⟨17931188710859189727875975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11954125807239459818583983 17931188710859189727875975)
              ·
                refine ⟨26896783066288784591813963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17931188710859189727875975 26896783066288784591813963)
                ·
                  refine ⟨40345174599433176887720945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26896783066288784591813963 40345174599433176887720945)
                  ·
                    refine ⟨30258880949574882665790709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40345174599433176887720945 30258880949574882665790709)
                    ·
                      refine ⟨2836770089022645249917879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30258880949574882665790709 2836770089022645249917879)
                      ·
                        rfl

theorem cell23_5524590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_5524590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524590 prefixEnd_5524590 := by exact prefixLift 5524590
  have htrace : WordTrace (prefixWord ++ tailWord_5524590) baseStart_5524590 baseEnd_5524590 := by
    simpa [prefixWord, tailWord_5524590, baseEnd_5524590] using wordTrace_append hprefix tailTrace_5524590
  have hstable : (prefixWord ++ tailWord_5524590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524590).length < 2 ^ (prefixWord ++ tailWord_5524590).sum := by decide
  have hdescent : baseEnd_5524590 < baseStart_5524590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524600 : List Nat := [2, 1, 2, 1, 1, 1, 4, 3, 2, 4, 2]
def baseStart_5524600 : Nat := 118140960795 + 5524600 * 2 ^ 59
def prefixEnd_5524600 : Nat := 4983230072969 + 3 ^ 40 * 5524600 * 2
def baseEnd_5524600 : Nat := 2836775223829190210792833

theorem tailTrace_5524600 : CollatzResearch.WordTrace tailWord_5524600 prefixEnd_5524600 2836775223829190210792833 := by
  unfold tailWord_5524600
  simp only [CollatzResearch.WordTrace]
  refine ⟨100749357892662600703561627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134332477190216800938082169 100749357892662600703561627)
  ·
    refine ⟨151124036838993901055342441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100749357892662600703561627 151124036838993901055342441)
    ·
      refine ⟨113343027629245425791506831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151124036838993901055342441 113343027629245425791506831)
      ·
        refine ⟨170014541443868138687260247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113343027629245425791506831 170014541443868138687260247)
        ·
          refine ⟨255021812165802208030890371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170014541443868138687260247 255021812165802208030890371)
          ·
            refine ⟨382532718248703312046335557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255021812165802208030890371 382532718248703312046335557)
            ·
              refine ⟨71724884671631871008687917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 382532718248703312046335557 71724884671631871008687917)
              ·
                refine ⟨26896831751861951628257969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71724884671631871008687917 26896831751861951628257969)
                ·
                  refine ⟨20172623813896463721193477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26896831751861951628257969 20172623813896463721193477)
                  ·
                    refine ⟨3782366965105586947723777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20172623813896463721193477 3782366965105586947723777)
                    ·
                      refine ⟨2836775223829190210792833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3782366965105586947723777 2836775223829190210792833)
                      ·
                        rfl

theorem cell23_5524600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 2, 4, 2].length) (baseStart_5524600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524600 prefixEnd_5524600 := by exact prefixLift 5524600
  have htrace : WordTrace (prefixWord ++ tailWord_5524600) baseStart_5524600 baseEnd_5524600 := by
    simpa [prefixWord, tailWord_5524600, baseEnd_5524600] using wordTrace_append hprefix tailTrace_5524600
  have hstable : (prefixWord ++ tailWord_5524600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524600).length < 2 ^ (prefixWord ++ tailWord_5524600).sum := by decide
  have hdescent : baseEnd_5524600 < baseStart_5524600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524603 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 3, 4, 3]
def baseStart_5524603 : Nat := 118140960795 + 5524603 * 2 ^ 59
def prefixEnd_5524603 : Nat := 4983230072969 + 3 ^ 40 * 5524603 * 2
def baseEnd_5524603 : Nat := 2836776764271153699055319

theorem tailTrace_5524603 : CollatzResearch.WordTrace tailWord_5524603 prefixEnd_5524603 2836776764271153699055319 := by
  unfold tailWord_5524603
  simp only [CollatzResearch.WordTrace]
  refine ⟨201498825204314332919482463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134332550136209555279654975 201498825204314332919482463)
  ·
    refine ⟨302248237806471499379223695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201498825204314332919482463 302248237806471499379223695)
    ·
      refine ⟨453372356709707249068835543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302248237806471499379223695 453372356709707249068835543)
      ·
        refine ⟨680058535064560873603253315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 453372356709707249068835543 680058535064560873603253315)
        ·
          refine ⟨1020087802596841310404879973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 680058535064560873603253315 1020087802596841310404879973)
          ·
            refine ⟨191266462986907745700914995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1020087802596841310404879973 191266462986907745700914995)
            ·
              refine ⟨286899694480361618551372493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191266462986907745700914995 286899694480361618551372493)
              ·
                refine ⟨107587385430135606956764685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 286899694480361618551372493 107587385430135606956764685)
                ·
                  refine ⟨40345269536300852608786757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 107587385430135606956764685 40345269536300852608786757)
                  ·
                    refine ⟨7564738038056409864147517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40345269536300852608786757 7564738038056409864147517)
                    ·
                      refine ⟨2836776764271153699055319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7564738038056409864147517 2836776764271153699055319)
                      ·
                        rfl

theorem cell23_5524603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 4, 3].length) (baseStart_5524603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524603 prefixEnd_5524603 := by exact prefixLift 5524603
  have htrace : WordTrace (prefixWord ++ tailWord_5524603) baseStart_5524603 baseEnd_5524603 := by
    simpa [prefixWord, tailWord_5524603, baseEnd_5524603] using wordTrace_append hprefix tailTrace_5524603
  have hstable : (prefixWord ++ tailWord_5524603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524603).length < 2 ^ (prefixWord ++ tailWord_5524603).sum := by decide
  have hdescent : baseEnd_5524603 < baseStart_5524603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524640 : List Nat := [2, 1, 1, 4, 2, 1, 4, 2, 6]
def baseStart_5524640 : Nat := 118140960795 + 5524640 * 2 ^ 59
def prefixEnd_5524640 : Nat := 4983230072969 + 3 ^ 40 * 5524640 * 2
def baseEnd_5524640 : Nat := 315199529228374450476961

theorem tailTrace_5524640 : CollatzResearch.WordTrace tailWord_5524640 prefixEnd_5524640 315199529228374450476961 := by
  unfold tailWord_5524640
  simp only [CollatzResearch.WordTrace]
  refine ⟨100750087352590144119289687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134333449803453525492386249 100750087352590144119289687)
  ·
    refine ⟨151125131028885216178934531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100750087352590144119289687 151125131028885216178934531)
    ·
      refine ⟨226687696543327824268401797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151125131028885216178934531 226687696543327824268401797)
      ·
        refine ⟨42503943101873967050325337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 226687696543327824268401797 42503943101873967050325337)
        ·
          refine ⟨31877957326405475287744003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42503943101873967050325337 31877957326405475287744003)
          ·
            refine ⟨47816935989608212931616005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31877957326405475287744003 47816935989608212931616005)
            ·
              refine ⟨8965675498051539924678001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47816935989608212931616005 8965675498051539924678001)
              ·
                refine ⟨6724256623538654943508501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8965675498051539924678001 6724256623538654943508501)
                ·
                  refine ⟨315199529228374450476961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6724256623538654943508501 315199529228374450476961)
                  ·
                    rfl

theorem cell23_5524640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 6].length) (baseStart_5524640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524640 prefixEnd_5524640 := by exact prefixLift 5524640
  have htrace : WordTrace (prefixWord ++ tailWord_5524640) baseStart_5524640 baseEnd_5524640 := by
    simpa [prefixWord, tailWord_5524640, baseEnd_5524640] using wordTrace_append hprefix tailTrace_5524640
  have hstable : (prefixWord ++ tailWord_5524640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524640).length < 2 ^ (prefixWord ++ tailWord_5524640).sum := by decide
  have hdescent : baseEnd_5524640 < baseStart_5524640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524644 : List Nat := [2, 3, 1, 2, 3, 2, 1, 4, 1, 4]
def baseStart_5524644 : Nat := 118140960795 + 5524644 * 2 ^ 59
def prefixEnd_5524644 : Nat := 4983230072969 + 3 ^ 40 * 5524644 * 2
def baseEnd_5524644 : Nat := 945599272325996012880877

theorem tailTrace_5524644 : CollatzResearch.WordTrace tailWord_5524644 prefixEnd_5524644 945599272325996012880877 := by
  unfold tailWord_5524644
  simp only [CollatzResearch.WordTrace]
  refine ⟨100750160298582898460862493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134333547064777197947816657 100750160298582898460862493)
  ·
    refine ⟨37781310111968586922823435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100750160298582898460862493 37781310111968586922823435)
    ·
      refine ⟨56671965167952880384235153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37781310111968586922823435 56671965167952880384235153)
      ·
        refine ⟨42503973875964660288176365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56671965167952880384235153 42503973875964660288176365)
        ·
          refine ⟨15938990203486747608066137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42503973875964660288176365 15938990203486747608066137)
          ·
            refine ⟨11954242652615060706049603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15938990203486747608066137 11954242652615060706049603)
            ·
              refine ⟨17931363978922591059074405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11954242652615060706049603 17931363978922591059074405)
              ·
                refine ⟨3362130746047985823576451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17931363978922591059074405 3362130746047985823576451)
                ·
                  refine ⟨5043196119071978735364677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3362130746047985823576451 5043196119071978735364677)
                  ·
                    refine ⟨945599272325996012880877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5043196119071978735364677 945599272325996012880877)
                    ·
                      rfl

theorem cell23_5524644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 4, 1, 4].length) (baseStart_5524644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524644 prefixEnd_5524644 := by exact prefixLift 5524644
  have htrace : WordTrace (prefixWord ++ tailWord_5524644) baseStart_5524644 baseEnd_5524644 := by
    simpa [prefixWord, tailWord_5524644, baseEnd_5524644] using wordTrace_append hprefix tailTrace_5524644
  have hstable : (prefixWord ++ tailWord_5524644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524644).length < 2 ^ (prefixWord ++ tailWord_5524644).sum := by decide
  have hdescent : baseEnd_5524644 < baseStart_5524644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524663 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 7]
def baseStart_5524663 : Nat := 118140960795 + 5524663 * 2 ^ 59
def prefixEnd_5524663 : Nat := 4983230072969 + 3 ^ 40 * 5524663 * 2
def baseEnd_5524663 : Nat := 2836807573110423464305043

theorem tailTrace_5524663 : CollatzResearch.WordTrace tailWord_5524663 prefixEnd_5524663 2836807573110423464305043 := by
  unfold tailWord_5524663
  simp only [CollatzResearch.WordTrace]
  refine ⟨201501013584096963166666643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134334009056064642111111095 201501013584096963166666643)
  ·
    refine ⟨302251520376145444749999965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201501013584096963166666643 302251520376145444749999965)
    ·
      refine ⟨113344320141054541781249987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302251520376145444749999965 113344320141054541781249987)
      ·
        refine ⟨170016480211581812671874981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113344320141054541781249987 170016480211581812671874981)
        ·
          refine ⟨31878090039671589875976559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 170016480211581812671874981 31878090039671589875976559)
          ·
            refine ⟨47817135059507384813964839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31878090039671589875976559 47817135059507384813964839)
            ·
              refine ⟨71725702589261077220947259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47817135059507384813964839 71725702589261077220947259)
              ·
                refine ⟨107588553883891615831420889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71725702589261077220947259 107588553883891615831420889)
                ·
                  refine ⟨80691415412918711873565667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107588553883891615831420889 80691415412918711873565667)
                  ·
                    refine ⟨121037123119378067810348501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80691415412918711873565667 121037123119378067810348501)
                    ·
                      refine ⟨2836807573110423464305043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 121037123119378067810348501 2836807573110423464305043)
                      ·
                        rfl

theorem cell23_5524663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_5524663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524663 prefixEnd_5524663 := by exact prefixLift 5524663
  have htrace : WordTrace (prefixWord ++ tailWord_5524663) baseStart_5524663 baseEnd_5524663 := by
    simpa [prefixWord, tailWord_5524663, baseEnd_5524663] using wordTrace_append hprefix tailTrace_5524663
  have hstable : (prefixWord ++ tailWord_5524663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524663).length < 2 ^ (prefixWord ++ tailWord_5524663).sum := by decide
  have hdescent : baseEnd_5524663 < baseStart_5524663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524683 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 3, 6]
def baseStart_5524683 : Nat := 118140960795 + 5524683 * 2 ^ 59
def prefixEnd_5524683 : Nat := 4983230072969 + 3 ^ 40 * 5524683 * 2
def baseEnd_5524683 : Nat := 945605947574504462018317

theorem tailTrace_5524683 : CollatzResearch.WordTrace tailWord_5524683 prefixEnd_5524683 945605947574504462018317 := by
  unfold tailWord_5524683
  simp only [CollatzResearch.WordTrace]
  refine ⟨201501743044024506582394703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134334495362683004388263135 201501743044024506582394703)
  ·
    refine ⟨302252614566036759873592055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201501743044024506582394703 302252614566036759873592055)
    ·
      refine ⟨453378921849055139810388083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302252614566036759873592055 453378921849055139810388083)
      ·
        refine ⟨680068382773582709715582125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 453378921849055139810388083 680068382773582709715582125)
        ·
          refine ⟨255025643540093516143343297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 680068382773582709715582125 255025643540093516143343297)
          ·
            refine ⟨191269232655070137107507473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255025643540093516143343297 191269232655070137107507473)
            ·
              refine ⟨143451924491302602830630605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191269232655070137107507473 143451924491302602830630605)
              ·
                refine ⟨53794471684238476061486477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143451924491302602830630605 53794471684238476061486477)
                ·
                  refine ⟨20172926881589428523057429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53794471684238476061486477 20172926881589428523057429)
                  ·
                    refine ⟨945605947574504462018317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20172926881589428523057429 945605947574504462018317)
                    ·
                      rfl

theorem cell23_5524683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 6].length) (baseStart_5524683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524683 prefixEnd_5524683 := by exact prefixLift 5524683
  have htrace : WordTrace (prefixWord ++ tailWord_5524683) baseStart_5524683 baseEnd_5524683 := by
    simpa [prefixWord, tailWord_5524683, baseEnd_5524683] using wordTrace_append hprefix tailTrace_5524683
  have hstable : (prefixWord ++ tailWord_5524683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524683).length < 2 ^ (prefixWord ++ tailWord_5524683).sum := by decide
  have hdescent : baseEnd_5524683 < baseStart_5524683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524701 : List Nat := [1, 4, 3, 2, 2, 1, 2, 1, 3, 1, 3]
def baseStart_5524701 : Nat := 118140960795 + 5524701 * 2 ^ 59
def prefixEnd_5524701 : Nat := 4983230072969 + 3 ^ 40 * 5524701 * 2
def baseEnd_5524701 : Nat := 2836827085375294315629869

theorem tailTrace_5524701 : CollatzResearch.WordTrace tailWord_5524701 prefixEnd_5524701 2836827085375294315629869 := by
  unfold tailWord_5524701
  simp only [CollatzResearch.WordTrace]
  refine ⟨201502399557959295656549957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134334933038639530437699971 201502399557959295656549957)
  ·
    refine ⟨37781699917117367935603117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201502399557959295656549957 37781699917117367935603117)
    ·
      refine ⟨14168137468919012975851169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37781699917117367935603117 14168137468919012975851169)
      ·
        refine ⟨10626103101689259731888377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14168137468919012975851169 10626103101689259731888377)
        ·
          refine ⟨7969577326266944798916283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10626103101689259731888377 7969577326266944798916283)
          ·
            refine ⟨11954365989400417198374425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7969577326266944798916283 11954365989400417198374425)
            ·
              refine ⟨8965774492050312898780819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11954365989400417198374425 8965774492050312898780819)
              ·
                refine ⟨13448661738075469348171229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8965774492050312898780819 13448661738075469348171229)
                ·
                  refine ⟨5043248151778301005564211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13448661738075469348171229 5043248151778301005564211)
                  ·
                    refine ⟨7564872227667451508346317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5043248151778301005564211 7564872227667451508346317)
                    ·
                      refine ⟨2836827085375294315629869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7564872227667451508346317 2836827085375294315629869)
                      ·
                        rfl

theorem cell23_5524701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_5524701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524701 prefixEnd_5524701 := by exact prefixLift 5524701
  have htrace : WordTrace (prefixWord ++ tailWord_5524701) baseStart_5524701 baseEnd_5524701 := by
    simpa [prefixWord, tailWord_5524701, baseEnd_5524701] using wordTrace_append hprefix tailTrace_5524701
  have hstable : (prefixWord ++ tailWord_5524701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524701).length < 2 ^ (prefixWord ++ tailWord_5524701).sum := by decide
  have hdescent : baseEnd_5524701 < baseStart_5524701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524717 : List Nat := [1, 5, 1, 2, 2, 1, 3, 1, 1, 6]
def baseStart_5524717 : Nat := 118140960795 + 5524717 * 2 ^ 59
def prefixEnd_5524717 : Nat := 4983230072969 + 3 ^ 40 * 5524717 * 2
def baseEnd_5524717 : Nat := 945611767021922084343265

theorem tailTrace_5524717 : CollatzResearch.WordTrace tailWord_5524717 prefixEnd_5524717 945611767021922084343265 := by
  unfold tailWord_5524717
  simp only [CollatzResearch.WordTrace]
  refine ⟨201502983125901330389132405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134335322083934220259421603 201502983125901330389132405)
  ·
    refine ⟨18890904668053249723981163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 201502983125901330389132405 18890904668053249723981163)
    ·
      refine ⟨28336357002079874585971745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18890904668053249723981163 28336357002079874585971745)
      ·
        refine ⟨21252267751559905939478809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28336357002079874585971745 21252267751559905939478809)
        ·
          refine ⟨15939200813669929454609107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21252267751559905939478809 15939200813669929454609107)
          ·
            refine ⟨23908801220504894181913661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15939200813669929454609107 23908801220504894181913661)
            ·
              refine ⟨8965800457689335318217623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23908801220504894181913661 8965800457689335318217623)
              ·
                refine ⟨13448700686534002977326435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8965800457689335318217623 13448700686534002977326435)
                ·
                  refine ⟨20173051029801004465989653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13448700686534002977326435 20173051029801004465989653)
                  ·
                    refine ⟨945611767021922084343265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20173051029801004465989653 945611767021922084343265)
                    ·
                      rfl

theorem cell23_5524717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_5524717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524717 prefixEnd_5524717 := by exact prefixLift 5524717
  have htrace : WordTrace (prefixWord ++ tailWord_5524717) baseStart_5524717 baseEnd_5524717 := by
    simpa [prefixWord, tailWord_5524717, baseEnd_5524717] using wordTrace_append hprefix tailTrace_5524717
  have hstable : (prefixWord ++ tailWord_5524717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524717).length < 2 ^ (prefixWord ++ tailWord_5524717).sum := by decide
  have hdescent : baseEnd_5524717 < baseStart_5524717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524768 : List Nat := [2, 1, 1, 5, 4, 1, 2, 1, 2, 4]
def baseStart_5524768 : Nat := 118140960795 + 5524768 * 2 ^ 59
def prefixEnd_5524768 : Nat := 4983230072969 + 3 ^ 40 * 5524768 * 2
def baseEnd_5524768 : Nat := 945620496193048517830687

theorem tailTrace_5524768 : CollatzResearch.WordTrace tailWord_5524768 prefixEnd_5524768 945620496193048517830687 := by
  unfold tailWord_5524768
  simp only [CollatzResearch.WordTrace]
  refine ⟨100752421624358283049619479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134336562165811044066159305 100752421624358283049619479)
  ·
    refine ⟨151128632436537424574429219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100752421624358283049619479 151128632436537424574429219)
    ·
      refine ⟨226692948654806136861643829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151128632436537424574429219 226692948654806136861643829)
      ·
        refine ⟨21252463936388075330779109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 226692948654806136861643829 21252463936388075330779109)
        ·
          refine ⟨3984836988072764124521083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21252463936388075330779109 3984836988072764124521083)
          ·
            refine ⟨5977255482109146186781625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3984836988072764124521083 5977255482109146186781625)
            ·
              refine ⟨4482941611581859640086219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5977255482109146186781625 4482941611581859640086219)
              ·
                refine ⟨6724412417372789460129329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4482941611581859640086219 6724412417372789460129329)
                ·
                  refine ⟨5043309313029592095096997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6724412417372789460129329 5043309313029592095096997)
                  ·
                    refine ⟨945620496193048517830687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5043309313029592095096997 945620496193048517830687)
                    ·
                      rfl

theorem cell23_5524768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 1, 2, 4].length) (baseStart_5524768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524768 prefixEnd_5524768 := by exact prefixLift 5524768
  have htrace : WordTrace (prefixWord ++ tailWord_5524768) baseStart_5524768 baseEnd_5524768 := by
    simpa [prefixWord, tailWord_5524768, baseEnd_5524768] using wordTrace_append hprefix tailTrace_5524768
  have hstable : (prefixWord ++ tailWord_5524768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524768).length < 2 ^ (prefixWord ++ tailWord_5524768).sum := by decide
  have hdescent : baseEnd_5524768 < baseStart_5524768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524800 : List Nat := [2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 5]
def baseStart_5524800 : Nat := 118140960795 + 5524800 * 2 ^ 59
def prefixEnd_5524800 : Nat := 4983230072969 + 3 ^ 40 * 5524800 * 2
def baseEnd_5524800 : Nat := 2836877919960089428291913

theorem tailTrace_5524800 : CollatzResearch.WordTrace tailWord_5524800 prefixEnd_5524800 2836877919960089428291913 := by
  unfold tailWord_5524800
  simp only [CollatzResearch.WordTrace]
  refine ⟨100753005192300317782201927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134337340256400423709602569 100753005192300317782201927)
  ·
    refine ⟨151129507788450476673302891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100753005192300317782201927 151129507788450476673302891)
    ·
      refine ⟨226694261682675715009954337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151129507788450476673302891 226694261682675715009954337)
      ·
        refine ⟨170020696262006786257465753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226694261682675715009954337 170020696262006786257465753)
        ·
          refine ⟨127515522196505089693099315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170020696262006786257465753 127515522196505089693099315)
          ·
            refine ⟨191273283294757634539648973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127515522196505089693099315 191273283294757634539648973)
            ·
              refine ⟨71727481235534112952368365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191273283294757634539648973 71727481235534112952368365)
              ·
                refine ⟨26897805463325292357138137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71727481235534112952368365 26897805463325292357138137)
                ·
                  refine ⟨20173354097493969267853603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26897805463325292357138137 20173354097493969267853603)
                  ·
                    refine ⟨30260031146240953901780405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20173354097493969267853603 30260031146240953901780405)
                    ·
                      refine ⟨2836877919960089428291913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30260031146240953901780405 2836877919960089428291913)
                      ·
                        rfl

theorem cell23_5524800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_5524800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524800 prefixEnd_5524800 := by exact prefixLift 5524800
  have htrace : WordTrace (prefixWord ++ tailWord_5524800) baseStart_5524800 baseEnd_5524800 := by
    simpa [prefixWord, tailWord_5524800, baseEnd_5524800] using wordTrace_append hprefix tailTrace_5524800
  have hstable : (prefixWord ++ tailWord_5524800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524800).length < 2 ^ (prefixWord ++ tailWord_5524800).sum := by decide
  have hdescent : baseEnd_5524800 < baseStart_5524800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524810 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 3, 4, 4]
def baseStart_5524810 : Nat := 118140960795 + 5524810 * 2 ^ 59
def prefixEnd_5524810 : Nat := 4983230072969 + 3 ^ 40 * 5524810 * 2
def baseEnd_5524810 : Nat := 2836883054766634389166867

theorem tailTrace_5524810 : CollatzResearch.WordTrace tailWord_5524810 prefixEnd_5524810 2836883054766634389166867 := by
  unfold tailWord_5524810
  simp only [CollatzResearch.WordTrace]
  refine ⟨50376593778641101818066971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134337583409709604848178589 50376593778641101818066971)
  ·
    refine ⟨75564890667961652727100457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50376593778641101818066971 75564890667961652727100457)
    ·
      refine ⟨56673668000971239545325343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75564890667961652727100457 56673668000971239545325343)
      ·
        refine ⟨85010502001456859317988015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56673668000971239545325343 85010502001456859317988015)
        ·
          refine ⟨127515753002185288976982023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85010502001456859317988015 127515753002185288976982023)
          ·
            refine ⟨191273629503277933465473035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127515753002185288976982023 191273629503277933465473035)
            ·
              refine ⟨286910444254916900198209553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191273629503277933465473035 286910444254916900198209553)
              ·
                refine ⟨215182833191187675148657165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 286910444254916900198209553 215182833191187675148657165)
                ·
                  refine ⟨80693562446695378180746437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 215182833191187675148657165 80693562446695378180746437)
                  ·
                    refine ⟨15130042958755383408889957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80693562446695378180746437 15130042958755383408889957)
                    ·
                      refine ⟨2836883054766634389166867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15130042958755383408889957 2836883054766634389166867)
                      ·
                        rfl

theorem cell23_5524810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_5524810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524810 prefixEnd_5524810 := by exact prefixLift 5524810
  have htrace : WordTrace (prefixWord ++ tailWord_5524810) baseStart_5524810 baseEnd_5524810 := by
    simpa [prefixWord, tailWord_5524810, baseEnd_5524810] using wordTrace_append hprefix tailTrace_5524810
  have hstable : (prefixWord ++ tailWord_5524810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524810).length < 2 ^ (prefixWord ++ tailWord_5524810).sum := by decide
  have hdescent : baseEnd_5524810 < baseStart_5524810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524865 : List Nat := [1, 2, 4, 3, 2, 2, 1, 2, 2, 2, 2]
def baseStart_5524865 : Nat := 118140960795 + 5524865 * 2 ^ 59
def prefixEnd_5524865 : Nat := 4983230072969 + 3 ^ 40 * 5524865 * 2
def baseEnd_5524865 : Nat := 2836911296202631673979115

theorem tailTrace_5524865 : CollatzResearch.WordTrace tailWord_5524865 prefixEnd_5524865 2836911296202631673979115 := by
  unfold tailWord_5524865
  simp only [CollatzResearch.WordTrace]
  refine ⟨201508381129365151665520049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134338920752910101110346699 201508381129365151665520049)
  ·
    refine ⟨151131285847023863749140037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201508381129365151665520049 151131285847023863749140037)
    ·
      refine ⟨28337116096316974452963757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151131285847023863749140037 28337116096316974452963757)
      ·
        refine ⟨10626418536118865419861409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28337116096316974452963757 10626418536118865419861409)
        ·
          refine ⟨7969813902089149064896057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10626418536118865419861409 7969813902089149064896057)
          ·
            refine ⟨5977360426566861798672043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7969813902089149064896057 5977360426566861798672043)
            ·
              refine ⟨8966040639850292698008065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5977360426566861798672043 8966040639850292698008065)
              ·
                refine ⟨6724530479887719523506049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8966040639850292698008065 6724530479887719523506049)
                ·
                  refine ⟨5043397859915789642629537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6724530479887719523506049 5043397859915789642629537)
                  ·
                    refine ⟨3782548394936842231972153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5043397859915789642629537 3782548394936842231972153)
                    ·
                      refine ⟨2836911296202631673979115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3782548394936842231972153 2836911296202631673979115)
                      ·
                        rfl

theorem cell23_5524865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_5524865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524865 prefixEnd_5524865 := by exact prefixLift 5524865
  have htrace : WordTrace (prefixWord ++ tailWord_5524865) baseStart_5524865 baseEnd_5524865 := by
    simpa [prefixWord, tailWord_5524865, baseEnd_5524865] using wordTrace_append hprefix tailTrace_5524865
  have hstable : (prefixWord ++ tailWord_5524865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524865).length < 2 ^ (prefixWord ++ tailWord_5524865).sum := by decide
  have hdescent : baseEnd_5524865 < baseStart_5524865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524882 : List Nat := [3, 2, 3, 3, 1, 1, 3, 1, 2, 2, 2]
def baseStart_5524882 : Nat := 118140960795 + 5524882 * 2 ^ 59
def prefixEnd_5524882 : Nat := 4983230072969 + 3 ^ 40 * 5524882 * 2
def baseEnd_5524882 : Nat := 2836920025373758107466537

theorem tailTrace_5524882 : CollatzResearch.WordTrace tailWord_5524882 prefixEnd_5524882 2836920025373758107466537 := by
  unfold tailWord_5524882
  simp only [CollatzResearch.WordTrace]
  refine ⟨50377250292575890892222225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134339334113535709045925933 50377250292575890892222225)
  ·
    refine ⟨37782937719431918169166669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50377250292575890892222225 37782937719431918169166669)
    ·
      refine ⟨14168601644786969313437501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37782937719431918169166669 14168601644786969313437501)
      ·
        refine ⟨5313225616795113492539063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14168601644786969313437501 5313225616795113492539063)
        ·
          refine ⟨7969838425192670238808595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5313225616795113492539063 7969838425192670238808595)
          ·
            refine ⟨11954757637789005358212893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7969838425192670238808595 11954757637789005358212893)
            ·
              refine ⟨4483034114170877009329835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11954757637789005358212893 4483034114170877009329835)
              ·
                refine ⟨6724551171256315513994753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4483034114170877009329835 6724551171256315513994753)
                ·
                  refine ⟨5043413378442236635496065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6724551171256315513994753 5043413378442236635496065)
                  ·
                    refine ⟨3782560033831677476622049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5043413378442236635496065 3782560033831677476622049)
                    ·
                      refine ⟨2836920025373758107466537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3782560033831677476622049 2836920025373758107466537)
                      ·
                        rfl

theorem cell23_5524882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_5524882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524882 prefixEnd_5524882 := by exact prefixLift 5524882
  have htrace : WordTrace (prefixWord ++ tailWord_5524882) baseStart_5524882 baseEnd_5524882 := by
    simpa [prefixWord, tailWord_5524882, baseEnd_5524882] using wordTrace_append hprefix tailTrace_5524882
  have hstable : (prefixWord ++ tailWord_5524882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524882).length < 2 ^ (prefixWord ++ tailWord_5524882).sum := by decide
  have hdescent : baseEnd_5524882 < baseStart_5524882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524964 : List Nat := [2, 3, 1, 1, 1, 1, 1, 5, 1, 5, 2]
def baseStart_5524964 : Nat := 118140960795 + 5524964 * 2 ^ 59
def prefixEnd_5524964 : Nat := 4983230072969 + 3 ^ 40 * 5524964 * 2
def baseEnd_5524964 : Nat := 2836962130787426786641159

theorem tailTrace_5524964 : CollatzResearch.WordTrace tailWord_5524964 prefixEnd_5524964 2836962130787426786641159 := by
  unfold tailWord_5524964
  simp only [CollatzResearch.WordTrace]
  refine ⟨100755995978003245786686973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134341327970670994382249297 100755995978003245786686973)
  ·
    refine ⟨37783498491751217170007615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100755995978003245786686973 37783498491751217170007615)
    ·
      refine ⟨56675247737626825755011423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37783498491751217170007615 56675247737626825755011423)
      ·
        refine ⟨85012871606440238632517135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56675247737626825755011423 85012871606440238632517135)
        ·
          refine ⟨127519307409660357948775703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85012871606440238632517135 127519307409660357948775703)
          ·
            refine ⟨191278961114490536923163555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127519307409660357948775703 191278961114490536923163555)
            ·
              refine ⟨286918441671735805384745333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191278961114490536923163555 286918441671735805384745333)
              ·
                refine ⟨26898603906725231754819875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 286918441671735805384745333 26898603906725231754819875)
                ·
                  refine ⟨40347905860087847632229813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26898603906725231754819875 40347905860087847632229813)
                  ·
                    refine ⟨3782616174383235715521545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40347905860087847632229813 3782616174383235715521545)
                    ·
                      refine ⟨2836962130787426786641159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3782616174383235715521545 2836962130787426786641159)
                      ·
                        rfl

theorem cell23_5524964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 1, 5, 2].length) (baseStart_5524964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524964 prefixEnd_5524964 := by exact prefixLift 5524964
  have htrace : WordTrace (prefixWord ++ tailWord_5524964) baseStart_5524964 baseEnd_5524964 := by
    simpa [prefixWord, tailWord_5524964, baseEnd_5524964] using wordTrace_append hprefix tailTrace_5524964
  have hstable : (prefixWord ++ tailWord_5524964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524964).length < 2 ^ (prefixWord ++ tailWord_5524964).sum := by decide
  have hdescent : baseEnd_5524964 < baseStart_5524964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5524997 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 3, 1, 5]
def baseStart_5524997 : Nat := 118140960795 + 5524997 * 2 ^ 59
def prefixEnd_5524997 : Nat := 4983230072969 + 3 ^ 40 * 5524997 * 2
def baseEnd_5524997 : Nat := 2836979075649025157528507

theorem tailTrace_5524997 : CollatzResearch.WordTrace tailWord_5524997 prefixEnd_5524997 2836979075649025157528507 := by
  unfold tailWord_5524997
  simp only [CollatzResearch.WordTrace]
  refine ⟨201513195564886938209325245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134342130376591292139550163 201513195564886938209325245)
  ·
    refine ⟨75567448336832601828496967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201513195564886938209325245 75567448336832601828496967)
    ·
      refine ⟨113351172505248902742745451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75567448336832601828496967 113351172505248902742745451)
      ·
        refine ⟨170026758757873354114118177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113351172505248902742745451 170026758757873354114118177)
        ·
          refine ⟨127520069068405015585588633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170026758757873354114118177 127520069068405015585588633)
          ·
            refine ⟨95640051801303761689191475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127520069068405015585588633 95640051801303761689191475)
            ·
              refine ⟨143460077701955642533787213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95640051801303761689191475 143460077701955642533787213)
              ·
                refine ⟨53797529138233365950170205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143460077701955642533787213 53797529138233365950170205)
                ·
                  refine ⟨20174073426837512231313827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53797529138233365950170205 20174073426837512231313827)
                  ·
                    refine ⟨30261110140256268346970741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20174073426837512231313827 30261110140256268346970741)
                    ·
                      refine ⟨2836979075649025157528507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30261110140256268346970741 2836979075649025157528507)
                      ·
                        rfl

theorem cell23_5524997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_5524997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5524997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5524997 prefixEnd_5524997 := by exact prefixLift 5524997
  have htrace : WordTrace (prefixWord ++ tailWord_5524997) baseStart_5524997 baseEnd_5524997 := by
    simpa [prefixWord, tailWord_5524997, baseEnd_5524997] using wordTrace_append hprefix tailTrace_5524997
  have hstable : (prefixWord ++ tailWord_5524997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5524997).length < 2 ^ (prefixWord ++ tailWord_5524997).sum := by decide
  have hdescent : baseEnd_5524997 < baseStart_5524997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5524997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525011 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 5, 2, 2]
def baseStart_5525011 : Nat := 118140960795 + 5525011 * 2 ^ 59
def prefixEnd_5525011 : Nat := 4983230072969 + 3 ^ 40 * 5525011 * 2
def baseEnd_5525011 : Nat := 2836986264378188102753443

theorem tailTrace_5525011 : CollatzResearch.WordTrace tailWord_5525011 prefixEnd_5525011 2836986264378188102753443 := by
  unfold tailWord_5525011
  simp only [CollatzResearch.WordTrace]
  refine ⟨201513706186836218600334887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134342470791224145733556591 201513706186836218600334887)
  ·
    refine ⟨302270559280254327900502331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201513706186836218600334887 302270559280254327900502331)
    ·
      refine ⟨453405838920381491850753497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302270559280254327900502331 453405838920381491850753497)
      ·
        refine ⟨340054379190286118888065123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 453405838920381491850753497 340054379190286118888065123)
        ·
          refine ⟨510081568785429178332097685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340054379190286118888065123 510081568785429178332097685)
          ·
            refine ⟨23910073536816992734317079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 510081568785429178332097685 23910073536816992734317079)
            ·
              refine ⟨35865110305225489101475619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23910073536816992734317079 35865110305225489101475619)
              ·
                refine ⟨53797665457838233652213429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35865110305225489101475619 53797665457838233652213429)
                ·
                  refine ⟨5043531136672334404895009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53797665457838233652213429 5043531136672334404895009)
                  ·
                    refine ⟨3782648352504250803671257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5043531136672334404895009 3782648352504250803671257)
                    ·
                      refine ⟨2836986264378188102753443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3782648352504250803671257 2836986264378188102753443)
                      ·
                        rfl

theorem cell23_5525011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 5, 2, 2].length) (baseStart_5525011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525011 prefixEnd_5525011 := by exact prefixLift 5525011
  have htrace : WordTrace (prefixWord ++ tailWord_5525011) baseStart_5525011 baseEnd_5525011 := by
    simpa [prefixWord, tailWord_5525011, baseEnd_5525011] using wordTrace_append hprefix tailTrace_5525011
  have hstable : (prefixWord ++ tailWord_5525011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525011).length < 2 ^ (prefixWord ++ tailWord_5525011).sum := by decide
  have hdescent : baseEnd_5525011 < baseStart_5525011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525038 : List Nat := [4, 1, 3, 1, 2, 1, 3, 2, 2, 4]
def baseStart_5525038 : Nat := 118140960795 + 5525038 * 2 ^ 59
def prefixEnd_5525038 : Nat := 4983230072969 + 3 ^ 40 * 5525038 * 2
def baseEnd_5525038 : Nat := 945666709451953165705273

theorem tailTrace_5525038 : CollatzResearch.WordTrace tailWord_5525038 prefixEnd_5525038 945666709451953165705273 := by
  unfold tailWord_5525038
  simp only [CollatzResearch.WordTrace]
  refine ⟨25189336369717300276445971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134343127305158934807711845 25189336369717300276445971)
  ·
    refine ⟨37784004554575950414668957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25189336369717300276445971 37784004554575950414668957)
    ·
      refine ⟨14169001707965981405500859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37784004554575950414668957 14169001707965981405500859)
      ·
        refine ⟨21253502561948972108251289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14169001707965981405500859 21253502561948972108251289)
        ·
          refine ⟨15940126921461729081188467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21253502561948972108251289 15940126921461729081188467)
          ·
            refine ⟨23910190382192593621782701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15940126921461729081188467 23910190382192593621782701)
            ·
              refine ⟨8966321393322222608168513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23910190382192593621782701 8966321393322222608168513)
              ·
                refine ⟨6724741044991666956126385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8966321393322222608168513 6724741044991666956126385)
                ·
                  refine ⟨5043555783743750217094789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6724741044991666956126385 5043555783743750217094789)
                  ·
                    refine ⟨945666709451953165705273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5043555783743750217094789 945666709451953165705273)
                    ·
                      rfl

theorem cell23_5525038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_5525038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525038 prefixEnd_5525038 := by exact prefixLift 5525038
  have htrace : WordTrace (prefixWord ++ tailWord_5525038) baseStart_5525038 baseEnd_5525038 := by
    simpa [prefixWord, tailWord_5525038, baseEnd_5525038] using wordTrace_append hprefix tailTrace_5525038
  have hstable : (prefixWord ++ tailWord_5525038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525038).length < 2 ^ (prefixWord ++ tailWord_5525038).sum := by decide
  have hdescent : baseEnd_5525038 < baseStart_5525038 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525045 : List Nat := [1, 3, 3, 1, 1, 3, 2, 4, 1, 2, 2]
def baseStart_5525045 : Nat := 118140960795 + 5525045 * 2 ^ 59
def prefixEnd_5525045 : Nat := 4983230072969 + 3 ^ 40 * 5525045 * 2
def baseEnd_5525045 : Nat := 2837003722720440969728287

theorem tailTrace_5525045 : CollatzResearch.WordTrace tailWord_5525045 prefixEnd_5525045 2837003722720440969728287 := by
  unfold tailWord_5525045
  simp only [CollatzResearch.WordTrace]
  refine ⟨201514946268713042407072589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134343297512475361604715059 201514946268713042407072589)
  ·
    refine ⟨75568104850767390902652221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201514946268713042407072589 75568104850767390902652221)
    ·
      refine ⟨28338039319037771588494583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75568104850767390902652221 28338039319037771588494583)
      ·
        refine ⟨42507058978556657382741875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28338039319037771588494583 42507058978556657382741875)
        ·
          refine ⟨63760588467834986074112813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42507058978556657382741875 63760588467834986074112813)
          ·
            refine ⟨23910220675438119777792305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63760588467834986074112813 23910220675438119777792305)
            ·
              refine ⟨17932665506578589833344229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23910220675438119777792305 17932665506578589833344229)
              ·
                refine ⟨3362374782483485593752043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17932665506578589833344229 3362374782483485593752043)
                ·
                  refine ⟨5043562173725228390628065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3362374782483485593752043 5043562173725228390628065)
                  ·
                    refine ⟨3782671630293921292971049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5043562173725228390628065 3782671630293921292971049)
                    ·
                      refine ⟨2837003722720440969728287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3782671630293921292971049 2837003722720440969728287)
                      ·
                        rfl

theorem cell23_5525045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_5525045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525045 prefixEnd_5525045 := by exact prefixLift 5525045
  have htrace : WordTrace (prefixWord ++ tailWord_5525045) baseStart_5525045 baseEnd_5525045 := by
    simpa [prefixWord, tailWord_5525045, baseEnd_5525045] using wordTrace_append hprefix tailTrace_5525045
  have hstable : (prefixWord ++ tailWord_5525045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525045).length < 2 ^ (prefixWord ++ tailWord_5525045).sum := by decide
  have hdescent : baseEnd_5525045 < baseStart_5525045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525074 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 2, 2, 5]
def baseStart_5525074 : Nat := 118140960795 + 5525074 * 2 ^ 59
def prefixEnd_5525074 : Nat := 4983230072969 + 3 ^ 40 * 5525074 * 2
def baseEnd_5525074 : Nat := 2837018613659421356265653

theorem tailTrace_5525074 : CollatzResearch.WordTrace tailWord_5525074 prefixEnd_5525074 2837018613659421356265653 := by
  unfold tailWord_5525074
  simp only [CollatzResearch.WordTrace]
  refine ⟨50379000996401995089969569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134344002657071986906585517 50379000996401995089969569)
  ·
    refine ⟨37784250747301496317477177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50379000996401995089969569 37784250747301496317477177)
    ·
      refine ⟨28338188060476122238107883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37784250747301496317477177 28338188060476122238107883)
      ·
        refine ⟨42507282090714183357161825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28338188060476122238107883 42507282090714183357161825)
        ·
          refine ⟨31880461568035637517871369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42507282090714183357161825 31880461568035637517871369)
          ·
            refine ⟨23910346176026728138403527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31880461568035637517871369 23910346176026728138403527)
            ·
              refine ⟨35865519264040092207605291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23910346176026728138403527 35865519264040092207605291)
              ·
                refine ⟨53798278896060138311407937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35865519264040092207605291 53798278896060138311407937)
                ·
                  refine ⟨40348709172045103733555953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53798278896060138311407937 40348709172045103733555953)
                  ·
                    refine ⟨30261531879033827800166965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40348709172045103733555953 30261531879033827800166965)
                    ·
                      refine ⟨2837018613659421356265653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30261531879033827800166965 2837018613659421356265653)
                      ·
                        rfl

theorem cell23_5525074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_5525074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525074 prefixEnd_5525074 := by exact prefixLift 5525074
  have htrace : WordTrace (prefixWord ++ tailWord_5525074) baseStart_5525074 baseEnd_5525074 := by
    simpa [prefixWord, tailWord_5525074, baseEnd_5525074] using wordTrace_append hprefix tailTrace_5525074
  have hstable : (prefixWord ++ tailWord_5525074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525074).length < 2 ^ (prefixWord ++ tailWord_5525074).sum := by decide
  have hdescent : baseEnd_5525074 < baseStart_5525074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525191 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 1, 6, 2]
def baseStart_5525191 : Nat := 118140960795 + 5525191 * 2 ^ 59
def prefixEnd_5525191 : Nat := 4983230072969 + 3 ^ 40 * 5525191 * 2
def baseEnd_5525191 : Nat := 2837078690895997398502615

theorem tailTrace_5525191 : CollatzResearch.WordTrace tailWord_5525191 prefixEnd_5525191 2837078690895997398502615 := by
  unfold tailWord_5525191
  simp only [CollatzResearch.WordTrace]
  refine ⟨201520271326184109341887427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134346847550789406227924951 201520271326184109341887427)
  ·
    refine ⟨302280406989276164012831141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201520271326184109341887427 302280406989276164012831141)
    ·
      refine ⟨56677576310489280752405839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 302280406989276164012831141 56677576310489280752405839)
      ·
        refine ⟨85016364465733921128608759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56677576310489280752405839 85016364465733921128608759)
        ·
          refine ⟨127524546698600881692913139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85016364465733921128608759 127524546698600881692913139)
          ·
            refine ⟨191286820047901322539369709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127524546698600881692913139 191286820047901322539369709)
            ·
              refine ⟨71732557517962995952263641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191286820047901322539369709 71732557517962995952263641)
              ·
                refine ⟨53799418138472246964197731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71732557517962995952263641 53799418138472246964197731)
                ·
                  refine ⟨80699127207708370446296597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53799418138472246964197731 80699127207708370446296597)
                  ·
                    refine ⟨3782771587861329864670153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 80699127207708370446296597 3782771587861329864670153)
                    ·
                      refine ⟨2837078690895997398502615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3782771587861329864670153 2837078690895997398502615)
                      ·
                        rfl

theorem cell23_5525191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 6, 2].length) (baseStart_5525191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525191 prefixEnd_5525191 := by exact prefixLift 5525191
  have htrace : WordTrace (prefixWord ++ tailWord_5525191) baseStart_5525191 baseEnd_5525191 := by
    simpa [prefixWord, tailWord_5525191, baseEnd_5525191] using wordTrace_append hprefix tailTrace_5525191
  have hstable : (prefixWord ++ tailWord_5525191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525191).length < 2 ^ (prefixWord ++ tailWord_5525191).sum := by decide
  have hdescent : baseEnd_5525191 < baseStart_5525191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525252 : List Nat := [2, 3, 2, 2, 1, 4, 1, 3, 1, 4]
def baseStart_5525252 : Nat := 118140960795 + 5525252 * 2 ^ 59
def prefixEnd_5525252 : Nat := 4983230072969 + 3 ^ 40 * 5525252 * 2
def baseEnd_5525252 : Nat := 945703337738640553279945

theorem tailTrace_5525252 : CollatzResearch.WordTrace tailWord_5525252 prefixEnd_5525252 945703337738640553279945 := by
  unfold tailWord_5525252
  simp only [CollatzResearch.WordTrace]
  refine ⟨100761248089481558379929005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134348330785975411173238673 100761248089481558379929005)
  ·
    refine ⟨37785468033555584392473377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100761248089481558379929005 37785468033555584392473377)
    ·
      refine ⟨28339101025166688294355033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37785468033555584392473377 28339101025166688294355033)
      ·
        refine ⟨21254325768875016220766275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28339101025166688294355033 21254325768875016220766275)
        ·
          refine ⟨31881488653312524331149413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21254325768875016220766275 31881488653312524331149413)
          ·
            refine ⟨5977779122496098312090515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31881488653312524331149413 5977779122496098312090515)
            ·
              refine ⟨8966668683744147468135773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5977779122496098312090515 8966668683744147468135773)
              ·
                refine ⟨3362500756404055300550915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8966668683744147468135773 3362500756404055300550915)
                ·
                  refine ⟨5043751134606082950826373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3362500756404055300550915 5043751134606082950826373)
                  ·
                    refine ⟨945703337738640553279945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5043751134606082950826373 945703337738640553279945)
                    ·
                      rfl

theorem cell23_5525252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_5525252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525252 prefixEnd_5525252 := by exact prefixLift 5525252
  have htrace : WordTrace (prefixWord ++ tailWord_5525252) baseStart_5525252 baseEnd_5525252 := by
    simpa [prefixWord, tailWord_5525252, baseEnd_5525252] using wordTrace_append hprefix tailTrace_5525252
  have hstable : (prefixWord ++ tailWord_5525252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525252).length < 2 ^ (prefixWord ++ tailWord_5525252).sum := by decide
  have hdescent : baseEnd_5525252 < baseStart_5525252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525298 : List Nat := [3, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4]
def baseStart_5525298 : Nat := 118140960795 + 5525298 * 2 ^ 59
def prefixEnd_5525298 : Nat := 4983230072969 + 3 ^ 40 * 5525298 * 2
def baseEnd_5525298 : Nat := 2837133633326028479864623

theorem tailTrace_5525298 : CollatzResearch.WordTrace tailWord_5525298 prefixEnd_5525298 2837133633326028479864623 := by
  unfold tailWord_5525298
  simp only [CollatzResearch.WordTrace]
  refine ⟨50381043484199116654008137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134349449291197644410688365 50381043484199116654008137)
  ·
    refine ⟨37785782613149337490506103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50381043484199116654008137 37785782613149337490506103)
    ·
      refine ⟨56678673919724006235759155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37785782613149337490506103 56678673919724006235759155)
      ·
        refine ⟨85018010879586009353638733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56678673919724006235759155 85018010879586009353638733)
        ·
          refine ⟨31881754079844753507614525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85018010879586009353638733 31881754079844753507614525)
          ·
            refine ⟨11955657779941782565355447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31881754079844753507614525 11955657779941782565355447)
            ·
              refine ⟨17933486669912673848033171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11955657779941782565355447 17933486669912673848033171)
              ·
                refine ⟨26900230004869010772049757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17933486669912673848033171 26900230004869010772049757)
                ·
                  refine ⟨10087586251825879039518659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26900230004869010772049757 10087586251825879039518659)
                  ·
                    refine ⟨15131379377738818559277989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10087586251825879039518659 15131379377738818559277989)
                    ·
                      refine ⟨2837133633326028479864623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15131379377738818559277989 2837133633326028479864623)
                      ·
                        rfl

theorem cell23_5525298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_5525298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525298 prefixEnd_5525298 := by exact prefixLift 5525298
  have htrace : WordTrace (prefixWord ++ tailWord_5525298) baseStart_5525298 baseEnd_5525298 := by
    simpa [prefixWord, tailWord_5525298, baseEnd_5525298] using wordTrace_append hprefix tailTrace_5525298
  have hstable : (prefixWord ++ tailWord_5525298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525298).length < 2 ^ (prefixWord ++ tailWord_5525298).sum := by decide
  have hdescent : baseEnd_5525298 < baseStart_5525298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525302 : List Nat := [5, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2]
def baseStart_5525302 : Nat := 118140960795 + 5525302 * 2 ^ 59
def prefixEnd_5525302 : Nat := 4983230072969 + 3 ^ 40 * 5525302 * 2
def baseEnd_5525302 : Nat := 2837135687248646464214605

theorem tailTrace_5525302 : CollatzResearch.WordTrace tailWord_5525302 prefixEnd_5525302 2837135687248646464214605 := by
  unfold tailWord_5525302
  simp only [CollatzResearch.WordTrace]
  refine ⟨12595269989298873456198635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134349546552521316866118773 12595269989298873456198635)
  ·
    refine ⟨18892904983948310184297953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12595269989298873456198635 18892904983948310184297953)
    ·
      refine ⟨14169678737961232638223465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18892904983948310184297953 14169678737961232638223465)
      ·
        refine ⟨10627259053470924478667599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14169678737961232638223465 10627259053470924478667599)
        ·
          refine ⟨15940888580206386718001399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10627259053470924478667599 15940888580206386718001399)
          ·
            refine ⟨23911332870309580077002099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15940888580206386718001399 23911332870309580077002099)
            ·
              refine ⟨35866999305464370115503149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23911332870309580077002099 35866999305464370115503149)
              ·
                refine ⟨13450124739549138793313681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35866999305464370115503149 13450124739549138793313681)
                ·
                  refine ⟨10087593554661854094985261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13450124739549138793313681 10087593554661854094985261)
                  ·
                    refine ⟨3782847582998195285619473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10087593554661854094985261 3782847582998195285619473)
                    ·
                      refine ⟨2837135687248646464214605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3782847582998195285619473 2837135687248646464214605)
                      ·
                        rfl

theorem cell23_5525302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_5525302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525302 prefixEnd_5525302 := by exact prefixLift 5525302
  have htrace : WordTrace (prefixWord ++ tailWord_5525302) baseStart_5525302 baseEnd_5525302 := by
    simpa [prefixWord, tailWord_5525302, baseEnd_5525302] using wordTrace_append hprefix tailTrace_5525302
  have hstable : (prefixWord ++ tailWord_5525302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525302).length < 2 ^ (prefixWord ++ tailWord_5525302).sum := by decide
  have hdescent : baseEnd_5525302 < baseStart_5525302 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525315 : List Nat := [1, 1, 1, 3, 1, 6, 3, 1, 1, 1, 4]
def baseStart_5525315 : Nat := 118140960795 + 5525315 * 2 ^ 59
def prefixEnd_5525315 : Nat := 4983230072969 + 3 ^ 40 * 5525315 * 2
def baseEnd_5525315 : Nat := 2837142362497154913352045

theorem tailTrace_5525315 : CollatzResearch.WordTrace tailWord_5525315 prefixEnd_5525315 2837142362497154913352045 := by
  unfold tailWord_5525315
  simp only [CollatzResearch.WordTrace]
  refine ⟨201524793977734878519401399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134349862651823252346267599 201524793977734878519401399)
  ·
    refine ⟨302287190966602317779102099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201524793977734878519401399 302287190966602317779102099)
    ·
      refine ⟨453430786449903476668653149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302287190966602317779102099 453430786449903476668653149)
      ·
        refine ⟨170036544918713803750744931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 453430786449903476668653149 170036544918713803750744931)
        ·
          refine ⟨255054817378070705626117397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170036544918713803750744931 255054817378070705626117397)
          ·
            refine ⟨11955694564597064326224253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 255054817378070705626117397 11955694564597064326224253)
            ·
              refine ⟨4483385461723899122334095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11955694564597064326224253 4483385461723899122334095)
              ·
                refine ⟨6725078192585848683501143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4483385461723899122334095 6725078192585848683501143)
                ·
                  refine ⟨10087617288878773025251715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6725078192585848683501143 10087617288878773025251715)
                  ·
                    refine ⟨15131425933318159537877573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10087617288878773025251715 15131425933318159537877573)
                    ·
                      refine ⟨2837142362497154913352045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15131425933318159537877573 2837142362497154913352045)
                      ·
                        rfl

theorem cell23_5525315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 1, 1, 4].length) (baseStart_5525315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525315 prefixEnd_5525315 := by exact prefixLift 5525315
  have htrace : WordTrace (prefixWord ++ tailWord_5525315) baseStart_5525315 baseEnd_5525315 := by
    simpa [prefixWord, tailWord_5525315, baseEnd_5525315] using wordTrace_append hprefix tailTrace_5525315
  have hstable : (prefixWord ++ tailWord_5525315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525315).length < 2 ^ (prefixWord ++ tailWord_5525315).sum := by decide
  have hdescent : baseEnd_5525315 < baseStart_5525315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525351 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 2, 7]
def baseStart_5525351 : Nat := 118140960795 + 5525351 * 2 ^ 59
def prefixEnd_5525351 : Nat := 4983230072969 + 3 ^ 40 * 5525351 * 2
def baseEnd_5525351 : Nat := 945720282600238924167293

theorem tailTrace_5525351 : CollatzResearch.WordTrace tailWord_5525351 prefixEnd_5525351 945720282600238924167293 := by
  unfold tailWord_5525351
  simp only [CollatzResearch.WordTrace]
  refine ⟨201526107005604456667711907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134350738003736304445141271 201526107005604456667711907)
  ·
    refine ⟨302289160508406685001567861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201526107005604456667711907 302289160508406685001567861)
    ·
      refine ⟨28339608797663126718896987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 302289160508406685001567861 28339608797663126718896987)
      ·
        refine ⟨42509413196494690078345481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28339608797663126718896987 42509413196494690078345481)
        ·
          refine ⟨31882059897371017558759111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42509413196494690078345481 31882059897371017558759111)
          ·
            refine ⟨47823089846056526338138667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31882059897371017558759111 47823089846056526338138667)
            ·
              refine ⟨71734634769084789507208001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47823089846056526338138667 71734634769084789507208001)
              ·
                refine ⟨53800976076813592130406001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71734634769084789507208001 53800976076813592130406001)
                ·
                  refine ⟨40350732057610194097804501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53800976076813592130406001 40350732057610194097804501)
                  ·
                    refine ⟨945720282600238924167293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40350732057610194097804501 945720282600238924167293)
                    ·
                      rfl

theorem cell23_5525351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_5525351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525351 prefixEnd_5525351 := by exact prefixLift 5525351
  have htrace : WordTrace (prefixWord ++ tailWord_5525351) baseStart_5525351 baseEnd_5525351 := by
    simpa [prefixWord, tailWord_5525351, baseEnd_5525351] using wordTrace_append hprefix tailTrace_5525351
  have hstable : (prefixWord ++ tailWord_5525351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525351).length < 2 ^ (prefixWord ++ tailWord_5525351).sum := by decide
  have hdescent : baseEnd_5525351 < baseStart_5525351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525361 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 2, 2, 5]
def baseStart_5525361 : Nat := 118140960795 + 5525361 * 2 ^ 59
def prefixEnd_5525361 : Nat := 4983230072969 + 3 ^ 40 * 5525361 * 2
def baseEnd_5525361 : Nat := 2837165982607261733376833

theorem tailTrace_5525361 : CollatzResearch.WordTrace tailWord_5525361 prefixEnd_5525361 2837165982607261733376833 := by
  unfold tailWord_5525361
  simp only [CollatzResearch.WordTrace]
  refine ⟨201526471735568228375575937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134350981157045485583717291 201526471735568228375575937)
  ·
    refine ⟨151144853801676171281681953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201526471735568228375575937 151144853801676171281681953)
    ·
      refine ⟨113358640351257128461261465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151144853801676171281681953 113358640351257128461261465)
      ·
        refine ⟨85018980263442846345946099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113358640351257128461261465 85018980263442846345946099)
        ·
          refine ⟨127528470395164269518919149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85018980263442846345946099 127528470395164269518919149)
          ·
            refine ⟨47823176398186601069594681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127528470395164269518919149 47823176398186601069594681)
            ·
              refine ⟨35867382298639950802196011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47823176398186601069594681 35867382298639950802196011)
              ·
                refine ⟨53801073447959926203294017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35867382298639950802196011 53801073447959926203294017)
                ·
                  refine ⟨40350805085969944652470513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53801073447959926203294017 40350805085969944652470513)
                  ·
                    refine ⟨30263103814477458489352885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40350805085969944652470513 30263103814477458489352885)
                    ·
                      refine ⟨2837165982607261733376833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30263103814477458489352885 2837165982607261733376833)
                      ·
                        rfl

theorem cell23_5525361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_5525361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525361 prefixEnd_5525361 := by exact prefixLift 5525361
  have htrace : WordTrace (prefixWord ++ tailWord_5525361) baseStart_5525361 baseEnd_5525361 := by
    simpa [prefixWord, tailWord_5525361, baseEnd_5525361] using wordTrace_append hprefix tailTrace_5525361
  have hstable : (prefixWord ++ tailWord_5525361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525361).length < 2 ^ (prefixWord ++ tailWord_5525361).sum := by decide
  have hdescent : baseEnd_5525361 < baseStart_5525361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525365 : List Nat := [1, 3, 4, 1, 1, 1, 2, 2, 4, 1, 3]
def baseStart_5525365 : Nat := 118140960795 + 5525365 * 2 ^ 59
def prefixEnd_5525365 : Nat := 4983230072969 + 3 ^ 40 * 5525365 * 2
def baseEnd_5525365 : Nat := 2837168036529879717726815

theorem tailTrace_5525365 : CollatzResearch.WordTrace tailWord_5525365 prefixEnd_5525365 2837168036529879717726815 := by
  unfold tailWord_5525365
  simp only [CollatzResearch.WordTrace]
  refine ⟨201526617627553737058721549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134351078418369158039147699 201526617627553737058721549)
  ·
    refine ⟨75572481610332651397020581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201526617627553737058721549 75572481610332651397020581)
    ·
      refine ⟨14169840301937372136941359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75572481610332651397020581 14169840301937372136941359)
      ·
        refine ⟨21254760452906058205412039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14169840301937372136941359 21254760452906058205412039)
        ·
          refine ⟨31882140679359087308118059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21254760452906058205412039 31882140679359087308118059)
          ·
            refine ⟨47823211019038630962177089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31882140679359087308118059 47823211019038630962177089)
            ·
              refine ⟨35867408264278973221632817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47823211019038630962177089 35867408264278973221632817)
              ·
                refine ⟨26900556198209229916224613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35867408264278973221632817 26900556198209229916224613)
                ·
                  refine ⟨5043854287164230609292115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26900556198209229916224613 5043854287164230609292115)
                  ·
                    refine ⟨7565781430746345913938173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5043854287164230609292115 7565781430746345913938173)
                    ·
                      refine ⟨2837168036529879717726815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7565781430746345913938173 2837168036529879717726815)
                      ·
                        rfl

theorem cell23_5525365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_5525365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525365 prefixEnd_5525365 := by exact prefixLift 5525365
  have htrace : WordTrace (prefixWord ++ tailWord_5525365) baseStart_5525365 baseEnd_5525365 := by
    simpa [prefixWord, tailWord_5525365, baseEnd_5525365] using wordTrace_append hprefix tailTrace_5525365
  have hstable : (prefixWord ++ tailWord_5525365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525365).length < 2 ^ (prefixWord ++ tailWord_5525365).sum := by decide
  have hdescent : baseEnd_5525365 < baseStart_5525365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525366 : List Nat := [5, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4]
def baseStart_5525366 : Nat := 118140960795 + 5525366 * 2 ^ 59
def prefixEnd_5525366 : Nat := 4983230072969 + 3 ^ 40 * 5525366 * 2
def baseEnd_5525366 : Nat := 2837168550010534213814311

theorem tailTrace_5525366 : CollatzResearch.WordTrace tailWord_5525366 prefixEnd_5525366 2837168550010534213814311 := by
  unfold tailWord_5525366
  simp only [CollatzResearch.WordTrace]
  refine ⟨12595415881284382139344247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134351102733700076153005301 12595415881284382139344247)
  ·
    refine ⟨18893123821926573209016371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12595415881284382139344247 18893123821926573209016371)
    ·
      refine ⟨28339685732889859813524557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18893123821926573209016371 28339685732889859813524557)
      ·
        refine ⟨10627382149833697430071709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28339685732889859813524557 10627382149833697430071709)
        ·
          refine ⟨3985268306187636536276891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10627382149833697430071709 3985268306187636536276891)
          ·
            refine ⟨5977902459281454804415337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3985268306187636536276891 5977902459281454804415337)
            ·
              refine ⟨4483426844461091103311503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5977902459281454804415337 4483426844461091103311503)
              ·
                refine ⟨6725140266691636654967255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4483426844461091103311503 6725140266691636654967255)
                ·
                  refine ⟨10087710400037454982450883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6725140266691636654967255 10087710400037454982450883)
                  ·
                    refine ⟨15131565600056182473676325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10087710400037454982450883 15131565600056182473676325)
                    ·
                      refine ⟨2837168550010534213814311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15131565600056182473676325 2837168550010534213814311)
                      ·
                        rfl

theorem cell23_5525366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_5525366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525366 prefixEnd_5525366 := by exact prefixLift 5525366
  have htrace : WordTrace (prefixWord ++ tailWord_5525366) baseStart_5525366 baseEnd_5525366 := by
    simpa [prefixWord, tailWord_5525366, baseEnd_5525366] using wordTrace_append hprefix tailTrace_5525366
  have hstable : (prefixWord ++ tailWord_5525366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525366).length < 2 ^ (prefixWord ++ tailWord_5525366).sum := by decide
  have hdescent : baseEnd_5525366 < baseStart_5525366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525381 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 4, 6]
def baseStart_5525381 : Nat := 118140960795 + 5525381 * 2 ^ 59
def prefixEnd_5525381 : Nat := 4983230072969 + 3 ^ 40 * 5525381 * 2
def baseEnd_5525381 : Nat := 945725417406783885042247

theorem tailTrace_5525381 : CollatzResearch.WordTrace tailWord_5525381 prefixEnd_5525381 945725417406783885042247 := by
  unfold tailWord_5525381
  simp only [CollatzResearch.WordTrace]
  refine ⟨201527201195495771791303997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134351467463663847860869331 201527201195495771791303997)
  ·
    refine ⟨75572700448310914421738999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201527201195495771791303997 75572700448310914421738999)
    ·
      refine ⟨113359050672466371632608499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75572700448310914421738999 113359050672466371632608499)
      ·
        refine ⟨170038576008699557448912749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113359050672466371632608499 170038576008699557448912749)
        ·
          refine ⟨63764466003262334043342281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170038576008699557448912749 63764466003262334043342281)
          ·
            refine ⟨47823349502446750532506711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63764466003262334043342281 47823349502446750532506711)
            ·
              refine ⟨71735024253670125798760067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47823349502446750532506711 71735024253670125798760067)
              ·
                refine ⟨107602536380505188698140101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71735024253670125798760067 107602536380505188698140101)
                ·
                  refine ⟨20175475571344722880901269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107602536380505188698140101 20175475571344722880901269)
                  ·
                    refine ⟨945725417406783885042247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20175475571344722880901269 945725417406783885042247)
                    ·
                      rfl

theorem cell23_5525381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 6].length) (baseStart_5525381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525381 prefixEnd_5525381 := by exact prefixLift 5525381
  have htrace : WordTrace (prefixWord ++ tailWord_5525381) baseStart_5525381 baseEnd_5525381 := by
    simpa [prefixWord, tailWord_5525381, baseEnd_5525381] using wordTrace_append hprefix tailTrace_5525381
  have hstable : (prefixWord ++ tailWord_5525381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525381).length < 2 ^ (prefixWord ++ tailWord_5525381).sum := by decide
  have hdescent : baseEnd_5525381 < baseStart_5525381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525409 : List Nat := [1, 2, 3, 4, 2, 1, 2, 2, 1, 3, 2]
def baseStart_5525409 : Nat := 118140960795 + 5525409 * 2 ^ 59
def prefixEnd_5525409 : Nat := 4983230072969 + 3 ^ 40 * 5525409 * 2
def baseEnd_5525409 : Nat := 2837190629678677545576613

theorem tailTrace_5525409 : CollatzResearch.WordTrace tailWord_5525409 prefixEnd_5525409 2837190629678677545576613 := by
  unfold tailWord_5525409
  simp only [CollatzResearch.WordTrace]
  refine ⟨201528222439394332573323281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134352148292929555048882187 201528222439394332573323281)
  ·
    refine ⟨151146166829545749429992461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201528222439394332573323281 151146166829545749429992461)
    ·
      refine ⟨56679812561079656036247173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151146166829545749429992461 56679812561079656036247173)
      ·
        refine ⟨10627464855202435506796345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56679812561079656036247173 10627464855202435506796345)
        ·
          refine ⟨7970598641401826630097259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10627464855202435506796345 7970598641401826630097259)
          ·
            refine ⟨11955897962102739945145889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7970598641401826630097259 11955897962102739945145889)
            ·
              refine ⟨8966923471577054958859417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11955897962102739945145889 8966923471577054958859417)
              ·
                refine ⟨6725192603682791219144563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8966923471577054958859417 6725192603682791219144563)
                ·
                  refine ⟨10087788905524186828716845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6725192603682791219144563 10087788905524186828716845)
                  ·
                    refine ⟨3782920839571570060768817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10087788905524186828716845 3782920839571570060768817)
                    ·
                      refine ⟨2837190629678677545576613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3782920839571570060768817 2837190629678677545576613)
                      ·
                        rfl

theorem cell23_5525409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_5525409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525409 prefixEnd_5525409 := by exact prefixLift 5525409
  have htrace : WordTrace (prefixWord ++ tailWord_5525409) baseStart_5525409 baseEnd_5525409 := by
    simpa [prefixWord, tailWord_5525409, baseEnd_5525409] using wordTrace_append hprefix tailTrace_5525409
  have hstable : (prefixWord ++ tailWord_5525409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525409).length < 2 ^ (prefixWord ++ tailWord_5525409).sum := by decide
  have hdescent : baseEnd_5525409 < baseStart_5525409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525475 : List Nat := [1, 1, 1, 6, 1, 3, 2, 1, 2, 5]
def baseStart_5525475 : Nat := 118140960795 + 5525475 * 2 ^ 59
def prefixEnd_5525475 : Nat := 4983230072969 + 3 ^ 40 * 5525475 * 2
def baseEnd_5525475 : Nat := 945741506467291429117103

theorem tailTrace_5525475 : CollatzResearch.WordTrace tailWord_5525475 prefixEnd_5525475 945741506467291429117103 := by
  unfold tailWord_5525475
  simp only [CollatzResearch.WordTrace]
  refine ⟨201530629657155225845225879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134353753104770150563483919 201530629657155225845225879)
  ·
    refine ⟨302295944485732838767838819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201530629657155225845225879 302295944485732838767838819)
    ·
      refine ⟨453443916728599258151758229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302295944485732838767838819 453443916728599258151758229)
      ·
        refine ⟨21255183596653090225863667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 453443916728599258151758229 21255183596653090225863667)
        ·
          refine ⟨31882775394979635338795501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21255183596653090225863667 31882775394979635338795501)
          ·
            refine ⟨11956040773117363252048313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31882775394979635338795501 11956040773117363252048313)
            ·
              refine ⟨8967030579838022439036235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11956040773117363252048313 8967030579838022439036235)
              ·
                refine ⟨13450545869757033658554353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8967030579838022439036235 13450545869757033658554353)
                ·
                  refine ⟨10087909402317775243915765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13450545869757033658554353 10087909402317775243915765)
                  ·
                    refine ⟨945741506467291429117103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10087909402317775243915765 945741506467291429117103)
                    ·
                      rfl

theorem cell23_5525475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 2, 5].length) (baseStart_5525475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525475 prefixEnd_5525475 := by exact prefixLift 5525475
  have htrace : WordTrace (prefixWord ++ tailWord_5525475) baseStart_5525475 baseEnd_5525475 := by
    simpa [prefixWord, tailWord_5525475, baseEnd_5525475] using wordTrace_append hprefix tailTrace_5525475
  have hstable : (prefixWord ++ tailWord_5525475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525475).length < 2 ^ (prefixWord ++ tailWord_5525475).sum := by decide
  have hdescent : baseEnd_5525475 < baseStart_5525475 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525481 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 11]
def baseStart_5525481 : Nat := 118140960795 + 5525481 * 2 ^ 59
def prefixEnd_5525481 : Nat := 4983230072969 + 3 ^ 40 * 5525481 * 2
def baseEnd_5525481 : Nat := 2837227600285801263876281

theorem tailTrace_5525481 : CollatzResearch.WordTrace tailWord_5525481 prefixEnd_5525481 2837227600285801263876281 := by
  unfold tailWord_5525481
  simp only [CollatzResearch.WordTrace]
  refine ⟨201530848495133488869944297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134353898996755659246629531 201530848495133488869944297)
  ·
    refine ⟨151148136371350116652458223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201530848495133488869944297 151148136371350116652458223)
    ·
      refine ⟨226722204557025174978687335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151148136371350116652458223 226722204557025174978687335)
      ·
        refine ⟨340083306835537762468031003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226722204557025174978687335 340083306835537762468031003)
        ·
          refine ⟨510124960253306643702046505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340083306835537762468031003 510124960253306643702046505)
          ·
            refine ⟨382593720189979982776534879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 510124960253306643702046505 382593720189979982776534879)
            ·
              refine ⟨573890580284969974164802319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382593720189979982776534879 573890580284969974164802319)
              ·
                refine ⟨860835870427454961247203479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 573890580284969974164802319 860835870427454961247203479)
                ·
                  refine ⟨1291253805641182441870805219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 860835870427454961247203479 1291253805641182441870805219)
                  ·
                    refine ⟨1936880708461773662806207829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1291253805641182441870805219 1936880708461773662806207829)
                    ·
                      refine ⟨2837227600285801263876281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 1936880708461773662806207829 2837227600285801263876281)
                      ·
                        rfl

theorem cell23_5525481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 11].length) (baseStart_5525481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525481 prefixEnd_5525481 := by exact prefixLift 5525481
  have htrace : WordTrace (prefixWord ++ tailWord_5525481) baseStart_5525481 baseEnd_5525481 := by
    simpa [prefixWord, tailWord_5525481, baseEnd_5525481] using wordTrace_append hprefix tailTrace_5525481
  have hstable : (prefixWord ++ tailWord_5525481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525481).length < 2 ^ (prefixWord ++ tailWord_5525481).sum := by decide
  have hdescent : baseEnd_5525481 < baseStart_5525481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525498 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 5, 4, 3]
def baseStart_5525498 : Nat := 118140960795 + 5525498 * 2 ^ 59
def prefixEnd_5525498 : Nat := 4983230072969 + 3 ^ 40 * 5525498 * 2
def baseEnd_5525498 : Nat := 2837236329456927697363703

theorem tailTrace_5525498 : CollatzResearch.WordTrace tailWord_5525498 prefixEnd_5525498 2837236329456927697363703 := by
  unfold tailWord_5525498
  simp only [CollatzResearch.WordTrace]
  refine ⟨50382867134017975193328287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134354312357381267182208765 50382867134017975193328287)
  ·
    refine ⟨75574300701026962789992431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50382867134017975193328287 75574300701026962789992431)
    ·
      refine ⟨113361451051540444184988647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75574300701026962789992431 113361451051540444184988647)
      ·
        refine ⟨170042176577310666277482971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113361451051540444184988647 170042176577310666277482971)
        ·
          refine ⟨255063264865965999416224457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170042176577310666277482971 255063264865965999416224457)
          ·
            refine ⟨191297448649474499562168343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255063264865965999416224457 191297448649474499562168343)
            ·
              refine ⟨286946172974211749343252515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191297448649474499562168343 286946172974211749343252515)
              ·
                refine ⟨430419259461317624014878773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 286946172974211749343252515 430419259461317624014878773)
                ·
                  refine ⟨40351805574498527251394885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 430419259461317624014878773 40351805574498527251394885)
                  ·
                    refine ⟨7565963545218473859636541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40351805574498527251394885 7565963545218473859636541)
                    ·
                      refine ⟨2837236329456927697363703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7565963545218473859636541 2837236329456927697363703)
                      ·
                        rfl

theorem cell23_5525498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 5, 4, 3].length) (baseStart_5525498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525498 prefixEnd_5525498 := by exact prefixLift 5525498
  have htrace : WordTrace (prefixWord ++ tailWord_5525498) baseStart_5525498 baseEnd_5525498 := by
    simpa [prefixWord, tailWord_5525498, baseEnd_5525498] using wordTrace_append hprefix tailTrace_5525498
  have hstable : (prefixWord ++ tailWord_5525498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525498).length < 2 ^ (prefixWord ++ tailWord_5525498).sum := by decide
  have hdescent : baseEnd_5525498 < baseStart_5525498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525505 : List Nat := [1, 2, 4, 1, 2, 1, 2, 3, 3, 4]
def baseStart_5525505 : Nat := 118140960795 + 5525505 * 2 ^ 59
def prefixEnd_5525505 : Nat := 4983230072969 + 3 ^ 40 * 5525505 * 2
def baseEnd_5525505 : Nat := 945746641273836389992057

theorem tailTrace_5525505 : CollatzResearch.WordTrace tailWord_5525505 prefixEnd_5525505 945746641273836389992057 := by
  unfold tailWord_5525505
  simp only [CollatzResearch.WordTrace]
  refine ⟨201531723847046540968817969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134354482564697693979211979 201531723847046540968817969)
  ·
    refine ⟨151148792885284905726613477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201531723847046540968817969 151148792885284905726613477)
    ·
      refine ⟨28340398665990919823740027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151148792885284905726613477 28340398665990919823740027)
      ·
        refine ⟨42510597998986379735610041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28340398665990919823740027 42510597998986379735610041)
        ·
          refine ⟨31882948499239784801707531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42510597998986379735610041 31882948499239784801707531)
          ·
            refine ⟨47824422748859677202561297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31882948499239784801707531 47824422748859677202561297)
            ·
              refine ⟨35868317061644757901920973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47824422748859677202561297 35868317061644757901920973)
              ·
                refine ⟨13450618898116784213220365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35868317061644757901920973 13450618898116784213220365)
                ·
                  refine ⟨5043982086793794079957637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13450618898116784213220365 5043982086793794079957637)
                  ·
                    refine ⟨945746641273836389992057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5043982086793794079957637 945746641273836389992057)
                    ·
                      rfl

theorem cell23_5525505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_5525505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525505 prefixEnd_5525505 := by exact prefixLift 5525505
  have htrace : WordTrace (prefixWord ++ tailWord_5525505) baseStart_5525505 baseEnd_5525505 := by
    simpa [prefixWord, tailWord_5525505, baseEnd_5525505] using wordTrace_append hprefix tailTrace_5525505
  have hstable : (prefixWord ++ tailWord_5525505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525505).length < 2 ^ (prefixWord ++ tailWord_5525505).sum := by decide
  have hdescent : baseEnd_5525505 < baseStart_5525505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525532 : List Nat := [2, 2, 3, 1, 3, 1, 3, 1, 2, 2, 3]
def baseStart_5525532 : Nat := 118140960795 + 5525532 * 2 ^ 59
def prefixEnd_5525532 : Nat := 4983230072969 + 3 ^ 40 * 5525532 * 2
def baseEnd_5525532 : Nat := 2837253787799180564338547

theorem tailTrace_5525532 : CollatzResearch.WordTrace tailWord_5525532 prefixEnd_5525532 2837253787799180564338547 := by
  unfold tailWord_5525532
  simp only [CollatzResearch.WordTrace]
  refine ⟨100766354308974362290025425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134355139078632483053367233 100766354308974362290025425)
  ·
    refine ⟨75574765731730771717519069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100766354308974362290025425 75574765731730771717519069)
    ·
      refine ⟨28340537149399039394069651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75574765731730771717519069 28340537149399039394069651)
      ·
        refine ⟨42510805724098559091104477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28340537149399039394069651 42510805724098559091104477)
        ·
          refine ⟨15941552146536959659164179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42510805724098559091104477 15941552146536959659164179)
          ·
            refine ⟨23912328219805439488746269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15941552146536959659164179 23912328219805439488746269)
            ·
              refine ⟨8967123082427039808279851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23912328219805439488746269 8967123082427039808279851)
              ·
                refine ⟨13450684623640559712419777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8967123082427039808279851 13450684623640559712419777)
                ·
                  refine ⟨10088013467730419784314833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13450684623640559712419777 10088013467730419784314833)
                  ·
                    refine ⟨7566010100797814838236125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10088013467730419784314833 7566010100797814838236125)
                    ·
                      refine ⟨2837253787799180564338547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7566010100797814838236125 2837253787799180564338547)
                      ·
                        rfl

theorem cell23_5525532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_5525532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525532 prefixEnd_5525532 := by exact prefixLift 5525532
  have htrace : WordTrace (prefixWord ++ tailWord_5525532) baseStart_5525532 baseEnd_5525532 := by
    simpa [prefixWord, tailWord_5525532, baseEnd_5525532] using wordTrace_append hprefix tailTrace_5525532
  have hstable : (prefixWord ++ tailWord_5525532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525532).length < 2 ^ (prefixWord ++ tailWord_5525532).sum := by decide
  have hdescent : baseEnd_5525532 < baseStart_5525532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525548 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 5, 5]
def baseStart_5525548 : Nat := 118140960795 + 5525548 * 2 ^ 59
def prefixEnd_5525548 : Nat := 4983230072969 + 3 ^ 40 * 5525548 * 2
def baseEnd_5525548 : Nat := 945754001163217500579491

theorem tailTrace_5525548 : CollatzResearch.WordTrace tailWord_5525548 prefixEnd_5525548 945754001163217500579491 := by
  unfold tailWord_5525548
  simp only [CollatzResearch.WordTrace]
  refine ⟨100766646092945379656316649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134355528123927172875088865 100766646092945379656316649)
  ·
    refine ⟨75574984569709034742237487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100766646092945379656316649 75574984569709034742237487)
    ·
      refine ⟨113362476854563552113356231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75574984569709034742237487 113362476854563552113356231)
      ·
        refine ⟨170043715281845328170034347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113362476854563552113356231 170043715281845328170034347)
        ·
          refine ⟨255065572922767992255051521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170043715281845328170034347 255065572922767992255051521)
          ·
            refine ⟨191299179692075994191288641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255065572922767992255051521 191299179692075994191288641)
            ·
              refine ⟨143474384769056995643466481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191299179692075994191288641 143474384769056995643466481)
              ·
                refine ⟨107605788576792746732599861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143474384769056995643466481 107605788576792746732599861)
                ·
                  refine ⟨10088042679074320006181237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 107605788576792746732599861 10088042679074320006181237)
                  ·
                    refine ⟨945754001163217500579491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10088042679074320006181237 945754001163217500579491)
                    ·
                      rfl

theorem cell23_5525548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 5].length) (baseStart_5525548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525548 prefixEnd_5525548 := by exact prefixLift 5525548
  have htrace : WordTrace (prefixWord ++ tailWord_5525548) baseStart_5525548 baseEnd_5525548 := by
    simpa [prefixWord, tailWord_5525548, baseEnd_5525548] using wordTrace_append hprefix tailTrace_5525548
  have hstable : (prefixWord ++ tailWord_5525548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525548).length < 2 ^ (prefixWord ++ tailWord_5525548).sum := by decide
  have hdescent : baseEnd_5525548 < baseStart_5525548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525582 : List Nat := [4, 1, 1, 1, 1, 5, 2, 2, 1, 5]
def baseStart_5525582 : Nat := 118140960795 + 5525582 * 2 ^ 59
def prefixEnd_5525582 : Nat := 4983230072969 + 3 ^ 40 * 5525582 * 2
def baseEnd_5525582 : Nat := 945759820610635122904439

theorem tailTrace_5525582 : CollatzResearch.WordTrace tailWord_5525582 prefixEnd_5525582 945759820610635122904439 := by
  unfold tailWord_5525582
  simp only [CollatzResearch.WordTrace]
  refine ⟨25191816533470947889921375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134356354845178388746247333 25191816533470947889921375)
  ·
    refine ⟨37787724800206421834882063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25191816533470947889921375 37787724800206421834882063)
    ·
      refine ⟨56681587200309632752323095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37787724800206421834882063 56681587200309632752323095)
      ·
        refine ⟨85022380800464449128484643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56681587200309632752323095 85022380800464449128484643)
        ·
          refine ⟨127533571200696673692726965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85022380800464449128484643 127533571200696673692726965)
          ·
            refine ⟨11956272300065313158693153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 127533571200696673692726965 11956272300065313158693153)
            ·
              refine ⟨8967204225048984869019865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11956272300065313158693153 8967204225048984869019865)
              ·
                refine ⟨6725403168786738651764899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8967204225048984869019865 6725403168786738651764899)
                ·
                  refine ⟨10088104753180107977647349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6725403168786738651764899 10088104753180107977647349)
                  ·
                    refine ⟨945759820610635122904439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10088104753180107977647349 945759820610635122904439)
                    ·
                      rfl

theorem cell23_5525582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_5525582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525582 prefixEnd_5525582 := by exact prefixLift 5525582
  have htrace : WordTrace (prefixWord ++ tailWord_5525582) baseStart_5525582 baseEnd_5525582 := by
    simpa [prefixWord, tailWord_5525582, baseEnd_5525582] using wordTrace_append hprefix tailTrace_5525582
  have hstable : (prefixWord ++ tailWord_5525582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525582).length < 2 ^ (prefixWord ++ tailWord_5525582).sum := by decide
  have hdescent : baseEnd_5525582 < baseStart_5525582 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525585 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 1, 8, 2]
def baseStart_5525585 : Nat := 118140960795 + 5525585 * 2 ^ 59
def prefixEnd_5525585 : Nat := 4983230072969 + 3 ^ 40 * 5525585 * 2
def baseEnd_5525585 : Nat := 2837281002273868856975803

theorem tailTrace_5525585 : CollatzResearch.WordTrace tailWord_5525585 prefixEnd_5525585 2837281002273868856975803 := by
  unfold tailWord_5525585
  simp only [CollatzResearch.WordTrace]
  refine ⟨201534641686756714631730209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134356427791171143087820139 201534641686756714631730209)
  ·
    refine ⟨151150981265067535973797657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201534641686756714631730209 151150981265067535973797657)
    ·
      refine ⟨113363235948800651980348243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151150981265067535973797657 113363235948800651980348243)
      ·
        refine ⟨170044853923200977970522365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113363235948800651980348243 170044853923200977970522365)
        ·
          refine ⟨63766820221200366738945887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170044853923200977970522365 63766820221200366738945887)
          ·
            refine ⟨95650230331800550108418831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63766820221200366738945887 95650230331800550108418831)
            ·
              refine ⟨143475345497700825162628247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95650230331800550108418831 143475345497700825162628247)
              ·
                refine ⟨215213018246551237743942371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143475345497700825162628247 215213018246551237743942371)
                ·
                  refine ⟨322819527369826856615913557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215213018246551237743942371 322819527369826856615913557)
                  ·
                    refine ⟨3783041336365158475967737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 322819527369826856615913557 3783041336365158475967737)
                    ·
                      refine ⟨2837281002273868856975803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3783041336365158475967737 2837281002273868856975803)
                      ·
                        rfl

theorem cell23_5525585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 8, 2].length) (baseStart_5525585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525585 prefixEnd_5525585 := by exact prefixLift 5525585
  have htrace : WordTrace (prefixWord ++ tailWord_5525585) baseStart_5525585 baseEnd_5525585 := by
    simpa [prefixWord, tailWord_5525585, baseEnd_5525585] using wordTrace_append hprefix tailTrace_5525585
  have hstable : (prefixWord ++ tailWord_5525585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525585).length < 2 ^ (prefixWord ++ tailWord_5525585).sum := by decide
  have hdescent : baseEnd_5525585 < baseStart_5525585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525596 : List Nat := [2, 2, 4, 1, 1, 2, 3, 3, 1, 1, 3]
def baseStart_5525596 : Nat := 118140960795 + 5525596 * 2 ^ 59
def prefixEnd_5525596 : Nat := 4983230072969 + 3 ^ 40 * 5525596 * 2
def baseEnd_5525596 : Nat := 2837286650561068313938253

theorem tailTrace_5525596 : CollatzResearch.WordTrace tailWord_5525596 prefixEnd_5525596 2837286650561068313938253 := by
  unfold tailWord_5525596
  simp only [CollatzResearch.WordTrace]
  refine ⟨100767521444858431755190321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134356695259811242340253761 100767521444858431755190321)
  ·
    refine ⟨75575641083643823816392741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100767521444858431755190321 75575641083643823816392741)
    ·
      refine ⟨14170432703183216965573639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75575641083643823816392741 14170432703183216965573639)
      ·
        refine ⟨21255649054774825448360459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14170432703183216965573639 21255649054774825448360459)
        ·
          refine ⟨31883473582162238172540689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21255649054774825448360459 31883473582162238172540689)
          ·
            refine ⟨23912605186621678629405517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31883473582162238172540689 23912605186621678629405517)
            ·
              refine ⟨8967226944983129486027069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23912605186621678629405517 8967226944983129486027069)
              ·
                refine ⟨3362710104368673557260151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8967226944983129486027069 3362710104368673557260151)
                ·
                  refine ⟨5044065156553010335890227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3362710104368673557260151 5044065156553010335890227)
                  ·
                    refine ⟨7566097734829515503835341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5044065156553010335890227 7566097734829515503835341)
                    ·
                      refine ⟨2837286650561068313938253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7566097734829515503835341 2837286650561068313938253)
                      ·
                        rfl

theorem cell23_5525596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_5525596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525596 prefixEnd_5525596 := by exact prefixLift 5525596
  have htrace : WordTrace (prefixWord ++ tailWord_5525596) baseStart_5525596 baseEnd_5525596 := by
    simpa [prefixWord, tailWord_5525596, baseEnd_5525596] using wordTrace_append hprefix tailTrace_5525596
  have hstable : (prefixWord ++ tailWord_5525596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525596).length < 2 ^ (prefixWord ++ tailWord_5525596).sum := by decide
  have hdescent : baseEnd_5525596 < baseStart_5525596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525605 : List Nat := [1, 3, 1, 3, 2, 2, 1, 3, 1, 1, 5]
def baseStart_5525605 : Nat := 118140960795 + 5525605 * 2 ^ 59
def prefixEnd_5525605 : Nat := 4983230072969 + 3 ^ 40 * 5525605 * 2
def baseEnd_5525605 : Nat := 2837291271886958778725711

theorem tailTrace_5525605 : CollatzResearch.WordTrace tailWord_5525605 prefixEnd_5525605 2837291271886958778725711 := by
  unfold tailWord_5525605
  simp only [CollatzResearch.WordTrace]
  refine ⟨201535371146684258047458269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134356914097789505364972179 201535371146684258047458269)
  ·
    refine ⟨75575764180006596767796851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201535371146684258047458269 75575764180006596767796851)
    ·
      refine ⟨113363646270009895151695277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75575764180006596767796851 113363646270009895151695277)
      ·
        refine ⟨42511367351253710681885729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113363646270009895151695277 42511367351253710681885729)
        ·
          refine ⟨31883525513440283011414297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42511367351253710681885729 31883525513440283011414297)
          ·
            refine ⟨23912644135080212258560723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31883525513440283011414297 23912644135080212258560723)
            ·
              refine ⟨35868966202620318387841085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23912644135080212258560723 35868966202620318387841085)
              ·
                refine ⟨13450862325982619395440407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35868966202620318387841085 13450862325982619395440407)
                ·
                  refine ⟨20176293488973929093160611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13450862325982619395440407 20176293488973929093160611)
                  ·
                    refine ⟨30264440233460893639740917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20176293488973929093160611 30264440233460893639740917)
                    ·
                      refine ⟨2837291271886958778725711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30264440233460893639740917 2837291271886958778725711)
                      ·
                        rfl

theorem cell23_5525605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_5525605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525605 prefixEnd_5525605 := by exact prefixLift 5525605
  have htrace : WordTrace (prefixWord ++ tailWord_5525605) baseStart_5525605 baseEnd_5525605 := by
    simpa [prefixWord, tailWord_5525605, baseEnd_5525605] using wordTrace_append hprefix tailTrace_5525605
  have hstable : (prefixWord ++ tailWord_5525605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525605).length < 2 ^ (prefixWord ++ tailWord_5525605).sum := by decide
  have hdescent : baseEnd_5525605 < baseStart_5525605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525622 : List Nat := [5, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5]
def baseStart_5525622 : Nat := 118140960795 + 5525622 * 2 ^ 59
def prefixEnd_5525622 : Nat := 4983230072969 + 3 ^ 40 * 5525622 * 2
def baseEnd_5525622 : Nat := 2837300001058085212213133

theorem tailTrace_5525622 : CollatzResearch.WordTrace tailWord_5525622 prefixEnd_5525622 2837300001058085212213133 := by
  unfold tailWord_5525622
  simp only [CollatzResearch.WordTrace]
  refine ⟨12595999449226416871926695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134357327458415113300551413 12595999449226416871926695)
  ·
    refine ⟨18893999173839625307890043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12595999449226416871926695 18893999173839625307890043)
    ·
      refine ⟨28340998760759437961835065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18893999173839625307890043 28340998760759437961835065)
      ·
        refine ⟨21255749070569578471376299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28340998760759437961835065 21255749070569578471376299)
        ·
          refine ⟨31883623605854367707064449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21255749070569578471376299 31883623605854367707064449)
          ·
            refine ⟨23912717704390775780298337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31883623605854367707064449 23912717704390775780298337)
            ·
              refine ⟨17934538278293081835223753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23912717704390775780298337 17934538278293081835223753)
              ·
                refine ⟨13450903708719811376417815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17934538278293081835223753 13450903708719811376417815)
                ·
                  refine ⟨20176355563079717064626723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13450903708719811376417815 20176355563079717064626723)
                  ·
                    refine ⟨30264533344619575596940085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20176355563079717064626723 30264533344619575596940085)
                    ·
                      refine ⟨2837300001058085212213133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30264533344619575596940085 2837300001058085212213133)
                      ·
                        rfl

theorem cell23_5525622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_5525622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525622 prefixEnd_5525622 := by exact prefixLift 5525622
  have htrace : WordTrace (prefixWord ++ tailWord_5525622) baseStart_5525622 baseEnd_5525622 := by
    simpa [prefixWord, tailWord_5525622, baseEnd_5525622] using wordTrace_append hprefix tailTrace_5525622
  have hstable : (prefixWord ++ tailWord_5525622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525622).length < 2 ^ (prefixWord ++ tailWord_5525622).sum := by decide
  have hdescent : baseEnd_5525622 < baseStart_5525622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525625 : List Nat := [1, 2, 1, 3, 4, 2, 2, 8]
def baseStart_5525625 : Nat := 118140960795 + 5525625 * 2 ^ 59
def prefixEnd_5525625 : Nat := 4983230072969 + 3 ^ 40 * 5525625 * 2
def baseEnd_5525625 : Nat := 105085242277779581499097

theorem tailTrace_5525625 : CollatzResearch.WordTrace tailWord_5525625 prefixEnd_5525625 105085242277779581499097 := by
  unfold tailWord_5525625
  simp only [CollatzResearch.WordTrace]
  refine ⟨201536100606611801463186329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134357400404407867642124219 201536100606611801463186329)
  ·
    refine ⟨151152075454958851097389747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201536100606611801463186329 151152075454958851097389747)
    ·
      refine ⟨226728113182438276646084621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151152075454958851097389747 226728113182438276646084621)
      ·
        refine ⟨85023042443414353742281733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226728113182438276646084621 85023042443414353742281733)
        ·
          refine ⟨15941820458140191326677825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85023042443414353742281733 15941820458140191326677825)
          ·
            refine ⟨11956365343605143495008369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15941820458140191326677825 11956365343605143495008369)
            ·
              refine ⟨8967274007703857621256277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11956365343605143495008369 8967274007703857621256277)
              ·
                refine ⟨105085242277779581499097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8967274007703857621256277 105085242277779581499097)
                ·
                  rfl

theorem cell23_5525625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 8].length) (baseStart_5525625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525625 prefixEnd_5525625 := by exact prefixLift 5525625
  have htrace : WordTrace (prefixWord ++ tailWord_5525625) baseStart_5525625 baseEnd_5525625 := by
    simpa [prefixWord, tailWord_5525625, baseEnd_5525625] using wordTrace_append hprefix tailTrace_5525625
  have hstable : (prefixWord ++ tailWord_5525625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525625).length < 2 ^ (prefixWord ++ tailWord_5525625).sum := by decide
  have hdescent : baseEnd_5525625 < baseStart_5525625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525629 : List Nat := [1, 4, 1, 1, 3, 2, 4, 1, 2, 4]
def baseStart_5525629 : Nat := 118140960795 + 5525629 * 2 ^ 59
def prefixEnd_5525629 : Nat := 4983230072969 + 3 ^ 40 * 5525629 * 2
def baseEnd_5525629 : Nat := 945767865140888894941867

theorem tailTrace_5525629 : CollatzResearch.WordTrace tailWord_5525629 prefixEnd_5525629 945767865140888894941867 := by
  unfold tailWord_5525629
  simp only [CollatzResearch.WordTrace]
  refine ⟨201536246498597310146331941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134357497665731540097554627 201536246498597310146331941)
  ·
    refine ⟨37788046218486995652437239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201536246498597310146331941 37788046218486995652437239)
    ·
      refine ⟨56682069327730493478655859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37788046218486995652437239 56682069327730493478655859)
      ·
        refine ⟨85023103991595740217983789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56682069327730493478655859 85023103991595740217983789)
        ·
          refine ⟨31883663996848402581743921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85023103991595740217983789 31883663996848402581743921)
          ·
            refine ⟨23912747997636301936307941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31883663996848402581743921 23912747997636301936307941)
            ·
              refine ⟨4483640249556806613057739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23912747997636301936307941 4483640249556806613057739)
              ·
                refine ⟨6725460374335209919586609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4483640249556806613057739 6725460374335209919586609)
                ·
                  refine ⟨5044095280751407439689957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6725460374335209919586609 5044095280751407439689957)
                  ·
                    refine ⟨945767865140888894941867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5044095280751407439689957 945767865140888894941867)
                    ·
                      rfl

theorem cell23_5525629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 2, 4].length) (baseStart_5525629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525629 prefixEnd_5525629 := by exact prefixLift 5525629
  have htrace : WordTrace (prefixWord ++ tailWord_5525629) baseStart_5525629 baseEnd_5525629 := by
    simpa [prefixWord, tailWord_5525629, baseEnd_5525629] using wordTrace_append hprefix tailTrace_5525629
  have hstable : (prefixWord ++ tailWord_5525629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525629).length < 2 ^ (prefixWord ++ tailWord_5525629).sum := by decide
  have hdescent : baseEnd_5525629 < baseStart_5525629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525656 : List Nat := [2, 1, 2, 4, 3, 1, 3, 1, 1, 2, 3]
def baseStart_5525656 : Nat := 118140960795 + 5525656 * 2 ^ 59
def prefixEnd_5525656 : Nat := 4983230072969 + 3 ^ 40 * 5525656 * 2
def baseEnd_5525656 : Nat := 2837317459400338079187977

theorem tailTrace_5525656 : CollatzResearch.WordTrace tailWord_5525656 prefixEnd_5525656 2837317459400338079187977 := by
  unfold tailWord_5525656
  simp only [CollatzResearch.WordTrace]
  refine ⟨100768615634749746878782411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134358154179666329171709881 100768615634749746878782411)
  ·
    refine ⟨151152923452124620318173617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100768615634749746878782411 151152923452124620318173617)
    ·
      refine ⟨113364692589093465238630213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151152923452124620318173617 113364692589093465238630213)
      ·
        refine ⟨21255879860455024732243165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113364692589093465238630213 21255879860455024732243165)
        ·
          refine ⟨7970954947670634274591187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21255879860455024732243165 7970954947670634274591187)
          ·
            refine ⟨11956432421505951411886781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7970954947670634274591187 11956432421505951411886781)
            ·
              refine ⟨4483662158064731779457543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11956432421505951411886781 4483662158064731779457543)
              ·
                refine ⟨6725493237097097669186315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4483662158064731779457543 6725493237097097669186315)
                ·
                  refine ⟨10088239855645646503779473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6725493237097097669186315 10088239855645646503779473)
                  ·
                    refine ⟨7566179891734234877834605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10088239855645646503779473 7566179891734234877834605)
                    ·
                      refine ⟨2837317459400338079187977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7566179891734234877834605 2837317459400338079187977)
                      ·
                        rfl

theorem cell23_5525656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_5525656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525656 prefixEnd_5525656 := by exact prefixLift 5525656
  have htrace : WordTrace (prefixWord ++ tailWord_5525656) baseStart_5525656 baseEnd_5525656 := by
    simpa [prefixWord, tailWord_5525656, baseEnd_5525656] using wordTrace_append hprefix tailTrace_5525656
  have hstable : (prefixWord ++ tailWord_5525656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525656).length < 2 ^ (prefixWord ++ tailWord_5525656).sum := by decide
  have hdescent : baseEnd_5525656 < baseStart_5525656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525669 : List Nat := [1, 3, 1, 2, 1, 3, 4, 2, 2, 1, 3]
def baseStart_5525669 : Nat := 118140960795 + 5525669 * 2 ^ 59
def prefixEnd_5525669 : Nat := 4983230072969 + 3 ^ 40 * 5525669 * 2
def baseEnd_5525669 : Nat := 2837324134648846528325417

theorem tailTrace_5525669 : CollatzResearch.WordTrace tailWord_5525669 prefixEnd_5525669 2837324134648846528325417 := by
  unfold tailWord_5525669
  simp only [CollatzResearch.WordTrace]
  refine ⟨201537705418452396977788061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134358470278968264651858707 201537705418452396977788061)
  ·
    refine ⟨75576639531919648866670523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201537705418452396977788061 75576639531919648866670523)
    ·
      refine ⟨113364959297879473300005785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75576639531919648866670523 113364959297879473300005785)
      ·
        refine ⟨85023719473409604975004339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113364959297879473300005785 85023719473409604975004339)
        ·
          refine ⟨127535579210114407462506509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85023719473409604975004339 127535579210114407462506509)
          ·
            refine ⟨47825842203792902798439941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127535579210114407462506509 47825842203792902798439941)
            ·
              refine ⟨8967345413211169274707489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47825842203792902798439941 8967345413211169274707489)
              ·
                refine ⟨6725509059908376956030617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8967345413211169274707489 6725509059908376956030617)
                ·
                  refine ⟨5044131794931282717022963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6725509059908376956030617 5044131794931282717022963)
                  ·
                    refine ⟨7566197692396924075534445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5044131794931282717022963 7566197692396924075534445)
                    ·
                      refine ⟨2837324134648846528325417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7566197692396924075534445 2837324134648846528325417)
                      ·
                        rfl

theorem cell23_5525669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 2, 1, 3].length) (baseStart_5525669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525669 prefixEnd_5525669 := by exact prefixLift 5525669
  have htrace : WordTrace (prefixWord ++ tailWord_5525669) baseStart_5525669 baseEnd_5525669 := by
    simpa [prefixWord, tailWord_5525669, baseEnd_5525669] using wordTrace_append hprefix tailTrace_5525669
  have hstable : (prefixWord ++ tailWord_5525669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525669).length < 2 ^ (prefixWord ++ tailWord_5525669).sum := by decide
  have hdescent : baseEnd_5525669 < baseStart_5525669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525695 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 4, 4, 3]
def baseStart_5525695 : Nat := 118140960795 + 5525695 * 2 ^ 59
def prefixEnd_5525695 : Nat := 4983230072969 + 3 ^ 40 * 5525695 * 2
def baseEnd_5525695 : Nat := 2837337485145863426600297

theorem tailTrace_5525695 : CollatzResearch.WordTrace tailWord_5525695 prefixEnd_5525695 2837337485145863426600297 := by
  unfold tailWord_5525695
  simp only [CollatzResearch.WordTrace]
  refine ⟨201538653716358203418234539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134359102477572135612156359 201538653716358203418234539)
  ·
    refine ⟨302307980574537305127351809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201538653716358203418234539 302307980574537305127351809)
    ·
      refine ⟨226730985430902978845513857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302307980574537305127351809 226730985430902978845513857)
      ·
        refine ⟨170048239073177234134135393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226730985430902978845513857 170048239073177234134135393)
        ·
          refine ⟨127536179304882925600601545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170048239073177234134135393 127536179304882925600601545)
          ·
            refine ⟨95652134478662194200451159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127536179304882925600601545 95652134478662194200451159)
            ·
              refine ⟨143478201717993291300676739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95652134478662194200451159 143478201717993291300676739)
              ·
                refine ⟨215217302576989936951015109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143478201717993291300676739 215217302576989936951015109)
                ·
                  refine ⟨40353244233185613178315333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 215217302576989936951015109 40353244233185613178315333)
                  ·
                    refine ⟨7566233293722302470934125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40353244233185613178315333 7566233293722302470934125)
                    ·
                      refine ⟨2837337485145863426600297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7566233293722302470934125 2837337485145863426600297)
                      ·
                        rfl

theorem cell23_5525695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 4, 3].length) (baseStart_5525695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525695 prefixEnd_5525695 := by exact prefixLift 5525695
  have htrace : WordTrace (prefixWord ++ tailWord_5525695) baseStart_5525695 baseEnd_5525695 := by
    simpa [prefixWord, tailWord_5525695, baseEnd_5525695] using wordTrace_append hprefix tailTrace_5525695
  have hstable : (prefixWord ++ tailWord_5525695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525695).length < 2 ^ (prefixWord ++ tailWord_5525695).sum := by decide
  have hdescent : baseEnd_5525695 < baseStart_5525695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525743 : List Nat := [1, 1, 2, 1, 6, 2, 3, 1, 2, 2, 2]
def baseStart_5525743 : Nat := 118140960795 + 5525743 * 2 ^ 59
def prefixEnd_5525743 : Nat := 4983230072969 + 3 ^ 40 * 5525743 * 2
def baseEnd_5525743 : Nat := 2837362132217279238800077

theorem tailTrace_5525743 : CollatzResearch.WordTrace tailWord_5525743 prefixEnd_5525743 2837362132217279238800077 := by
  unfold tailWord_5525743
  simp only [CollatzResearch.WordTrace]
  refine ⟨201540404420184307615981883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134360269613456205077321255 201540404420184307615981883)
  ·
    refine ⟨302310606630276461423972825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201540404420184307615981883 302310606630276461423972825)
    ·
      refine ⟨226732954972707346067979619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302310606630276461423972825 226732954972707346067979619)
      ·
        refine ⟨340099432459061019101969429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226732954972707346067979619 340099432459061019101969429)
        ·
          refine ⟨15942160896518485270404817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 340099432459061019101969429 15942160896518485270404817)
          ·
            refine ⟨11956620672388863952803613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15942160896518485270404817 11956620672388863952803613)
            ·
              refine ⟨4483732752145823982301355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11956620672388863952803613 4483732752145823982301355)
              ·
                refine ⟨6725599128218735973452033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4483732752145823982301355 6725599128218735973452033)
                ·
                  refine ⟨5044199346164051980089025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6725599128218735973452033 5044199346164051980089025)
                  ·
                    refine ⟨3783149509623038985066769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5044199346164051980089025 3783149509623038985066769)
                    ·
                      refine ⟨2837362132217279238800077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3783149509623038985066769 2837362132217279238800077)
                      ·
                        rfl

theorem cell23_5525743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 2, 2, 2].length) (baseStart_5525743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525743 prefixEnd_5525743 := by exact prefixLift 5525743
  have htrace : WordTrace (prefixWord ++ tailWord_5525743) baseStart_5525743 baseEnd_5525743 := by
    simpa [prefixWord, tailWord_5525743, baseEnd_5525743] using wordTrace_append hprefix tailTrace_5525743
  have hstable : (prefixWord ++ tailWord_5525743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525743).length < 2 ^ (prefixWord ++ tailWord_5525743).sum := by decide
  have hdescent : baseEnd_5525743 < baseStart_5525743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525745 : List Nat := [1, 2, 2, 2, 2, 1, 3, 2, 1, 7]
def baseStart_5525745 : Nat := 118140960795 + 5525745 * 2 ^ 59
def prefixEnd_5525745 : Nat := 4983230072969 + 3 ^ 40 * 5525745 * 2
def baseEnd_5525745 : Nat := 945787719726196076991689

theorem tailTrace_5525745 : CollatzResearch.WordTrace tailWord_5525745 prefixEnd_5525745 945787719726196076991689 := by
  unfold tailWord_5525745
  simp only [CollatzResearch.WordTrace]
  refine ⟨201540477366177061957554689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134360318244118041305036459 201540477366177061957554689)
  ·
    refine ⟨151155358024632796468166017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201540477366177061957554689 151155358024632796468166017)
    ·
      refine ⟨113366518518474597351124513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151155358024632796468166017 113366518518474597351124513)
      ·
        refine ⟨85024888888855948013343385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113366518518474597351124513 85024888888855948013343385)
        ·
          refine ⟨63768666666641961010007539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85024888888855948013343385 63768666666641961010007539)
          ·
            refine ⟨95652999999962941515011309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63768666666641961010007539 95652999999962941515011309)
            ·
              refine ⟨35869874999986103068129241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95652999999962941515011309 35869874999986103068129241)
              ·
                refine ⟨26902406249989577301096931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35869874999986103068129241 26902406249989577301096931)
                ·
                  refine ⟨40353609374984365951645397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26902406249989577301096931 40353609374984365951645397)
                  ·
                    refine ⟨945787719726196076991689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40353609374984365951645397 945787719726196076991689)
                    ·
                      rfl

theorem cell23_5525745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 7].length) (baseStart_5525745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525745 prefixEnd_5525745 := by exact prefixLift 5525745
  have htrace : WordTrace (prefixWord ++ tailWord_5525745) baseStart_5525745 baseEnd_5525745 := by
    simpa [prefixWord, tailWord_5525745, baseEnd_5525745] using wordTrace_append hprefix tailTrace_5525745
  have hstable : (prefixWord ++ tailWord_5525745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525745).length < 2 ^ (prefixWord ++ tailWord_5525745).sum := by decide
  have hdescent : baseEnd_5525745 < baseStart_5525745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525752 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 2, 5, 2]
def baseStart_5525752 : Nat := 118140960795 + 5525752 * 2 ^ 59
def prefixEnd_5525752 : Nat := 4983230072969 + 3 ^ 40 * 5525752 * 2
def baseEnd_5525752 : Nat := 2837366753543169703587535

theorem tailTrace_5525752 : CollatzResearch.WordTrace tailWord_5525752 prefixEnd_5525752 2837366753543169703587535 := by
  unfold tailWord_5525752
  simp only [CollatzResearch.WordTrace]
  refine ⟨100770366338575851076529755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134360488451434468102039673 100770366338575851076529755)
  ·
    refine ⟨151155549507863776614794633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100770366338575851076529755 151155549507863776614794633)
    ·
      refine ⟨113366662130897832461095975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151155549507863776614794633 113366662130897832461095975)
      ·
        refine ⟨170049993196346748691643963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113366662130897832461095975 170049993196346748691643963)
        ·
          refine ⟨255074989794520123037465945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170049993196346748691643963 255074989794520123037465945)
          ·
            refine ⟨191306242345890092278099459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255074989794520123037465945 191306242345890092278099459)
            ·
              refine ⟨286959363518835138417149189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191306242345890092278099459 286959363518835138417149189)
              ·
                refine ⟨53804880659781588453215473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 286959363518835138417149189 53804880659781588453215473)
                ·
                  refine ⟨40353660494836191339911605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53804880659781588453215473 40353660494836191339911605)
                  ·
                    refine ⟨3783155671390892938116713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40353660494836191339911605 3783155671390892938116713)
                    ·
                      refine ⟨2837366753543169703587535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3783155671390892938116713 2837366753543169703587535)
                      ·
                        rfl

theorem cell23_5525752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 2, 5, 2].length) (baseStart_5525752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525752 prefixEnd_5525752 := by exact prefixLift 5525752
  have htrace : WordTrace (prefixWord ++ tailWord_5525752) baseStart_5525752 baseEnd_5525752 := by
    simpa [prefixWord, tailWord_5525752, baseEnd_5525752] using wordTrace_append hprefix tailTrace_5525752
  have hstable : (prefixWord ++ tailWord_5525752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525752).length < 2 ^ (prefixWord ++ tailWord_5525752).sum := by decide
  have hdescent : baseEnd_5525752 < baseStart_5525752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525789 : List Nat := [1, 4, 2, 3, 2, 1, 1, 1, 1, 2, 5]
def baseStart_5525789 : Nat := 118140960795 + 5525789 * 2 ^ 59
def prefixEnd_5525789 : Nat := 4983230072969 + 3 ^ 40 * 5525789 * 2
def baseEnd_5525789 : Nat := 2837385752327386058824865

theorem tailTrace_5525789 : CollatzResearch.WordTrace tailWord_5525789 prefixEnd_5525789 2837385752327386058824865 := by
  unfold tailWord_5525789
  simp only [CollatzResearch.WordTrace]
  refine ⟨201542082178017657472156421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134361388118678438314770947 201542082178017657472156421)
  ·
    refine ⟨37789140408378310776029329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201542082178017657472156421 37789140408378310776029329)
    ·
      refine ⟨28341855306283733082021997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37789140408378310776029329 28341855306283733082021997)
      ·
        refine ⟨10628195739856399905758249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28341855306283733082021997 10628195739856399905758249)
        ·
          refine ⟨7971146804892299929318687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10628195739856399905758249 7971146804892299929318687)
          ·
            refine ⟨11956720207338449893978031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7971146804892299929318687 11956720207338449893978031)
            ·
              refine ⟨17935080311007674840967047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11956720207338449893978031 17935080311007674840967047)
              ·
                refine ⟨26902620466511512261450571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17935080311007674840967047 26902620466511512261450571)
                ·
                  refine ⟨40353930699767268392175857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26902620466511512261450571 40353930699767268392175857)
                  ·
                    refine ⟨30265448024825451294131893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40353930699767268392175857 30265448024825451294131893)
                    ·
                      refine ⟨2837385752327386058824865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30265448024825451294131893 2837385752327386058824865)
                      ·
                        rfl

theorem cell23_5525789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_5525789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525789 prefixEnd_5525789 := by exact prefixLift 5525789
  have htrace : WordTrace (prefixWord ++ tailWord_5525789) baseStart_5525789 baseEnd_5525789 := by
    simpa [prefixWord, tailWord_5525789, baseEnd_5525789] using wordTrace_append hprefix tailTrace_5525789
  have hstable : (prefixWord ++ tailWord_5525789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525789).length < 2 ^ (prefixWord ++ tailWord_5525789).sum := by decide
  have hdescent : baseEnd_5525789 < baseStart_5525789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525849 : List Nat := [1, 2, 1, 2, 2, 2, 1, 5, 3, 1, 3]
def baseStart_5525849 : Nat := 118140960795 + 5525849 * 2 ^ 59
def prefixEnd_5525849 : Nat := 4983230072969 + 3 ^ 40 * 5525849 * 2
def baseEnd_5525849 : Nat := 2837416561166655824074589

theorem tailTrace_5525849 : CollatzResearch.WordTrace tailWord_5525849 prefixEnd_5525849 2837416561166655824074589 := by
  unfold tailWord_5525849
  simp only [CollatzResearch.WordTrace]
  refine ⟨201544270557800287719340601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134362847038533525146227067 201544270557800287719340601)
  ·
    refine ⟨151158202918350215789505451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201544270557800287719340601 151158202918350215789505451)
    ·
      refine ⟨226737304377525323684258177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151158202918350215789505451 226737304377525323684258177)
      ·
        refine ⟨170052978283143992763193633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226737304377525323684258177 170052978283143992763193633)
        ·
          refine ⟨127539733712357994572395225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170052978283143992763193633 127539733712357994572395225)
          ·
            refine ⟨95654800284268495929296419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127539733712357994572395225 95654800284268495929296419)
            ·
              refine ⟨143482200426402743893944629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95654800284268495929296419 143482200426402743893944629)
              ·
                refine ⟨13451456289975257240057309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 143482200426402743893944629 13451456289975257240057309)
                ·
                  refine ⟨5044296108740721465021491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13451456289975257240057309 5044296108740721465021491)
                  ·
                    refine ⟨7566444163111082197532237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5044296108740721465021491 7566444163111082197532237)
                    ·
                      refine ⟨2837416561166655824074589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7566444163111082197532237 2837416561166655824074589)
                      ·
                        rfl

theorem cell23_5525849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 3, 1, 3].length) (baseStart_5525849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525849 prefixEnd_5525849 := by exact prefixLift 5525849
  have htrace : WordTrace (prefixWord ++ tailWord_5525849) baseStart_5525849 baseEnd_5525849 := by
    simpa [prefixWord, tailWord_5525849, baseEnd_5525849] using wordTrace_append hprefix tailTrace_5525849
  have hstable : (prefixWord ++ tailWord_5525849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525849).length < 2 ^ (prefixWord ++ tailWord_5525849).sum := by decide
  have hdescent : baseEnd_5525849 < baseStart_5525849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525859 : List Nat := [1, 1, 1, 5, 2, 1, 2, 2, 1, 5, 2]
def baseStart_5525859 : Nat := 118140960795 + 5525859 * 2 ^ 59
def prefixEnd_5525859 : Nat := 4983230072969 + 3 ^ 40 * 5525859 * 2
def baseEnd_5525859 : Nat := 2837421695973200784949543

theorem tailTrace_5525859 : CollatzResearch.WordTrace tailWord_5525859 prefixEnd_5525859 2837421695973200784949543 := by
  unfold tailWord_5525859
  simp only [CollatzResearch.WordTrace]
  refine ⟨201544635287764059427204631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134363090191842706284803087 201544635287764059427204631)
  ·
    refine ⟨302316952931646089140806947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201544635287764059427204631 302316952931646089140806947)
    ·
      refine ⟨453475429397469133711210421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302316952931646089140806947 453475429397469133711210421)
      ·
        refine ⟨42513321506012731285425977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 453475429397469133711210421 42513321506012731285425977)
        ·
          refine ⟨31884991129509548464069483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42513321506012731285425977 31884991129509548464069483)
          ·
            refine ⟨47827486694264322696104225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31884991129509548464069483 47827486694264322696104225)
            ·
              refine ⟨35870615020698242022078169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47827486694264322696104225 35870615020698242022078169)
              ·
                refine ⟨26902961265523681516558627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35870615020698242022078169 26902961265523681516558627)
                ·
                  refine ⟨40354441898285522274837941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26902961265523681516558627 40354441898285522274837941)
                  ·
                    refine ⟨3783228927964267713266057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40354441898285522274837941 3783228927964267713266057)
                    ·
                      refine ⟨2837421695973200784949543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3783228927964267713266057 2837421695973200784949543)
                      ·
                        rfl

theorem cell23_5525859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_5525859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525859 prefixEnd_5525859 := by exact prefixLift 5525859
  have htrace : WordTrace (prefixWord ++ tailWord_5525859) baseStart_5525859 baseEnd_5525859 := by
    simpa [prefixWord, tailWord_5525859, baseEnd_5525859] using wordTrace_append hprefix tailTrace_5525859
  have hstable : (prefixWord ++ tailWord_5525859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525859).length < 2 ^ (prefixWord ++ tailWord_5525859).sum := by decide
  have hdescent : baseEnd_5525859 < baseStart_5525859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525866 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 5, 1, 3]
def baseStart_5525866 : Nat := 118140960795 + 5525866 * 2 ^ 59
def prefixEnd_5525866 : Nat := 4983230072969 + 3 ^ 40 * 5525866 * 2
def baseEnd_5525866 : Nat := 2837425290337782257562011

theorem tailTrace_5525866 : CollatzResearch.WordTrace tailWord_5525866 prefixEnd_5525866 2837425290337782257562011 := by
  unfold tailWord_5525866
  simp only [CollatzResearch.WordTrace]
  refine ⟨50386222649684674905677363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134363260399159133081806301 50386222649684674905677363)
  ·
    refine ⟨75579333974527012358516045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50386222649684674905677363 75579333974527012358516045)
    ·
      refine ⟨28342250240447629634443517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75579333974527012358516045 28342250240447629634443517)
      ·
        refine ⟨10628343840167861112916319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28342250240447629634443517 10628343840167861112916319)
        ·
          refine ⟨15942515760251791669374479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10628343840167861112916319 15942515760251791669374479)
          ·
            refine ⟨23913773640377687504061719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15942515760251791669374479 23913773640377687504061719)
            ·
              refine ⟨35870660460566531256092579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23913773640377687504061719 35870660460566531256092579)
              ·
                refine ⟨53805990690849796884138869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35870660460566531256092579 53805990690849796884138869)
                ·
                  refine ⟨5044311627267168457888019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53805990690849796884138869 5044311627267168457888019)
                  ·
                    refine ⟨7566467440900752686832029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5044311627267168457888019 7566467440900752686832029)
                    ·
                      refine ⟨2837425290337782257562011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7566467440900752686832029 2837425290337782257562011)
                      ·
                        rfl

theorem cell23_5525866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_5525866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525866 prefixEnd_5525866 := by exact prefixLift 5525866
  have htrace : WordTrace (prefixWord ++ tailWord_5525866) baseStart_5525866 baseEnd_5525866 := by
    simpa [prefixWord, tailWord_5525866, baseEnd_5525866] using wordTrace_append hprefix tailTrace_5525866
  have hstable : (prefixWord ++ tailWord_5525866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525866).length < 2 ^ (prefixWord ++ tailWord_5525866).sum := by decide
  have hdescent : baseEnd_5525866 < baseStart_5525866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525869 : List Nat := [1, 5, 1, 1, 1, 2, 2, 4, 1, 5]
def baseStart_5525869 : Nat := 118140960795 + 5525869 * 2 ^ 59
def prefixEnd_5525869 : Nat := 4983230072969 + 3 ^ 40 * 5525869 * 2
def baseEnd_5525869 : Nat := 945808943593248581941499

theorem tailTrace_5525869 : CollatzResearch.WordTrace tailWord_5525869 prefixEnd_5525869 945808943593248581941499 := by
  unfold tailWord_5525869
  simp only [CollatzResearch.WordTrace]
  refine ⟨201545000017727831135068661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134363333345151887423379107 201545000017727831135068661)
  ·
    refine ⟨18894843751661984168912687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 201545000017727831135068661 18894843751661984168912687)
    ·
      refine ⟨28342265627492976253369031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18894843751661984168912687 28342265627492976253369031)
      ·
        refine ⟨42513398441239464380053547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28342265627492976253369031 42513398441239464380053547)
        ·
          refine ⟨63770097661859196570080321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42513398441239464380053547 63770097661859196570080321)
          ·
            refine ⟨47827573246394397427560241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63770097661859196570080321 47827573246394397427560241)
            ·
              refine ⟨35870679934795798070670181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47827573246394397427560241 35870679934795798070670181)
              ·
                refine ⟨6725752487774212138250659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35870679934795798070670181 6725752487774212138250659)
                ·
                  refine ⟨10088628731661318207375989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6725752487774212138250659 10088628731661318207375989)
                  ·
                    refine ⟨945808943593248581941499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10088628731661318207375989 945808943593248581941499)
                    ·
                      rfl

theorem cell23_5525869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_5525869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525869 prefixEnd_5525869 := by exact prefixLift 5525869
  have htrace : WordTrace (prefixWord ++ tailWord_5525869) baseStart_5525869 baseEnd_5525869 := by
    simpa [prefixWord, tailWord_5525869, baseEnd_5525869] using wordTrace_append hprefix tailTrace_5525869
  have hstable : (prefixWord ++ tailWord_5525869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525869).length < 2 ^ (prefixWord ++ tailWord_5525869).sum := by decide
  have hdescent : baseEnd_5525869 < baseStart_5525869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525883 : List Nat := [1, 1, 1, 1, 1, 8, 2, 3, 1, 1, 3]
def baseStart_5525883 : Nat := 118140960795 + 5525883 * 2 ^ 59
def prefixEnd_5525883 : Nat := 4983230072969 + 3 ^ 40 * 5525883 * 2
def baseEnd_5525883 : Nat := 2837434019508908691049433

theorem tailTrace_5525883 : CollatzResearch.WordTrace tailWord_5525883 prefixEnd_5525883 2837434019508908691049433 := by
  unfold tailWord_5525883
  simp only [CollatzResearch.WordTrace]
  refine ⟨201545510639677111526078303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134363673759784741017385535 201545510639677111526078303)
  ·
    refine ⟨302318265959515667289117455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201545510639677111526078303 302318265959515667289117455)
    ·
      refine ⟨453477398939273500933676183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302318265959515667289117455 453477398939273500933676183)
      ·
        refine ⟨680216098408910251400514275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 453477398939273500933676183 680216098408910251400514275)
        ·
          refine ⟨1020324147613365377100771413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 680216098408910251400514275 1020324147613365377100771413)
          ·
            refine ⟨11956923604844125512899665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1020324147613365377100771413 11956923604844125512899665)
            ·
              refine ⟨8967692703633094134674749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11956923604844125512899665 8967692703633094134674749)
              ·
                refine ⟨3362884763862410300503031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8967692703633094134674749 3362884763862410300503031)
                ·
                  refine ⟨5044327145793615450754547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3362884763862410300503031 5044327145793615450754547)
                  ·
                    refine ⟨7566490718690423176131821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5044327145793615450754547 7566490718690423176131821)
                    ·
                      refine ⟨2837434019508908691049433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7566490718690423176131821 2837434019508908691049433)
                      ·
                        rfl

theorem cell23_5525883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 3, 1, 1, 3].length) (baseStart_5525883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525883 prefixEnd_5525883 := by exact prefixLift 5525883
  have htrace : WordTrace (prefixWord ++ tailWord_5525883) baseStart_5525883 baseEnd_5525883 := by
    simpa [prefixWord, tailWord_5525883, baseEnd_5525883] using wordTrace_append hprefix tailTrace_5525883
  have hstable : (prefixWord ++ tailWord_5525883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525883).length < 2 ^ (prefixWord ++ tailWord_5525883).sum := by decide
  have hdescent : baseEnd_5525883 < baseStart_5525883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525890 : List Nat := [3, 4, 2, 1, 3, 1, 1, 2, 6]
def baseStart_5525890 : Nat := 118140960795 + 5525890 * 2 ^ 59
def prefixEnd_5525890 : Nat := 4983230072969 + 3 ^ 40 * 5525890 * 2
def baseEnd_5525890 : Nat := 315270845985943351517989

theorem tailTrace_5525890 : CollatzResearch.WordTrace tailWord_5525890 prefixEnd_5525890 315270845985943351517989 := by
  unfold tailWord_5525890
  simp only [CollatzResearch.WordTrace]
  refine ⟨50386441487662937930395781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134363843967101167814388749 50386441487662937930395781)
  ·
    refine ⟨9447457778936800861949209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50386441487662937930395781 9447457778936800861949209)
    ·
      refine ⟨7085593334202600646461907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9447457778936800861949209 7085593334202600646461907)
      ·
        refine ⟨10628390001303900969692861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7085593334202600646461907 10628390001303900969692861)
        ·
          refine ⟨3985646250488962863634823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10628390001303900969692861 3985646250488962863634823)
          ·
            refine ⟨5978469375733444295452235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3985646250488962863634823 5978469375733444295452235)
            ·
              refine ⟨8967704063600166443178353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5978469375733444295452235 8967704063600166443178353)
              ·
                refine ⟨6725778047700124832383765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8967704063600166443178353 6725778047700124832383765)
                ·
                  refine ⟨315270845985943351517989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6725778047700124832383765 315270845985943351517989)
                  ·
                    rfl

theorem cell23_5525890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_5525890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525890 prefixEnd_5525890 := by exact prefixLift 5525890
  have htrace : WordTrace (prefixWord ++ tailWord_5525890) baseStart_5525890 baseEnd_5525890 := by
    simpa [prefixWord, tailWord_5525890, baseEnd_5525890] using wordTrace_append hprefix tailTrace_5525890
  have hstable : (prefixWord ++ tailWord_5525890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525890).length < 2 ^ (prefixWord ++ tailWord_5525890).sum := by decide
  have hdescent : baseEnd_5525890 < baseStart_5525890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525899 : List Nat := [1, 1, 1, 1, 4, 5, 1, 1, 4, 4]
def baseStart_5525899 : Nat := 118140960795 + 5525899 * 2 ^ 59
def prefixEnd_5525899 : Nat := 4983230072969 + 3 ^ 40 * 5525899 * 2
def baseEnd_5525899 : Nat := 945814078399793542816453

theorem tailTrace_5525899 : CollatzResearch.WordTrace tailWord_5525899 prefixEnd_5525899 945814078399793542816453 := by
  unfold tailWord_5525899
  simp only [CollatzResearch.WordTrace]
  refine ⟨201546094207619146258660751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134364062805079430839107167 201546094207619146258660751)
  ·
    refine ⟨302319141311428719387991127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201546094207619146258660751 302319141311428719387991127)
    ·
      refine ⟨453478711967143079081986691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302319141311428719387991127 453478711967143079081986691)
      ·
        refine ⟨680218067950714618622980037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 453478711967143079081986691 680218067950714618622980037)
        ·
          refine ⟨127540887740758990991808757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 680218067950714618622980037 127540887740758990991808757)
          ·
            refine ⟨11956958225696155405482071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 127540887740758990991808757 11956958225696155405482071)
            ·
              refine ⟨17935437338544233108223107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11956958225696155405482071 17935437338544233108223107)
              ·
                refine ⟨26903156007816349662334661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17935437338544233108223107 26903156007816349662334661)
                ·
                  refine ⟨5044341751465565561687749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26903156007816349662334661 5044341751465565561687749)
                  ·
                    refine ⟨945814078399793542816453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5044341751465565561687749 945814078399793542816453)
                    ·
                      rfl

theorem cell23_5525899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 4, 4].length) (baseStart_5525899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525899 prefixEnd_5525899 := by exact prefixLift 5525899
  have htrace : WordTrace (prefixWord ++ tailWord_5525899) baseStart_5525899 baseEnd_5525899 := by
    simpa [prefixWord, tailWord_5525899, baseEnd_5525899] using wordTrace_append hprefix tailTrace_5525899
  have hstable : (prefixWord ++ tailWord_5525899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525899).length < 2 ^ (prefixWord ++ tailWord_5525899).sum := by decide
  have hdescent : baseEnd_5525899 < baseStart_5525899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525952 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 5]
def baseStart_5525952 : Nat := 118140960795 + 5525952 * 2 ^ 59
def prefixEnd_5525952 : Nat := 4983230072969 + 3 ^ 40 * 5525952 * 2
def baseEnd_5525952 : Nat := 2837469449674068921086615

theorem tailTrace_5525952 : CollatzResearch.WordTrace tailWord_5525952 prefixEnd_5525952 2837469449674068921086615 := by
  unfold tailWord_5525952
  simp only [CollatzResearch.WordTrace]
  refine ⟨100774013638213568155170055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134365351517618090873560073 100774013638213568155170055)
  ·
    refine ⟨151161020457320352232755083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100774013638213568155170055 151161020457320352232755083)
    ·
      refine ⟨226741530685980528349132625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151161020457320352232755083 226741530685980528349132625)
      ·
        refine ⟨170056148014485396261849469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226741530685980528349132625 170056148014485396261849469)
        ·
          refine ⟨63771055505432023598193551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170056148014485396261849469 63771055505432023598193551)
          ·
            refine ⟨95656583258148035397290327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63771055505432023598193551 95656583258148035397290327)
            ·
              refine ⟨143484874887222053095935491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95656583258148035397290327 143484874887222053095935491)
              ·
                refine ⟨215227312330833079643903237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143484874887222053095935491 215227312330833079643903237)
                ·
                  refine ⟨40355121062031202433231857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 215227312330833079643903237 40355121062031202433231857)
                  ·
                    refine ⟨30266340796523401824923893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40355121062031202433231857 30266340796523401824923893)
                    ·
                      refine ⟨2837469449674068921086615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30266340796523401824923893 2837469449674068921086615)
                      ·
                        rfl

theorem cell23_5525952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_5525952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525952 prefixEnd_5525952 := by exact prefixLift 5525952
  have htrace : WordTrace (prefixWord ++ tailWord_5525952) baseStart_5525952 baseEnd_5525952 := by
    simpa [prefixWord, tailWord_5525952, baseEnd_5525952] using wordTrace_append hprefix tailTrace_5525952
  have hstable : (prefixWord ++ tailWord_5525952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525952).length < 2 ^ (prefixWord ++ tailWord_5525952).sum := by decide
  have hdescent : baseEnd_5525952 < baseStart_5525952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525966 : List Nat := [4, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2]
def baseStart_5525966 : Nat := 118140960795 + 5525966 * 2 ^ 59
def prefixEnd_5525966 : Nat := 4983230072969 + 3 ^ 40 * 5525966 * 2
def baseEnd_5525966 : Nat := 2837476638403231866311551

theorem tailTrace_5525966 : CollatzResearch.WordTrace tailWord_5525966 prefixEnd_5525966 2837476638403231866311551 := by
  unfold tailWord_5525966
  simp only [CollatzResearch.WordTrace]
  refine ⟨25193567237297052087668719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134365691932250944467566501 25193567237297052087668719)
  ·
    refine ⟨37790350855945578131503079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25193567237297052087668719 37790350855945578131503079)
    ·
      refine ⟨56685526283918367197254619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37790350855945578131503079 56685526283918367197254619)
      ·
        refine ⟨85028289425877550795881929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56685526283918367197254619 85028289425877550795881929)
        ·
          refine ⟨63771217069408163096911447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85028289425877550795881929 63771217069408163096911447)
          ·
            refine ⟨95656825604112244645367171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63771217069408163096911447 95656825604112244645367171)
            ·
              refine ⟨143485238406168366968050757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95656825604112244645367171 143485238406168366968050757)
              ·
                refine ⟨26903482201156568806509517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 143485238406168366968050757 26903482201156568806509517)
                ·
                  refine ⟨10088805825433713302441069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26903482201156568806509517 10088805825433713302441069)
                  ·
                    refine ⟨3783302184537642488415401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10088805825433713302441069 3783302184537642488415401)
                    ·
                      refine ⟨2837476638403231866311551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3783302184537642488415401 2837476638403231866311551)
                      ·
                        rfl

theorem cell23_5525966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2].length) (baseStart_5525966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525966 prefixEnd_5525966 := by exact prefixLift 5525966
  have htrace : WordTrace (prefixWord ++ tailWord_5525966) baseStart_5525966 baseEnd_5525966 := by
    simpa [prefixWord, tailWord_5525966, baseEnd_5525966] using wordTrace_append hprefix tailTrace_5525966
  have hstable : (prefixWord ++ tailWord_5525966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525966).length < 2 ^ (prefixWord ++ tailWord_5525966).sum := by decide
  have hdescent : baseEnd_5525966 < baseStart_5525966 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525973 : List Nat := [1, 3, 2, 3, 1, 3, 1, 3, 2, 1, 3]
def baseStart_5525973 : Nat := 118140960795 + 5525973 * 2 ^ 59
def prefixEnd_5525973 : Nat := 4983230072969 + 3 ^ 40 * 5525973 * 2
def baseEnd_5525973 : Nat := 2837480232767813338924019

theorem tailTrace_5525973 : CollatzResearch.WordTrace tailWord_5525973 prefixEnd_5525973 2837480232767813338924019 := by
  unfold tailWord_5525973
  simp only [CollatzResearch.WordTrace]
  refine ⟨201548793209351056896854573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134365862139567371264569715 201548793209351056896854573)
  ·
    refine ⟨75580797453506646336320465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201548793209351056896854573 75580797453506646336320465)
    ·
      refine ⟨56685598090129984752240349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75580797453506646336320465 56685598090129984752240349)
      ·
        refine ⟨21257099283798744282090131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56685598090129984752240349 21257099283798744282090131)
        ·
          refine ⟨31885648925698116423135197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21257099283798744282090131 31885648925698116423135197)
          ·
            refine ⟨11957118347136793658675699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31885648925698116423135197 11957118347136793658675699)
            ·
              refine ⟨17935677520705190488013549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11957118347136793658675699 17935677520705190488013549)
              ·
                refine ⟨6725879070264446433005081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17935677520705190488013549 6725879070264446433005081)
                ·
                  refine ⟨5044409302698334824753811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6725879070264446433005081 5044409302698334824753811)
                  ·
                    refine ⟨7566613954047502237130717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5044409302698334824753811 7566613954047502237130717)
                    ·
                      refine ⟨2837480232767813338924019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7566613954047502237130717 2837480232767813338924019)
                      ·
                        rfl

theorem cell23_5525973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_5525973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525973 prefixEnd_5525973 := by exact prefixLift 5525973
  have htrace : WordTrace (prefixWord ++ tailWord_5525973) baseStart_5525973 baseEnd_5525973 := by
    simpa [prefixWord, tailWord_5525973, baseEnd_5525973] using wordTrace_append hprefix tailTrace_5525973
  have hstable : (prefixWord ++ tailWord_5525973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525973).length < 2 ^ (prefixWord ++ tailWord_5525973).sum := by decide
  have hdescent : baseEnd_5525973 < baseStart_5525973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525983 : List Nat := [1, 1, 2, 3, 3, 2, 3, 2, 1, 3, 2]
def baseStart_5525983 : Nat := 118140960795 + 5525983 * 2 ^ 59
def prefixEnd_5525983 : Nat := 4983230072969 + 3 ^ 40 * 5525983 * 2
def baseEnd_5525983 : Nat := 2837485367574358299798973

theorem tailTrace_5525983 : CollatzResearch.WordTrace tailWord_5525983 prefixEnd_5525983 2837485367574358299798973 := by
  unfold tailWord_5525983
  simp only [CollatzResearch.WordTrace]
  refine ⟨201549157939314828604718603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134366105292876552403145735 201549157939314828604718603)
  ·
    refine ⟨302323736908972242907077905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201549157939314828604718603 302323736908972242907077905)
    ·
      refine ⟨226742802681729182180308429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302323736908972242907077905 226742802681729182180308429)
      ·
        refine ⟨85028551005648443317615661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226742802681729182180308429 85028551005648443317615661)
        ·
          refine ⟨31885706627118166244105873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85028551005648443317615661 31885706627118166244105873)
          ·
            refine ⟨23914279970338624683079405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31885706627118166244105873 23914279970338624683079405)
            ·
              refine ⟨8967854988876984256154777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23914279970338624683079405 8967854988876984256154777)
              ·
                refine ⟨6725891241657738192116083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8967854988876984256154777 6725891241657738192116083)
                ·
                  refine ⟨10088836862486607288174125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6725891241657738192116083 10088836862486607288174125)
                  ·
                    refine ⟨3783313823432477733065297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10088836862486607288174125 3783313823432477733065297)
                    ·
                      refine ⟨2837485367574358299798973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3783313823432477733065297 2837485367574358299798973)
                      ·
                        rfl

theorem cell23_5525983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 3, 2].length) (baseStart_5525983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525983 prefixEnd_5525983 := by exact prefixLift 5525983
  have htrace : WordTrace (prefixWord ++ tailWord_5525983) baseStart_5525983 baseEnd_5525983 := by
    simpa [prefixWord, tailWord_5525983, baseEnd_5525983] using wordTrace_append hprefix tailTrace_5525983
  have hstable : (prefixWord ++ tailWord_5525983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525983).length < 2 ^ (prefixWord ++ tailWord_5525983).sum := by decide
  have hdescent : baseEnd_5525983 < baseStart_5525983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5525996 : List Nat := [2, 2, 1, 1, 2, 1, 5, 2, 1, 4, 2]
def baseStart_5525996 : Nat := 118140960795 + 5525996 * 2 ^ 59
def prefixEnd_5525996 : Nat := 4983230072969 + 3 ^ 40 * 5525996 * 2
def baseEnd_5525996 : Nat := 2837492042822866748936413

theorem tailTrace_5525996 : CollatzResearch.WordTrace tailWord_5525996 prefixEnd_5525996 2837492042822866748936413 := by
  unfold tailWord_5525996
  simp only [CollatzResearch.WordTrace]
  refine ⟨100774816044133865912470921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134366421392178487883294561 100774816044133865912470921)
  ·
    refine ⟨75581112033100399434353191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100774816044133865912470921 75581112033100399434353191)
    ·
      refine ⟨113371668049650599151529787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75581112033100399434353191 113371668049650599151529787)
      ·
        refine ⟨170057502074475898727294681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113371668049650599151529787 170057502074475898727294681)
        ·
          refine ⟨127543126555856924045471011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170057502074475898727294681 127543126555856924045471011)
          ·
            refine ⟨191314689833785386068206517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127543126555856924045471011 191314689833785386068206517)
            ·
              refine ⟨17935752171917379943894361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 191314689833785386068206517 17935752171917379943894361)
              ·
                refine ⟨13451814128938034957920771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17935752171917379943894361 13451814128938034957920771)
                ·
                  refine ⟨20177721193407052436881157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13451814128938034957920771 20177721193407052436881157)
                  ·
                    refine ⟨3783322723763822331915217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20177721193407052436881157 3783322723763822331915217)
                    ·
                      refine ⟨2837492042822866748936413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3783322723763822331915217 2837492042822866748936413)
                      ·
                        rfl

theorem cell23_5525996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 4, 2].length) (baseStart_5525996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5525996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5525996 prefixEnd_5525996 := by exact prefixLift 5525996
  have htrace : WordTrace (prefixWord ++ tailWord_5525996) baseStart_5525996 baseEnd_5525996 := by
    simpa [prefixWord, tailWord_5525996, baseEnd_5525996] using wordTrace_append hprefix tailTrace_5525996
  have hstable : (prefixWord ++ tailWord_5525996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5525996).length < 2 ^ (prefixWord ++ tailWord_5525996).sum := by decide
  have hdescent : baseEnd_5525996 < baseStart_5525996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5525996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526030 : List Nat := [4, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2]
def baseStart_5526030 : Nat := 118140960795 + 5526030 * 2 ^ 59
def prefixEnd_5526030 : Nat := 4983230072969 + 3 ^ 40 * 5526030 * 2
def baseEnd_5526030 : Nat := 2837509501165119615911257

theorem tailTrace_5526030 : CollatzResearch.WordTrace tailWord_5526030 prefixEnd_5526030 2837509501165119615911257 := by
  unfold tailWord_5526030
  simp only [CollatzResearch.WordTrace]
  refine ⟨25193859021268069453959943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134367248113429703754453029 25193859021268069453959943)
  ·
    refine ⟨37790788531902104180939915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25193859021268069453959943 37790788531902104180939915)
    ·
      refine ⟨56686182797853156271409873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37790788531902104180939915 56686182797853156271409873)
      ·
        refine ⟨42514637098389867203557405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56686182797853156271409873 42514637098389867203557405)
        ·
          refine ⟨15942988911896200201334027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42514637098389867203557405 15942988911896200201334027)
          ·
            refine ⟨23914483367844300302001041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15942988911896200201334027 23914483367844300302001041)
            ·
              refine ⟨17935862525883225226500781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23914483367844300302001041 17935862525883225226500781)
              ·
                refine ⟨6725948447206209459937793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17935862525883225226500781 6725948447206209459937793)
                ·
                  refine ⟨5044461335404657094953345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6725948447206209459937793 5044461335404657094953345)
                  ·
                    refine ⟨3783346001553492821215009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5044461335404657094953345 3783346001553492821215009)
                    ·
                      refine ⟨2837509501165119615911257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3783346001553492821215009 2837509501165119615911257)
                      ·
                        rfl

theorem cell23_5526030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_5526030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526030 prefixEnd_5526030 := by exact prefixLift 5526030
  have htrace : WordTrace (prefixWord ++ tailWord_5526030) baseStart_5526030 baseEnd_5526030 := by
    simpa [prefixWord, tailWord_5526030, baseEnd_5526030] using wordTrace_append hprefix tailTrace_5526030
  have hstable : (prefixWord ++ tailWord_5526030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526030).length < 2 ^ (prefixWord ++ tailWord_5526030).sum := by decide
  have hdescent : baseEnd_5526030 < baseStart_5526030 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526032 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 2, 11]
def baseStart_5526032 : Nat := 118140960795 + 5526032 * 2 ^ 59
def prefixEnd_5526032 : Nat := 4983230072969 + 3 ^ 40 * 5526032 * 2
def baseEnd_5526032 : Nat := 945836842708809536028749

theorem tailTrace_5526032 : CollatzResearch.WordTrace tailWord_5526032 prefixEnd_5526032 945836842708809536028749 := by
  unfold tailWord_5526032
  simp only [CollatzResearch.WordTrace]
  refine ⟨100775472558068654986626175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134367296744091539982168233 100775472558068654986626175)
  ·
    refine ⟨151163208837102982479939263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100775472558068654986626175 151163208837102982479939263)
    ·
      refine ⟨226744813255654473719908895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151163208837102982479939263 226744813255654473719908895)
      ·
        refine ⟨340117219883481710579863343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226744813255654473719908895 340117219883481710579863343)
        ·
          refine ⟨510175829825222565869795015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340117219883481710579863343 510175829825222565869795015)
          ·
            refine ⟨765263744737833848804692523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510175829825222565869795015 765263744737833848804692523)
            ·
              refine ⟨1147895617106750773207038785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 765263744737833848804692523 1147895617106750773207038785)
              ·
                refine ⟨860921712830063079905279089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1147895617106750773207038785 860921712830063079905279089)
                ·
                  refine ⟨645691284622547309928959317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 860921712830063079905279089 645691284622547309928959317)
                  ·
                    refine ⟨945836842708809536028749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 645691284622547309928959317 945836842708809536028749)
                    ·
                      rfl

theorem cell23_5526032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 11].length) (baseStart_5526032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526032 prefixEnd_5526032 := by exact prefixLift 5526032
  have htrace : WordTrace (prefixWord ++ tailWord_5526032) baseStart_5526032 baseEnd_5526032 := by
    simpa [prefixWord, tailWord_5526032, baseEnd_5526032] using wordTrace_append hprefix tailTrace_5526032
  have hstable : (prefixWord ++ tailWord_5526032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526032).length < 2 ^ (prefixWord ++ tailWord_5526032).sum := by decide
  have hdescent : baseEnd_5526032 < baseStart_5526032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526036 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 9]
def baseStart_5526036 : Nat := 118140960795 + 5526036 * 2 ^ 59
def prefixEnd_5526036 : Nat := 4983230072969 + 3 ^ 40 * 5526036 * 2
def baseEnd_5526036 : Nat := 315279175783227399159581

theorem tailTrace_5526036 : CollatzResearch.WordTrace tailWord_5526036 prefixEnd_5526036 315279175783227399159581 := by
  unfold tailWord_5526036
  simp only [CollatzResearch.WordTrace]
  refine ⟨100775545504061409328198981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134367394005415212437598641 100775545504061409328198981)
  ·
    refine ⟨18895414782011514249037309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100775545504061409328198981 18895414782011514249037309)
    ·
      refine ⟨7085780543254317843388991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18895414782011514249037309 7085780543254317843388991)
      ·
        refine ⟨10628670814881476765083487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7085780543254317843388991 10628670814881476765083487)
        ·
          refine ⟨15943006222322215147625231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10628670814881476765083487 15943006222322215147625231)
          ·
            refine ⟨23914509333483322721437847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15943006222322215147625231 23914509333483322721437847)
            ·
              refine ⟨35871764000224984082156771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23914509333483322721437847 35871764000224984082156771)
              ·
                refine ⟨53807646000337476123235157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35871764000224984082156771 53807646000337476123235157)
                ·
                  refine ⟨315279175783227399159581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53807646000337476123235157 315279175783227399159581)
                  ·
                    rfl

theorem cell23_5526036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_5526036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526036 prefixEnd_5526036 := by exact prefixLift 5526036
  have htrace : WordTrace (prefixWord ++ tailWord_5526036) baseStart_5526036 baseEnd_5526036 := by
    simpa [prefixWord, tailWord_5526036, baseEnd_5526036] using wordTrace_append hprefix tailTrace_5526036
  have hstable : (prefixWord ++ tailWord_5526036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526036).length < 2 ^ (prefixWord ++ tailWord_5526036).sum := by decide
  have hdescent : baseEnd_5526036 < baseStart_5526036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526049 : List Nat := [1, 2, 3, 2, 2, 1, 3, 1, 1, 7]
def baseStart_5526049 : Nat := 118140960795 + 5526049 * 2 ^ 59
def prefixEnd_5526049 : Nat := 4983230072969 + 3 ^ 40 * 5526049 * 2
def baseEnd_5526049 : Nat := 945839752432518347191223

theorem tailTrace_5526049 : CollatzResearch.WordTrace tailWord_5526049 prefixEnd_5526049 945839752432518347191223 := by
  unfold tailWord_5526049
  simp only [CollatzResearch.WordTrace]
  refine ⟨201551565157075721876621201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134367710104717147917747467 201551565157075721876621201)
  ·
    refine ⟨151163673867806791407465901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201551565157075721876621201 151163673867806791407465901)
    ·
      refine ⟨56686377700427546777799713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151163673867806791407465901 56686377700427546777799713)
      ·
        refine ⟨42514783275320660083349785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56686377700427546777799713 42514783275320660083349785)
        ·
          refine ⟨31886087456490495062512339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42514783275320660083349785 31886087456490495062512339)
          ·
            refine ⟨47829131184735742593768509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31886087456490495062512339 47829131184735742593768509)
            ·
              refine ⟨17935924194275903472663191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47829131184735742593768509 17935924194275903472663191)
              ·
                refine ⟨26903886291413855208994787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17935924194275903472663191 26903886291413855208994787)
                ·
                  refine ⟨40355829437120782813492181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26903886291413855208994787 40355829437120782813492181)
                  ·
                    refine ⟨945839752432518347191223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40355829437120782813492181 945839752432518347191223)
                    ·
                      rfl

theorem cell23_5526049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_5526049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526049 prefixEnd_5526049 := by exact prefixLift 5526049
  have htrace : WordTrace (prefixWord ++ tailWord_5526049) baseStart_5526049 baseEnd_5526049 := by
    simpa [prefixWord, tailWord_5526049, baseEnd_5526049] using wordTrace_append hprefix tailTrace_5526049
  have hstable : (prefixWord ++ tailWord_5526049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526049).length < 2 ^ (prefixWord ++ tailWord_5526049).sum := by decide
  have hdescent : baseEnd_5526049 < baseStart_5526049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526126 : List Nat := [4, 1, 2, 2, 2, 1, 2, 1, 8]
def baseStart_5526126 : Nat := 118140960795 + 5526126 * 2 ^ 59
def prefixEnd_5526126 : Nat := 4983230072969 + 3 ^ 40 * 5526126 * 2
def baseEnd_5526126 : Nat := 315284310589772360034535

theorem tailTrace_5526126 : CollatzResearch.WordTrace tailWord_5526126 prefixEnd_5526126 315284310589772360034535 := by
  unfold tailWord_5526126
  simp only [CollatzResearch.WordTrace]
  refine ⟨25194296697224595503396779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134369582385197842684782821 25194296697224595503396779)
  ·
    refine ⟨37791445045836893255095169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25194296697224595503396779 37791445045836893255095169)
    ·
      refine ⟨28343583784377669941321377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37791445045836893255095169 28343583784377669941321377)
      ·
        refine ⟨21257687838283252455991033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28343583784377669941321377 21257687838283252455991033)
        ·
          refine ⟨15943265878712439341993275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21257687838283252455991033 15943265878712439341993275)
          ·
            refine ⟨23914898818068659012989913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15943265878712439341993275 23914898818068659012989913)
            ·
              refine ⟨17936174113551494259742435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23914898818068659012989913 17936174113551494259742435)
              ·
                refine ⟨26904261170327241389613653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17936174113551494259742435 26904261170327241389613653)
                ·
                  refine ⟨315284310589772360034535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26904261170327241389613653 315284310589772360034535)
                  ·
                    rfl

theorem cell23_5526126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 8].length) (baseStart_5526126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526126 prefixEnd_5526126 := by exact prefixLift 5526126
  have htrace : WordTrace (prefixWord ++ tailWord_5526126) baseStart_5526126 baseEnd_5526126 := by
    simpa [prefixWord, tailWord_5526126, baseEnd_5526126] using wordTrace_append hprefix tailTrace_5526126
  have hstable : (prefixWord ++ tailWord_5526126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526126).length < 2 ^ (prefixWord ++ tailWord_5526126).sum := by decide
  have hdescent : baseEnd_5526126 < baseStart_5526126 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526130 : List Nat := [3, 2, 1, 2, 4, 2, 1, 1, 3, 4]
def baseStart_5526130 : Nat := 118140960795 + 5526130 * 2 ^ 59
def prefixEnd_5526130 : Nat := 4983230072969 + 3 ^ 40 * 5526130 * 2
def baseEnd_5526130 : Nat := 945853616410189741553599

theorem tailTrace_5526130 : CollatzResearch.WordTrace tailWord_5526130 prefixEnd_5526130 945853616410189741553599 := by
  unfold tailWord_5526130
  simp only [CollatzResearch.WordTrace]
  refine ⟨50388629867445568177579961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134369679646521515140213229 50388629867445568177579961)
  ·
    refine ⟨37791472400584176133184971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50388629867445568177579961 37791472400584176133184971)
    ·
      refine ⟨56687208600876264199777457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37791472400584176133184971 56687208600876264199777457)
      ·
        refine ⟨42515406450657198149833093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56687208600876264199777457 42515406450657198149833093)
        ·
          refine ⟨7971638709498224653093705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42515406450657198149833093 7971638709498224653093705)
          ·
            refine ⟨5978729032123668489820279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7971638709498224653093705 5978729032123668489820279)
            ·
              refine ⟨8968093548185502734730419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5978729032123668489820279 8968093548185502734730419)
              ·
                refine ⟨13452140322278254102095629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8968093548185502734730419 13452140322278254102095629)
                ·
                  refine ⟨5044552620854345288285861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13452140322278254102095629 5044552620854345288285861)
                  ·
                    refine ⟨945853616410189741553599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5044552620854345288285861 945853616410189741553599)
                    ·
                      rfl

theorem cell23_5526130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_5526130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526130 prefixEnd_5526130 := by exact prefixLift 5526130
  have htrace : WordTrace (prefixWord ++ tailWord_5526130) baseStart_5526130 baseEnd_5526130 := by
    simpa [prefixWord, tailWord_5526130, baseEnd_5526130] using wordTrace_append hprefix tailTrace_5526130
  have hstable : (prefixWord ++ tailWord_5526130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526130).length < 2 ^ (prefixWord ++ tailWord_5526130).sum := by decide
  have hdescent : baseEnd_5526130 < baseStart_5526130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526156 : List Nat := [2, 2, 1, 2, 1, 1, 2, 6, 1, 5]
def baseStart_5526156 : Nat := 118140960795 + 5526156 * 2 ^ 59
def prefixEnd_5526156 : Nat := 4983230072969 + 3 ^ 40 * 5526156 * 2
def baseEnd_5526156 : Nat := 945858066575862040978559

theorem tailTrace_5526156 : CollatzResearch.WordTrace tailWord_5526156 prefixEnd_5526156 945858066575862040978559 := by
  unfold tailWord_5526156
  simp only [CollatzResearch.WordTrace]
  refine ⟨100777733883844039575383161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134370311845125386100510881 100777733883844039575383161)
  ·
    refine ⟨75583300412883029681537371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100777733883844039575383161 75583300412883029681537371)
    ·
      refine ⟨113374950619324544522306057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75583300412883029681537371 113374950619324544522306057)
      ·
        refine ⟨85031212964493408391729543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113374950619324544522306057 85031212964493408391729543)
        ·
          refine ⟨127546819446740112587594315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85031212964493408391729543 127546819446740112587594315)
          ·
            refine ⟨191320229170110168881391473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127546819446740112587594315 191320229170110168881391473)
            ·
              refine ⟨143490171877582626661043605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191320229170110168881391473 143490171877582626661043605)
              ·
                refine ⟨6726101806761685624736419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 143490171877582626661043605 6726101806761685624736419)
                ·
                  refine ⟨10089152710142528437104629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6726101806761685624736419 10089152710142528437104629)
                  ·
                    refine ⟨945858066575862040978559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10089152710142528437104629 945858066575862040978559)
                    ·
                      rfl

theorem cell23_5526156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 1, 5].length) (baseStart_5526156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526156 prefixEnd_5526156 := by exact prefixLift 5526156
  have htrace : WordTrace (prefixWord ++ tailWord_5526156) baseStart_5526156 baseEnd_5526156 := by
    simpa [prefixWord, tailWord_5526156, baseEnd_5526156] using wordTrace_append hprefix tailTrace_5526156
  have hstable : (prefixWord ++ tailWord_5526156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526156).length < 2 ^ (prefixWord ++ tailWord_5526156).sum := by decide
  have hdescent : baseEnd_5526156 < baseStart_5526156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526159 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 4]
def baseStart_5526159 : Nat := 118140960795 + 5526159 * 2 ^ 59
def prefixEnd_5526159 : Nat := 4983230072969 + 3 ^ 40 * 5526159 * 2
def baseEnd_5526159 : Nat := 2837575740169549611198163

theorem tailTrace_5526159 : CollatzResearch.WordTrace tailWord_5526159 prefixEnd_5526159 2837575740169549611198163 := by
  unfold tailWord_5526159
  simp only [CollatzResearch.WordTrace]
  refine ⟨201555577186677210663125531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134370384791118140442083687 201555577186677210663125531)
  ·
    refine ⟨302333365780015815994688297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201555577186677210663125531 302333365780015815994688297)
    ·
      refine ⟨226750024335011861996016223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302333365780015815994688297 226750024335011861996016223)
      ·
        refine ⟨340125036502517792994024335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226750024335011861996016223 340125036502517792994024335)
        ·
          refine ⟨510187554753776689491036503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340125036502517792994024335 510187554753776689491036503)
          ·
            refine ⟨765281332130665034236554755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510187554753776689491036503 765281332130665034236554755)
            ·
              refine ⟨1147921998195997551354832133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 765281332130665034236554755 1147921998195997551354832133)
              ·
                refine ⟨215235374661749540879031025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1147921998195997551354832133 215235374661749540879031025)
                ·
                  refine ⟨161426530996312155659273269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 215235374661749540879031025 161426530996312155659273269)
                  ·
                    refine ⟨15133737280904264593056869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 161426530996312155659273269 15133737280904264593056869)
                    ·
                      refine ⟨2837575740169549611198163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15133737280904264593056869 2837575740169549611198163)
                      ·
                        rfl

theorem cell23_5526159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 4].length) (baseStart_5526159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526159 prefixEnd_5526159 := by exact prefixLift 5526159
  have htrace : WordTrace (prefixWord ++ tailWord_5526159) baseStart_5526159 baseEnd_5526159 := by
    simpa [prefixWord, tailWord_5526159, baseEnd_5526159] using wordTrace_append hprefix tailTrace_5526159
  have hstable : (prefixWord ++ tailWord_5526159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526159).length < 2 ^ (prefixWord ++ tailWord_5526159).sum := by decide
  have hdescent : baseEnd_5526159 < baseStart_5526159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526214 : List Nat := [6, 1, 2, 1, 2, 1, 1, 1, 1, 5, 2]
def baseStart_5526214 : Nat := 118140960795 + 5526214 * 2 ^ 59
def prefixEnd_5526214 : Nat := 4983230072969 + 3 ^ 40 * 5526214 * 2
def baseEnd_5526214 : Nat := 2837603981605546896010411

theorem tailTrace_5526214 : CollatzResearch.WordTrace tailWord_5526214 prefixEnd_5526214 2837603981605546896010411 := by
  unfold tailWord_5526214
  simp only [CollatzResearch.WordTrace]
  refine ⟨6298674475046186095511803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 134371722134318636704251797 6298674475046186095511803)
  ·
    refine ⟨9448011712569279143267705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6298674475046186095511803 9448011712569279143267705)
    ·
      refine ⟨7086008784426959357450779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9448011712569279143267705 7086008784426959357450779)
      ·
        refine ⟨10629013176640439036176169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7086008784426959357450779 10629013176640439036176169)
        ·
          refine ⟨7971759882480329277132127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10629013176640439036176169 7971759882480329277132127)
          ·
            refine ⟨11957639823720493915698191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7971759882480329277132127 11957639823720493915698191)
            ·
              refine ⟨17936459735580740873547287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11957639823720493915698191 17936459735580740873547287)
              ·
                refine ⟨26904689603371111310320931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17936459735580740873547287 26904689603371111310320931)
                ·
                  refine ⟨40357034405056666965481397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26904689603371111310320931 40357034405056666965481397)
                  ·
                    refine ⟨3783471975474062528013881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40357034405056666965481397 3783471975474062528013881)
                    ·
                      refine ⟨2837603981605546896010411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3783471975474062528013881 2837603981605546896010411)
                      ·
                        rfl

theorem cell23_5526214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_5526214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526214 prefixEnd_5526214 := by exact prefixLift 5526214
  have htrace : WordTrace (prefixWord ++ tailWord_5526214) baseStart_5526214 baseEnd_5526214 := by
    simpa [prefixWord, tailWord_5526214, baseEnd_5526214] using wordTrace_append hprefix tailTrace_5526214
  have hstable : (prefixWord ++ tailWord_5526214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526214).length < 2 ^ (prefixWord ++ tailWord_5526214).sum := by decide
  have hdescent : baseEnd_5526214 < baseStart_5526214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526221 : List Nat := [1, 6, 2, 1, 2, 1, 2, 3, 1, 1, 3]
def baseStart_5526221 : Nat := 118140960795 + 5526221 * 2 ^ 59
def prefixEnd_5526221 : Nat := 4983230072969 + 3 ^ 40 * 5526221 * 2
def baseEnd_5526221 : Nat := 2837607575970128368622879

theorem tailTrace_5526221 : CollatzResearch.WordTrace tailWord_5526221 prefixEnd_5526221 2837607575970128368622879 := by
  unfold tailWord_5526221
  simp only [CollatzResearch.WordTrace]
  refine ⟨201557838512452595251882517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134371892341635063501255011 201557838512452595251882517)
  ·
    refine ⟨9448023680271215402431993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 201557838512452595251882517 9448023680271215402431993)
    ·
      refine ⟨7086017760203411551823995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9448023680271215402431993 7086017760203411551823995)
      ·
        refine ⟨10629026640305117327735993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7086017760203411551823995 10629026640305117327735993)
        ·
          refine ⟨7971769980228837995801995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10629026640305117327735993 7971769980228837995801995)
          ·
            refine ⟨11957654970343256993702993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7971769980228837995801995 11957654970343256993702993)
            ·
              refine ⟨8968241227757442745277245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11957654970343256993702993 8968241227757442745277245)
              ·
                refine ⟨3363090460409041029478967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8968241227757442745277245 3363090460409041029478967)
                ·
                  refine ⟨5044635690613561544218451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3363090460409041029478967 5044635690613561544218451)
                  ·
                    refine ⟨7566953535920342316327677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5044635690613561544218451 7566953535920342316327677)
                    ·
                      refine ⟨2837607575970128368622879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7566953535920342316327677 2837607575970128368622879)
                      ·
                        rfl

theorem cell23_5526221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_5526221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526221 prefixEnd_5526221 := by exact prefixLift 5526221
  have htrace : WordTrace (prefixWord ++ tailWord_5526221) baseStart_5526221 baseEnd_5526221 := by
    simpa [prefixWord, tailWord_5526221, baseEnd_5526221] using wordTrace_append hprefix tailTrace_5526221
  have hstable : (prefixWord ++ tailWord_5526221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526221).length < 2 ^ (prefixWord ++ tailWord_5526221).sum := by decide
  have hdescent : baseEnd_5526221 < baseStart_5526221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526266 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 2, 3, 4]
def baseStart_5526266 : Nat := 118140960795 + 5526266 * 2 ^ 59
def prefixEnd_5526266 : Nat := 4983230072969 + 3 ^ 40 * 5526266 * 2
def baseEnd_5526266 : Nat := 2837630682599580692560171

theorem tailTrace_5526266 : CollatzResearch.WordTrace tailWord_5526266 prefixEnd_5526266 2837630682599580692560171 := by
  unfold tailWord_5526266
  simp only [CollatzResearch.WordTrace]
  refine ⟨50389869949322391984317663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134372986531526378624847101 50389869949322391984317663)
  ·
    refine ⟨75584804923983587976476495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50389869949322391984317663 75584804923983587976476495)
    ·
      refine ⟨113377207385975381964714743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75584804923983587976476495 113377207385975381964714743)
      ·
        refine ⟨170065811078963072947072115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113377207385975381964714743 170065811078963072947072115)
        ·
          refine ⟨255098716618444609420608173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170065811078963072947072115 255098716618444609420608173)
          ·
            refine ⟨95662018731916728532728065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 255098716618444609420608173 95662018731916728532728065)
            ·
              refine ⟨71746514048937546399546049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95662018731916728532728065 71746514048937546399546049)
              ·
                refine ⟨53809885536703159799659537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71746514048937546399546049 53809885536703159799659537)
                ·
                  refine ⟨40357414152527369849744653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53809885536703159799659537 40357414152527369849744653)
                  ·
                    refine ⟨15134030307197763693654245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40357414152527369849744653 15134030307197763693654245)
                    ·
                      refine ⟨2837630682599580692560171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15134030307197763693654245 2837630682599580692560171)
                      ·
                        rfl

theorem cell23_5526266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_5526266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526266 prefixEnd_5526266 := by exact prefixLift 5526266
  have htrace : WordTrace (prefixWord ++ tailWord_5526266) baseStart_5526266 baseEnd_5526266 := by
    simpa [prefixWord, tailWord_5526266, baseEnd_5526266] using wordTrace_append hprefix tailTrace_5526266
  have hstable : (prefixWord ++ tailWord_5526266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526266).length < 2 ^ (prefixWord ++ tailWord_5526266).sum := by decide
  have hdescent : baseEnd_5526266 < baseStart_5526266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526283 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 3, 4, 2]
def baseStart_5526283 : Nat := 118140960795 + 5526283 * 2 ^ 59
def prefixEnd_5526283 : Nat := 4983230072969 + 3 ^ 40 * 5526283 * 2
def baseEnd_5526283 : Nat := 2837639411770707126047593

theorem tailTrace_5526283 : CollatzResearch.WordTrace tailWord_5526283 prefixEnd_5526283 2837639411770707126047593 := by
  unfold tailWord_5526283
  simp only [CollatzResearch.WordTrace]
  refine ⟨201560099838227979840639503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134373399892151986560426335 201560099838227979840639503)
  ·
    refine ⟨302340149757341969760959255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201560099838227979840639503 302340149757341969760959255)
    ·
      refine ⟨453510224636012954641438883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302340149757341969760959255 453510224636012954641438883)
      ·
        refine ⟨680265336954019431962158325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 453510224636012954641438883 680265336954019431962158325)
        ·
          refine ⟨63774875339439321746452343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 680265336954019431962158325 63774875339439321746452343)
          ·
            refine ⟨95662313009158982619678515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63774875339439321746452343 95662313009158982619678515)
            ·
              refine ⟨143493469513738473929517773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95662313009158982619678515 143493469513738473929517773)
              ·
                refine ⟨53810051067651927723569165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143493469513738473929517773 53810051067651927723569165)
                ·
                  refine ⟨20178769150369472896338437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53810051067651927723569165 20178769150369472896338437)
                  ·
                    refine ⟨3783519215694276168063457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20178769150369472896338437 3783519215694276168063457)
                    ·
                      refine ⟨2837639411770707126047593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3783519215694276168063457 2837639411770707126047593)
                      ·
                        rfl

theorem cell23_5526283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 4, 2].length) (baseStart_5526283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526283 prefixEnd_5526283 := by exact prefixLift 5526283
  have htrace : WordTrace (prefixWord ++ tailWord_5526283) baseStart_5526283 baseEnd_5526283 := by
    simpa [prefixWord, tailWord_5526283, baseEnd_5526283] using wordTrace_append hprefix tailTrace_5526283
  have hstable : (prefixWord ++ tailWord_5526283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526283).length < 2 ^ (prefixWord ++ tailWord_5526283).sum := by decide
  have hdescent : baseEnd_5526283 < baseStart_5526283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526336 : List Nat := [2, 1, 1, 2, 2, 1, 1, 5, 1, 7]
def baseStart_5526336 : Nat := 118140960795 + 5526336 * 2 ^ 59
def prefixEnd_5526336 : Nat := 4983230072969 + 3 ^ 40 * 5526336 * 2
def baseEnd_5526336 : Nat := 945888875415131806228283

theorem tailTrace_5526336 : CollatzResearch.WordTrace tailWord_5526336 prefixEnd_5526336 945888875415131806228283 := by
  unfold tailWord_5526336
  simp only [CollatzResearch.WordTrace]
  refine ⟨100781016453517984946159431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134374688604690646594879241 100781016453517984946159431)
  ·
    refine ⟨151171524680276977419239147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100781016453517984946159431 151171524680276977419239147)
    ·
      refine ⟨226757287020415466128858721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151171524680276977419239147 226757287020415466128858721)
      ·
        refine ⟨170067965265311599596644041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226757287020415466128858721 170067965265311599596644041)
        ·
          refine ⟨127550973948983699697483031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170067965265311599596644041 127550973948983699697483031)
          ·
            refine ⟨191326460923475549546224547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127550973948983699697483031 191326460923475549546224547)
            ·
              refine ⟨286989691385213324319336821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191326460923475549546224547 286989691385213324319336821)
              ·
                refine ⟨26905283567363749154937827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 286989691385213324319336821 26905283567363749154937827)
                ·
                  refine ⟨40357925351045623732406741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26905283567363749154937827 40357925351045623732406741)
                  ·
                    refine ⟨945888875415131806228283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40357925351045623732406741 945888875415131806228283)
                    ·
                      rfl

theorem cell23_5526336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 1, 7].length) (baseStart_5526336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526336 prefixEnd_5526336 := by exact prefixLift 5526336
  have htrace : WordTrace (prefixWord ++ tailWord_5526336) baseStart_5526336 baseEnd_5526336 := by
    simpa [prefixWord, tailWord_5526336, baseEnd_5526336] using wordTrace_append hprefix tailTrace_5526336
  have hstable : (prefixWord ++ tailWord_5526336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526336).length < 2 ^ (prefixWord ++ tailWord_5526336).sum := by decide
  have hdescent : baseEnd_5526336 < baseStart_5526336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526373 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 4, 1, 4]
def baseStart_5526373 : Nat := 118140960795 + 5526373 * 2 ^ 59
def prefixEnd_5526373 : Nat := 4983230072969 + 3 ^ 40 * 5526373 * 2
def baseEnd_5526373 : Nat := 2837685625029611773922179

theorem tailTrace_5526373 : CollatzResearch.WordTrace tailWord_5526373 prefixEnd_5526373 2837685625029611773922179 := by
  unfold tailWord_5526373
  simp only [CollatzResearch.WordTrace]
  refine ⟨201563382407901925211415773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134375588271934616807610515 201563382407901925211415773)
  ·
    refine ⟨75586268402963221954280915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201563382407901925211415773 75586268402963221954280915)
    ·
      refine ⟨113379402604444832931421373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75586268402963221954280915 113379402604444832931421373)
      ·
        refine ⟨42517275976666812349283015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113379402604444832931421373 42517275976666812349283015)
        ·
          refine ⟨63775913965000218523924523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42517275976666812349283015 63775913965000218523924523)
          ·
            refine ⟨95663870947500327785886785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63775913965000218523924523 95663870947500327785886785)
            ·
              refine ⟨71747903210625245839415089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95663870947500327785886785 71747903210625245839415089)
              ·
                refine ⟨53810927407968934379561317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71747903210625245839415089 53810927407968934379561317)
                ·
                  refine ⟨10089548888994175196167747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53810927407968934379561317 10089548888994175196167747)
                  ·
                    refine ⟨15134323333491262794251621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10089548888994175196167747 15134323333491262794251621)
                    ·
                      refine ⟨2837685625029611773922179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15134323333491262794251621 2837685625029611773922179)
                      ·
                        rfl

theorem cell23_5526373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_5526373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526373 prefixEnd_5526373 := by exact prefixLift 5526373
  have htrace : WordTrace (prefixWord ++ tailWord_5526373) baseStart_5526373 baseEnd_5526373 := by
    simpa [prefixWord, tailWord_5526373, baseEnd_5526373] using wordTrace_append hprefix tailTrace_5526373
  have hstable : (prefixWord ++ tailWord_5526373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526373).length < 2 ^ (prefixWord ++ tailWord_5526373).sum := by decide
  have hdescent : baseEnd_5526373 < baseStart_5526373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526468 : List Nat := [2, 3, 3, 3, 1, 1, 3, 2, 1, 4]
def baseStart_5526468 : Nat := 118140960795 + 5526468 * 2 ^ 59
def prefixEnd_5526468 : Nat := 4983230072969 + 3 ^ 40 * 5526468 * 2
def baseEnd_5526468 : Nat := 945911468563929634078081

theorem tailTrace_5526468 : CollatzResearch.WordTrace tailWord_5526468 prefixEnd_5526468 945911468563929634078081 := by
  unfold tailWord_5526468
  simp only [CollatzResearch.WordTrace]
  refine ⟨100783423671278878218062029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134377898228371837624082705 100783423671278878218062029)
  ·
    refine ⟨37793783876729579331773261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100783423671278878218062029 37793783876729579331773261)
    ·
      refine ⟨14172668953773592249414973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37793783876729579331773261 14172668953773592249414973)
      ·
        refine ⟨5314750857665097093530615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14172668953773592249414973 5314750857665097093530615)
        ·
          refine ⟨7972126286497645640295923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5314750857665097093530615 7972126286497645640295923)
          ·
            refine ⟨11958189429746468460443885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7972126286497645640295923 11958189429746468460443885)
            ·
              refine ⟨4484321036154925672666457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11958189429746468460443885 4484321036154925672666457)
              ·
                refine ⟨3363240777116194254499843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4484321036154925672666457 3363240777116194254499843)
                ·
                  refine ⟨5044861165674291381749765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3363240777116194254499843 5044861165674291381749765)
                  ·
                    refine ⟨945911468563929634078081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5044861165674291381749765 945911468563929634078081)
                    ·
                      rfl

theorem cell23_5526468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_5526468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526468 prefixEnd_5526468 := by exact prefixLift 5526468
  have htrace : WordTrace (prefixWord ++ tailWord_5526468) baseStart_5526468 baseEnd_5526468 := by
    simpa [prefixWord, tailWord_5526468, baseEnd_5526468] using wordTrace_append hprefix tailTrace_5526468
  have hstable : (prefixWord ++ tailWord_5526468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526468).length < 2 ^ (prefixWord ++ tailWord_5526468).sum := by decide
  have hdescent : baseEnd_5526468 < baseStart_5526468 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526497 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 5, 2, 2]
def baseStart_5526497 : Nat := 118140960795 + 5526497 * 2 ^ 59
def prefixEnd_5526497 : Nat := 4983230072969 + 3 ^ 40 * 5526497 * 2
def baseEnd_5526497 : Nat := 2837749296630769288771609

theorem tailTrace_5526497 : CollatzResearch.WordTrace tailWord_5526497 prefixEnd_5526497 2837749296630769288771609 := by
  unfold tailWord_5526497
  simp only [CollatzResearch.WordTrace]
  refine ⟨201567905059452694388929745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134378603372968462925953163 201567905059452694388929745)
  ·
    refine ⟨151175928794589520791697309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201567905059452694388929745 151175928794589520791697309)
    ·
      refine ⟨56690973297971070296886491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151175928794589520791697309 56690973297971070296886491)
      ·
        refine ⟨85036459946956605445329737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56690973297971070296886491 85036459946956605445329737)
        ·
          refine ⟨63777344960217454083997303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85036459946956605445329737 63777344960217454083997303)
          ·
            refine ⟨95666017440326181125995955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63777344960217454083997303 95666017440326181125995955)
            ·
              refine ⟨143499026160489271688993933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95666017440326181125995955 143499026160489271688993933)
              ·
                refine ⟨53812134810183476883372725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143499026160489271688993933 53812134810183476883372725)
                ·
                  refine ⟨5044887638454700957816193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53812134810183476883372725 5044887638454700957816193)
                  ·
                    refine ⟨3783665728841025718362145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5044887638454700957816193 3783665728841025718362145)
                    ·
                      refine ⟨2837749296630769288771609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3783665728841025718362145 2837749296630769288771609)
                      ·
                        rfl

theorem cell23_5526497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 5, 2, 2].length) (baseStart_5526497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526497 prefixEnd_5526497 := by exact prefixLift 5526497
  have htrace : WordTrace (prefixWord ++ tailWord_5526497) baseStart_5526497 baseEnd_5526497 := by
    simpa [prefixWord, tailWord_5526497, baseEnd_5526497] using wordTrace_append hprefix tailTrace_5526497
  have hstable : (prefixWord ++ tailWord_5526497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526497).length < 2 ^ (prefixWord ++ tailWord_5526497).sum := by decide
  have hdescent : baseEnd_5526497 < baseStart_5526497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526501 : List Nat := [1, 3, 1, 6, 1, 1, 2, 1, 2, 3, 2]
def baseStart_5526501 : Nat := 118140960795 + 5526501 * 2 ^ 59
def prefixEnd_5526501 : Nat := 4983230072969 + 3 ^ 40 * 5526501 * 2
def baseEnd_5526501 : Nat := 2837751350553387273121591

theorem tailTrace_5526501 : CollatzResearch.WordTrace tailWord_5526501 prefixEnd_5526501 2837751350553387273121591 := by
  unfold tailWord_5526501
  simp only [CollatzResearch.WordTrace]
  refine ⟨201568050951438203072075357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134378700634292135381383571 201568050951438203072075357)
  ·
    refine ⟨75588019106789326152028259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201568050951438203072075357 75588019106789326152028259)
    ·
      refine ⟨113382028660183989228042389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75588019106789326152028259 113382028660183989228042389)
      ·
        refine ⟨5314782593446124495064487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 113382028660183989228042389 5314782593446124495064487)
        ·
          refine ⟨7972173890169186742596731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5314782593446124495064487 7972173890169186742596731)
          ·
            refine ⟨11958260835253780113895097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7972173890169186742596731 11958260835253780113895097)
            ·
              refine ⟨8968695626440335085421323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11958260835253780113895097 8968695626440335085421323)
              ·
                refine ⟨13453043439660502628131985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8968695626440335085421323 13453043439660502628131985)
                ·
                  refine ⟨10089782579745376971098989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13453043439660502628131985 10089782579745376971098989)
                  ·
                    refine ⟨3783668467404516364162121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10089782579745376971098989 3783668467404516364162121)
                    ·
                      refine ⟨2837751350553387273121591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3783668467404516364162121 2837751350553387273121591)
                      ·
                        rfl

theorem cell23_5526501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_5526501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526501 prefixEnd_5526501 := by exact prefixLift 5526501
  have htrace : WordTrace (prefixWord ++ tailWord_5526501) baseStart_5526501 baseEnd_5526501 := by
    simpa [prefixWord, tailWord_5526501, baseEnd_5526501] using wordTrace_append hprefix tailTrace_5526501
  have hstable : (prefixWord ++ tailWord_5526501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526501).length < 2 ^ (prefixWord ++ tailWord_5526501).sum := by decide
  have hdescent : baseEnd_5526501 < baseStart_5526501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526533 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 1, 9]
def baseStart_5526533 : Nat := 118140960795 + 5526533 * 2 ^ 59
def prefixEnd_5526533 : Nat := 4983230072969 + 3 ^ 40 * 5526533 * 2
def baseEnd_5526533 : Nat := 945922593978110382640481

theorem tailTrace_5526533 : CollatzResearch.WordTrace tailWord_5526533 prefixEnd_5526533 945922593978110382640481 := by
  unfold tailWord_5526533
  simp only [CollatzResearch.WordTrace]
  refine ⟨201569218087322272537240253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134379478724881515024826835 201569218087322272537240253)
  ·
    refine ⟨75588456782745852201465095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201569218087322272537240253 75588456782745852201465095)
    ·
      refine ⟨113382685174118778302197643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75588456782745852201465095 113382685174118778302197643)
      ·
        refine ⟨170074027761178167453296465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113382685174118778302197643 170074027761178167453296465)
        ·
          refine ⟨127555520820883625589972349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170074027761178167453296465 127555520820883625589972349)
          ·
            refine ⟨47833320307831359596239631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127555520820883625589972349 47833320307831359596239631)
            ·
              refine ⟨71749980461747039394359447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47833320307831359596239631 71749980461747039394359447)
              ·
                refine ⟨107624970692620559091539171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71749980461747039394359447 107624970692620559091539171)
                ·
                  refine ⟨161437456038930838637308757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107624970692620559091539171 161437456038930838637308757)
                  ·
                    refine ⟨945922593978110382640481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 161437456038930838637308757 945922593978110382640481)
                    ·
                      rfl

theorem cell23_5526533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 9].length) (baseStart_5526533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526533 prefixEnd_5526533 := by exact prefixLift 5526533
  have htrace : WordTrace (prefixWord ++ tailWord_5526533) baseStart_5526533 baseEnd_5526533 := by
    simpa [prefixWord, tailWord_5526533, baseEnd_5526533] using wordTrace_append hprefix tailTrace_5526533
  have hstable : (prefixWord ++ tailWord_5526533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526533).length < 2 ^ (prefixWord ++ tailWord_5526533).sum := by decide
  have hdescent : baseEnd_5526533 < baseStart_5526533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526543 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 5]
def baseStart_5526543 : Nat := 118140960795 + 5526543 * 2 ^ 59
def prefixEnd_5526543 : Nat := 4983230072969 + 3 ^ 40 * 5526543 * 2
def baseEnd_5526543 : Nat := 2837772916740876108796397

theorem tailTrace_5526543 : CollatzResearch.WordTrace tailWord_5526543 prefixEnd_5526543 2837772916740876108796397 := by
  unfold tailWord_5526543
  simp only [CollatzResearch.WordTrace]
  refine ⟨201569582817286044245104283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134379721878190696163402855 201569582817286044245104283)
  ·
    refine ⟨302354374225929066367656425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201569582817286044245104283 302354374225929066367656425)
    ·
      refine ⟨226765780669446799775742319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302354374225929066367656425 226765780669446799775742319)
      ·
        refine ⟨340148671004170199663613479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226765780669446799775742319 340148671004170199663613479)
        ·
          refine ⟨510223006506255299495420219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340148671004170199663613479 510223006506255299495420219)
          ·
            refine ⟨765334509759382949243130329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510223006506255299495420219 765334509759382949243130329)
            ·
              refine ⟨574000882319537211932347747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 765334509759382949243130329 574000882319537211932347747)
              ·
                refine ⟨861001323479305817898521621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 574000882319537211932347747 861001323479305817898521621)
                ·
                  refine ⟨40359437038092460213993201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 861001323479305817898521621 40359437038092460213993201)
                  ·
                    refine ⟨30269577778569345160494901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40359437038092460213993201 30269577778569345160494901)
                    ·
                      refine ⟨2837772916740876108796397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30269577778569345160494901 2837772916740876108796397)
                      ·
                        rfl

theorem cell23_5526543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 5].length) (baseStart_5526543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526543 prefixEnd_5526543 := by exact prefixLift 5526543
  have htrace : WordTrace (prefixWord ++ tailWord_5526543) baseStart_5526543 baseEnd_5526543 := by
    simpa [prefixWord, tailWord_5526543, baseEnd_5526543] using wordTrace_append hprefix tailTrace_5526543
  have hstable : (prefixWord ++ tailWord_5526543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526543).length < 2 ^ (prefixWord ++ tailWord_5526543).sum := by decide
  have hdescent : baseEnd_5526543 < baseStart_5526543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526600 : List Nat := [2, 1, 3, 1, 1, 1, 3, 3, 2, 2, 4]
def baseStart_5526600 : Nat := 118140960795 + 5526600 * 2 ^ 59
def prefixEnd_5526600 : Nat := 4983230072969 + 3 ^ 40 * 5526600 * 2
def baseEnd_5526600 : Nat := 2837802185138182385783635

theorem tailTrace_5526600 : CollatzResearch.WordTrace tailWord_5526600 prefixEnd_5526600 2837802185138182385783635 := by
  unfold tailWord_5526600
  simp only [CollatzResearch.WordTrace]
  refine ⟨100785830889039771489964627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134381107852053028653286169 100785830889039771489964627)
  ·
    refine ⟨151178746333559657234946941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100785830889039771489964627 151178746333559657234946941)
    ·
      refine ⟨56692029875084871463105103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151178746333559657234946941 56692029875084871463105103)
      ·
        refine ⟨85038044812627307194657655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56692029875084871463105103 85038044812627307194657655)
        ·
          refine ⟨127557067218940960791986483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85038044812627307194657655 127557067218940960791986483)
          ·
            refine ⟨191335600828411441187979725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127557067218940960791986483 191335600828411441187979725)
            ·
              refine ⟨71750850310654290445492397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191335600828411441187979725 71750850310654290445492397)
              ·
                refine ⟨26906568866495358917059649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71750850310654290445492397 26906568866495358917059649)
                ·
                  refine ⟨20179926649871519187794737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26906568866495358917059649 20179926649871519187794737)
                  ·
                    refine ⟨15134944987403639390846053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20179926649871519187794737 15134944987403639390846053)
                    ·
                      refine ⟨2837802185138182385783635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15134944987403639390846053 2837802185138182385783635)
                      ·
                        rfl

theorem cell23_5526600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_5526600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526600 prefixEnd_5526600 := by exact prefixLift 5526600
  have htrace : WordTrace (prefixWord ++ tailWord_5526600) baseStart_5526600 baseEnd_5526600 := by
    simpa [prefixWord, tailWord_5526600, baseEnd_5526600] using wordTrace_append hprefix tailTrace_5526600
  have hstable : (prefixWord ++ tailWord_5526600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526600).length < 2 ^ (prefixWord ++ tailWord_5526600).sum := by decide
  have hdescent : baseEnd_5526600 < baseStart_5526600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526647 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 2, 5, 2]
def baseStart_5526647 : Nat := 118140960795 + 5526647 * 2 ^ 59
def prefixEnd_5526647 : Nat := 4983230072969 + 3 ^ 40 * 5526647 * 2
def baseEnd_5526647 : Nat := 2837826318728943701895919

theorem tailTrace_5526647 : CollatzResearch.WordTrace tailWord_5526647 prefixEnd_5526647 2837826318728943701895919 := by
  unfold tailWord_5526647
  simp only [CollatzResearch.WordTrace]
  refine ⟨201573376008909270006890195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134382250672606180004593463 201573376008909270006890195)
  ·
    refine ⟨302360064013363905010335293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201573376008909270006890195 302360064013363905010335293)
    ·
      refine ⟨113385024005011464378875735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302360064013363905010335293 113385024005011464378875735)
      ·
        refine ⟨170077536007517196568313603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113385024005011464378875735 170077536007517196568313603)
        ·
          refine ⟨255116304011275794852470405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170077536007517196568313603 255116304011275794852470405)
          ·
            refine ⟨47834307002114211534838201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 255116304011275794852470405 47834307002114211534838201)
            ·
              refine ⟨35875730251585658651128651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47834307002114211534838201 35875730251585658651128651)
              ·
                refine ⟨53813595377378487976692977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35875730251585658651128651 53813595377378487976692977)
                ·
                  refine ⟨40360196533033865982519733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53813595377378487976692977 40360196533033865982519733)
                  ·
                    refine ⟨3783768424971924935861225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40360196533033865982519733 3783768424971924935861225)
                    ·
                      refine ⟨2837826318728943701895919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3783768424971924935861225 2837826318728943701895919)
                      ·
                        rfl

theorem cell23_5526647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 5, 2].length) (baseStart_5526647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526647 prefixEnd_5526647 := by exact prefixLift 5526647
  have htrace : WordTrace (prefixWord ++ tailWord_5526647) baseStart_5526647 baseEnd_5526647 := by
    simpa [prefixWord, tailWord_5526647, baseEnd_5526647] using wordTrace_append hprefix tailTrace_5526647
  have hstable : (prefixWord ++ tailWord_5526647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526647).length < 2 ^ (prefixWord ++ tailWord_5526647).sum := by decide
  have hdescent : baseEnd_5526647 < baseStart_5526647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526674 : List Nat := [3, 2, 3, 1, 1, 3, 2, 1, 2, 5]
def baseStart_5526674 : Nat := 118140960795 + 5526674 * 2 ^ 59
def prefixEnd_5526674 : Nat := 4983230072969 + 3 ^ 40 * 5526674 * 2
def baseEnd_5526674 : Nat := 945946727568871698752765

theorem tailTrace_5526674 : CollatzResearch.WordTrace tailWord_5526674 prefixEnd_5526674 945946727568871698752765 := by
  unfold tailWord_5526674
  simp only [CollatzResearch.WordTrace]
  refine ⟨50393590194952863404530769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134382907186540969078748717 50393590194952863404530769)
  ·
    refine ⟨37795192646214647553398077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50393590194952863404530769 37795192646214647553398077)
    ·
      refine ⟨14173197242330492832524279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37795192646214647553398077 14173197242330492832524279)
      ·
        refine ⟨21259795863495739248786419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14173197242330492832524279 21259795863495739248786419)
        ·
          refine ⟨31889693795243608873179629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21259795863495739248786419 31889693795243608873179629)
          ·
            refine ⟨11958635173216353327442361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31889693795243608873179629 11958635173216353327442361)
            ·
              refine ⟨8968976379912264995581771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11958635173216353327442361 8968976379912264995581771)
              ·
                refine ⟨13453464569868397493372657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8968976379912264995581771 13453464569868397493372657)
                ·
                  refine ⟨10090098427401298120029493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13453464569868397493372657 10090098427401298120029493)
                  ·
                    refine ⟨945946727568871698752765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10090098427401298120029493 945946727568871698752765)
                    ·
                      rfl

theorem cell23_5526674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_5526674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526674 prefixEnd_5526674 := by exact prefixLift 5526674
  have htrace : WordTrace (prefixWord ++ tailWord_5526674) baseStart_5526674 baseEnd_5526674 := by
    simpa [prefixWord, tailWord_5526674, baseEnd_5526674] using wordTrace_append hprefix tailTrace_5526674
  have hstable : (prefixWord ++ tailWord_5526674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526674).length < 2 ^ (prefixWord ++ tailWord_5526674).sum := by decide
  have hdescent : baseEnd_5526674 < baseStart_5526674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526677 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 3, 6, 2]
def baseStart_5526677 : Nat := 118140960795 + 5526677 * 2 ^ 59
def prefixEnd_5526677 : Nat := 4983230072969 + 3 ^ 40 * 5526677 * 2
def baseEnd_5526677 : Nat := 2837841723148578584520781

theorem tailTrace_5526677 : CollatzResearch.WordTrace tailWord_5526677 prefixEnd_5526677 2837841723148578584520781 := by
  unfold tailWord_5526677
  simp only [CollatzResearch.WordTrace]
  refine ⟨201574470198800585130482285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134382980132533723420321523 201574470198800585130482285)
  ·
    refine ⟨75590426324550219423930857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201574470198800585130482285 75590426324550219423930857)
    ·
      refine ⟨56692819743412664567948143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75590426324550219423930857 56692819743412664567948143)
      ·
        refine ⟨85039229615118996851922215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56692819743412664567948143 85039229615118996851922215)
        ·
          refine ⟨127558844422678495277883323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85039229615118996851922215 127558844422678495277883323)
          ·
            refine ⟨191338266634017742916824985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127558844422678495277883323 191338266634017742916824985)
            ·
              refine ⟨143503699975513307187618739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191338266634017742916824985 143503699975513307187618739)
              ·
                refine ⟨215255549963269960781428109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143503699975513307187618739 215255549963269960781428109)
                ·
                  refine ⟨80720831236226235293035541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 215255549963269960781428109 80720831236226235293035541)
                  ·
                    refine ⟨3783788964198104779361041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 80720831236226235293035541 3783788964198104779361041)
                    ·
                      refine ⟨2837841723148578584520781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3783788964198104779361041 2837841723148578584520781)
                      ·
                        rfl

theorem cell23_5526677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 6, 2].length) (baseStart_5526677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526677 prefixEnd_5526677 := by exact prefixLift 5526677
  have htrace : WordTrace (prefixWord ++ tailWord_5526677) baseStart_5526677 baseEnd_5526677 := by
    simpa [prefixWord, tailWord_5526677, baseEnd_5526677] using wordTrace_append hprefix tailTrace_5526677
  have hstable : (prefixWord ++ tailWord_5526677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526677).length < 2 ^ (prefixWord ++ tailWord_5526677).sum := by decide
  have hdescent : baseEnd_5526677 < baseStart_5526677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526704 : List Nat := [2, 1, 1, 1, 2, 1, 2, 8, 1, 4]
def baseStart_5526704 : Nat := 118140960795 + 5526704 * 2 ^ 59
def prefixEnd_5526704 : Nat := 4983230072969 + 3 ^ 40 * 5526704 * 2
def baseEnd_5526704 : Nat := 945951862375416659627719

theorem tailTrace_5526704 : CollatzResearch.WordTrace tailWord_5526704 prefixEnd_5526704 945951862375416659627719 := by
  unfold tailWord_5526704
  simp only [CollatzResearch.WordTrace]
  refine ⟨100787727484851384370857583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134383636646468512494476777 100787727484851384370857583)
  ·
    refine ⟨151181591227277076556286375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100787727484851384370857583 151181591227277076556286375)
    ·
      refine ⟨226772386840915614834429563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151181591227277076556286375 226772386840915614834429563)
      ·
        refine ⟨340158580261373422251644345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226772386840915614834429563 340158580261373422251644345)
        ·
          refine ⟨255118935196030066688733259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 340158580261373422251644345 255118935196030066688733259)
          ·
            refine ⟨382678402794045100033099889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255118935196030066688733259 382678402794045100033099889)
            ·
              refine ⟨287008802095533825024824917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 382678402794045100033099889 287008802095533825024824917)
              ·
                refine ⟨3363384399557037012009667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 287008802095533825024824917 3363384399557037012009667)
                ·
                  refine ⟨5045076599335555518014501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3363384399557037012009667 5045076599335555518014501)
                  ·
                    refine ⟨945951862375416659627719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5045076599335555518014501 945951862375416659627719)
                    ·
                      rfl

theorem cell23_5526704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 8, 1, 4].length) (baseStart_5526704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526704 prefixEnd_5526704 := by exact prefixLift 5526704
  have htrace : WordTrace (prefixWord ++ tailWord_5526704) baseStart_5526704 baseEnd_5526704 := by
    simpa [prefixWord, tailWord_5526704, baseEnd_5526704] using wordTrace_append hprefix tailTrace_5526704
  have hstable : (prefixWord ++ tailWord_5526704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526704).length < 2 ^ (prefixWord ++ tailWord_5526704).sum := by decide
  have hdescent : baseEnd_5526704 < baseStart_5526704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526717 : List Nat := [1, 4, 1, 2, 1, 1, 4, 3, 6]
def baseStart_5526717 : Nat := 118140960795 + 5526717 * 2 ^ 59
def prefixEnd_5526717 : Nat := 4983230072969 + 3 ^ 40 * 5526717 * 2
def baseEnd_5526717 : Nat := 315318029152750936446733

theorem tailTrace_5526717 : CollatzResearch.WordTrace tailWord_5526717 prefixEnd_5526717 315318029152750936446733 := by
  unfold tailWord_5526717
  simp only [CollatzResearch.WordTrace]
  refine ⟨201575929118655671961938405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134383952745770447974625603 201575929118655671961938405)
  ·
    refine ⟨37795486709747938492863451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201575929118655671961938405 37795486709747938492863451)
    ·
      refine ⟨56693230064621907739295177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37795486709747938492863451 56693230064621907739295177)
      ·
        refine ⟨42519922548466430804471383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56693230064621907739295177 42519922548466430804471383)
        ·
          refine ⟨63779883822699646206707075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42519922548466430804471383 63779883822699646206707075)
          ·
            refine ⟨95669825734049469310060613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63779883822699646206707075 95669825734049469310060613)
            ·
              refine ⟨17938092325134275495636365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95669825734049469310060613 17938092325134275495636365)
              ·
                refine ⟨6726784621925353310863637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17938092325134275495636365 6726784621925353310863637)
                ·
                  refine ⟨315318029152750936446733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6726784621925353310863637 315318029152750936446733)
                  ·
                    rfl

theorem cell23_5526717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 6].length) (baseStart_5526717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526717 prefixEnd_5526717 := by exact prefixLift 5526717
  have htrace : WordTrace (prefixWord ++ tailWord_5526717) baseStart_5526717 baseEnd_5526717 := by
    simpa [prefixWord, tailWord_5526717, baseEnd_5526717] using wordTrace_append hprefix tailTrace_5526717
  have hstable : (prefixWord ++ tailWord_5526717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526717).length < 2 ^ (prefixWord ++ tailWord_5526717).sum := by decide
  have hdescent : baseEnd_5526717 < baseStart_5526717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526721 : List Nat := [1, 2, 6, 1, 1, 2, 1, 2, 3, 4]
def baseStart_5526721 : Nat := 118140960795 + 5526721 * 2 ^ 59
def prefixEnd_5526721 : Nat := 4983230072969 + 3 ^ 40 * 5526721 * 2
def baseEnd_5526721 : Nat := 945954772099125470790193

theorem tailTrace_5526721 : CollatzResearch.WordTrace tailWord_5526721 prefixEnd_5526721 945954772099125470790193 := by
  unfold tailWord_5526721
  simp only [CollatzResearch.WordTrace]
  refine ⟨201576075010641180645084017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134384050007094120430056011 201576075010641180645084017)
  ·
    refine ⟨151182056257980885483813013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201576075010641180645084017 151182056257980885483813013)
    ·
      refine ⟨7086658887092854007053735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 151182056257980885483813013 7086658887092854007053735)
      ·
        refine ⟨10629988330639281010580603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7086658887092854007053735 10629988330639281010580603)
        ·
          refine ⟨15944982495958921515870905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10629988330639281010580603 15944982495958921515870905)
          ·
            refine ⟨11958736871969191136903179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15944982495958921515870905 11958736871969191136903179)
            ·
              refine ⟨17938105307953786705354769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11958736871969191136903179 17938105307953786705354769)
              ·
                refine ⟨13453578980965340029016077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17938105307953786705354769 13453578980965340029016077)
                ·
                  refine ⟨5045092117862002510881029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13453578980965340029016077 5045092117862002510881029)
                  ·
                    refine ⟨945954772099125470790193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5045092117862002510881029 945954772099125470790193)
                    ·
                      rfl

theorem cell23_5526721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_5526721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526721 prefixEnd_5526721 := by exact prefixLift 5526721
  have htrace : WordTrace (prefixWord ++ tailWord_5526721) baseStart_5526721 baseEnd_5526721 := by
    simpa [prefixWord, tailWord_5526721, baseEnd_5526721] using wordTrace_append hprefix tailTrace_5526721
  have hstable : (prefixWord ++ tailWord_5526721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526721).length < 2 ^ (prefixWord ++ tailWord_5526721).sum := by decide
  have hdescent : baseEnd_5526721 < baseStart_5526721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526824 : List Nat := [2, 1, 5, 1, 2, 2, 2, 8]
def baseStart_5526824 : Nat := 118140960795 + 5526824 * 2 ^ 59
def prefixEnd_5526824 : Nat := 4983230072969 + 3 ^ 40 * 5526824 * 2
def baseEnd_5526824 : Nat := 105108044622399611458615

theorem tailTrace_5526824 : CollatzResearch.WordTrace tailWord_5526824 prefixEnd_5526824 105108044622399611458615 := by
  unfold tailWord_5526824
  simp only [CollatzResearch.WordTrace]
  refine ⟨100789915864634014618041763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134386554486178686157389017 100789915864634014618041763)
  ·
    refine ⟨151184873796951021927062645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100789915864634014618041763 151184873796951021927062645)
    ·
      refine ⟨14173581918464158305662123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 151184873796951021927062645 14173581918464158305662123)
      ·
        refine ⟨21260372877696237458493185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14173581918464158305662123 21260372877696237458493185)
        ·
          refine ⟨15945279658272178093869889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21260372877696237458493185 15945279658272178093869889)
          ·
            refine ⟨11958959743704133570402417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15945279658272178093869889 11958959743704133570402417)
            ·
              refine ⟨8969219807778100177801813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11958959743704133570402417 8969219807778100177801813)
              ·
                refine ⟨105108044622399611458615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8969219807778100177801813 105108044622399611458615)
                ·
                  rfl

theorem cell23_5526824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 8].length) (baseStart_5526824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526824 prefixEnd_5526824 := by exact prefixLift 5526824
  have htrace : WordTrace (prefixWord ++ tailWord_5526824) baseStart_5526824 baseEnd_5526824 := by
    simpa [prefixWord, tailWord_5526824, baseEnd_5526824] using wordTrace_append hprefix tailTrace_5526824
  have hstable : (prefixWord ++ tailWord_5526824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526824).length < 2 ^ (prefixWord ++ tailWord_5526824).sum := by decide
  have hdescent : baseEnd_5526824 < baseStart_5526824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526867 : List Nat := [1, 1, 1, 2, 1, 1, 6, 2, 2, 6]
def baseStart_5526867 : Nat := 118140960795 + 5526867 * 2 ^ 59
def prefixEnd_5526867 : Nat := 4983230072969 + 3 ^ 40 * 5526867 * 2
def baseEnd_5526867 : Nat := 945979761490977613714969

theorem tailTrace_5526867 : CollatzResearch.WordTrace tailWord_5526867 prefixEnd_5526867 945979761490977613714969 := by
  unfold tailWord_5526867
  simp only [CollatzResearch.WordTrace]
  refine ⟨201581400068112247579898855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134387600045408165053265903 201581400068112247579898855)
  ·
    refine ⟨302372100102168371369848283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201581400068112247579898855 302372100102168371369848283)
    ·
      refine ⟨453558150153252557054772425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302372100102168371369848283 453558150153252557054772425)
      ·
        refine ⟨340168612614939417791079319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 453558150153252557054772425 340168612614939417791079319)
        ·
          refine ⟨510252918922409126686618979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340168612614939417791079319 510252918922409126686618979)
          ·
            refine ⟨765379378383613690029928469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510252918922409126686618979 765379378383613690029928469)
            ·
              refine ⟨35877158361731891720152897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 765379378383613690029928469 35877158361731891720152897)
              ·
                refine ⟨26907868771298918790114673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35877158361731891720152897 26907868771298918790114673)
                ·
                  refine ⟨20180901578474189092586005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26907868771298918790114673 20180901578474189092586005)
                  ·
                    refine ⟨945979761490977613714969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20180901578474189092586005 945979761490977613714969)
                    ·
                      rfl

theorem cell23_5526867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 6].length) (baseStart_5526867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526867 prefixEnd_5526867 := by exact prefixLift 5526867
  have htrace : WordTrace (prefixWord ++ tailWord_5526867) baseStart_5526867 baseEnd_5526867 := by
    simpa [prefixWord, tailWord_5526867, baseEnd_5526867] using wordTrace_append hprefix tailTrace_5526867
  have hstable : (prefixWord ++ tailWord_5526867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526867).length < 2 ^ (prefixWord ++ tailWord_5526867).sum := by decide
  have hdescent : baseEnd_5526867 < baseStart_5526867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526868 : List Nat := [2, 4, 1, 1, 2, 1, 4, 2, 2, 1, 3]
def baseStart_5526868 : Nat := 118140960795 + 5526868 * 2 ^ 59
def prefixEnd_5526868 : Nat := 4983230072969 + 3 ^ 40 * 5526868 * 2
def baseEnd_5526868 : Nat := 2837939797953587337232403

theorem tailTrace_5526868 : CollatzResearch.WordTrace tailWord_5526868 prefixEnd_5526868 2837939797953587337232403 := by
  unfold tailWord_5526868
  simp only [CollatzResearch.WordTrace]
  refine ⟨100790718270554312375342629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134387624360739083167123505 100790718270554312375342629)
  ·
    refine ⟨18898259675728933570376743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100790718270554312375342629 18898259675728933570376743)
    ·
      refine ⟨28347389513593400355565115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18898259675728933570376743 28347389513593400355565115)
      ·
        refine ⟨42521084270390100533347673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28347389513593400355565115 42521084270390100533347673)
        ·
          refine ⟨31890813202792575400010755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42521084270390100533347673 31890813202792575400010755)
          ·
            refine ⟨47836219804188863100016133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31890813202792575400010755 47836219804188863100016133)
            ·
              refine ⟨8969291213285411831253025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47836219804188863100016133 8969291213285411831253025)
              ·
                refine ⟨6726968409964058873439769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8969291213285411831253025 6726968409964058873439769)
                ·
                  refine ⟨5045226307473044155079827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6726968409964058873439769 5045226307473044155079827)
                  ·
                    refine ⟨7567839461209566232619741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5045226307473044155079827 7567839461209566232619741)
                    ·
                      refine ⟨2837939797953587337232403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7567839461209566232619741 2837939797953587337232403)
                      ·
                        rfl

theorem cell23_5526868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_5526868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526868 prefixEnd_5526868 := by exact prefixLift 5526868
  have htrace : WordTrace (prefixWord ++ tailWord_5526868) baseStart_5526868 baseEnd_5526868 := by
    simpa [prefixWord, tailWord_5526868, baseEnd_5526868] using wordTrace_append hprefix tailTrace_5526868
  have hstable : (prefixWord ++ tailWord_5526868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526868).length < 2 ^ (prefixWord ++ tailWord_5526868).sum := by decide
  have hdescent : baseEnd_5526868 < baseStart_5526868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526884 : List Nat := [2, 3, 1, 1, 3, 3, 1, 1, 2, 6]
def baseStart_5526884 : Nat := 118140960795 + 5526884 * 2 ^ 59
def prefixEnd_5526884 : Nat := 4983230072969 + 3 ^ 40 * 5526884 * 2
def baseEnd_5526884 : Nat := 945982671214686424877443

theorem tailTrace_5526884 : CollatzResearch.WordTrace tailWord_5526884 prefixEnd_5526884 945982671214686424877443 := by
  unfold tailWord_5526884
  simp only [CollatzResearch.WordTrace]
  refine ⟨100791010054525329741633853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134388013406033772988845137 100791010054525329741633853)
  ·
    refine ⟨37796628770446998653112695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100791010054525329741633853 37796628770446998653112695)
    ·
      refine ⟨56694943155670497979669043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37796628770446998653112695 56694943155670497979669043)
      ·
        refine ⟨85042414733505746969503565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56694943155670497979669043 85042414733505746969503565)
        ·
          refine ⟨31890905525064655113563837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85042414733505746969503565 31890905525064655113563837)
          ·
            refine ⟨11959089571899245667586439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31890905525064655113563837 11959089571899245667586439)
            ·
              refine ⟨17938634357848868501379659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11959089571899245667586439 17938634357848868501379659)
              ·
                refine ⟨26907951536773302752069489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17938634357848868501379659 26907951536773302752069489)
                ·
                  refine ⟨20180963652579977064052117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26907951536773302752069489 20180963652579977064052117)
                  ·
                    refine ⟨945982671214686424877443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20180963652579977064052117 945982671214686424877443)
                    ·
                      rfl

theorem cell23_5526884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_5526884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526884 prefixEnd_5526884 := by exact prefixLift 5526884
  have htrace : WordTrace (prefixWord ++ tailWord_5526884) baseStart_5526884 baseEnd_5526884 := by
    simpa [prefixWord, tailWord_5526884, baseEnd_5526884] using wordTrace_append hprefix tailTrace_5526884
  have hstable : (prefixWord ++ tailWord_5526884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526884).length < 2 ^ (prefixWord ++ tailWord_5526884).sum := by decide
  have hdescent : baseEnd_5526884 < baseStart_5526884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526897 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 9]
def baseStart_5526897 : Nat := 118140960795 + 5526897 * 2 ^ 59
def prefixEnd_5526897 : Nat := 4983230072969 + 3 ^ 40 * 5526897 * 2
def baseEnd_5526897 : Nat := 315328298765840858196641

theorem tailTrace_5526897 : CollatzResearch.WordTrace tailWord_5526897 prefixEnd_5526897 315328298765840858196641 := by
  unfold tailWord_5526897
  simp only [CollatzResearch.WordTrace]
  refine ⟨201582494258003562703490945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134388329505335708468993963 201582494258003562703490945)
  ·
    refine ⟨151186870693502672027618209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201582494258003562703490945 151186870693502672027618209)
    ·
      refine ⟨113390153020127004020713657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151186870693502672027618209 113390153020127004020713657)
      ·
        refine ⟨85042614765095253015535243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113390153020127004020713657 85042614765095253015535243)
        ·
          refine ⟨127563922147642879523302865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85042614765095253015535243 127563922147642879523302865)
          ·
            refine ⟨95672941610732159642477149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127563922147642879523302865 95672941610732159642477149)
            ·
              refine ⟨35877353104024559865928931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95672941610732159642477149 35877353104024559865928931)
              ·
                refine ⟨53816029656036839798893397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35877353104024559865928931 53816029656036839798893397)
                ·
                  refine ⟨315328298765840858196641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53816029656036839798893397 315328298765840858196641)
                  ·
                    rfl

theorem cell23_5526897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 9].length) (baseStart_5526897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526897 prefixEnd_5526897 := by exact prefixLift 5526897
  have htrace : WordTrace (prefixWord ++ tailWord_5526897) baseStart_5526897 baseEnd_5526897 := by
    simpa [prefixWord, tailWord_5526897, baseEnd_5526897] using wordTrace_append hprefix tailTrace_5526897
  have hstable : (prefixWord ++ tailWord_5526897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526897).length < 2 ^ (prefixWord ++ tailWord_5526897).sum := by decide
  have hdescent : baseEnd_5526897 < baseStart_5526897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526924 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 4, 3, 3]
def baseStart_5526924 : Nat := 118140960795 + 5526924 * 2 ^ 59
def prefixEnd_5526924 : Nat := 4983230072969 + 3 ^ 40 * 5526924 * 2
def baseEnd_5526924 : Nat := 2837968552870239118132145

theorem tailTrace_5526924 : CollatzResearch.WordTrace tailWord_5526924 prefixEnd_5526924 2837968552870239118132145 := by
  unfold tailWord_5526924
  simp only [CollatzResearch.WordTrace]
  refine ⟨100791739514452873157361913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134388986019270497543149217 100791739514452873157361913)
  ·
    refine ⟨75593804635839654868021435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100791739514452873157361913 75593804635839654868021435)
    ·
      refine ⟨113390706953759482302032153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75593804635839654868021435 113390706953759482302032153)
      ·
        refine ⟨85043030215319611726524115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113390706953759482302032153 85043030215319611726524115)
        ·
          refine ⟨127564545322979417589786173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85043030215319611726524115 127564545322979417589786173)
          ·
            refine ⟨47836704496117281596169815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127564545322979417589786173 47836704496117281596169815)
            ·
              refine ⟨71755056744175922394254723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47836704496117281596169815 71755056744175922394254723)
              ·
                refine ⟨107632585116263883591382085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71755056744175922394254723 107632585116263883591382085)
                ·
                  refine ⟨20181109709299478173384141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107632585116263883591382085 20181109709299478173384141)
                  ·
                    refine ⟨7567916140987304315019053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20181109709299478173384141 7567916140987304315019053)
                    ·
                      refine ⟨2837968552870239118132145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7567916140987304315019053 2837968552870239118132145)
                      ·
                        rfl

theorem cell23_5526924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_5526924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526924 prefixEnd_5526924 := by exact prefixLift 5526924
  have htrace : WordTrace (prefixWord ++ tailWord_5526924) baseStart_5526924 baseEnd_5526924 := by
    simpa [prefixWord, tailWord_5526924, baseEnd_5526924] using wordTrace_append hprefix tailTrace_5526924
  have hstable : (prefixWord ++ tailWord_5526924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526924).length < 2 ^ (prefixWord ++ tailWord_5526924).sum := by decide
  have hdescent : baseEnd_5526924 < baseStart_5526924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526941 : List Nat := [1, 4, 2, 1, 3, 1, 2, 1, 2, 3, 3]
def baseStart_5526941 : Nat := 118140960795 + 5526941 * 2 ^ 59
def prefixEnd_5526941 : Nat := 4983230072969 + 3 ^ 40 * 5526941 * 2
def baseEnd_5526941 : Nat := 2837977282041365551619567

theorem tailTrace_5526941 : CollatzResearch.WordTrace tailWord_5526941 prefixEnd_5526941 2837977282041365551619567 := by
  unfold tailWord_5526941
  simp only [CollatzResearch.WordTrace]
  refine ⟨201584099069844158218092677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134389399379896105478728451 201584099069844158218092677)
  ·
    refine ⟨37797018575595779665892377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201584099069844158218092677 37797018575595779665892377)
    ·
      refine ⟨28347763931696834749419283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37797018575595779665892377 28347763931696834749419283)
      ·
        refine ⟨42521645897545252124128925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28347763931696834749419283 42521645897545252124128925)
        ·
          refine ⟨15945617211579469546548347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42521645897545252124128925 15945617211579469546548347)
          ·
            refine ⟨23918425817369204319822521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15945617211579469546548347 23918425817369204319822521)
            ·
              refine ⟨17938819363026903239866891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23918425817369204319822521 17938819363026903239866891)
              ·
                refine ⟨26908229044540354859800337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17938819363026903239866891 26908229044540354859800337)
                ·
                  refine ⟨20181171783405266144850253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26908229044540354859800337 20181171783405266144850253)
                  ·
                    refine ⟨7567939418776974804318845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20181171783405266144850253 7567939418776974804318845)
                    ·
                      refine ⟨2837977282041365551619567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7567939418776974804318845 2837977282041365551619567)
                      ·
                        rfl

theorem cell23_5526941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_5526941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526941 prefixEnd_5526941 := by exact prefixLift 5526941
  have htrace : WordTrace (prefixWord ++ tailWord_5526941) baseStart_5526941 baseEnd_5526941 := by
    simpa [prefixWord, tailWord_5526941, baseEnd_5526941] using wordTrace_append hprefix tailTrace_5526941
  have hstable : (prefixWord ++ tailWord_5526941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526941).length < 2 ^ (prefixWord ++ tailWord_5526941).sum := by decide
  have hdescent : baseEnd_5526941 < baseStart_5526941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526942 : List Nat := [4, 3, 1, 2, 2, 2, 1, 1, 1, 4, 2]
def baseStart_5526942 : Nat := 118140960795 + 5526942 * 2 ^ 59
def prefixEnd_5526942 : Nat := 4983230072969 + 3 ^ 40 * 5526942 * 2
def baseEnd_5526942 : Nat := 2837977795522020047707063

theorem tailTrace_5526942 : CollatzResearch.WordTrace tailWord_5526942 prefixEnd_5526942 2837977795522020047707063 := by
  unfold tailWord_5526942
  simp only [CollatzResearch.WordTrace]
  refine ⟨25198016942855066923609885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134389423695227023592586053 25198016942855066923609885)
  ·
    refine ⟨9449256353570650096353707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25198016942855066923609885 9449256353570650096353707)
    ·
      refine ⟨14173884530355975144530561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9449256353570650096353707 14173884530355975144530561)
      ·
        refine ⟨10630413397766981358397921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14173884530355975144530561 10630413397766981358397921)
        ·
          refine ⟨7972810048325236018798441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10630413397766981358397921 7972810048325236018798441)
          ·
            refine ⟨5979607536243927014098831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7972810048325236018798441 5979607536243927014098831)
            ·
              refine ⟨8969411304365890521148247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5979607536243927014098831 8969411304365890521148247)
              ·
                refine ⟨13454116956548835781722371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8969411304365890521148247 13454116956548835781722371)
                ·
                  refine ⟨20181175434823253672583557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13454116956548835781722371 20181175434823253672583557)
                  ·
                    refine ⟨3783970394029360063609417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20181175434823253672583557 3783970394029360063609417)
                    ·
                      refine ⟨2837977795522020047707063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3783970394029360063609417 2837977795522020047707063)
                      ·
                        rfl

theorem cell23_5526942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_5526942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526942 prefixEnd_5526942 := by exact prefixLift 5526942
  have htrace : WordTrace (prefixWord ++ tailWord_5526942) baseStart_5526942 baseEnd_5526942 := by
    simpa [prefixWord, tailWord_5526942, baseEnd_5526942] using wordTrace_append hprefix tailTrace_5526942
  have hstable : (prefixWord ++ tailWord_5526942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526942).length < 2 ^ (prefixWord ++ tailWord_5526942).sum := by decide
  have hdescent : baseEnd_5526942 < baseStart_5526942 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5526991 : List Nat := [1, 1, 2, 1, 1, 4, 5, 1, 3, 4]
def baseStart_5526991 : Nat := 118140960795 + 5526991 * 2 ^ 59
def prefixEnd_5526991 : Nat := 4983230072969 + 3 ^ 40 * 5526991 * 2
def baseEnd_5526991 : Nat := 946000985358030118664779

theorem tailTrace_5526991 : CollatzResearch.WordTrace tailWord_5526991 prefixEnd_5526991 946000985358030118664779 := by
  unfold tailWord_5526991
  simp only [CollatzResearch.WordTrace]
  refine ⟨201585922719663016757412827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134390615146442011171608551 201585922719663016757412827)
  ·
    refine ⟨302378884079494525136119241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201585922719663016757412827 302378884079494525136119241)
    ·
      refine ⟨226784163059620893852089431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302378884079494525136119241 226784163059620893852089431)
      ·
        refine ⟨340176244589431340778134147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226784163059620893852089431 340176244589431340778134147)
        ·
          refine ⟨510264366884147011167201221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340176244589431340778134147 510264366884147011167201221)
          ·
            refine ⟨95674568790777564593850229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 510264366884147011167201221 95674568790777564593850229)
            ·
              refine ⟨8969490824135396680673459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95674568790777564593850229 8969490824135396680673459)
              ·
                refine ⟨13454236236203095021010189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8969490824135396680673459 13454236236203095021010189)
                ·
                  refine ⟨5045338588576160632878821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13454236236203095021010189 5045338588576160632878821)
                  ·
                    refine ⟨946000985358030118664779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5045338588576160632878821 946000985358030118664779)
                    ·
                      rfl

theorem cell23_5526991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 3, 4].length) (baseStart_5526991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5526991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5526991 prefixEnd_5526991 := by exact prefixLift 5526991
  have htrace : WordTrace (prefixWord ++ tailWord_5526991) baseStart_5526991 baseEnd_5526991 := by
    simpa [prefixWord, tailWord_5526991, baseEnd_5526991] using wordTrace_append hprefix tailTrace_5526991
  have hstable : (prefixWord ++ tailWord_5526991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5526991).length < 2 ^ (prefixWord ++ tailWord_5526991).sum := by decide
  have hdescent : baseEnd_5526991 < baseStart_5526991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5526991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527031 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 7, 1, 3]
def baseStart_5527031 : Nat := 118140960795 + 5527031 * 2 ^ 59
def prefixEnd_5527031 : Nat := 4983230072969 + 3 ^ 40 * 5527031 * 2
def baseEnd_5527031 : Nat := 2838023495300270199494153

theorem tailTrace_5527031 : CollatzResearch.WordTrace tailWord_5527031 prefixEnd_5527031 2838023495300270199494153 := by
  unfold tailWord_5527031
  simp only [CollatzResearch.WordTrace]
  refine ⟨201587381639518103588868947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134391587759678735725912631 201587381639518103588868947)
  ·
    refine ⟨302381072459277155383303421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201587381639518103588868947 302381072459277155383303421)
    ·
      refine ⟨113392902172228933268738783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302381072459277155383303421 113392902172228933268738783)
      ·
        refine ⟨170089353258343399903108175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113392902172228933268738783 170089353258343399903108175)
        ·
          refine ⟨255134029887515099854662263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170089353258343399903108175 255134029887515099854662263)
          ·
            refine ⟨382701044831272649781993395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255134029887515099854662263 382701044831272649781993395)
            ·
              refine ⟨574051567246908974672990093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382701044831272649781993395 574051567246908974672990093)
              ·
                refine ⟨215269337717590865502371285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 574051567246908974672990093 215269337717590865502371285)
                ·
                  refine ⟨5045375102756035910211827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 215269337717590865502371285 5045375102756035910211827)
                  ·
                    refine ⟨7568062654134053865317741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5045375102756035910211827 7568062654134053865317741)
                    ·
                      refine ⟨2838023495300270199494153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7568062654134053865317741 2838023495300270199494153)
                      ·
                        rfl

theorem cell23_5527031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 7, 1, 3].length) (baseStart_5527031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527031 prefixEnd_5527031 := by exact prefixLift 5527031
  have htrace : WordTrace (prefixWord ++ tailWord_5527031) baseStart_5527031 baseEnd_5527031 := by
    simpa [prefixWord, tailWord_5527031, baseEnd_5527031] using wordTrace_append hprefix tailTrace_5527031
  have hstable : (prefixWord ++ tailWord_5527031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527031).length < 2 ^ (prefixWord ++ tailWord_5527031).sum := by decide
  have hdescent : baseEnd_5527031 < baseStart_5527031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527042 : List Nat := [3, 4, 1, 2, 1, 2, 1, 4, 1, 4]
def baseStart_5527042 : Nat := 118140960795 + 5527042 * 2 ^ 59
def prefixEnd_5527042 : Nat := 4983230072969 + 3 ^ 40 * 5527042 * 2
def baseEnd_5527042 : Nat := 946009714529156552152201

theorem tailTrace_5527042 : CollatzResearch.WordTrace tailWord_5527042 prefixEnd_5527042 946009714529156552152201 := by
  unfold tailWord_5527042
  simp only [CollatzResearch.WordTrace]
  refine ⟨50396945710619563116879845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134391855228318834978346253 50396945710619563116879845)
  ·
    refine ⟨9449427320741168084414971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50396945710619563116879845 9449427320741168084414971)
    ·
      refine ⟨14174140981111752126622457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9449427320741168084414971 14174140981111752126622457)
      ·
        refine ⟨10630605735833814094966843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14174140981111752126622457 10630605735833814094966843)
        ·
          refine ⟨15945908603750721142450265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10630605735833814094966843 15945908603750721142450265)
          ·
            refine ⟨11959431452813040856837699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15945908603750721142450265 11959431452813040856837699)
            ·
              refine ⟨17939147179219561285256549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11959431452813040856837699 17939147179219561285256549)
              ·
                refine ⟨3363590096103667740985603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17939147179219561285256549 3363590096103667740985603)
                ·
                  refine ⟨5045385144155501611478405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3363590096103667740985603 5045385144155501611478405)
                  ·
                    refine ⟨946009714529156552152201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5045385144155501611478405 946009714529156552152201)
                    ·
                      rfl

theorem cell23_5527042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_5527042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527042 prefixEnd_5527042 := by exact prefixLift 5527042
  have htrace : WordTrace (prefixWord ++ tailWord_5527042) baseStart_5527042 baseEnd_5527042 := by
    simpa [prefixWord, tailWord_5527042, baseEnd_5527042] using wordTrace_append hprefix tailTrace_5527042
  have hstable : (prefixWord ++ tailWord_5527042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527042).length < 2 ^ (prefixWord ++ tailWord_5527042).sum := by decide
  have hdescent : baseEnd_5527042 < baseStart_5527042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527071 : List Nat := [1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 4]
def baseStart_5527071 : Nat := 118140960795 + 5527071 * 2 ^ 59
def prefixEnd_5527071 : Nat := 4983230072969 + 3 ^ 40 * 5527071 * 2
def baseEnd_5527071 : Nat := 2838044034526450042993969

theorem tailTrace_5527071 : CollatzResearch.WordTrace tailWord_5527071 prefixEnd_5527071 2838044034526450042993969 := by
  unfold tailWord_5527071
  simp only [CollatzResearch.WordTrace]
  refine ⟨201588840559373190420325067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134392560372915460280216711 201588840559373190420325067)
  ·
    refine ⟨302383260839059785630487601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201588840559373190420325067 302383260839059785630487601)
    ·
      refine ⟨226787445629294839222865701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302383260839059785630487601 226787445629294839222865701)
      ·
        refine ⟨42522646055492782354287319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 226787445629294839222865701 42522646055492782354287319)
        ·
          refine ⟨63783969083239173531430979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42522646055492782354287319 63783969083239173531430979)
          ·
            refine ⟨95675953624858760297146469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63783969083239173531430979 95675953624858760297146469)
            ·
              refine ⟨17939241304661017555714963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95675953624858760297146469 17939241304661017555714963)
              ·
                refine ⟨26908861956991526333572445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17939241304661017555714963 26908861956991526333572445)
                ·
                  refine ⟨10090823233871822375089667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26908861956991526333572445 10090823233871822375089667)
                  ·
                    refine ⟨15136234850807733562634501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10090823233871822375089667 15136234850807733562634501)
                    ·
                      refine ⟨2838044034526450042993969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15136234850807733562634501 2838044034526450042993969)
                      ·
                        rfl

theorem cell23_5527071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_5527071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527071 prefixEnd_5527071 := by exact prefixLift 5527071
  have htrace : WordTrace (prefixWord ++ tailWord_5527071) baseStart_5527071 baseEnd_5527071 := by
    simpa [prefixWord, tailWord_5527071, baseEnd_5527071] using wordTrace_append hprefix tailTrace_5527071
  have hstable : (prefixWord ++ tailWord_5527071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527071).length < 2 ^ (prefixWord ++ tailWord_5527071).sum := by decide
  have hdescent : baseEnd_5527071 < baseStart_5527071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527082 : List Nat := [3, 1, 4, 1, 1, 1, 4, 3, 1, 1, 3]
def baseStart_5527082 : Nat := 118140960795 + 5527082 * 2 ^ 59
def prefixEnd_5527082 : Nat := 4983230072969 + 3 ^ 40 * 5527082 * 2
def baseEnd_5527082 : Nat := 2838049682813649499956419

theorem tailTrace_5527082 : CollatzResearch.WordTrace tailWord_5527082 prefixEnd_5527082 2838049682813649499956419 := by
  unfold tailWord_5527082
  simp only [CollatzResearch.WordTrace]
  refine ⟨50397310440583334824743875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134392827841555559532650333 50397310440583334824743875)
  ·
    refine ⟨75595965660875002237115813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50397310440583334824743875 75595965660875002237115813)
    ·
      refine ⟨14174243561414062919459215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75595965660875002237115813 14174243561414062919459215)
      ·
        refine ⟨21261365342121094379188823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14174243561414062919459215 21261365342121094379188823)
        ·
          refine ⟨31892048013181641568783235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21261365342121094379188823 31892048013181641568783235)
          ·
            refine ⟨47838072019772462353174853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31892048013181641568783235 47838072019772462353174853)
            ·
              refine ⟨8969638503707336691220285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47838072019772462353174853 8969638503707336691220285)
              ·
                refine ⟨3363614438890251259207607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8969638503707336691220285 3363614438890251259207607)
                ·
                  refine ⟨5045421658335376888811411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3363614438890251259207607 5045421658335376888811411)
                  ·
                    refine ⟨7568132487503065333217117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5045421658335376888811411 7568132487503065333217117)
                    ·
                      refine ⟨2838049682813649499956419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7568132487503065333217117 2838049682813649499956419)
                      ·
                        rfl

theorem cell23_5527082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_5527082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527082 prefixEnd_5527082 := by exact prefixLift 5527082
  have htrace : WordTrace (prefixWord ++ tailWord_5527082) baseStart_5527082 baseEnd_5527082 := by
    simpa [prefixWord, tailWord_5527082, baseEnd_5527082] using wordTrace_append hprefix tailTrace_5527082
  have hstable : (prefixWord ++ tailWord_5527082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527082).length < 2 ^ (prefixWord ++ tailWord_5527082).sum := by decide
  have hdescent : baseEnd_5527082 < baseStart_5527082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527084 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 6]
def baseStart_5527084 : Nat := 118140960795 + 5527084 * 2 ^ 59
def prefixEnd_5527084 : Nat := 4983230072969 + 3 ^ 40 * 5527084 * 2
def baseEnd_5527084 : Nat := 2838050709774958492131409

theorem tailTrace_5527084 : CollatzResearch.WordTrace tailWord_5527084 prefixEnd_5527084 2838050709774958492131409 := by
  unfold tailWord_5527084
  simp only [CollatzResearch.WordTrace]
  refine ⟨100794657354163046820274153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134392876472217395760365537 100794657354163046820274153)
  ·
    refine ⟨75595993015622285115205615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100794657354163046820274153 75595993015622285115205615)
    ·
      refine ⟨113393989523433427672808423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75595993015622285115205615 113393989523433427672808423)
      ·
        refine ⟨170090984285150141509212635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113393989523433427672808423 170090984285150141509212635)
        ·
          refine ⟨255136476427725212263818953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170090984285150141509212635 255136476427725212263818953)
          ·
            refine ⟨191352357320793909197864215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255136476427725212263818953 191352357320793909197864215)
            ·
              refine ⟨287028535981190863796796323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191352357320793909197864215 287028535981190863796796323)
              ·
                refine ⟨430542803971786295695194485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 287028535981190863796796323 430542803971786295695194485)
                ·
                  refine ⟨40363387872354965221424483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 430542803971786295695194485 40363387872354965221424483)
                  ·
                    refine ⟨60545081808532447832136725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40363387872354965221424483 60545081808532447832136725)
                    ·
                      refine ⟨2838050709774958492131409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60545081808532447832136725 2838050709774958492131409)
                      ·
                        rfl

theorem cell23_5527084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_5527084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527084 prefixEnd_5527084 := by exact prefixLift 5527084
  have htrace : WordTrace (prefixWord ++ tailWord_5527084) baseStart_5527084 baseEnd_5527084 := by
    simpa [prefixWord, tailWord_5527084, baseEnd_5527084] using wordTrace_append hprefix tailTrace_5527084
  have hstable : (prefixWord ++ tailWord_5527084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527084).length < 2 ^ (prefixWord ++ tailWord_5527084).sum := by decide
  have hdescent : baseEnd_5527084 < baseStart_5527084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527088 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 7, 2, 2]
def baseStart_5527088 : Nat := 118140960795 + 5527088 * 2 ^ 59
def prefixEnd_5527088 : Nat := 4983230072969 + 3 ^ 40 * 5527088 * 2
def baseEnd_5527088 : Nat := 2838052763697576476481391

theorem tailTrace_5527088 : CollatzResearch.WordTrace tailWord_5527088 prefixEnd_5527088 2838052763697576476481391 := by
  unfold tailWord_5527088
  simp only [CollatzResearch.WordTrace]
  refine ⟨100794730300155801161846959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134392973733541068215795945 100794730300155801161846959)
  ·
    refine ⟨151192095450233701742770439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100794730300155801161846959 151192095450233701742770439)
    ·
      refine ⟨226788143175350552614155659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151192095450233701742770439 226788143175350552614155659)
      ·
        refine ⟨340182214763025828921233489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226788143175350552614155659 340182214763025828921233489)
        ·
          refine ⟨255136661072269371690925117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 340182214763025828921233489 255136661072269371690925117)
          ·
            refine ⟨95676247902101014384096919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 255136661072269371690925117 95676247902101014384096919)
            ·
              refine ⟨143514371853151521576145379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95676247902101014384096919 143514371853151521576145379)
              ·
                refine ⟨215271557779727282364218069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143514371853151521576145379 215271557779727282364218069)
                ·
                  refine ⟨5045427135462358180411361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 215271557779727282364218069 5045427135462358180411361)
                  ·
                    refine ⟨3784070351596768635308521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5045427135462358180411361 3784070351596768635308521)
                    ·
                      refine ⟨2838052763697576476481391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3784070351596768635308521 2838052763697576476481391)
                      ·
                        rfl

theorem cell23_5527088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 7, 2, 2].length) (baseStart_5527088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527088 prefixEnd_5527088 := by exact prefixLift 5527088
  have htrace : WordTrace (prefixWord ++ tailWord_5527088) baseStart_5527088 baseEnd_5527088 := by
    simpa [prefixWord, tailWord_5527088, baseEnd_5527088] using wordTrace_append hprefix tailTrace_5527088
  have hstable : (prefixWord ++ tailWord_5527088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527088).length < 2 ^ (prefixWord ++ tailWord_5527088).sum := by decide
  have hdescent : baseEnd_5527088 < baseStart_5527088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527104 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 7]
def baseStart_5527104 : Nat := 118140960795 + 5527104 * 2 ^ 59
def prefixEnd_5527104 : Nat := 4983230072969 + 3 ^ 40 * 5527104 * 2
def baseEnd_5527104 : Nat := 2838060979388048413881317

theorem tailTrace_5527104 : CollatzResearch.WordTrace tailWord_5527104 prefixEnd_5527104 2838060979388048413881317 := by
  unfold tailWord_5527104
  simp only [CollatzResearch.WordTrace]
  refine ⟨100795022084126818528138183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134393362778835758037517577 100795022084126818528138183)
  ·
    refine ⟨151192533126190227792207275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100795022084126818528138183 151192533126190227792207275)
    ·
      refine ⟨226788799689285341688310913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151192533126190227792207275 226788799689285341688310913)
      ·
        refine ⟨170091599766964006266233185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226788799689285341688310913 170091599766964006266233185)
        ·
          refine ⟨127568699825223004699674889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170091599766964006266233185 127568699825223004699674889)
          ·
            refine ⟨95676524868917253524756167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127568699825223004699674889 95676524868917253524756167)
            ·
              refine ⟨143514787303375880287134251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95676524868917253524756167 143514787303375880287134251)
              ·
                refine ⟨215272180955063820430701377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143514787303375880287134251 215272180955063820430701377)
                ·
                  refine ⟨161454135716297865323026033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 215272180955063820430701377 161454135716297865323026033)
                  ·
                    refine ⟨121090601787223398992269525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 161454135716297865323026033 121090601787223398992269525)
                    ·
                      refine ⟨2838060979388048413881317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 121090601787223398992269525 2838060979388048413881317)
                      ·
                        rfl

theorem cell23_5527104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_5527104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527104 prefixEnd_5527104 := by exact prefixLift 5527104
  have htrace : WordTrace (prefixWord ++ tailWord_5527104) baseStart_5527104 baseEnd_5527104 := by
    simpa [prefixWord, tailWord_5527104, baseEnd_5527104] using wordTrace_append hprefix tailTrace_5527104
  have hstable : (prefixWord ++ tailWord_5527104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527104).length < 2 ^ (prefixWord ++ tailWord_5527104).sum := by decide
  have hdescent : baseEnd_5527104 < baseStart_5527104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527133 : List Nat := [1, 4, 4, 2, 2, 1, 1, 3, 1, 1, 3]
def baseStart_5527133 : Nat := 118140960795 + 5527133 * 2 ^ 59
def prefixEnd_5527133 : Nat := 4983230072969 + 3 ^ 40 * 5527133 * 2
def baseEnd_5527133 : Nat := 2838075870327028800418685

theorem tailTrace_5527133 : CollatzResearch.WordTrace tailWord_5527133 prefixEnd_5527133 2838075870327028800418685 := by
  unfold tailWord_5527133
  simp only [CollatzResearch.WordTrace]
  refine ⟨201591101885148575009082053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134394067923432383339388035 201591101885148575009082053)
  ·
    refine ⟨37798331603465357814202885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201591101885148575009082053 37798331603465357814202885)
    ·
      refine ⟨7087187175649754590163041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37798331603465357814202885 7087187175649754590163041)
      ·
        refine ⟨5315390381737315942622281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7087187175649754590163041 5315390381737315942622281)
        ·
          refine ⟨3986542786302986956966711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5315390381737315942622281 3986542786302986956966711)
          ·
            refine ⟨5979814179454480435450067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3986542786302986956966711 5979814179454480435450067)
            ·
              refine ⟨8969721269181720653175101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5979814179454480435450067 8969721269181720653175101)
              ·
                refine ⟨3363645475943145244940663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8969721269181720653175101 3363645475943145244940663)
                ·
                  refine ⟨5045468213914717867410995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3363645475943145244940663 5045468213914717867410995)
                  ·
                    refine ⟨7568202320872076801116493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5045468213914717867410995 7568202320872076801116493)
                    ·
                      refine ⟨2838075870327028800418685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7568202320872076801116493 2838075870327028800418685)
                      ·
                        rfl

theorem cell23_5527133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_5527133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527133 prefixEnd_5527133 := by exact prefixLift 5527133
  have htrace : WordTrace (prefixWord ++ tailWord_5527133) baseStart_5527133 baseEnd_5527133 := by
    simpa [prefixWord, tailWord_5527133, baseEnd_5527133] using wordTrace_append hprefix tailTrace_5527133
  have hstable : (prefixWord ++ tailWord_5527133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527133).length < 2 ^ (prefixWord ++ tailWord_5527133).sum := by decide
  have hdescent : baseEnd_5527133 < baseStart_5527133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527139 : List Nat := [1, 1, 1, 5, 1, 5, 1, 3, 1, 2, 2]
def baseStart_5527139 : Nat := 118140960795 + 5527139 * 2 ^ 59
def prefixEnd_5527139 : Nat := 4983230072969 + 3 ^ 40 * 5527139 * 2
def baseEnd_5527139 : Nat := 2838078951210955776943657

theorem tailTrace_5527139 : CollatzResearch.WordTrace tailWord_5527139 prefixEnd_5527139 2838078951210955776943657 := by
  unfold tailWord_5527139
  simp only [CollatzResearch.WordTrace]
  refine ⟨201591320723126838033800471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134394213815417892022533647 201591320723126838033800471)
  ·
    refine ⟨302386981084690257050700707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201591320723126838033800471 302386981084690257050700707)
    ·
      refine ⟨453580471627035385576051061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302386981084690257050700707 453580471627035385576051061)
      ·
        refine ⟨42523169215034567397754787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 453580471627035385576051061 42523169215034567397754787)
        ·
          refine ⟨63784753822551851096632181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42523169215034567397754787 63784753822551851096632181)
          ·
            refine ⟨5979820670864236040309267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63784753822551851096632181 5979820670864236040309267)
            ·
              refine ⟨8969731006296354060463901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5979820670864236040309267 8969731006296354060463901)
              ·
                refine ⟨3363649127361132772673963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8969731006296354060463901 3363649127361132772673963)
                ·
                  refine ⟨5045473691041699159010945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3363649127361132772673963 5045473691041699159010945)
                  ·
                    refine ⟨3784105268281274369258209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5045473691041699159010945 3784105268281274369258209)
                    ·
                      refine ⟨2838078951210955776943657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3784105268281274369258209 2838078951210955776943657)
                      ·
                        rfl

theorem cell23_5527139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_5527139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527139 prefixEnd_5527139 := by exact prefixLift 5527139
  have htrace : WordTrace (prefixWord ++ tailWord_5527139) baseStart_5527139 baseEnd_5527139 := by
    simpa [prefixWord, tailWord_5527139, baseEnd_5527139] using wordTrace_append hprefix tailTrace_5527139
  have hstable : (prefixWord ++ tailWord_5527139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527139).length < 2 ^ (prefixWord ++ tailWord_5527139).sum := by decide
  have hdescent : baseEnd_5527139 < baseStart_5527139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527148 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 5, 3, 2]
def baseStart_5527148 : Nat := 118140960795 + 5527148 * 2 ^ 59
def prefixEnd_5527148 : Nat := 4983230072969 + 3 ^ 40 * 5527148 * 2
def baseEnd_5527148 : Nat := 2838083572536846241731115

theorem tailTrace_5527148 : CollatzResearch.WordTrace tailWord_5527148 prefixEnd_5527148 2838083572536846241731115 := by
  unfold tailWord_5527148
  simp only [CollatzResearch.WordTrace]
  refine ⟨100795824490047116285439049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134394432653396155047252065 100795824490047116285439049)
  ·
    refine ⟨75596868367535337214079287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100795824490047116285439049 75596868367535337214079287)
    ·
      refine ⟨113395302551303005821118931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75596868367535337214079287 113395302551303005821118931)
      ·
        refine ⟨170092953826954508731678397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113395302551303005821118931 170092953826954508731678397)
        ·
          refine ⟨63784857685107940774379399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170092953826954508731678397 63784857685107940774379399)
          ·
            refine ⟨95677286527661911161569099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63784857685107940774379399 95677286527661911161569099)
            ·
              refine ⟨143515929791492866742353649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95677286527661911161569099 143515929791492866742353649)
              ·
                refine ⟨107636947343619650056765237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143515929791492866742353649 107636947343619650056765237)
                ·
                  refine ⟨10090963813464342192821741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 107636947343619650056765237 10090963813464342192821741)
                  ·
                    refine ⟨3784111430049128322308153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10090963813464342192821741 3784111430049128322308153)
                    ·
                      refine ⟨2838083572536846241731115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3784111430049128322308153 2838083572536846241731115)
                      ·
                        rfl

theorem cell23_5527148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 3, 2].length) (baseStart_5527148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527148 prefixEnd_5527148 := by exact prefixLift 5527148
  have htrace : WordTrace (prefixWord ++ tailWord_5527148) baseStart_5527148 baseEnd_5527148 := by
    simpa [prefixWord, tailWord_5527148, baseEnd_5527148] using wordTrace_append hprefix tailTrace_5527148
  have hstable : (prefixWord ++ tailWord_5527148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527148).length < 2 ^ (prefixWord ++ tailWord_5527148).sum := by decide
  have hdescent : baseEnd_5527148 < baseStart_5527148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527161 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 2, 3, 4]
def baseStart_5527161 : Nat := 118140960795 + 5527161 * 2 ^ 59
def prefixEnd_5527161 : Nat := 4983230072969 + 3 ^ 40 * 5527161 * 2
def baseEnd_5527161 : Nat := 2838090247785354690868555

theorem tailTrace_5527161 : CollatzResearch.WordTrace tailWord_5527161 prefixEnd_5527161 2838090247785354690868555 := by
  unfold tailWord_5527161
  simp only [CollatzResearch.WordTrace]
  refine ⟨201592123129047135791101337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134394748752698090527400891 201592123129047135791101337)
  ·
    refine ⟨151194092346785351843326003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201592123129047135791101337 151194092346785351843326003)
    ·
      refine ⟨226791138520178027764989005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151194092346785351843326003 226791138520178027764989005)
      ·
        refine ⟨85046676945066760411870877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226791138520178027764989005 85046676945066760411870877)
        ·
          refine ⟨31892503854400035154451579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85046676945066760411870877 31892503854400035154451579)
          ·
            refine ⟨47838755781600052731677369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31892503854400035154451579 47838755781600052731677369)
            ·
              refine ⟨35879066836200039548758027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47838755781600052731677369 35879066836200039548758027)
              ·
                refine ⟨53818600254300059323137041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35879066836200039548758027 53818600254300059323137041)
                ·
                  refine ⟨40363950190725044492352781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53818600254300059323137041 40363950190725044492352781)
                  ·
                    refine ⟨15136481321521891684632293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40363950190725044492352781 15136481321521891684632293)
                    ·
                      refine ⟨2838090247785354690868555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15136481321521891684632293 2838090247785354690868555)
                      ·
                        rfl

theorem cell23_5527161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_5527161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527161 prefixEnd_5527161 := by exact prefixLift 5527161
  have htrace : WordTrace (prefixWord ++ tailWord_5527161) baseStart_5527161 baseEnd_5527161 := by
    simpa [prefixWord, tailWord_5527161, baseEnd_5527161] using wordTrace_append hprefix tailTrace_5527161
  have hstable : (prefixWord ++ tailWord_5527161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527161).length < 2 ^ (prefixWord ++ tailWord_5527161).sum := by decide
  have hdescent : baseEnd_5527161 < baseStart_5527161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527172 : List Nat := [2, 3, 2, 1, 4, 1, 1, 3, 2, 1, 3]
def baseStart_5527172 : Nat := 118140960795 + 5527172 * 2 ^ 59
def prefixEnd_5527172 : Nat := 4983230072969 + 3 ^ 40 * 5527172 * 2
def baseEnd_5527172 : Nat := 2838095896072554147831005

theorem tailTrace_5527172 : CollatzResearch.WordTrace tailWord_5527172 prefixEnd_5527172 2838095896072554147831005 := by
  unfold tailWord_5527172
  simp only [CollatzResearch.WordTrace]
  refine ⟨100796262166003642334875885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134395016221338189779834513 100796262166003642334875885)
  ·
    refine ⟨37798598312251365875578457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100796262166003642334875885 37798598312251365875578457)
    ·
      refine ⟨28348948734188524406683843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37798598312251365875578457 28348948734188524406683843)
      ·
        refine ⟨42523423101282786610025765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28348948734188524406683843 42523423101282786610025765)
        ·
          refine ⟨7973141831490522489379831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42523423101282786610025765 7973141831490522489379831)
          ·
            refine ⟨11959712747235783734069747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7973141831490522489379831 11959712747235783734069747)
            ·
              refine ⟨17939569120853675601104621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11959712747235783734069747 17939569120853675601104621)
              ·
                refine ⟨6727338420320128350414233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17939569120853675601104621 6727338420320128350414233)
                ·
                  refine ⟨5045503815240096262810675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6727338420320128350414233 5045503815240096262810675)
                  ·
                    refine ⟨7568255722860144394216013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5045503815240096262810675 7568255722860144394216013)
                    ·
                      refine ⟨2838095896072554147831005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7568255722860144394216013 2838095896072554147831005)
                      ·
                        rfl

theorem cell23_5527172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_5527172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527172 prefixEnd_5527172 := by exact prefixLift 5527172
  have htrace : WordTrace (prefixWord ++ tailWord_5527172) baseStart_5527172 baseEnd_5527172 := by
    simpa [prefixWord, tailWord_5527172, baseEnd_5527172] using wordTrace_append hprefix tailTrace_5527172
  have hstable : (prefixWord ++ tailWord_5527172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527172).length < 2 ^ (prefixWord ++ tailWord_5527172).sum := by decide
  have hdescent : baseEnd_5527172 < baseStart_5527172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527182 : List Nat := [4, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2]
def baseStart_5527182 : Nat := 118140960795 + 5527182 * 2 ^ 59
def prefixEnd_5527182 : Nat := 4983230072969 + 3 ^ 40 * 5527182 * 2
def baseEnd_5527182 : Nat := 2838101030879099108705959

theorem tailTrace_5527182 : CollatzResearch.WordTrace tailWord_5527182 prefixEnd_5527182 2838101030879099108705959 := by
  unfold tailWord_5527182
  simp only [CollatzResearch.WordTrace]
  refine ⟨25199111132746382047201975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134395259374647370918410533 25199111132746382047201975)
  ·
    refine ⟨37798666699119573070802963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25199111132746382047201975 37798666699119573070802963)
    ·
      refine ⟨56698000048679359606204445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37798666699119573070802963 56698000048679359606204445)
      ·
        refine ⟨21261750018254759852326667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56698000048679359606204445 21261750018254759852326667)
        ·
          refine ⟨31892625027382139778490001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21261750018254759852326667 31892625027382139778490001)
          ·
            refine ⟨23919468770536604833867501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31892625027382139778490001 23919468770536604833867501)
            ·
              refine ⟨8969800788951226812700313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23919468770536604833867501 8969800788951226812700313)
              ·
                refine ⟨6727350591713420109525235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8969800788951226812700313 6727350591713420109525235)
                ·
                  refine ⟨10091025887570130164287853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6727350591713420109525235 10091025887570130164287853)
                  ·
                    refine ⟨3784134707838798811607945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10091025887570130164287853 3784134707838798811607945)
                    ·
                      refine ⟨2838101030879099108705959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3784134707838798811607945 2838101030879099108705959)
                      ·
                        rfl

theorem cell23_5527182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_5527182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527182 prefixEnd_5527182 := by exact prefixLift 5527182
  have htrace : WordTrace (prefixWord ++ tailWord_5527182) baseStart_5527182 baseEnd_5527182 := by
    simpa [prefixWord, tailWord_5527182, baseEnd_5527182] using wordTrace_append hprefix tailTrace_5527182
  have hstable : (prefixWord ++ tailWord_5527182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527182).length < 2 ^ (prefixWord ++ tailWord_5527182).sum := by decide
  have hdescent : baseEnd_5527182 < baseStart_5527182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527228 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 1, 5, 3]
def baseStart_5527228 : Nat := 118140960795 + 5527228 * 2 ^ 59
def prefixEnd_5527228 : Nat := 4983230072969 + 3 ^ 40 * 5527228 * 2
def baseEnd_5527228 : Nat := 2838124650989205928730747

theorem tailTrace_5527228 : CollatzResearch.WordTrace tailWord_5527228 prefixEnd_5527228 2838124650989205928730747 := by
  unfold tailWord_5527228
  simp only [CollatzResearch.WordTrace]
  refine ⟨100797283409902203116895169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134396377879869604155860225 100797283409902203116895169)
  ·
    refine ⟨75597962557426652337671377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100797283409902203116895169 75597962557426652337671377)
    ·
      refine ⟨56698471918069989253253533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75597962557426652337671377 56698471918069989253253533)
      ·
        refine ⟨21261926969276245969970075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56698471918069989253253533 21261926969276245969970075)
        ·
          refine ⟨31892890453914368954955113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21261926969276245969970075 31892890453914368954955113)
          ·
            refine ⟨23919667840435776716216335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31892890453914368954955113 23919667840435776716216335)
            ·
              refine ⟨35879501760653665074324503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23919667840435776716216335 35879501760653665074324503)
              ·
                refine ⟨53819252640980497611486755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35879501760653665074324503 53819252640980497611486755)
                ·
                  refine ⟨80728878961470746417230133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53819252640980497611486755 80728878961470746417230133)
                  ·
                    refine ⟨7568332402637882476615325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80728878961470746417230133 7568332402637882476615325)
                    ·
                      refine ⟨2838124650989205928730747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7568332402637882476615325 2838124650989205928730747)
                      ·
                        rfl

theorem cell23_5527228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_5527228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527228 prefixEnd_5527228 := by exact prefixLift 5527228
  have htrace : WordTrace (prefixWord ++ tailWord_5527228) baseStart_5527228 baseEnd_5527228 := by
    simpa [prefixWord, tailWord_5527228, baseEnd_5527228] using wordTrace_append hprefix tailTrace_5527228
  have hstable : (prefixWord ++ tailWord_5527228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527228).length < 2 ^ (prefixWord ++ tailWord_5527228).sum := by decide
  have hdescent : baseEnd_5527228 < baseStart_5527228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527231 : List Nat := [1, 1, 2, 2, 2, 3, 2, 2, 1, 7]
def baseStart_5527231 : Nat := 118140960795 + 5527231 * 2 ^ 59
def prefixEnd_5527231 : Nat := 4983230072969 + 3 ^ 40 * 5527231 * 2
def baseEnd_5527231 : Nat := 946042063810389805664411

theorem tailTrace_5527231 : CollatzResearch.WordTrace tailWord_5527231 prefixEnd_5527231 946042063810389805664411 := by
  unfold tailWord_5527231
  simp only [CollatzResearch.WordTrace]
  refine ⟨201594676238793537746149547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134396450825862358497433031 201594676238793537746149547)
  ·
    refine ⟨302392014358190306619224321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201594676238793537746149547 302392014358190306619224321)
    ·
      refine ⟨226794010768642729964418241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302392014358190306619224321 226794010768642729964418241)
      ·
        refine ⟨170095508076482047473313681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226794010768642729964418241 170095508076482047473313681)
        ·
          refine ⟨127571631057361535604985261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170095508076482047473313681 127571631057361535604985261)
          ·
            refine ⟨47839361646510575851869473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127571631057361535604985261 47839361646510575851869473)
            ·
              refine ⟨35879521234882931888902105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47839361646510575851869473 35879521234882931888902105)
              ·
                refine ⟨26909640926162198916676579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35879521234882931888902105 26909640926162198916676579)
                ·
                  refine ⟨40364461389243298375014869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26909640926162198916676579 40364461389243298375014869)
                  ·
                    refine ⟨946042063810389805664411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40364461389243298375014869 946042063810389805664411)
                    ·
                      rfl

theorem cell23_5527231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 7].length) (baseStart_5527231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527231 prefixEnd_5527231 := by exact prefixLift 5527231
  have htrace : WordTrace (prefixWord ++ tailWord_5527231) baseStart_5527231 baseEnd_5527231 := by
    simpa [prefixWord, tailWord_5527231, baseEnd_5527231] using wordTrace_append hprefix tailTrace_5527231
  have hstable : (prefixWord ++ tailWord_5527231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527231).length < 2 ^ (prefixWord ++ tailWord_5527231).sum := by decide
  have hdescent : baseEnd_5527231 < baseStart_5527231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527252 : List Nat := [2, 4, 1, 3, 1, 2, 2, 3, 5]
def baseStart_5527252 : Nat := 118140960795 + 5527252 * 2 ^ 59
def prefixEnd_5527252 : Nat := 4983230072969 + 3 ^ 40 * 5527252 * 2
def baseEnd_5527252 : Nat := 315348552724990426092293

theorem tailTrace_5527252 : CollatzResearch.WordTrace tailWord_5527252 prefixEnd_5527252 315348552724990426092293 := by
  unfold tailWord_5527252
  simp only [CollatzResearch.WordTrace]
  refine ⟨100797721085858729166332005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134396961447811638888442673 100797721085858729166332005)
  ·
    refine ⟨18899572703598511718687251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100797721085858729166332005 18899572703598511718687251)
    ·
      refine ⟨28349359055397767578030877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18899572703598511718687251 28349359055397767578030877)
      ·
        refine ⟨10631009645774162841761579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28349359055397767578030877 10631009645774162841761579)
        ·
          refine ⟨15946514468661244262642369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10631009645774162841761579 15946514468661244262642369)
          ·
            refine ⟨11959885851495933196981777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15946514468661244262642369 11959885851495933196981777)
            ·
              refine ⟨8969914388621949897736333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11959885851495933196981777 8969914388621949897736333)
              ·
                refine ⟨3363717895733231211651125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8969914388621949897736333 3363717895733231211651125)
                ·
                  refine ⟨315348552724990426092293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3363717895733231211651125 315348552724990426092293)
                  ·
                    rfl

theorem cell23_5527252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_5527252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527252 prefixEnd_5527252 := by exact prefixLift 5527252
  have htrace : WordTrace (prefixWord ++ tailWord_5527252) baseStart_5527252 baseEnd_5527252 := by
    simpa [prefixWord, tailWord_5527252, baseEnd_5527252] using wordTrace_append hprefix tailTrace_5527252
  have hstable : (prefixWord ++ tailWord_5527252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527252).length < 2 ^ (prefixWord ++ tailWord_5527252).sum := by decide
  have hdescent : baseEnd_5527252 < baseStart_5527252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527268 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 4, 1, 4]
def baseStart_5527268 : Nat := 118140960795 + 5527268 * 2 ^ 59
def prefixEnd_5527268 : Nat := 4983230072969 + 3 ^ 40 * 5527268 * 2
def baseEnd_5527268 : Nat := 2838145190215385772230563

theorem tailTrace_5527268 : CollatzResearch.WordTrace tailWord_5527268 prefixEnd_5527268 2838145190215385772230563 := by
  unfold tailWord_5527268
  simp only [CollatzResearch.WordTrace]
  refine ⟨100798012869829746532623229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134397350493106328710164305 100798012869829746532623229)
  ·
    refine ⟨37799254826186154949733711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100798012869829746532623229 37799254826186154949733711)
    ·
      refine ⟨56698882239279232424600567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37799254826186154949733711 56698882239279232424600567)
      ·
        refine ⟨85048323358918848636900851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56698882239279232424600567 85048323358918848636900851)
        ·
          refine ⟨127572485038378272955351277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85048323358918848636900851 127572485038378272955351277)
          ·
            refine ⟨47839681889391852358256729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 127572485038378272955351277 47839681889391852358256729)
            ·
              refine ⟨35879761417043889268692547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47839681889391852358256729 35879761417043889268692547)
              ·
                refine ⟨53819642125565833903038821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35879761417043889268692547 53819642125565833903038821)
                ·
                  refine ⟨10091182898543593856819779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53819642125565833903038821 10091182898543593856819779)
                  ·
                    refine ⟨15136774347815390785229669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10091182898543593856819779 15136774347815390785229669)
                    ·
                      refine ⟨2838145190215385772230563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15136774347815390785229669 2838145190215385772230563)
                      ·
                        rfl

theorem cell23_5527268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_5527268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527268 prefixEnd_5527268 := by exact prefixLift 5527268
  have htrace : WordTrace (prefixWord ++ tailWord_5527268) baseStart_5527268 baseEnd_5527268 := by
    simpa [prefixWord, tailWord_5527268, baseEnd_5527268] using wordTrace_append hprefix tailTrace_5527268
  have hstable : (prefixWord ++ tailWord_5527268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527268).length < 2 ^ (prefixWord ++ tailWord_5527268).sum := by decide
  have hdescent : baseEnd_5527268 < baseStart_5527268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527288 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 6, 2, 3]
def baseStart_5527288 : Nat := 118140960795 + 5527288 * 2 ^ 59
def prefixEnd_5527288 : Nat := 4983230072969 + 3 ^ 40 * 5527288 * 2
def baseEnd_5527288 : Nat := 2838155459828475693980471

theorem tailTrace_5527288 : CollatzResearch.WordTrace tailWord_5527288 prefixEnd_5527288 2838155459828475693980471 := by
  unfold tailWord_5527288
  simp only [CollatzResearch.WordTrace]
  refine ⟨100798377599793518240487259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134397836799724690987316345 100798377599793518240487259)
  ·
    refine ⟨151197566399690277360730889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100798377599793518240487259 151197566399690277360730889)
    ·
      refine ⟨113398174799767708020548167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151197566399690277360730889 113398174799767708020548167)
      ·
        refine ⟨170097262199651562030822251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113398174799767708020548167 170097262199651562030822251)
        ·
          refine ⟨255145893299477343046233377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170097262199651562030822251 255145893299477343046233377)
          ·
            refine ⟨191359419974608007284675033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255145893299477343046233377 191359419974608007284675033)
            ·
              refine ⟨143519564980956005463506275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191359419974608007284675033 143519564980956005463506275)
              ·
                refine ⟨215279347471434008195259413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143519564980956005463506275 215279347471434008195259413)
                ·
                  refine ⟨10091219412723469134152785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 215279347471434008195259413 10091219412723469134152785)
                  ·
                    refine ⟨7568414559542601850614589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10091219412723469134152785 7568414559542601850614589)
                    ·
                      refine ⟨2838155459828475693980471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7568414559542601850614589 2838155459828475693980471)
                      ·
                        rfl

theorem cell23_5527288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 6, 2, 3].length) (baseStart_5527288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527288 prefixEnd_5527288 := by exact prefixLift 5527288
  have htrace : WordTrace (prefixWord ++ tailWord_5527288) baseStart_5527288 baseEnd_5527288 := by
    simpa [prefixWord, tailWord_5527288, baseEnd_5527288] using wordTrace_append hprefix tailTrace_5527288
  have hstable : (prefixWord ++ tailWord_5527288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527288).length < 2 ^ (prefixWord ++ tailWord_5527288).sum := by decide
  have hdescent : baseEnd_5527288 < baseStart_5527288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527301 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 2, 1, 9]
def baseStart_5527301 : Nat := 118140960795 + 5527301 * 2 ^ 59
def prefixEnd_5527301 : Nat := 4983230072969 + 3 ^ 40 * 5527301 * 2
def baseEnd_5527301 : Nat := 2838162135076984143117911

theorem tailTrace_5527301 : CollatzResearch.WordTrace tailWord_5527301 prefixEnd_5527301 2838162135076984143117911 := by
  unfold tailWord_5527301
  simp only [CollatzResearch.WordTrace]
  refine ⟨201597229348539939701197757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134398152899026626467465171 201597229348539939701197757)
  ·
    refine ⟨75598961005702477387949159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201597229348539939701197757 75598961005702477387949159)
    ·
      refine ⟨113398441508553716081923739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75598961005702477387949159 113398441508553716081923739)
      ·
        refine ⟨170097662262830574122885609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113398441508553716081923739 170097662262830574122885609)
        ·
          refine ⟨127573246697122930592164207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170097662262830574122885609 127573246697122930592164207)
          ·
            refine ⟨191359870045684395888246311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127573246697122930592164207 191359870045684395888246311)
            ·
              refine ⟨287039805068526593832369467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191359870045684395888246311 287039805068526593832369467)
              ·
                refine ⟨430559707602789890748554201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 287039805068526593832369467 430559707602789890748554201)
                ·
                  refine ⟨322919780702092418061415651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 430559707602789890748554201 322919780702092418061415651)
                  ·
                    refine ⟨484379671053138627092123477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 322919780702092418061415651 484379671053138627092123477)
                    ·
                      refine ⟨2838162135076984143117911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 484379671053138627092123477 2838162135076984143117911)
                      ·
                        rfl

theorem cell23_5527301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_5527301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527301 prefixEnd_5527301 := by exact prefixLift 5527301
  have htrace : WordTrace (prefixWord ++ tailWord_5527301) baseStart_5527301 baseEnd_5527301 := by
    simpa [prefixWord, tailWord_5527301, baseEnd_5527301] using wordTrace_append hprefix tailTrace_5527301
  have hstable : (prefixWord ++ tailWord_5527301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527301).length < 2 ^ (prefixWord ++ tailWord_5527301).sum := by decide
  have hdescent : baseEnd_5527301 < baseStart_5527301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527311 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 8]
def baseStart_5527311 : Nat := 118140960795 + 5527311 * 2 ^ 59
def prefixEnd_5527311 : Nat := 4983230072969 + 3 ^ 40 * 5527311 * 2
def baseEnd_5527311 : Nat := 2838167269883529103992865

theorem tailTrace_5527311 : CollatzResearch.WordTrace tailWord_5527311 prefixEnd_5527311 2838167269883529103992865 := by
  unfold tailWord_5527311
  simp only [CollatzResearch.WordTrace]
  refine ⟨201597594078503711409061787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134398396052335807606041191 201597594078503711409061787)
  ·
    refine ⟨302396391117755567113592681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201597594078503711409061787 302396391117755567113592681)
    ·
      refine ⟨226797293338316675335194511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302396391117755567113592681 226797293338316675335194511)
      ·
        refine ⟨340195940007475013002791767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226797293338316675335194511 340195940007475013002791767)
        ·
          refine ⟨510293910011212519504187651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340195940007475013002791767 510293910011212519504187651)
          ·
            refine ⟨765440865016818779256281477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510293910011212519504187651 765440865016818779256281477)
            ·
              refine ⟨143520162190653521110552777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 765440865016818779256281477 143520162190653521110552777)
              ·
                refine ⟨107640121642990140832914583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143520162190653521110552777 107640121642990140832914583)
                ·
                  refine ⟨161460182464485211249371875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107640121642990140832914583 161460182464485211249371875)
                  ·
                    refine ⟨242190273696727816874057813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 161460182464485211249371875 242190273696727816874057813)
                    ·
                      refine ⟨2838167269883529103992865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 242190273696727816874057813 2838167269883529103992865)
                      ·
                        rfl

theorem cell23_5527311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 8].length) (baseStart_5527311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527311 prefixEnd_5527311 := by exact prefixLift 5527311
  have htrace : WordTrace (prefixWord ++ tailWord_5527311) baseStart_5527311 baseEnd_5527311 := by
    simpa [prefixWord, tailWord_5527311, baseEnd_5527311] using wordTrace_append hprefix tailTrace_5527311
  have hstable : (prefixWord ++ tailWord_5527311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527311).length < 2 ^ (prefixWord ++ tailWord_5527311).sum := by decide
  have hdescent : baseEnd_5527311 < baseStart_5527311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527321 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 1, 11]
def baseStart_5527321 : Nat := 118140960795 + 5527321 * 2 ^ 59
def prefixEnd_5527321 : Nat := 4983230072969 + 3 ^ 40 * 5527321 * 2
def baseEnd_5527321 : Nat := 946057468230024688289273

theorem tailTrace_5527321 : CollatzResearch.WordTrace tailWord_5527321 prefixEnd_5527321 946057468230024688289273 := by
  unfold tailWord_5527321
  simp only [CollatzResearch.WordTrace]
  refine ⟨201597958808467483116925817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134398639205644988744617211 201597958808467483116925817)
  ·
    refine ⟨151198469106350612337694363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201597958808467483116925817 151198469106350612337694363)
    ·
      refine ⟨226797703659525918506541545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151198469106350612337694363 226797703659525918506541545)
      ·
        refine ⟨170098277744644438879906159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226797703659525918506541545 170098277744644438879906159)
        ·
          refine ⟨255147416616966658319859239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170098277744644438879906159 255147416616966658319859239)
          ·
            refine ⟨382721124925449987479788859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255147416616966658319859239 382721124925449987479788859)
            ·
              refine ⟨574081687388174981219683289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382721124925449987479788859 574081687388174981219683289)
              ·
                refine ⟨430561265541131235914762467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 574081687388174981219683289 430561265541131235914762467)
                ·
                  refine ⟨645841898311696853872143701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 430561265541131235914762467 645841898311696853872143701)
                  ·
                    refine ⟨946057468230024688289273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 645841898311696853872143701 946057468230024688289273)
                    ·
                      rfl

theorem cell23_5527321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 11].length) (baseStart_5527321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527321 prefixEnd_5527321 := by exact prefixLift 5527321
  have htrace : WordTrace (prefixWord ++ tailWord_5527321) baseStart_5527321 baseEnd_5527321 := by
    simpa [prefixWord, tailWord_5527321, baseEnd_5527321] using wordTrace_append hprefix tailTrace_5527321
  have hstable : (prefixWord ++ tailWord_5527321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527321).length < 2 ^ (prefixWord ++ tailWord_5527321).sum := by decide
  have hdescent : baseEnd_5527321 < baseStart_5527321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527329 : List Nat := [1, 2, 3, 2, 1, 4, 3, 2, 1, 4]
def baseStart_5527329 : Nat := 118140960795 + 5527329 * 2 ^ 59
def prefixEnd_5527329 : Nat := 4983230072969 + 3 ^ 40 * 5527329 * 2
def baseEnd_5527329 : Nat := 946058837511770011189261

theorem tailTrace_5527329 : CollatzResearch.WordTrace tailWord_5527329 prefixEnd_5527329 946058837511770011189261 := by
  unfold tailWord_5527329
  simp only [CollatzResearch.WordTrace]
  refine ⟨201598250592438500483217041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134398833728292333655478027 201598250592438500483217041)
  ·
    refine ⟨151198687944328875362412781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201598250592438500483217041 151198687944328875362412781)
    ·
      refine ⟨56699507979123328260904793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151198687944328875362412781 56699507979123328260904793)
      ·
        refine ⟨42524630984342496195678595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56699507979123328260904793 42524630984342496195678595)
        ·
          refine ⟨63786946476513744293517893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42524630984342496195678595 63786946476513744293517893)
          ·
            refine ⟨11960052464346327055034605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63786946476513744293517893 11960052464346327055034605)
            ·
              refine ⟨4485019674129872645637977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11960052464346327055034605 4485019674129872645637977)
              ·
                refine ⟨3363764755597404484228483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4485019674129872645637977 3363764755597404484228483)
                ·
                  refine ⟨5045647133396106726342725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3363764755597404484228483 5045647133396106726342725)
                  ·
                    refine ⟨946058837511770011189261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5045647133396106726342725 946058837511770011189261)
                    ·
                      rfl

theorem cell23_5527329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 2, 1, 4].length) (baseStart_5527329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527329 prefixEnd_5527329 := by exact prefixLift 5527329
  have htrace : WordTrace (prefixWord ++ tailWord_5527329) baseStart_5527329 baseEnd_5527329 := by
    simpa [prefixWord, tailWord_5527329, baseEnd_5527329] using wordTrace_append hprefix tailTrace_5527329
  have hstable : (prefixWord ++ tailWord_5527329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527329).length < 2 ^ (prefixWord ++ tailWord_5527329).sum := by decide
  have hdescent : baseEnd_5527329 < baseStart_5527329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527342 : List Nat := [4, 1, 3, 2, 2, 1, 1, 3, 6]
def baseStart_5527342 : Nat := 118140960795 + 5527342 * 2 ^ 59
def prefixEnd_5527342 : Nat := 4983230072969 + 3 ^ 40 * 5527342 * 2
def baseEnd_5527342 : Nat := 315353687531535386967247

theorem tailTrace_5527342 : CollatzResearch.WordTrace tailWord_5527342 prefixEnd_5527342 315353687531535386967247 := by
  unfold tailWord_5527342
  simp only [CollatzResearch.WordTrace]
  refine ⟨25199840592673925462930035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 134399149827594269135626853 25199840592673925462930035)
  ·
    refine ⟨37799760889010888194395053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25199840592673925462930035 37799760889010888194395053)
    ·
      refine ⟨14174910333379083072898145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37799760889010888194395053 14174910333379083072898145)
      ·
        refine ⟨10631182750034312304673609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14174910333379083072898145 10631182750034312304673609)
        ·
          refine ⟨7973387062525734228505207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10631182750034312304673609 7973387062525734228505207)
          ·
            refine ⟨11960080593788601342757811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7973387062525734228505207 11960080593788601342757811)
            ·
              refine ⟨17940120890682902014136717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11960080593788601342757811 17940120890682902014136717)
              ·
                refine ⟨6727545334006088255301269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17940120890682902014136717 6727545334006088255301269)
                ·
                  refine ⟨315353687531535386967247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6727545334006088255301269 315353687531535386967247)
                  ·
                    rfl

theorem cell23_5527342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 6].length) (baseStart_5527342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527342 prefixEnd_5527342 := by exact prefixLift 5527342
  have htrace : WordTrace (prefixWord ++ tailWord_5527342) baseStart_5527342 baseEnd_5527342 := by
    simpa [prefixWord, tailWord_5527342, baseEnd_5527342] using wordTrace_append hprefix tailTrace_5527342
  have hstable : (prefixWord ++ tailWord_5527342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527342).length < 2 ^ (prefixWord ++ tailWord_5527342).sum := by decide
  have hdescent : baseEnd_5527342 < baseStart_5527342 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527368 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 3, 6]
def baseStart_5527368 : Nat := 118140960795 + 5527368 * 2 ^ 59
def prefixEnd_5527368 : Nat := 4983230072969 + 3 ^ 40 * 5527368 * 2
def baseEnd_5527368 : Nat := 946065512760278460326701

theorem tailTrace_5527368 : CollatzResearch.WordTrace tailWord_5527368 prefixEnd_5527368 946065512760278460326701 := by
  unfold tailWord_5527368
  simp only [CollatzResearch.WordTrace]
  refine ⟨100799836519648605071943379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134399782026198140095924505 100799836519648605071943379)
  ·
    refine ⟨151199754779472907607915069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 100799836519648605071943379 151199754779472907607915069)
    ·
      refine ⟨56699908042302340352968151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151199754779472907607915069 56699908042302340352968151)
      ·
        refine ⟨85049862063453510529452227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56699908042302340352968151 85049862063453510529452227)
        ·
          refine ⟨127574793095180265794178341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85049862063453510529452227 127574793095180265794178341)
          ·
            refine ⟨23920273705346299836408439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127574793095180265794178341 23920273705346299836408439)
            ·
              refine ⟨35880410558019449754612659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23920273705346299836408439 35880410558019449754612659)
              ·
                refine ⟨53820615837029174631918989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35880410558019449754612659 53820615837029174631918989)
                ·
                  refine ⟨20182730938885940486969621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53820615837029174631918989 20182730938885940486969621)
                  ·
                    refine ⟨946065512760278460326701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20182730938885940486969621 946065512760278460326701)
                    ·
                      rfl

theorem cell23_5527368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_5527368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527368 prefixEnd_5527368 := by exact prefixLift 5527368
  have htrace : WordTrace (prefixWord ++ tailWord_5527368) baseStart_5527368 baseEnd_5527368 := by
    simpa [prefixWord, tailWord_5527368, baseEnd_5527368] using wordTrace_append hprefix tailTrace_5527368
  have hstable : (prefixWord ++ tailWord_5527368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527368).length < 2 ^ (prefixWord ++ tailWord_5527368).sum := by decide
  have hdescent : baseEnd_5527368 < baseStart_5527368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527405 : List Nat := [1, 5, 1, 1, 1, 1, 3, 3, 1, 2, 4]
def baseStart_5527405 : Nat := 118140960795 + 5527405 * 2 ^ 59
def prefixEnd_5527405 : Nat := 4983230072969 + 3 ^ 40 * 5527405 * 2
def baseEnd_5527405 : Nat := 2838215537065051736217433

theorem tailTrace_5527405 : CollatzResearch.WordTrace tailWord_5527405 prefixEnd_5527405 2838215537065051736217433 := by
  unfold tailWord_5527405
  simp only [CollatzResearch.WordTrace]
  refine ⟨201601022540163165462983669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134400681693442110308655779 201601022540163165462983669)
  ·
    refine ⟨18900095863140296762154719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 201601022540163165462983669 18900095863140296762154719)
    ·
      refine ⟨28350143794710445143232079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18900095863140296762154719 28350143794710445143232079)
      ·
        refine ⟨42525215692065667714848119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28350143794710445143232079 42525215692065667714848119)
        ·
          refine ⟨63787823538098501572272179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42525215692065667714848119 63787823538098501572272179)
          ·
            refine ⟨95681735307147752358408269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63787823538098501572272179 95681735307147752358408269)
            ·
              refine ⟨35880650740180407134403101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95681735307147752358408269 35880650740180407134403101)
              ·
                refine ⟨13455244027567652675401163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35880650740180407134403101 13455244027567652675401163)
                ·
                  refine ⟨20182866041351479013101745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13455244027567652675401163 20182866041351479013101745)
                  ·
                    refine ⟨15137149531013609259826309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20182866041351479013101745 15137149531013609259826309)
                    ·
                      refine ⟨2838215537065051736217433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15137149531013609259826309 2838215537065051736217433)
                      ·
                        rfl

theorem cell23_5527405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_5527405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527405 prefixEnd_5527405 := by exact prefixLift 5527405
  have htrace : WordTrace (prefixWord ++ tailWord_5527405) baseStart_5527405 baseEnd_5527405 := by
    simpa [prefixWord, tailWord_5527405, baseEnd_5527405] using wordTrace_append hprefix tailTrace_5527405
  have hstable : (prefixWord ++ tailWord_5527405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527405).length < 2 ^ (prefixWord ++ tailWord_5527405).sum := by decide
  have hdescent : baseEnd_5527405 < baseStart_5527405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527446 : List Nat := [5, 3, 1, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_5527446 : Nat := 118140960795 + 5527446 * 2 ^ 59
def prefixEnd_5527446 : Nat := 4983230072969 + 3 ^ 40 * 5527446 * 2
def baseEnd_5527446 : Nat := 2838236589771886075804745

theorem tailTrace_5527446 : CollatzResearch.WordTrace tailWord_5527446 prefixEnd_5527446 2838236589771886075804745 := by
  unfold tailWord_5527446
  simp only [CollatzResearch.WordTrace]
  refine ⟨12600157370813414341576637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134401678622009752976817461 12600157370813414341576637)
  ·
    refine ⟨4725059014055030378091239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12600157370813414341576637 4725059014055030378091239)
    ·
      refine ⟨7087588521082545567136859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4725059014055030378091239 7087588521082545567136859)
      ·
        refine ⟨10631382781623818350705289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7087588521082545567136859 10631382781623818350705289)
        ·
          refine ⟨7973537086217863763028967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10631382781623818350705289 7973537086217863763028967)
          ·
            refine ⟨11960305629326795644543451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7973537086217863763028967 11960305629326795644543451)
            ·
              refine ⟨17940458443990193466815177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11960305629326795644543451 17940458443990193466815177)
              ·
                refine ⟨13455343832992645100111383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17940458443990193466815177 13455343832992645100111383)
                ·
                  refine ⟨20183015749488967650167075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13455343832992645100111383 20183015749488967650167075)
                  ·
                    refine ⟨30274523624233451475250613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20183015749488967650167075 30274523624233451475250613)
                    ·
                      refine ⟨2838236589771886075804745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30274523624233451475250613 2838236589771886075804745)
                      ·
                        rfl

theorem cell23_5527446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_5527446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527446 prefixEnd_5527446 := by exact prefixLift 5527446
  have htrace : WordTrace (prefixWord ++ tailWord_5527446) baseStart_5527446 baseEnd_5527446 := by
    simpa [prefixWord, tailWord_5527446, baseEnd_5527446] using wordTrace_append hprefix tailTrace_5527446
  have hstable : (prefixWord ++ tailWord_5527446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527446).length < 2 ^ (prefixWord ++ tailWord_5527446).sum := by decide
  have hdescent : baseEnd_5527446 < baseStart_5527446 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527485 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 1, 3, 5]
def baseStart_5527485 : Nat := 118140960795 + 5527485 * 2 ^ 59
def prefixEnd_5527485 : Nat := 4983230072969 + 3 ^ 40 * 5527485 * 2
def baseEnd_5527485 : Nat := 2838256615517411423217065

theorem tailTrace_5527485 : CollatzResearch.WordTrace tailWord_5527485 prefixEnd_5527485 2838256615517411423217065 := by
  unfold tailWord_5527485
  simp only [CollatzResearch.WordTrace]
  refine ⟨201603940379873339125895909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134402626919915559417263939 201603940379873339125895909)
  ·
    refine ⟨37800738821226251086105483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201603940379873339125895909 37800738821226251086105483)
    ·
      refine ⟨56701108231839376629158225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37800738821226251086105483 56701108231839376629158225)
      ·
        refine ⟨42525831173879532471868669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56701108231839376629158225 42525831173879532471868669)
        ·
          refine ⟨15947186690204824676950751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42525831173879532471868669 15947186690204824676950751)
          ·
            refine ⟨23920780035307237015426127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15947186690204824676950751 23920780035307237015426127)
            ·
              refine ⟨35881170052960855523139191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23920780035307237015426127 35881170052960855523139191)
              ·
                refine ⟨53821755079441283284708787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35881170052960855523139191 53821755079441283284708787)
                ·
                  refine ⟨80732632619161924927063181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53821755079441283284708787 80732632619161924927063181)
                  ·
                    refine ⟨30274737232185721847648693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80732632619161924927063181 30274737232185721847648693)
                    ·
                      refine ⟨2838256615517411423217065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30274737232185721847648693 2838256615517411423217065)
                      ·
                        rfl

theorem cell23_5527485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_5527485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527485 prefixEnd_5527485 := by exact prefixLift 5527485
  have htrace : WordTrace (prefixWord ++ tailWord_5527485) baseStart_5527485 baseEnd_5527485 := by
    simpa [prefixWord, tailWord_5527485, baseEnd_5527485] using wordTrace_append hprefix tailTrace_5527485
  have hstable : (prefixWord ++ tailWord_5527485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527485).length < 2 ^ (prefixWord ++ tailWord_5527485).sum := by decide
  have hdescent : baseEnd_5527485 < baseStart_5527485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527499 : List Nat := [1, 1, 1, 1, 3, 4, 2, 4, 2, 2, 2]
def baseStart_5527499 : Nat := 118140960795 + 5527499 * 2 ^ 59
def prefixEnd_5527499 : Nat := 4983230072969 + 3 ^ 40 * 5527499 * 2
def baseEnd_5527499 : Nat := 2838263804246574368442001

theorem tailTrace_5527499 : CollatzResearch.WordTrace tailWord_5527499 prefixEnd_5527499 2838263804246574368442001 := by
  unfold tailWord_5527499
  simp only [CollatzResearch.WordTrace]
  refine ⟨201604451001822619516905551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134402967334548413011270367 201604451001822619516905551)
  ·
    refine ⟨302406676502733929275358327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201604451001822619516905551 302406676502733929275358327)
    ·
      refine ⟨453610014754100893913037491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302406676502733929275358327 453610014754100893913037491)
      ·
        refine ⟨680415022131151340869556237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 453610014754100893913037491 680415022131151340869556237)
        ·
          refine ⟨255155633299181752826083589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 680415022131151340869556237 255155633299181752826083589)
          ·
            refine ⟨47841681243596578654890673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 255155633299181752826083589 47841681243596578654890673)
            ·
              refine ⟨35881260932697433991168005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47841681243596578654890673 35881260932697433991168005)
              ·
                refine ⟨6727736424880768873344001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35881260932697433991168005 6727736424880768873344001)
                ·
                  refine ⟨5045802318660576655008001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6727736424880768873344001 5045802318660576655008001)
                  ·
                    refine ⟨3784351738995432491256001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5045802318660576655008001 3784351738995432491256001)
                    ·
                      refine ⟨2838263804246574368442001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3784351738995432491256001 2838263804246574368442001)
                      ·
                        rfl

theorem cell23_5527499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 2, 2, 2].length) (baseStart_5527499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527499 prefixEnd_5527499 := by exact prefixLift 5527499
  have htrace : WordTrace (prefixWord ++ tailWord_5527499) baseStart_5527499 baseEnd_5527499 := by
    simpa [prefixWord, tailWord_5527499, baseEnd_5527499] using wordTrace_append hprefix tailTrace_5527499
  have hstable : (prefixWord ++ tailWord_5527499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527499).length < 2 ^ (prefixWord ++ tailWord_5527499).sum := by decide
  have hdescent : baseEnd_5527499 < baseStart_5527499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527510 : List Nat := [5, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3]
def baseStart_5527510 : Nat := 118140960795 + 5527510 * 2 ^ 59
def prefixEnd_5527510 : Nat := 4983230072969 + 3 ^ 40 * 5527510 * 2
def baseEnd_5527510 : Nat := 2838269452533773825404451

theorem tailTrace_5527510 : CollatzResearch.WordTrace tailWord_5527510 prefixEnd_5527510 2838269452533773825404451 := by
  unfold tailWord_5527510
  simp only [CollatzResearch.WordTrace]
  refine ⟨12600303262798923024722249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 134403234803188512263703989 12600303262798923024722249)
  ·
    refine ⟨9450227447099192268541687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12600303262798923024722249 9450227447099192268541687)
    ·
      refine ⟨14175341170648788402812531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9450227447099192268541687 14175341170648788402812531)
      ·
        refine ⟨21263011755973182604218797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14175341170648788402812531 21263011755973182604218797)
        ·
          refine ⟨7973629408489943476582049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21263011755973182604218797 7973629408489943476582049)
          ·
            refine ⟨5980222056367457607436537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7973629408489943476582049 5980222056367457607436537)
            ·
              refine ⟨4485166542275593205577403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5980222056367457607436537 4485166542275593205577403)
              ·
                refine ⟨6727749813413389808366105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4485166542275593205577403 6727749813413389808366105)
                ·
                  refine ⟨5045812360060042356274579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6727749813413389808366105 5045812360060042356274579)
                  ·
                    refine ⟨7568718540090063534411869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5045812360060042356274579 7568718540090063534411869)
                    ·
                      refine ⟨2838269452533773825404451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7568718540090063534411869 2838269452533773825404451)
                      ·
                        rfl

theorem cell23_5527510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_5527510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527510 prefixEnd_5527510 := by exact prefixLift 5527510
  have htrace : WordTrace (prefixWord ++ tailWord_5527510) baseStart_5527510 baseEnd_5527510 := by
    simpa [prefixWord, tailWord_5527510, baseEnd_5527510] using wordTrace_append hprefix tailTrace_5527510
  have hstable : (prefixWord ++ tailWord_5527510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527510).length < 2 ^ (prefixWord ++ tailWord_5527510).sum := by decide
  have hdescent : baseEnd_5527510 < baseStart_5527510 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527545 : List Nat := [1, 2, 1, 3, 1, 4, 1, 2, 1, 2, 5]
def baseStart_5527545 : Nat := 118140960795 + 5527545 * 2 ^ 59
def prefixEnd_5527545 : Nat := 4983230072969 + 3 ^ 40 * 5527545 * 2
def baseEnd_5527545 : Nat := 2838287424356681188466789

theorem tailTrace_5527545 : CollatzResearch.WordTrace tailWord_5527545 prefixEnd_5527545 2838287424356681188466789 := by
  unfold tailWord_5527545
  simp only [CollatzResearch.WordTrace]
  refine ⟨201606128759655969373080089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134404085839770646248720059 201606128759655969373080089)
  ·
    refine ⟨151204596569741977029810067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201606128759655969373080089 151204596569741977029810067)
    ·
      refine ⟨226806894854612965544715101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151204596569741977029810067 226806894854612965544715101)
      ·
        refine ⟨85052585570479862079268163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 226806894854612965544715101 85052585570479862079268163)
        ·
          refine ⟨127578878355719793118902245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85052585570479862079268163 127578878355719793118902245)
          ·
            refine ⟨23921039691697461209794171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127578878355719793118902245 23921039691697461209794171)
            ·
              refine ⟨35881559537546191814691257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23921039691697461209794171 35881559537546191814691257)
              ·
                refine ⟨26911169653159643861018443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35881559537546191814691257 26911169653159643861018443)
                ·
                  refine ⟨40366754479739465791527665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26911169653159643861018443 40366754479739465791527665)
                  ·
                    refine ⟨30275065859804599343645749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40366754479739465791527665 30275065859804599343645749)
                    ·
                      refine ⟨2838287424356681188466789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30275065859804599343645749 2838287424356681188466789)
                      ·
                        rfl

theorem cell23_5527545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_5527545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527545 prefixEnd_5527545 := by exact prefixLift 5527545
  have htrace : WordTrace (prefixWord ++ tailWord_5527545) baseStart_5527545 baseEnd_5527545 := by
    simpa [prefixWord, tailWord_5527545, baseEnd_5527545] using wordTrace_append hprefix tailTrace_5527545
  have hstable : (prefixWord ++ tailWord_5527545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527545).length < 2 ^ (prefixWord ++ tailWord_5527545).sum := by decide
  have hdescent : baseEnd_5527545 < baseStart_5527545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527556 : List Nat := [2, 3, 2, 4, 1, 1, 1, 4, 5]
def baseStart_5527556 : Nat := 118140960795 + 5527556 * 2 ^ 59
def prefixEnd_5527556 : Nat := 4983230072969 + 3 ^ 40 * 5527556 * 2
def baseEnd_5527556 : Nat := 315365896960431182825471

theorem tailTrace_5527556 : CollatzResearch.WordTrace tailWord_5527556 prefixEnd_5527556 315365896960431182825471 := by
  unfold tailWord_5527556
  simp only [CollatzResearch.WordTrace]
  refine ⟨100803264981308059125865261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134404353308410745501153681 100803264981308059125865261)
  ·
    refine ⟨37801224367990522172199473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100803264981308059125865261 37801224367990522172199473)
    ·
      refine ⟨28350918275992891629149605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37801224367990522172199473 28350918275992891629149605)
      ·
        refine ⟨5315797176748667180465551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28350918275992891629149605 5315797176748667180465551)
        ·
          refine ⟨7973695765123000770698327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5315797176748667180465551 7973695765123000770698327)
          ·
            refine ⟨11960543647684501156047491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7973695765123000770698327 11960543647684501156047491)
            ·
              refine ⟨17940815471526751734071237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11960543647684501156047491 17940815471526751734071237)
              ·
                refine ⟨3363902900911265950138357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17940815471526751734071237 3363902900911265950138357)
                ·
                  refine ⟨315365896960431182825471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3363902900911265950138357 315365896960431182825471)
                  ·
                    rfl

theorem cell23_5527556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 4, 5].length) (baseStart_5527556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527556 prefixEnd_5527556 := by exact prefixLift 5527556
  have htrace : WordTrace (prefixWord ++ tailWord_5527556) baseStart_5527556 baseEnd_5527556 := by
    simpa [prefixWord, tailWord_5527556, baseEnd_5527556] using wordTrace_append hprefix tailTrace_5527556
  have hstable : (prefixWord ++ tailWord_5527556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527556).length < 2 ^ (prefixWord ++ tailWord_5527556).sum := by decide
  have hdescent : baseEnd_5527556 < baseStart_5527556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527589 : List Nat := [1, 3, 1, 2, 2, 5, 1, 1, 2, 1, 4]
def baseStart_5527589 : Nat := 118140960795 + 5527589 * 2 ^ 59
def prefixEnd_5527589 : Nat := 4983230072969 + 3 ^ 40 * 5527589 * 2
def baseEnd_5527589 : Nat := 2838310017505479016316587

theorem tailTrace_5527589 : CollatzResearch.WordTrace tailWord_5527589 prefixEnd_5527589 2838310017505479016316587 := by
  unfold tailWord_5527589
  simp only [CollatzResearch.WordTrace]
  refine ⟨201607733571496564887681821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134405155714331043258454547 201607733571496564887681821)
  ·
    refine ⟨75602900089311211832880683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 201607733571496564887681821 75602900089311211832880683)
    ·
      refine ⟨113404350133966817749321025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75602900089311211832880683 113404350133966817749321025)
      ·
        refine ⟨85053262600475113311990769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113404350133966817749321025 85053262600475113311990769)
        ·
          refine ⟨63789946950356334983993077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85053262600475113311990769 63789946950356334983993077)
          ·
            refine ⟨5980307526595906404749351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63789946950356334983993077 5980307526595906404749351)
            ·
              refine ⟨8970461289893859607124027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5980307526595906404749351 8970461289893859607124027)
              ·
                refine ⟨13455691934840789410686041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8970461289893859607124027 13455691934840789410686041)
                ·
                  refine ⟨10091768951130592058014531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13455691934840789410686041 10091768951130592058014531)
                  ·
                    refine ⟨15137653426695888087021797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10091768951130592058014531 15137653426695888087021797)
                    ·
                      refine ⟨2838310017505479016316587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15137653426695888087021797 2838310017505479016316587)
                      ·
                        rfl

theorem cell23_5527589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_5527589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527589 prefixEnd_5527589 := by exact prefixLift 5527589
  have htrace : WordTrace (prefixWord ++ tailWord_5527589) baseStart_5527589 baseEnd_5527589 := by
    simpa [prefixWord, tailWord_5527589, baseEnd_5527589] using wordTrace_append hprefix tailTrace_5527589
  have hstable : (prefixWord ++ tailWord_5527589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527589).length < 2 ^ (prefixWord ++ tailWord_5527589).sum := by decide
  have hdescent : baseEnd_5527589 < baseStart_5527589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527615 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 6]
def baseStart_5527615 : Nat := 118140960795 + 5527615 * 2 ^ 59
def prefixEnd_5527615 : Nat := 4983230072969 + 3 ^ 40 * 5527615 * 2
def baseEnd_5527615 : Nat := 2838323368002495914591467

theorem tailTrace_5527615 : CollatzResearch.WordTrace tailWord_5527615 prefixEnd_5527615 2838323368002495914591467 := by
  unfold tailWord_5527615
  simp only [CollatzResearch.WordTrace]
  refine ⟨201608681869402371328128299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134405787912934914218752199 201608681869402371328128299)
  ·
    refine ⟨302413022804103556992192449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201608681869402371328128299 302413022804103556992192449)
    ·
      refine ⟨226809767103077667744144337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302413022804103556992192449 226809767103077667744144337)
      ·
        refine ⟨170107325327308250808108253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226809767103077667744144337 170107325327308250808108253)
        ·
          refine ⟨63790246997740594053040595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170107325327308250808108253 63790246997740594053040595)
          ·
            refine ⟨95685370496610891079560893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63790246997740594053040595 95685370496610891079560893)
            ·
              refine ⟨35882013936229084154835335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 95685370496610891079560893 35882013936229084154835335)
              ·
                refine ⟨53823020904343626232253003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35882013936229084154835335 53823020904343626232253003)
                ·
                  refine ⟨80734531356515439348379505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53823020904343626232253003 80734531356515439348379505)
                  ·
                    refine ⟨60550898517386579511284629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80734531356515439348379505 60550898517386579511284629)
                    ·
                      refine ⟨2838323368002495914591467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60550898517386579511284629 2838323368002495914591467)
                      ·
                        rfl

theorem cell23_5527615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_5527615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527615 prefixEnd_5527615 := by exact prefixLift 5527615
  have htrace : WordTrace (prefixWord ++ tailWord_5527615) baseStart_5527615 baseEnd_5527615 := by
    simpa [prefixWord, tailWord_5527615, baseEnd_5527615] using wordTrace_append hprefix tailTrace_5527615
  have hstable : (prefixWord ++ tailWord_5527615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527615).length < 2 ^ (prefixWord ++ tailWord_5527615).sum := by decide
  have hdescent : baseEnd_5527615 < baseStart_5527615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527639 : List Nat := [1, 1, 3, 2, 2, 1, 4, 2, 3, 1, 3]
def baseStart_5527639 : Nat := 118140960795 + 5527639 * 2 ^ 59
def prefixEnd_5527639 : Nat := 4983230072969 + 3 ^ 40 * 5527639 * 2
def baseEnd_5527639 : Nat := 2838335691538203820691357

theorem tailTrace_5527639 : CollatzResearch.WordTrace tailWord_5527639 prefixEnd_5527639 2838335691538203820691357 := by
  unfold tailWord_5527639
  simp only [CollatzResearch.WordTrace]
  refine ⟨201609557221315423427001971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134406371480876948951334647 201609557221315423427001971)
  ·
    refine ⟨302414335831973135140502957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201609557221315423427001971 302414335831973135140502957)
    ·
      refine ⟨113405375936989925677688609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302414335831973135140502957 113405375936989925677688609)
      ·
        refine ⟨85054031952742444258266457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113405375936989925677688609 85054031952742444258266457)
        ·
          refine ⟨63790523964556833193699843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85054031952742444258266457 63790523964556833193699843)
          ·
            refine ⟨95685785946835249790549765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63790523964556833193699843 95685785946835249790549765)
            ·
              refine ⟨17941084865031609335728081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 95685785946835249790549765 17941084865031609335728081)
              ·
                refine ⟨13455813648773707001796061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17941084865031609335728081 13455813648773707001796061)
                ·
                  refine ⟨5045930118290140125673523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13455813648773707001796061 5045930118290140125673523)
                  ·
                    refine ⟨7568895177435210188510285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5045930118290140125673523 7568895177435210188510285)
                    ·
                      refine ⟨2838335691538203820691357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7568895177435210188510285 2838335691538203820691357)
                      ·
                        rfl

theorem cell23_5527639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 3, 1, 3].length) (baseStart_5527639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527639 prefixEnd_5527639 := by exact prefixLift 5527639
  have htrace : WordTrace (prefixWord ++ tailWord_5527639) baseStart_5527639 baseEnd_5527639 := by
    simpa [prefixWord, tailWord_5527639, baseEnd_5527639] using wordTrace_append hprefix tailTrace_5527639
  have hstable : (prefixWord ++ tailWord_5527639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527639).length < 2 ^ (prefixWord ++ tailWord_5527639).sum := by decide
  have hdescent : baseEnd_5527639 < baseStart_5527639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527649 : List Nat := [1, 2, 3, 1, 1, 2, 1, 5, 2, 3, 2]
def baseStart_5527649 : Nat := 118140960795 + 5527649 * 2 ^ 59
def prefixEnd_5527649 : Nat := 4983230072969 + 3 ^ 40 * 5527649 * 2
def baseEnd_5527649 : Nat := 2838340826344748781566311

theorem tailTrace_5527649 : CollatzResearch.WordTrace tailWord_5527649 prefixEnd_5527649 2838340826344748781566311 := by
  unfold tailWord_5527649
  simp only [CollatzResearch.WordTrace]
  refine ⟨201609921951279195134866001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134406614634186130089910667 201609921951279195134866001)
  ·
    refine ⟨151207441463459396351149501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201609921951279195134866001 151207441463459396351149501)
    ·
      refine ⟨56702790548797273631681063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151207441463459396351149501 56702790548797273631681063)
      ·
        refine ⟨85054185823195910447521595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56702790548797273631681063 85054185823195910447521595)
        ·
          refine ⟨127581278734793865671282393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85054185823195910447521595 127581278734793865671282393)
          ·
            refine ⟨95685959051095399253461795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127581278734793865671282393 95685959051095399253461795)
            ·
              refine ⟨143528938576643098880192693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95685959051095399253461795 143528938576643098880192693)
              ·
                refine ⟨13455837991560290520018065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 143528938576643098880192693 13455837991560290520018065)
                ·
                  refine ⟨10091878493670217890013549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13455837991560290520018065 10091878493670217890013549)
                  ·
                    refine ⟨3784454435126331708755081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10091878493670217890013549 3784454435126331708755081)
                    ·
                      refine ⟨2838340826344748781566311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3784454435126331708755081 2838340826344748781566311)
                      ·
                        rfl

theorem cell23_5527649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 3, 2].length) (baseStart_5527649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527649 prefixEnd_5527649 := by exact prefixLift 5527649
  have htrace : WordTrace (prefixWord ++ tailWord_5527649) baseStart_5527649 baseEnd_5527649 := by
    simpa [prefixWord, tailWord_5527649, baseEnd_5527649] using wordTrace_append hprefix tailTrace_5527649
  have hstable : (prefixWord ++ tailWord_5527649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527649).length < 2 ^ (prefixWord ++ tailWord_5527649).sum := by decide
  have hdescent : baseEnd_5527649 < baseStart_5527649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527650 : List Nat := [3, 3, 2, 2, 2, 2, 1, 3, 1, 4]
def baseStart_5527650 : Nat := 118140960795 + 5527650 * 2 ^ 59
def prefixEnd_5527650 : Nat := 4983230072969 + 3 ^ 40 * 5527650 * 2
def baseEnd_5527650 : Nat := 946113779941801092551269

theorem tailTrace_5527650 : CollatzResearch.WordTrace tailWord_5527650 prefixEnd_5527650 946113779941801092551269 := by
  unfold tailWord_5527650
  simp only [CollatzResearch.WordTrace]
  refine ⟨50402489606068893076413101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134406638949517048203768269 50402489606068893076413101)
  ·
    refine ⟨18900933602275834903654913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50402489606068893076413101 18900933602275834903654913)
    ·
      refine ⟨14175700201706876177741185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18900933602275834903654913 14175700201706876177741185)
      ·
        refine ⟨10631775151280157133305889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14175700201706876177741185 10631775151280157133305889)
        ·
          refine ⟨7973831363460117849979417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10631775151280157133305889 7973831363460117849979417)
          ·
            refine ⟨5980373522595088387484563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7973831363460117849979417 5980373522595088387484563)
            ·
              refine ⟨8970560283892632581226845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5980373522595088387484563 8970560283892632581226845)
              ·
                refine ⟨3363960106459737217960067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8970560283892632581226845 3363960106459737217960067)
                ·
                  refine ⟨5045940159689605826940101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3363960106459737217960067 5045940159689605826940101)
                  ·
                    refine ⟨946113779941801092551269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5045940159689605826940101 946113779941801092551269)
                    ·
                      rfl

theorem cell23_5527650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_5527650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527650 prefixEnd_5527650 := by exact prefixLift 5527650
  have htrace : WordTrace (prefixWord ++ tailWord_5527650) baseStart_5527650 baseEnd_5527650 := by
    simpa [prefixWord, tailWord_5527650, baseEnd_5527650] using wordTrace_append hprefix tailTrace_5527650
  have hstable : (prefixWord ++ tailWord_5527650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527650).length < 2 ^ (prefixWord ++ tailWord_5527650).sum := by decide
  have hdescent : baseEnd_5527650 < baseStart_5527650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527666 : List Nat := [3, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2]
def baseStart_5527666 : Nat := 118140960795 + 5527666 * 2 ^ 59
def prefixEnd_5527666 : Nat := 4983230072969 + 3 ^ 40 * 5527666 * 2
def baseEnd_5527666 : Nat := 2838349555515875215053733

theorem tailTrace_5527666 : CollatzResearch.WordTrace tailWord_5527666 prefixEnd_5527666 2838349555515875215053733 := by
  unfold tailWord_5527666
  simp only [CollatzResearch.WordTrace]
  refine ⟨50402635498054401759558713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 134407027994811738025489901 50402635498054401759558713)
  ·
    refine ⟨37801976623540801319669035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50402635498054401759558713 37801976623540801319669035)
    ·
      refine ⟨56702964935311201979503553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37801976623540801319669035 56702964935311201979503553)
      ·
        refine ⟨42527223701483401484627665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56702964935311201979503553 42527223701483401484627665)
        ·
          refine ⟨31895417776112551113470749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42527223701483401484627665 31895417776112551113470749)
          ·
            refine ⟨11960781666042206667551531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31895417776112551113470749 11960781666042206667551531)
            ·
              refine ⟨17941172499063310001327297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11960781666042206667551531 17941172499063310001327297)
              ·
                refine ⟨13455879374297482500995473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17941172499063310001327297 13455879374297482500995473)
                ·
                  refine ⟨10091909530723111875746605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13455879374297482500995473 10091909530723111875746605)
                  ·
                    refine ⟨3784466074021166953404977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10091909530723111875746605 3784466074021166953404977)
                    ·
                      refine ⟨2838349555515875215053733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3784466074021166953404977 2838349555515875215053733)
                      ·
                        rfl

theorem cell23_5527666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_5527666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527666 prefixEnd_5527666 := by exact prefixLift 5527666
  have htrace : WordTrace (prefixWord ++ tailWord_5527666) baseStart_5527666 baseEnd_5527666 := by
    simpa [prefixWord, tailWord_5527666, baseEnd_5527666] using wordTrace_append hprefix tailTrace_5527666
  have hstable : (prefixWord ++ tailWord_5527666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527666).length < 2 ^ (prefixWord ++ tailWord_5527666).sum := by decide
  have hdescent : baseEnd_5527666 < baseStart_5527666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527689 : List Nat := [1, 2, 1, 1, 4, 2, 3, 3, 2, 4]
def baseStart_5527689 : Nat := 118140960795 + 5527689 * 2 ^ 59
def prefixEnd_5527689 : Nat := 4983230072969 + 3 ^ 40 * 5527689 * 2
def baseEnd_5527689 : Nat := 946120455190309541688709

theorem tailTrace_5527689 : CollatzResearch.WordTrace tailWord_5527689 prefixEnd_5527689 946120455190309541688709 := by
  unfold tailWord_5527689
  simp only [CollatzResearch.WordTrace]
  refine ⟨201611380871134281966322121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134407587247422854644214747 201611380871134281966322121)
  ·
    refine ⟨151208535653350711474741591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 201611380871134281966322121 151208535653350711474741591)
    ·
      refine ⟨226812803480026067212112387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151208535653350711474741591 226812803480026067212112387)
      ·
        refine ⟨340219205220039100818168581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226812803480026067212112387 340219205220039100818168581)
        ·
          refine ⟨63791100978757331403406609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 340219205220039100818168581 63791100978757331403406609)
          ·
            refine ⟨47843325734067998552554957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63791100978757331403406609 47843325734067998552554957)
            ·
              refine ⟨17941247150275499457208109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47843325734067998552554957 17941247150275499457208109)
              ·
                refine ⟨6727967681353312296453041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17941247150275499457208109 6727967681353312296453041)
                ·
                  refine ⟨5045975761014984222339781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6727967681353312296453041 5045975761014984222339781)
                  ·
                    refine ⟨946120455190309541688709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5045975761014984222339781 946120455190309541688709)
                    ·
                      rfl

theorem cell23_5527689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 2, 4].length) (baseStart_5527689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527689 prefixEnd_5527689 := by exact prefixLift 5527689
  have htrace : WordTrace (prefixWord ++ tailWord_5527689) baseStart_5527689 baseEnd_5527689 := by
    simpa [prefixWord, tailWord_5527689, baseEnd_5527689] using wordTrace_append hprefix tailTrace_5527689
  have hstable : (prefixWord ++ tailWord_5527689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527689).length < 2 ^ (prefixWord ++ tailWord_5527689).sum := by decide
  have hdescent : baseEnd_5527689 < baseStart_5527689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527700 : List Nat := [2, 4, 2, 3, 1, 1, 2, 1, 2, 3, 2]
def baseStart_5527700 : Nat := 118140960795 + 5527700 * 2 ^ 59
def prefixEnd_5527700 : Nat := 4983230072969 + 3 ^ 40 * 5527700 * 2
def baseEnd_5527700 : Nat := 2838367013858128082028577

theorem tailTrace_5527700 : CollatzResearch.WordTrace tailWord_5527700 prefixEnd_5527700 2838367013858128082028577 := by
  unfold tailWord_5527700
  simp only [CollatzResearch.WordTrace]
  refine ⟨100805891037047215422486277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134407854716062953896648369 100805891037047215422486277)
  ·
    refine ⟨18901104569446352891716177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 100805891037047215422486277 18901104569446352891716177)
    ·
      refine ⟨14175828427084764668787133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18901104569446352891716177 14175828427084764668787133)
      ·
        refine ⟨5315935660156786750795175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14175828427084764668787133 5315935660156786750795175)
        ·
          refine ⟨7973903490235180126192763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5315935660156786750795175 7973903490235180126192763)
          ·
            refine ⟨11960855235352770189289145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7973903490235180126192763 11960855235352770189289145)
            ·
              refine ⟨8970641426514577641966859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11960855235352770189289145 8970641426514577641966859)
              ·
                refine ⟨13455962139771866462950289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8970641426514577641966859 13455962139771866462950289)
                ·
                  refine ⟨10091971604828899847212717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13455962139771866462950289 10091971604828899847212717)
                  ·
                    refine ⟨3784489351810837442704769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10091971604828899847212717 3784489351810837442704769)
                    ·
                      refine ⟨2838367013858128082028577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3784489351810837442704769 2838367013858128082028577)
                      ·
                        rfl

theorem cell23_5527700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_5527700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527700 prefixEnd_5527700 := by exact prefixLift 5527700
  have htrace : WordTrace (prefixWord ++ tailWord_5527700) baseStart_5527700 baseEnd_5527700 := by
    simpa [prefixWord, tailWord_5527700, baseEnd_5527700] using wordTrace_append hprefix tailTrace_5527700
  have hstable : (prefixWord ++ tailWord_5527700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527700).length < 2 ^ (prefixWord ++ tailWord_5527700).sum := by decide
  have hdescent : baseEnd_5527700 < baseStart_5527700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527709 : List Nat := [1, 4, 2, 1, 1, 4, 1, 2, 1, 2, 4]
def baseStart_5527709 : Nat := 118140960795 + 5527709 * 2 ^ 59
def prefixEnd_5527709 : Nat := 4983230072969 + 3 ^ 40 * 5527709 * 2
def baseEnd_5527709 : Nat := 2838371635184018546816035

theorem tailTrace_5527709 : CollatzResearch.WordTrace tailWord_5527709 prefixEnd_5527709 2838371635184018546816035 := by
  unfold tailWord_5527709
  simp only [CollatzResearch.WordTrace]
  refine ⟨201612110331061825382050181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134408073554041216921366787 201612110331061825382050181)
  ·
    refine ⟨37802270687074092259134409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 201612110331061825382050181 37802270687074092259134409)
    ·
      refine ⟨28351703015305569194350807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37802270687074092259134409 28351703015305569194350807)
      ·
        refine ⟨42527554522958353791526211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28351703015305569194350807 42527554522958353791526211)
        ·
          refine ⟨63791331784437530687289317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42527554522958353791526211 63791331784437530687289317)
          ·
            refine ⟨11960874709582037003866747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63791331784437530687289317 11960874709582037003866747)
            ·
              refine ⟨17941312064373055505800121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11960874709582037003866747 17941312064373055505800121)
              ·
                refine ⟨13455984048279791629350091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17941312064373055505800121 13455984048279791629350091)
                ·
                  refine ⟨20183976072419687444025137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13455984048279791629350091 20183976072419687444025137)
                  ·
                    refine ⟨15137982054314765583018853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20183976072419687444025137 15137982054314765583018853)
                    ·
                      refine ⟨2838371635184018546816035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15137982054314765583018853 2838371635184018546816035)
                      ·
                        rfl

theorem cell23_5527709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_5527709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527709 prefixEnd_5527709 := by exact prefixLift 5527709
  have htrace : WordTrace (prefixWord ++ tailWord_5527709) baseStart_5527709 baseEnd_5527709 := by
    simpa [prefixWord, tailWord_5527709, baseEnd_5527709] using wordTrace_append hprefix tailTrace_5527709
  have hstable : (prefixWord ++ tailWord_5527709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527709).length < 2 ^ (prefixWord ++ tailWord_5527709).sum := by decide
  have hdescent : baseEnd_5527709 < baseStart_5527709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527716 : List Nat := [2, 3, 1, 2, 4, 2, 1, 1, 1, 1, 5]
def baseStart_5527716 : Nat := 118140960795 + 5527716 * 2 ^ 59
def prefixEnd_5527716 : Nat := 4983230072969 + 3 ^ 40 * 5527716 * 2
def baseEnd_5527716 : Nat := 2838375229548600019428503

theorem tailTrace_5527716 : CollatzResearch.WordTrace tailWord_5527716 prefixEnd_5527716 2838375229548600019428503 := by
  unfold tailWord_5527716
  simp only [CollatzResearch.WordTrace]
  refine ⟨100806182821018232788777501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 134408243761357643718370001 100806182821018232788777501)
  ·
    refine ⟨37802318557881837295791563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 100806182821018232788777501 37802318557881837295791563)
    ·
      refine ⟨56703477836822755943687345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37802318557881837295791563 56703477836822755943687345)
      ·
        refine ⟨42527608377617066957765509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56703477836822755943687345 42527608377617066957765509)
        ·
          refine ⟨7973926570803200054581033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42527608377617066957765509 7973926570803200054581033)
          ·
            refine ⟨5980444928102400040935775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7973926570803200054581033 5980444928102400040935775)
            ·
              refine ⟨8970667392153600061403663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5980444928102400040935775 8970667392153600061403663)
              ·
                refine ⟨13456001088230400092105495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8970667392153600061403663 13456001088230400092105495)
                ·
                  refine ⟨20184001632345600138158243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13456001088230400092105495 20184001632345600138158243)
                  ·
                    refine ⟨30276002448518400207237365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20184001632345600138158243 30276002448518400207237365)
                    ·
                      refine ⟨2838375229548600019428503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30276002448518400207237365 2838375229548600019428503)
                      ·
                        rfl

theorem cell23_5527716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_5527716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527716 prefixEnd_5527716 := by exact prefixLift 5527716
  have htrace : WordTrace (prefixWord ++ tailWord_5527716) baseStart_5527716 baseEnd_5527716 := by
    simpa [prefixWord, tailWord_5527716, baseEnd_5527716] using wordTrace_append hprefix tailTrace_5527716
  have hstable : (prefixWord ++ tailWord_5527716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527716).length < 2 ^ (prefixWord ++ tailWord_5527716).sum := by decide
  have hdescent : baseEnd_5527716 < baseStart_5527716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5527719 : List Nat := [1, 1, 6, 2, 3, 10]
def baseStart_5527719 : Nat := 118140960795 + 5527719 * 2 ^ 59
def prefixEnd_5527719 : Nat := 4983230072969 + 3 ^ 40 * 5527719 * 2
def baseEnd_5527719 : Nat := 11680562839467339537823

theorem tailTrace_5527719 : CollatzResearch.WordTrace tailWord_5527719 prefixEnd_5527719 11680562839467339537823 := by
  unfold tailWord_5527719
  simp only [CollatzResearch.WordTrace]
  refine ⟨201612475061025597089914211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 134408316707350398059942807 201612475061025597089914211)
  ·
    refine ⟨302418712591538395634871317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201612475061025597089914211 302418712591538395634871317)
    ·
      refine ⟨14175877152728362295384593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 302418712591538395634871317 14175877152728362295384593)
      ·
        refine ⟨10631907864546271721538445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14175877152728362295384593 10631907864546271721538445)
        ·
          refine ⟨3986965449204851895576917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10631907864546271721538445 3986965449204851895576917)
          ·
            refine ⟨11680562839467339537823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3986965449204851895576917 11680562839467339537823)
            ·
              rfl

theorem cell23_5527719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 10].length) (baseStart_5527719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5527719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5527719 prefixEnd_5527719 := by exact prefixLift 5527719
  have htrace : WordTrace (prefixWord ++ tailWord_5527719) baseStart_5527719 baseEnd_5527719 := by
    simpa [prefixWord, tailWord_5527719, baseEnd_5527719] using wordTrace_append hprefix tailTrace_5527719
  have hstable : (prefixWord ++ tailWord_5527719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5527719).length < 2 ^ (prefixWord ++ tailWord_5527719).sum := by decide
  have hdescent : baseEnd_5527719 < baseStart_5527719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5527719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
